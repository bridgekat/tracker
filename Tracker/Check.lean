import Tracker.Types
import Tracker.Plan
import Tracker.Cache

/-!
# `tracker check`

Import the project, collect its declarations (`moduleDecls`, by the filter `isHandWritten`), look
up every planned declaration's id, and record what the compiled library says. This is the only
part of the tool that touches Lean's environment. Every other constant of the project is looked through by
the searches, never recorded.

## Performance

Two facts about a declaration are transitive — the axioms it rests on, and the declarations its
proof reaches through the constants in between — and both are shared by every declaration that
uses it. `Reach` computes each once per constant for the whole run, by memoized depth-first
search, so the work is linear in the union of the closures rather than in their sum:
`Lean.collectAxioms` walks the whole closure of a declaration afresh on every call, and on a
library standing on Mathlib that made a check of eight thousand planned declarations take a
quarter of an hour.

Two lesser traps, recorded because both cost more than the searches themselves:
`Environment.allImportedModuleNames` rebuilds an array of every imported module on each call, so
the module of a constant is looked up through a table built once; and sorting names by their
printed form converts two strings per comparison, so names are printed once before sorting.
-/

open Lean Meta

namespace Tracker

/-- Whether a module belongs to the project, i.e. sits under one of the roots. -/
def isProjectModule (roots : Array Name) (m : Name) : Bool :=
  roots.any fun r => r.isPrefixOf m

/-- Whether a constant could be a declaration: written by someone, not generated beside one. -/
def isHandWritten (id : Name) : CoreM Bool := do
  let env ← getEnv
  if id.isInternalDetail || id.hasMacroScopes then return false
  let some ci := env.find? id | return false
  unless ci matches .defnInfo .. | .thmInfo .. | .inductInfo .. | .opaqueInfo .. do return false
  if isAuxRecursor env id || isNoConfusion env id || (← isProjectionFn id) then return false
  return !(← isAutoDeclOrPrivate_Internal id)

private def startsBefore (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

/-- Whether one declaration's text encloses another's, and so was what generated it. -/
private def encloses (outer inner : DeclarationRange) : Bool :=
  let le (a b : Position) := !startsBefore b a
  le outer.pos inner.pos && le inner.endPos outer.endPos
    && (outer.pos != inner.pos || outer.endPos != inner.endPos)

/--
The declarations of one module: the hand-written constants whose text stands on its own. One
whose text sits inside another's was generated beside it, as `deriving` and `where` generate
theirs, and one with no text at all was written nowhere.
-/
def moduleDecls (m : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | return #[]
  let some data := env.header.moduleData[idx.toNat]? | return #[]
  let mut placed : Array (Name × DeclarationRange) := #[]
  for id in data.constNames do
    if ← isHandWritten id then
      if let some r ← findDeclarationRanges? id then placed := placed.push (id, r.range)
  return placed.filterMap fun (id, r) => if placed.any (encloses ·.2 r) then none else some id

/--
The memo tables of one check, shared by every search.

* `moduleNames` — the imported modules by index, `isProject` beside it: whether each is the
  project's. Both are read once from the environment.
* `axiomsOf c` — the axioms in the transitive closure of `c`, as a bitmask over `axiomNames`.
-/
structure Reach where
  env : Environment
  moduleNames : Array Name
  isProject : Array Bool
  axiomsOf : IO.Ref (Std.HashMap Name Nat)
  axiomIndex : IO.Ref (Std.HashMap Name Nat)
  axiomNames : IO.Ref (Array Name)

/--
A search for the constants of `targets` reachable from a constant, passing through the other
constants of the project and stopping at anything outside it. `memo c`, for a constant `c` passed
through, is the answer from `c`. The search visits every constant once, which is sound because
the graph `Reach.used` walks is acyclic: on a cycle, the constant first reached would be
memoized with a partial answer.
-/
structure Closure where
  targets : Std.HashSet Name
  memo : IO.Ref (Std.HashMap Name (Array Name))

def Closure.new (targets : Std.HashSet Name) : IO Closure := do
  return { targets, memo := ← IO.mkRef {} }

namespace Reach

/-- Empty memos over an environment. -/
def init (env : Environment) (roots : Array Name) : IO Reach := do
  let moduleNames := env.allImportedModuleNames
  return {
    env, moduleNames
    isProject := moduleNames.map (isProjectModule roots)
    axiomsOf := ← IO.mkRef {}, axiomIndex := ← IO.mkRef {}, axiomNames := ← IO.mkRef #[] }

/-- The module a constant was declared in, if it was imported. -/
def moduleOf (r : Reach) (c : Name) : Option Name :=
  (r.env.getModuleIdxFor? c).bind fun i => r.moduleNames[i.toNat]?

/-- Whether a constant was declared in one of the project's modules. -/
def isProjectConst (r : Reach) (c : Name) : Bool :=
  (r.env.getModuleIdxFor? c).any fun i => r.isProject[i.toNat]?.getD false

/-- The project's modules, in import order. -/
def projectModules (r : Reach) : Array Name := Id.run do
  let mut out := #[]
  for m in r.moduleNames, p in r.isProject do
    if p then out := out.push m
  return out

/--
The constants a constant uses: those in its type and value, and for an inductive type those in
its constructors' types, but never itself, its constructors or the other types of its mutual
block. `ConstantInfo.getUsedConstantsAsSet` has an inductive type use its constructors and a
constructor use itself, which makes cycles of every inductive type; with those left out the graph
is acyclic, as the memoized searches need it to be.
-/
def used (r : Reach) (c : Name) : Array Name :=
  match r.env.find? c with
  | some (.inductInfo val) => Id.run do
    let block := val.all.flatMap fun t => match r.env.find? t with
      | some (.inductInfo v) => t :: v.ctors
      | _ => [t]
    let mut out := val.type.getUsedConstantsAsSet
    for ctor in val.ctors do
      if let some ci := r.env.find? ctor then out := out ++ ci.type.getUsedConstantsAsSet
    return out.toArray.filter (!block.contains ·)
  | some (.ctorInfo val) => (val.type.getUsedConstantsAsSet.erase c).toArray
  | some ci => (ci.getUsedConstantsAsSet.erase c).toArray
  | none => #[]

/-- The bit of an axiom in the masks of `axioms`, allocated on first sight. -/
def axiomBit (r : Reach) (a : Name) : IO Nat := do
  if let some i := (← r.axiomIndex.get)[a]? then return 1 <<< i
  let i := (← r.axiomNames.get).size
  r.axiomNames.modify (·.push a)
  r.axiomIndex.modify (·.insert a i)
  return 1 <<< i

/--
The axioms in the transitive closure of `c`, as a bitmask, memoized over the whole run: the answer
of `Lean.collectAxioms`, computed once per constant instead of once per declaration.
-/
partial def axioms (r : Reach) (c : Name) : IO Nat := do
  if let some m := (← r.axiomsOf.get)[c]? then return m
  -- marked before descending, so that a (never expected) cycle ends with a partial answer
  r.axiomsOf.modify (·.insert c 0)
  let mut m : Nat := 0
  match r.env.find? c with
  | some (.axiomInfo _) => m := ← r.axiomBit c
  | some _ =>
    for d in r.used c do
      m := m ||| (← r.axioms d)
  | none => pure ()
  r.axiomsOf.modify (·.insert c m)
  return m

/-- The names in an axiom mask, sorted. -/
def axiomList (r : Reach) (m : Nat) : IO (Array Name) := do
  let names ← r.axiomNames.get
  let mut out := #[]
  for i in [:names.size] do
    if m.testBit i then out := out.push names[i]!
  return sortNames out

/-- The targets reachable from `c`, a project constant that is not one, memoized and unsorted. -/
partial def through (r : Reach) (cl : Closure) (c : Name) : IO (Array Name) := do
  if let some out := (← cl.memo.get)[c]? then return out
  cl.memo.modify (·.insert c #[])
  let mut acc : Std.HashSet Name := {}
  for d in r.used c do
    if cl.targets.contains d then acc := acc.insert d
    else if r.isProjectConst d then acc := acc.insertMany (← r.through cl d)
  let out := acc.toArray
  cl.memo.modify (·.insert c out)
  return out

/--
The targets reachable from `start`: pass through the other constants of the project, stop at
targets and at anything outside the project. A declaration that uses itself (a recursive
definition) does not list itself. Unsorted.
-/
def reach (r : Reach) (cl : Closure) (start : Name) : IO (Array Name) := do
  let mut acc : Std.HashSet Name := {}
  for d in r.used start do
    if cl.targets.contains d then acc := acc.insert d
    else if r.isProjectConst d then acc := acc.insertMany (← r.through cl d)
  return (acc.erase start).toArray

end Reach

/--
Resolve one id: what it is, where, what it rests on, and the entries it refers to through the
other constants of the project, as ids. Runs in `CoreM` for ranges and pretty printing.
-/
def resolveEntry (r : Reach) (all : Closure) (declaration : Bool) (id : Name) :
    CoreM (CacheEntry × Option Name × Array Name) := do
  let env ← getEnv
  match env.find? id with
  | none => return ({ id, declaration }, none, #[])
  | some ci =>
    let axioms ← r.axiomList (← r.axioms id)
    let range ← findDeclarationRanges? id
    let sig ← try
        let f ← MetaM.run' (PrettyPrinter.ppSignature id)
        pure (f.fmt.pretty 100)
      catch _ => pure ""
    let kind : DeclKind := if ci.isTheorem then .theorem else if ci.isAxiom then .axiom else .definition
    let entry : CacheEntry := {
      id, declaration, kind
      line := range.map (·.range.pos.line)
      axioms := if axioms.all standardAxioms.contains then #[] else axioms
      signature := sig
      doc := (← findDocString? env id).map trim }
    return (entry, r.moduleOf id, ← r.reach all id)

/-- Import the project's root modules, running their initializers unless `loadExts` is false. -/
unsafe def importProject (roots : Array Name) (loadExts : Bool) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules (roots.map fun r => { module := r }) {} (trustLevel := 1024)
    (loadExts := loadExts)
  let t1 ← IO.monoMsNow
  IO.eprintln s!"imported {roots} in {t1 - t0} ms ({env.header.modules.size} modules)"
  return env

/-- Run a `CoreM` against an imported environment. -/
def runCore (env : Environment) (x : CoreM α) (ns : Name := .anonymous) : IO α := do
  let ctx : Core.Context := { fileName := "<tracker>", fileMap := default, currNamespace := ns }
  return (← x.toIO ctx { env }).1

/--
The planned declarations whose state went down since the previous cache. One marked `wrong` now is
left out, whatever its declaration did.
-/
def regressionsSince (plan : Plan) (previous : Option Cache) (entries : Array CacheEntry) :
    Array Regression := Id.run do
  let some p := previous | return #[]
  let stateOf (es : Array CacheEntry) : Std.HashMap Name NodeState :=
    es.foldl (init := {}) fun m e => m.insert e.id e.state
  let before := stateOf p.entries
  let after := stateOf entries
  let mut out := #[]
  for id in sortNames (plan.nodes.fold (init := #[]) fun a id _ => a.push id) do
    if ((plan.node? id).bind (·.wrong)).isSome then continue
    let some b := before[id]? | continue
    let a := after.getD id .«open»
    if a.rank < b.rank then out := out.push { id, before := b.toString, after := a.toString }
  return out

/-- Check the declarations and every planned declaration against an environment the project was
imported into. -/
def checkEnv (env : Environment) (plan : Plan) (roots : Array Name)
    (loadExts : Bool) (previous : Option Cache) : IO Cache := do
  let t1 ← IO.monoMsNow
  let r ← Reach.init env roots
  let projectModules := sortNames r.projectModules
  -- the declarations, and the planned declarations beside them, which need not be declarations
  let mut declSet : Std.HashSet Name := {}
  for m in projectModules do
    declSet := declSet.insertMany (← runCore env (moduleDecls m))
  let plannedSet : Std.HashSet Name := plan.nodes.fold (init := {}) fun s id _ => s.insert id
  let targets := declSet.insertMany plannedSet
  let ids := sortNames targets.toArray
  let index : Std.HashMap Name Nat := ids.foldl (init := {}) fun m id => m.insert id m.size
  let all ← Closure.new targets
  -- the project's modules first, fingerprinted so that later commands can tell when the build
  -- changed, and with the first `/-! … -/` block as the module's description; then any other
  -- module an entry is in, by name only
  let mut modules : Array ModuleRec := #[]
  for m in projectModules do
    let olean ← findOLean m
    let doc := (getModuleDoc? env m).bind fun ds => ds[0]?.map fun d => trim d.doc
    modules := modules.push {
      name := m, olean := some olean.toString, hash := ← oleanFingerprint olean, doc }
  let mut moduleIdx : Std.HashMap Name Nat :=
    modules.foldl (init := {}) fun m rec => m.insert rec.name m.size
  let mut entries : Array CacheEntry := #[]
  for id in ids do
    let (e, m?, refs) ← runCore env (resolveEntry r all (declSet.contains id) id) id.getPrefix
    let mut module := none
    if let some m := m? then
      unless moduleIdx.contains m do
        moduleIdx := moduleIdx.insert m modules.size
        modules := modules.push { name := m }
      module := moduleIdx[m]?
    entries := entries.push { e with module, refs := (refs.filterMap (index[·]?)).qsort (· < ·) }
  let t2 ← IO.monoMsNow
  IO.eprintln s!"resolved {ids.size} ids ({declSet.size} declarations, {plannedSet.size} planned \
    declarations) in {t2 - t1} ms"
  return { roots, loadExts, modules, entries, regressions := regressionsSince plan previous entries }

/-- Import the project and check it. -/
unsafe def runCheck (plan : Plan) (roots : Array Name)
    (loadExts : Bool) (previous : Option Cache) : IO Cache := do
  checkEnv (← importProject roots loadExts) plan roots loadExts previous

end Tracker
