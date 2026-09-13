import Tracker.Types
import Tracker.Plan
import Tracker.Graph
import Tracker.Cache

/-!
# `tracker check`

Import the project, look every node id up, and record what the compiled library says. This is
the only part of the tool that touches Lean's environment.

## Performance

Two facts about a declaration are transitive — the axioms it rests on, and the tracked ids its
proof reaches through untracked constants — and both are shared by every declaration that uses it.
`Reach` computes each once per constant for the whole run, by memoized depth-first search, so the
work is linear in the union of the closures rather than in their sum: `Lean.collectAxioms` walks
the whole closure of a declaration afresh on every call, and on a library standing on Mathlib
that made a check of eight thousand nodes take a quarter of an hour.

Two lesser traps, recorded because both cost more than the searches themselves:
`Environment.allImportedModuleNames` rebuilds an array of every imported module on each call, so
the module of a constant is looked up through a table built once; and sorting names by their
printed form converts two strings per comparison, so only what goes into the cache is sorted.
-/

open Lean Meta

namespace Tracker

/-- Whether a module belongs to the project, i.e. sits under one of the roots. -/
def isProjectModule (roots : Array Name) (m : Name) : Bool :=
  roots.any fun r => r.isPrefixOf m

/--
The memo tables of one check, shared by every node.

* `moduleNames` — the imported modules by index, `isProject` beside it: whether each is the
  project's. Both are read once from the environment.
* `axiomsOf c` — the axioms in the transitive closure of `c`, as a bitmask over `axiomNames`.
* `reachOf c`, for an *untracked project* constant `c` — the tracked ids reachable from `c` through
  untracked project constants.

The searches that fill the two memos visit every constant once, which is sound because the
dependency graph of a consistent environment is acyclic.
-/
structure Reach where
  env : Environment
  tracked : Std.HashMap Name Node
  moduleNames : Array Name
  isProject : Array Bool
  axiomsOf : IO.Ref (Std.HashMap Name Nat)
  axiomIndex : IO.Ref (Std.HashMap Name Nat)
  axiomNames : IO.Ref (Array Name)
  reachOf : IO.Ref (Std.HashMap Name (Array Name))

namespace Reach

/-- Empty memos over an environment. -/
def init (env : Environment) (roots : Array Name) (tracked : Std.HashMap Name Node) :
    IO Reach := do
  let moduleNames := env.allImportedModuleNames
  return {
    env, tracked, moduleNames
    isProject := moduleNames.map (isProjectModule roots)
    axiomsOf := ← IO.mkRef {}, axiomIndex := ← IO.mkRef {}, axiomNames := ← IO.mkRef #[]
    reachOf := ← IO.mkRef {} }

/-- The module a constant was declared in, if it was imported. -/
def moduleOf (r : Reach) (c : Name) : Option Name :=
  (r.env.getModuleIdxFor? c).bind fun i => r.moduleNames[i.toNat]?

/-- Whether a constant was declared in one of the project's modules. -/
def isProjectConst (r : Reach) (c : Name) : Bool :=
  (r.env.getModuleIdxFor? c).any fun i => r.isProject[i.toNat]?.getD false

/-- A constant that belongs to the project but is not a node: the ones a search passes through. -/
def isPassThrough (r : Reach) (c : Name) : Bool :=
  !r.tracked.contains c && r.isProjectConst c

/-- The constants a constant's type and value use. -/
def used (r : Reach) (c : Name) : Array Name :=
  match r.env.find? c with
  | some ci => ci.getUsedConstantsAsSet.toArray
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
of `Lean.collectAxioms`, computed once per constant instead of once per node.
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
  return out.qsort (·.toString < ·.toString)

/--
Tracked ids reachable from an untracked project constant `c` through untracked project constants,
memoized over the whole run and unsorted.
-/
partial def reach (r : Reach) (c : Name) : IO (Array Name) := do
  if let some out := (← r.reachOf.get)[c]? then return out
  r.reachOf.modify (·.insert c #[])
  let mut acc : Std.HashSet Name := {}
  for d in r.used c do
    if r.tracked.contains d then acc := acc.insert d
    else if r.isPassThrough d then acc := acc.insertMany (← r.reach d)
  let out := acc.toArray
  r.reachOf.modify (·.insert c out)
  return out

/--
Tracked ids reachable from the node `start`: pass through untracked constants that belong to the
project, stop at tracked ids and at anything outside the project. A node that uses itself (a
recursive definition) does not list itself. Sorted, as everything written to the cache is.
-/
def reachTracked (r : Reach) (start : Name) : IO (Array Name) := do
  let mut acc : Std.HashSet Name := {}
  for d in r.used start do
    if r.tracked.contains d then acc := acc.insert d
    else if r.isPassThrough d then acc := acc.insertMany (← r.reach d)
  return (acc.erase start).toArray.qsort (·.toString < ·.toString)

end Reach

/-- Resolve one id. Runs in `CoreM` for ranges and pretty printing. -/
def resolveDecl (r : Reach) (id : Name) : CoreM DeclInfo := do
  let env ← getEnv
  match env.find? id with
  | none => return { id }
  | some ci =>
    let axioms ← r.axiomList (← r.axioms id)
    let range ← findDeclarationRanges? id
    let sig ← try
        let f ← MetaM.run' (PrettyPrinter.ppSignature id)
        pure (f.fmt.pretty 100)
      catch _ => pure ""
    let uses ← r.reachTracked id
    let doc := (← findDocString? env id).map trim
    return {
      id, found := true
      module := r.moduleOf id
      line := range.map (·.range.pos.line)
      isTheorem := ci.isTheorem
      isAxiom := ci.isAxiom
      hasSorry := axioms.contains ``sorryAx
      axioms
      axiomsOk := axioms.all fun a => standardAxioms.contains a
      uses, signature := sig, doc }

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

/-- Check every node against an environment the project was imported into. -/
def checkEnv (env : Environment) (plan : Plan) (roots : Array Name)
    (loadExts : Bool) (previous : Option Cache) : IO Cache := do
  let t1 ← IO.monoMsNow
  let r ← Reach.init env roots plan.nodes
  let ids := plan.nodes.toArray.map (·.1) |>.qsort (·.toString < ·.toString)
  let mut decls : Array DeclInfo := #[]
  for id in ids do
    decls := decls.push (← runCore env (resolveDecl r id) id.getPrefix)
  let t2 ← IO.monoMsNow
  IO.eprintln s!"resolved {ids.size} ids in {t2 - t1} ms"
  -- the project's modules: fingerprinted, so that later commands can tell when the build
  -- changed, and with the first `/-! … -/` block as the module's description
  let mut modules : Array ModuleRec := #[]
  for m in r.moduleNames, isProj in r.isProject do
    if isProj then
      let olean ← findOLean m
      let doc := (getModuleDoc? env m).bind fun ds => ds[0]?.map fun d => trim d.doc
      modules := modules.push {
        module := m, olean := olean.toString, hash := (← oleanFingerprint olean).getD "", doc }
  -- states, and regressions against the previous cache
  let cache : Cache := { roots, loadExts, planHash := plan.hash, modules, decls }
  let view := mkView plan (some cache)
  let states := ids.map fun id => ({ id, state := (view.state id).toString } : StateRec)
  let prev : Std.HashMap Name String := match previous with
    | some p => p.states.foldl (init := {}) fun m s => m.insert s.id s.state
    | none => {}
  let regressions := states.filterMap fun s =>
    match prev[s.id]?.bind NodeState.parse?, NodeState.parse? s.state with
    | some b, some a =>
      if b != .wrong && a != .wrong && a.rank < b.rank then
        some ({ id := s.id, before := b.toString, after := a.toString } : Regression)
      else none
    | _, _ => none
  return { cache with states, regressions }

/-- Import the project and check every node. -/
unsafe def runCheck (plan : Plan) (roots : Array Name)
    (loadExts : Bool) (previous : Option Cache) : IO Cache := do
  checkEnv (← importProject roots loadExts) plan roots loadExts previous

end Tracker
