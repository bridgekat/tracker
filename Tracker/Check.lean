import Tracker.Types
import Tracker.Plan
import Tracker.Graph
import Tracker.Cache

/-!
# `tracker check`

Import the project, look every node id up, and record what the compiled library says. This is
the only part of the tool that touches Lean's environment.
-/

open Lean Meta

namespace Tracker

/-- The module a constant was declared in, if it was imported. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).bind fun i => env.allImportedModuleNames[i.toNat]?

/-- Whether a module belongs to the project, i.e. sits under one of the roots. -/
def isProjectModule (roots : Array Name) (m : Name) : Bool :=
  roots.any fun r => r.isPrefixOf m

/--
Tracked ids reachable from `start`'s constants: pass through untracked constants that belong to
the project, stop at tracked ids and at anything outside the project. `used` memoizes the
constants of each project constant across calls.
-/
partial def reachTracked (env : Environment) (roots : Array Name) (tracked : Std.HashMap Name Node)
    (used : IO.Ref (Std.HashMap Name (Array Name))) (start : Name) : IO (Array Name) := do
  let consts (c : Name) : IO (Array Name) := do
    if let some cs := (← used.get)[c]? then return cs
    let cs := match env.find? c with
      | some ci => ci.getUsedConstantsAsSet.toArray
      | none => #[]
    used.modify (·.insert c cs)
    return cs
  let mut out := #[]
  let mut seen : Std.HashSet Name := {}
  let mut queue := ← consts start
  while h : queue.size > 0 do
    let c := queue[queue.size - 1]
    queue := queue.pop
    if c == start || seen.contains c then continue
    seen := seen.insert c
    if tracked.contains c then
      out := out.push c
    else match moduleOf env c with
      | some m => if isProjectModule roots m then queue := queue ++ (← consts c)
      | none => pure ()
  return out.qsort (·.toString < ·.toString)

/-- Resolve one id. Runs in `CoreM` for axioms, ranges, and pretty printing. -/
def resolveDecl (roots : Array Name) (tracked : Std.HashMap Name Node)
    (used : IO.Ref (Std.HashMap Name (Array Name))) (id : Name) : CoreM DeclInfo := do
  let env ← getEnv
  match env.find? id with
  | none => return { id }
  | some ci =>
    let axioms ← collectAxioms id
    let range ← findDeclarationRanges? id
    let sig ← try
        let f ← MetaM.run' (PrettyPrinter.ppSignature id)
        pure (f.fmt.pretty 100)
      catch _ => pure ""
    let uses ← reachTracked env roots tracked used id
    let doc := (← findDocString? env id).map trim
    return {
      id, found := true
      module := moduleOf env id
      line := range.map (·.range.pos.line)
      isTheorem := ci.isTheorem
      isAxiom := ci.isAxiom
      hasSorry := axioms.contains ``sorryAx
      axioms
      axiomsOk := axioms.all fun a => standardAxioms.contains a
      uses, signature := sig, doc }

/-- Import the project and check every node. -/
unsafe def runCheck (plan : Plan) (roots : Array Name)
    (loadExts : Bool) (previous : Option Cache) : IO Cache := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules (roots.map fun r => { module := r }) {} (trustLevel := 1024)
    (loadExts := loadExts)
  let t1 ← IO.monoMsNow
  IO.eprintln s!"imported {roots} in {t1 - t0} ms ({env.allImportedModuleNames.size} modules)"
  let used ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let ids := plan.nodes.toArray.map (·.1) |>.qsort (·.toString < ·.toString)
  let mut decls : Array DeclInfo := #[]
  for id in ids do
    let ctx : Core.Context := {
      fileName := "<tracker>", fileMap := default, currNamespace := id.getPrefix }
    let (d, _) ← (resolveDecl roots plan.nodes used id).toIO ctx { env }
    decls := decls.push d
  let t2 ← IO.monoMsNow
  IO.eprintln s!"resolved {ids.size} ids in {t2 - t1} ms"
  -- the project's modules: fingerprinted, so that later commands can tell when the build
  -- changed, and with the first `/-! … -/` block as the module's description
  let mut modules : Array ModuleRec := #[]
  for m in env.allImportedModuleNames do
    if isProjectModule roots m then
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

end Tracker
