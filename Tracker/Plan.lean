import Tracker.Types
import Tracker.Toml

/-!
# Loading the plan

Read every `*.toml` file under the plan directory as a module plan, of the module whose source
file sits at the same path under the project root (`Numbers/Odd.toml` plans the module named
`Numbers.Odd`), resolve planned node ids and suggested dependencies, and index everything. Errors
are collected, not thrown, so that one bad file does not hide the others. No plan directory is an
empty plan.
-/

open Lean

namespace Tracker

/-- Resolve an id as written relative to a namespace, honouring `_root_`. -/
def resolveId (ns : Option Name) (raw : String) : Name :=
  if raw.startsWith "_root_." then (raw.drop 7).toName
  else match ns with
    | some ns => ns ++ raw.toName
    | none => raw.toName

/-- The candidates a written dependency may refer to, most specific first. -/
def depCandidates (ns : Option Name) (raw : String) : List Name :=
  if raw.startsWith "_root_." then [(raw.drop 7).toName]
  else match ns with
    | some ns => [ns ++ raw.toName, raw.toName]
    | none => [raw.toName]

open Toml in
private def decodeNode (module : Name) (ns : Option Name) (ictx : Parser.InputContext)
    (nt : Lake.Toml.Table) (ref : Syntax) : Lake.Toml.EDecodeM Node := do
  let rawId ← str nt `id ref
  unknownKeys nt [`id, `kind, `desc, `description, `deps, `source, `wrong, `deprecated]
    s!"node {rawId} has id, kind, desc, deps, source, wrong and deprecated"
  let kind ← match ← str? nt `kind with
    | none => pure none
    | some kindS => match NodeKind.parse? kindS with
      | some k => pure (some k)
      | none => fail ref s!"unknown node kind '{kindS}' (use definition or theorem)"
  let desc ← match ← str? nt `desc with
    | some d => pure (some d)
    | none => str? nt `description
  let rawDeps ← strArray? nt `deps
  let source ← str? nt `source
  let wrong ← str? nt `wrong
  let deprecated ← str? nt `deprecated
  return {
    id := resolveId ns rawId, kind, desc, source, wrong, deprecated, module,
    line := lineOf ictx ref, rawId, rawDeps }

open Toml in
private def decodeModulePlan (module : Name) (path : System.FilePath)
    (ictx : Parser.InputContext) (t : Lake.Toml.Table) : Lake.Toml.EDecodeM ModulePlan := do
  unknownKeys t [`namespace, `desc, `description, `node]
    "a module plan has namespace, desc and [[node]] tables"
  let ns ← name? t `namespace
  let desc ← match ← str? t `desc with
    | some d => pure (some d)
    | none => str? t `description
  let mut nodes : Array Node := #[]
  -- one bad node does not hide the others: errors accumulate, decoding goes on
  for (nt, ref) in ← tables t `node do
    if let some n ← recover (decodeNode module ns ictx nt ref) then
      nodes := nodes.push n
  return { module, «namespace» := ns, desc, nodes, path }

/-- Load one module plan: its errors, and the module plan if it could be decoded at all. -/
def loadModulePlan (module : Name) (path : System.FilePath) :
    IO (Array String × Option ModulePlan) := do
  match ← Toml.load path with
  | .error e => return (#[s!"{path}:{e}"], none)
  | .ok l =>
    let (errs, mp?) := Toml.run l.ictx (decodeModulePlan module path l.ictx l.table)
    return (errs.map fun e => s!"{path}:{e}", mp?)

/--
The module plans under `dir` as (path components under `dir` without `.toml`, file): the `.toml`
files of a directory, then those of its subdirectories, each in sorted order.
-/
partial def planFiles (dir : System.FilePath) (above : List String := []) :
    IO (Array (List String × System.FilePath)) := do
  let entries := (← dir.readDir).qsort (·.fileName < ·.fileName)
  let mut out := #[]
  for e in entries do
    if e.path.extension == some "toml" && !(← e.path.isDir) then
      out := out.push (above ++ [e.path.fileStem.getD e.fileName], e.path)
  for e in entries do
    if ← e.path.isDir then
      out := out ++ (← planFiles e.path (above ++ [e.fileName]))
  return out

/-- Load every module plan under a directory and resolve dependencies. -/
def loadPlan (dir : System.FilePath) : IO Plan := do
  unless ← dir.isDir do return {}
  let mut plan : Plan := {}
  for (components, f) in ← planFiles dir do
    let (errs, mp?) ← loadModulePlan (planModuleName components) f
    plan := { plan with errors := plan.errors ++ errs }
    if let some mp := mp? then
      plan := { plan with
        moduleIdx := plan.moduleIdx.insert mp.module plan.modules.size
        modules := plan.modules.push mp }
  -- index planned nodes, catching duplicate ids
  for mp in plan.modules do
    for n in mp.nodes do
      match plan.nodes[n.id]? with
      | some other =>
        let m := s!"{mp.path}:{n.line}: duplicate id {n.id}, also planned in {other.module}"
        plan := { plan with errors := plan.errors.push m }
      | none => plan := { plan with nodes := plan.nodes.insert n.id n }
  -- resolve suggested dependencies
  let mut modules := #[]
  for mp in plan.modules do
    let mut nodes := #[]
    for n in mp.nodes do
      let mut deps := #[]
      for raw in n.rawDeps do
        match (depCandidates mp.namespace raw).find? plan.nodes.contains with
        | some d =>
          if d == n.id then
            let m := s!"{mp.path}:{n.line}: {n.id} depends on itself"
            plan := { plan with errors := plan.errors.push m }
          else deps := deps.push d
        | none =>
          let m := s!"{mp.path}:{n.line}: unknown dependency '{raw}' of {n.id}"
          plan := { plan with errors := plan.errors.push m }
      nodes := nodes.push { n with deps }
    modules := modules.push { mp with nodes }
  plan := { plan with modules }
  -- re-index with resolved deps
  let mut nodeMap : Std.HashMap Name Node := {}
  for mp in plan.modules do
    for n in mp.nodes do
      if !nodeMap.contains n.id then nodeMap := nodeMap.insert n.id n
  return { plan with nodes := nodeMap }

/-- Display a planned node's id relative to its module plan's namespace. -/
def Plan.shortId (p : Plan) (n : Node) : String :=
  match p.modulePlan? n.module >>= (·.namespace) with
  | some ns => if ns.isPrefixOf n.id then (n.id.replacePrefix ns .anonymous).toString else n.id.toString
  | none => n.id.toString

end Tracker
