import Tracker.Types
import Tracker.Toml

/-!
# Loading the plan

Read every `*.toml` file in the tracker directory as a group, resolve node ids and suggested
dependencies, and index everything. Errors are collected, not thrown, so that one bad file does
not hide the others.
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
private def decodeNode (group : String) (ns : Option Name) (ictx : Parser.InputContext)
    (nt : Lake.Toml.Table) (ref : Syntax) : Lake.Toml.EDecodeM Node := do
  let rawId ← str nt `id ref
  let kindS ← str nt `kind ref
  let some kind := NodeKind.parse? kindS
    | fail ref s!"unknown node kind '{kindS}' (use definition or theorem)"
  let desc ← match ← str? nt `desc with
    | some d => pure d
    | none => str nt `description ref
  let rawDeps ← strArray? nt `deps
  let source ← str? nt `source
  let wrong ← str? nt `wrong
  return {
    id := resolveId ns rawId, kind, desc, source, wrong, group := group,
    line := lineOf ictx ref, rawId, rawDeps }

open Toml in
private def decodeGroup (name : String) (path : System.FilePath) (ictx : Parser.InputContext)
    (t : Lake.Toml.Table) : Lake.Toml.EDecodeM Group := do
  let kind := (← str? t `kind).getD "task"
  let title := (← str? t `title).getD name
  let parent ← str? t `parent
  let module ← name? t `module
  let ns ← name? t `namespace
  let notes ← str? t `notes
  let mut nodes : Array Node := #[]
  -- one bad node does not hide the others: errors accumulate, decoding goes on
  for (nt, ref) in ← tables t `node do
    if let some n ← recover (decodeNode name ns ictx nt ref) then
      nodes := nodes.push n
  return { name, kind, title, parent, module, «namespace» := ns, notes, nodes, path }

/-- Load one group file: its errors, and the group if it could be decoded at all. -/
def loadGroup (path : System.FilePath) : IO (Array String × Option Group) := do
  let name := path.fileStem.getD path.toString
  match ← Toml.load path with
  | .error e => return (#[s!"{path}:{e}"], none)
  | .ok l =>
    let (errs, g?) := Toml.run l.ictx (decodeGroup name path l.ictx l.table)
    return (errs.map fun e => s!"{path}:{e}", g?)

/-- Load every group in a directory and resolve dependencies. -/
def loadPlan (dir : System.FilePath) : IO Plan := do
  unless ← dir.isDir do
    throw <| IO.userError s!"no tracker directory at {dir}"
  let entries ← dir.readDir
  let files := entries.filterMap fun e =>
    if e.path.extension == some "toml" then some e.path else none
  let files := files.qsort (·.toString < ·.toString)
  let mut plan : Plan := {}
  for f in files do
    let (errs, g?) ← loadGroup f
    plan := { plan with errors := plan.errors ++ errs }
    if let some g := g? then
      plan := { plan with
        groupIdx := plan.groupIdx.insert g.name plan.groups.size
        groups := plan.groups.push g }
  -- index nodes, catching duplicate ids
  for g in plan.groups do
    for n in g.nodes do
      match plan.nodes[n.id]? with
      | some other =>
        let m := s!"{g.path}:{n.line}: duplicate id {n.id}, also in group {other.group}"
        plan := { plan with errors := plan.errors.push m }
      | none => plan := { plan with nodes := plan.nodes.insert n.id n }
  -- resolve suggested dependencies
  let mut groups := #[]
  for g in plan.groups do
    let mut nodes := #[]
    for n in g.nodes do
      let mut deps := #[]
      for raw in n.rawDeps do
        match (depCandidates g.namespace raw).find? plan.nodes.contains with
        | some d =>
          if d == n.id then
            let m := s!"{g.path}:{n.line}: {n.id} depends on itself"
            plan := { plan with errors := plan.errors.push m }
          else deps := deps.push d
        | none =>
          let m := s!"{g.path}:{n.line}: unknown dependency '{raw}' of {n.id}"
          plan := { plan with errors := plan.errors.push m }
      nodes := nodes.push { n with deps }
    groups := groups.push { g with nodes }
  plan := { plan with groups }
  -- re-index with resolved deps
  let mut nodeMap : Std.HashMap Name Node := {}
  for g in plan.groups do
    for n in g.nodes do
      if !nodeMap.contains n.id then nodeMap := nodeMap.insert n.id n
  plan := { plan with nodes := nodeMap }
  -- parents must exist
  for g in plan.groups do
    if let some p := g.parent then
      unless plan.groupIdx.contains p do
        let m := s!"{g.path}: parent group '{p}' does not exist"
        plan := { plan with errors := plan.errors.push m }
  return plan

/-- Display an id relative to its group's namespace. -/
def Plan.shortId (p : Plan) (n : Node) : String :=
  match p.group? n.group >>= (·.namespace) with
  | some ns => if ns.isPrefixOf n.id then (n.id.replacePrefix ns .anonymous).toString else n.id.toString
  | none => n.id.toString

end Tracker
