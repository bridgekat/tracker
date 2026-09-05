import Tracker.Types
import Tracker.Toml

/-!
# Loading the plan

Read every `*.toml` file under the tracker directory as a group named by its path there,
resolve node ids and suggested dependencies, and index everything. Errors are collected, not
thrown, so that one bad file does not hide the others.
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
  return {
    id := resolveId ns rawId, kind, desc, source, wrong, group := group,
    line := lineOf ictx ref, rawId, rawDeps }

open Toml in
private def decodeGroup (name : String) (path : System.FilePath) (ictx : Parser.InputContext)
    (t : Lake.Toml.Table) : Lake.Toml.EDecodeM Group := do
  let kind := (← str? t `kind).getD "task"
  let title := (← str? t `title).getD (groupStem name)
  let module ← name? t `module
  let ns ← name? t `namespace
  let notes ← str? t `notes
  let mut nodes : Array Node := #[]
  -- one bad node does not hide the others: errors accumulate, decoding goes on
  for (nt, ref) in ← tables t `node do
    if let some n ← recover (decodeNode name ns ictx nt ref) then
      nodes := nodes.push n
  return { name, kind, title, module, «namespace» := ns, notes, nodes, path }

/-- Load one group file: its errors, and the group if it could be decoded at all. -/
def loadGroup (name : String) (path : System.FilePath) : IO (Array String × Option Group) := do
  match ← Toml.load path with
  | .error e => return (#[s!"{path}:{e}"], none)
  | .ok l =>
    let (errs, g?) := Toml.run l.ictx (decodeGroup name path l.ictx l.table)
    return (errs.map fun e => s!"{path}:{e}", g?)

/--
The group files under `dir` as (name, path): the `.toml` files of a directory, then those of its
subdirectories, each in sorted order, so that a group comes before its children.
-/
partial def groupFiles (dir : System.FilePath) (base : String := "") :
    IO (Array (String × System.FilePath)) := do
  let entries := (← dir.readDir).qsort (·.fileName < ·.fileName)
  let mut out := #[]
  for e in entries do
    if e.path.extension == some "toml" && !(← e.path.isDir) then
      out := out.push (base ++ e.path.fileStem.getD e.fileName, e.path)
  for e in entries do
    if ← e.path.isDir then
      out := out ++ (← groupFiles e.path (base ++ e.fileName ++ "/"))
  return out

/-- Load every group under a directory and resolve dependencies. -/
def loadPlan (dir : System.FilePath) : IO Plan := do
  unless ← dir.isDir do
    throw <| IO.userError s!"no tracker directory at {dir}"
  let mut plan : Plan := {}
  let mut h : UInt64 := 0
  for (name, f) in ← groupFiles dir do
    h := mixHash h (mixHash name.hash (← IO.FS.readFile f).hash)
    let (errs, g?) ← loadGroup name f
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
  -- a directory holds the children of the group file beside it, which must exist
  let mut missing : Array String := #[]
  for g in plan.groups do
    let mut above := groupEnclosing? g.name
    while true do
      match above with
      | none => break
      | some p =>
        if !plan.groupIdx.contains p && !missing.contains p then missing := missing.push p
        above := groupEnclosing? p
  for p in missing.qsort (· < ·) do
    let m := s!"{dir / System.FilePath.mk p}: directory has no group file {p}.toml beside it"
    plan := { plan with errors := plan.errors.push m }
  return { plan with hash := hex h }

/-- Display an id relative to its group's namespace. -/
def Plan.shortId (p : Plan) (n : Node) : String :=
  match p.group? n.group >>= (·.namespace) with
  | some ns => if ns.isPrefixOf n.id then (n.id.replacePrefix ns .anonymous).toString else n.id.toString
  | none => n.id.toString

end Tracker
