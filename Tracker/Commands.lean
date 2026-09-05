import Tracker.Types
import Tracker.Plan
import Tracker.Graph
import Tracker.Cache

/-!
# Commands

`status`, `ready`, `show`, `lint`, `graph`. Each takes a `View` and prints; `--json` variants
print `Lean.Json`.
-/

open Lean

namespace Tracker

/-- Pad or truncate to width. -/
def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ "".pushn ' ' (w - s.length)

def indent (s : String) (n : Nat := 2) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map fun l => if l.isEmpty then l else "".pushn ' ' n ++ l)

private def firstLine (s : String) : String :=
  (s.splitOn "\n").headD ""

/-- Group rows in tree order: roots first, children under their parents. -/
partial def groupOrder (v : View) (from? : Option String := none) : Array (String × Nat) := Id.run do
  let roots : Array String := match from? with
    | some g => #[g]
    | none => v.plan.groups.filterMap fun (g : Group) => if g.parent.isNone then some g.name else none
  let mut out := #[]
  let mut stack : List (String × Nat) := roots.toList.map (·, 0)
  while true do
    match stack with
    | [] => break
    | (g, d) :: rest =>
      out := out.push (g, d)
      let kids := (v.children.getD g #[]).toList.map (·, d + 1)
      stack := kids ++ rest
  return out

def noCacheWarning (v : View) : IO Unit := do
  if v.cache.isNone then
    IO.eprintln "warning: no check cache; every node reads as open. Run `tracker check` first."

def isBlank (s : String) : Bool := s.all Char.isWhitespace

-- ## status

def groupJson (v : View) (name : String) : Json :=
  let c := v.counts name
  let g := v.plan.group? name
  Json.mkObj [
    ("group", name), ("kind", toJson (g.map (·.kind))), ("title", toJson (g.map (·.title))),
    ("parent", toJson (g.bind (·.parent))),
    ("proved", c.proved), ("stated", c.stated), ("open", c.open), ("axioms", c.axioms),
    ("wrong", c.wrong), ("done", v.groupDone name), ("ready", v.groupReady name)]

def status (v : View) (group? : Option String) (json : Bool) : IO UInt32 := do
  if let some g := group? then
    unless v.plan.groupIdx.contains g do
      IO.eprintln s!"no group named '{g}'"
      return 1
  let rows := groupOrder v group?
  if json then
    let groups := rows.map fun (g, _) => groupJson v g
    let regs := (v.cache.map (·.regressions)).getD #[]
    IO.println (Json.mkObj [
      ("commit", toJson (v.cache.map (·.commit))),
      ("groups", toJson groups), ("regressions", toJson regs)]).pretty
    return 0
  noCacheWarning v
  if let some c := v.cache then
    if !c.commit.isEmpty then IO.println s!"checked at {c.commit}"
  IO.println s!"{pad "group" 34} {pad "kind" 9} {pad "proved" 7} {pad "stated" 7} {pad "open" 6} {pad "wrong" 6} {pad "axioms" 7} state"
  for (g, depth) in rows do
    let c := v.counts g
    let kind := (v.plan.group? g).map (·.kind) |>.getD ""
    let st := if v.groupDone g then "done" else if v.groupReady g then "ready" else if c.total == 0 then "" else "blocked"
    let name := "".pushn ' ' (2 * depth) ++ g
    IO.println s!"{pad name 34} {pad kind 9} {pad (toString c.proved) 7} {pad (toString c.stated) 7} {pad (toString c.open) 6} {pad (toString c.wrong) 6} {pad (toString c.axioms) 7} {st}"
  -- wrong nodes and regressions
  let wrongs := v.plan.nodes.toArray.filterMap fun (_, n) =>
    if let some w := n.wrong then some (n, w) else none
  let wrongs := wrongs.filter fun (n, _) => group?.isNone || (v.subtree group?.get!).contains n.group
  if !wrongs.isEmpty then
    IO.println "\nwrong:"
    for (n, w) in wrongs.qsort (·.1.id.toString < ·.1.id.toString) do
      IO.println s!"  {n.id}  ({n.group}): {firstLine w}"
  if let some c := v.cache then
    if !c.regressions.isEmpty then
      IO.println "\nregressed since the previous check:"
      for r in c.regressions do
        IO.println s!"  {r.id}: {r.before} → {r.after}"
  if !v.plan.errors.isEmpty then
    IO.println s!"\n{v.plan.errors.size} plan error(s); run `tracker lint`."
  return 0

-- ## ready

def ready (v : View) (kind? : Option String) (all : Bool) (json : Bool) : IO UInt32 := do
  let kind := kind?.getD "task"
  let groups := v.plan.groups.filter fun g =>
    (all || g.kind == kind) && v.groupReady g.name
  if json then
    IO.println (toJson (groups.map fun g =>
      Json.mkObj [("group", g.name), ("kind", g.kind), ("title", g.title),
        ("module", toJson (g.module.map (·.toString))),
        ("nodes", toJson ((v.groupNodes g.name).filterMap fun n =>
          if v.state n.id != .proved then some (n.id.toString) else none))])).pretty
    return 0
  noCacheWarning v
  if groups.isEmpty then
    IO.println (if all then "no ready groups" else s!"no ready groups of kind '{kind}' (try --all)")
    return 0
  for g in groups do
    let c := v.counts g.name
    let m := g.module.map (fun m => s!"  {m}") |>.getD ""
    IO.println s!"{g.name}  [{g.kind}] {g.title}{m}"
    IO.println s!"  {c.open} open, {c.stated} stated, {c.proved} proved"
    for n in v.groupNodes g.name do
      if v.state n.id != .proved then
        IO.println s!"    {pad (v.state n.id).toString 7} {v.plan.shortId n}  — {firstLine (v.descOf n.id)}"
  return 0

-- ## show

private def depLine (v : View) (d : Name) (tag : String) : String :=
  let st := v.state d
  let sig := match v.decl[d]? with
    | some i => if i.signature.isEmpty then "" else "\n" ++ indent i.signature 6
    | none => ""
  s!"  {pad st.toString 7} {d}{tag}{sig}"

def showNode (v : View) (n : Node) : IO Unit := do
  let st := v.state n.id
  IO.println s!"{n.id}  [{v.kindName n.id}, {st}]  group {n.group}"
  let desc := v.descOf n.id
  if desc.isEmpty then IO.println "  (no description: no desc in the plan and no doc comment)"
  else IO.println (indent desc)
  if v.hasDoc n.id then
    if let some d := n.desc then IO.println (indent s!"(from the doc comment; the plan's desc is superseded: {firstLine d})")
  if let some s := n.source then IO.println s!"  source: {s}"
  if let some w := n.wrong then IO.println s!"  wrong: {w}"
  if let some d := v.decl[n.id]? then
    if d.found then
      IO.println s!"  at {d.module.map (·.toString) |>.getD "?"}:{d.line.map toString |>.getD "?"}"
      if !d.signature.isEmpty then IO.println (indent d.signature 4)
      if !d.axiomsOk then IO.println s!"  axioms: {d.axioms}"
  let real := v.realDeps n.id
  let eff := v.effDeps n.id
  if !eff.isEmpty then
    IO.println "  depends on:"
    for d in eff do
      let tag := if real.contains d then (if n.deps.contains d then "" else "  (real, not suggested)")
        else "  (suggested)"
      IO.println (depLine v d tag)
  let unused := n.deps.filter fun d => !eff.contains d
  if !unused.isEmpty then
    IO.println s!"  suggested but not used: {unused}"
  let dependents := v.dependents.getD n.id #[]
  if !dependents.isEmpty then
    IO.println s!"  needed by: {dependents}"

def showGroup (v : View) (g : Group) : IO Unit := do
  let c := v.counts g.name
  IO.println s!"{g.name}  [{g.kind}] {g.title}"
  if let some m := g.module then IO.println s!"  module: {m}"
  if let some ns := g.namespace then IO.println s!"  namespace: {ns}"
  if let some p := g.parent then IO.println s!"  parent: {p}"
  IO.println s!"  {c.proved} proved, {c.stated} stated, {c.open} open, {c.wrong} wrong, {c.axioms} axioms; {if v.groupDone g.name then "done" else if v.groupReady g.name then "ready" else "blocked"}"
  if let some notes := g.notes then
    IO.println "\nnotes:"
    IO.println (indent notes)
  let kids := v.children.getD g.name #[]
  if !kids.isEmpty then
    IO.println "\ngroups:"
    for k in kids do
      let kc := v.counts k
      IO.println s!"  {pad k 30} {kc.proved}/{kc.total} proved"
  if !g.nodes.isEmpty then
    IO.println "\nnodes:"
    for n in g.nodes do
      IO.println s!"  {pad (v.state n.id).toString 7} {pad (v.kindName n.id) 10} {v.plan.shortId n}"
      IO.println (indent (v.descOf n.id) 20)
      if let some w := n.wrong then IO.println (indent s!"wrong: {w}" 20)
  let outside := v.outsideDeps g.name
  if !outside.isEmpty then
    IO.println "\noutside dependencies:"
    for d in outside do IO.println (depLine v d "")

def «show» (v : View) (target : String) : IO UInt32 := do
  noCacheWarning v
  if let some g := v.plan.group? target then
    showGroup v g
    return 0
  let id := target.toName
  if let some n := v.plan.node? id then
    showNode v n
    return 0
  -- try as a suffix: any node whose id ends with the target
  let hits := v.plan.nodes.toArray.filter fun (k, _) =>
    k == id || (k.toString.endsWith ("." ++ target))
  match hits with
  | #[(_, n)] => showNode v n; return 0
  | #[] => IO.eprintln s!"no group or node named '{target}'"; return 1
  | ms =>
    IO.eprintln s!"'{target}' is ambiguous:"
    for (k, _) in ms do IO.eprintln s!"  {k}"
    return 1

-- ## lint

def lint (v : View) : IO UInt32 := do
  let mut errors : Array String := v.plan.errors
  let mut warnings : Array String := #[]
  if let some cyc := v.suggestedCycle then
    errors := errors.push s!"cycle among suggested dependencies: {String.intercalate " → " (cyc.map (·.toString))}"
  for g in v.plan.groups do
    if isBlank g.kind then errors := errors.push s!"{g.path}: empty kind"
    for n in g.nodes do
      if let some w := n.wrong then
        if isBlank w then errors := errors.push s!"{g.path}:{n.line}: {n.id} is marked wrong without a reason"
      -- descriptions: the plan's `desc` until there is a doc comment, then the doc comment
      if let some d := n.desc then
        if isBlank d then errors := errors.push s!"{g.path}:{n.line}: {n.id} has an empty desc"
      if v.cache.isSome then
        let attached := (v.decl[n.id]?.map (·.found)).getD false
        if !attached && n.desc.isNone then
          errors := errors.push s!"{g.path}:{n.line}: {n.id} is open and has no desc"
        if attached && !v.hasDoc n.id && n.desc.isNone then
          warnings := warnings.push s!"{g.path}:{n.line}: {n.id} has neither a desc nor a doc comment"
        if v.hasDoc n.id && n.desc.isSome then
          warnings := warnings.push s!"{g.path}:{n.line}: {n.id}: desc is superseded by its doc comment; remove it"
        if v.state n.id == .proved && !n.deps.isEmpty then
          warnings := warnings.push s!"{g.path}:{n.line}: {n.id}: deps is superseded by the real dependencies; remove it"
      if v.cache.isSome && n.kind.isNone && !((v.decl[n.id]?.map (·.found)).getD false) then
        errors := errors.push s!"{g.path}:{n.line}: {n.id} is open and has no kind"
      if let some d := v.decl[n.id]? then
        if d.found then
          match n.kind with
          | some .theorem =>
            if !d.isTheorem && !d.isAxiom then
              warnings := warnings.push s!"{g.path}:{n.line}: {n.id} is planned as a theorem but the declaration is not one"
            else
              warnings := warnings.push s!"{g.path}:{n.line}: {n.id}: kind is superseded by the declaration; remove it"
          | some .definition =>
            if d.isTheorem then
              warnings := warnings.push s!"{g.path}:{n.line}: {n.id} is planned as a definition but the declaration is a theorem"
            else
              warnings := warnings.push s!"{g.path}:{n.line}: {n.id}: kind is superseded by the declaration; remove it"
          | none => pure ()
          if d.isAxiom then
            errors := errors.push s!"{g.path}:{n.line}: {n.id} is an axiom"
          match g.module, d.module with
          | some gm, some dm =>
            if gm != dm then
              warnings := warnings.push s!"{g.path}:{n.line}: {n.id} lives in {dm}, group says {gm}"
          | _, _ => pure ()
  for e in errors do IO.println s!"error: {e}"
  for w in warnings do IO.println s!"warning: {w}"
  if errors.isEmpty && warnings.isEmpty then IO.println "ok"
  return if errors.isEmpty then 0 else 1

-- ## graph

def graphJson (v : View) (under? : Option String) : Json :=
  let groups : Array String := match under? with
    | some g => v.subtree g
    | none => v.plan.groups.map (·.name)
  let inGroups : Std.HashSet String := groups.foldl (init := {}) (·.insert ·)
  let nodes : Array (Name × Node) := v.plan.nodes.toArray.filter (fun p => inGroups.contains p.2.group)
    |>.qsort (·.1.toString < ·.1.toString)
  let nodeJson := nodes.map fun (id, n) => Json.mkObj [
    ("id", id.toString), ("group", n.group), ("kind", toJson ((v.kindOf id).map toString)),
    ("state", (v.state id).toString), ("desc", v.descOf id),
    ("source", toJson n.source), ("wrong", toJson n.wrong)]
  let edges := nodes.flatMap fun (id, n) =>
    let real := v.realDeps id
    let sugg := n.deps
    let all := real ++ sugg.filter (!real.contains ·)
    all.map fun d => Json.mkObj [
      ("from", id.toString), ("to", d.toString),
      ("real", real.contains d), ("suggested", sugg.contains d)]
  let groupJson := groups.filterMap fun g => (v.plan.group? g).map fun g => Json.mkObj [
    ("name", g.name), ("kind", g.kind), ("title", g.title), ("parent", toJson g.parent),
    ("module", toJson (g.module.map (·.toString))),
    ("done", v.groupDone g.name), ("ready", v.groupReady g.name)]
  Json.mkObj [("groups", toJson groupJson), ("nodes", toJson nodeJson), ("edges", toJson edges)]

private def dotEscape (s : String) : String :=
  s.replace "\"" "\\\""

def graphDot (v : View) (under? : Option String) : String := Id.run do
  let groups : Array String := match under? with
    | some g => v.subtree g
    | none => v.plan.groups.map (·.name)
  let mut out := "digraph tracker {\n  rankdir=BT;\n  node [shape=box, fontsize=10];\n"
  for g in groups do
    if let some grp := v.plan.group? g then
      out := out ++ s!"  subgraph \"cluster_{g}\" \{\n    label=\"{dotEscape grp.title}\";\n"
      for n in grp.nodes do
        let color := match v.state n.id with
          | .proved => "palegreen" | .stated => "khaki" | .wrong => "lightcoral"
          | .axioms => "orange" | .«open» => "white"
        out := out ++ s!"    \"{n.id}\" [label=\"{dotEscape (v.plan.shortId n)}\", style=filled, fillcolor={color}];\n"
      out := out ++ "  }\n"
  let inGroups : Std.HashSet String := groups.foldl (init := {}) (·.insert ·)
  for (id, n) in v.plan.nodes.toArray do
    if inGroups.contains n.group then
      let real := v.realDeps id
      for d in real do
        if inGroups.contains ((v.plan.node? d).map (·.group) |>.getD "") then
          out := out ++ s!"  \"{id}\" -> \"{d}\";\n"
      for d in n.deps do
        if !real.contains d && inGroups.contains ((v.plan.node? d).map (·.group) |>.getD "") then
          out := out ++ s!"  \"{id}\" -> \"{d}\" [style=dashed];\n"
  out := out ++ "}\n"
  return out

def graph (v : View) (under? : Option String) (dot : Bool) : IO UInt32 := do
  if let some g := under? then
    unless v.plan.groupIdx.contains g do
      IO.eprintln s!"no group named '{g}'"
      return 1
  if dot then IO.print (graphDot v under?)
  else IO.println (graphJson v under?).pretty
  return 0

end Tracker
