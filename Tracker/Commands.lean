import Tracker.Types
import Tracker.Plan
import Tracker.Graph
import Tracker.Cache

/-!
# Commands

`status`, `ready`, `show`, `lint`, `graph`. Each takes a `View` and prints; `--json` variants
print `Lean.Json`.

A module is named on the command line by its module name (`Numbers.Odd`) or an unambiguous
trailing part of it (`Odd`); a planned node or a declaration by its id, likewise.
-/

open Lean

namespace Tracker

/-- Pad to width. -/
def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ "".pushn ' ' (w - s.length)

def indent (s : String) (n : Nat := 2) : String :=
  String.intercalate "\n" (s.splitOn "\n" |>.map fun l => if l.isEmpty then l else "".pushn ' ' n ++ l)

private def firstLine (s : String) : String :=
  (s.splitOn "\n").headD ""

def isBlank (s : String) : Bool := s.all Char.isWhitespace

/-- A count and a noun, the noun plural unless the count is one. -/
def plural (n : Nat) (noun : String) : String :=
  if n == 1 then s!"1 {noun}" else s!"{n} {noun}s"

/-- `11 declarations (3 definitions, 8 theorems)`. -/
def declSummary (d : View.DeclCounts) : String :=
  s!"{plural d.total "declaration"} ({plural d.definitions "definition"}, {plural d.theorems "theorem"})"

/-- Whether a module name or an id is `target`, or ends with it after a dot. -/
private def namedBy (n : Name) (target : String) : Bool :=
  let s := n.toString
  s == target || s.endsWith ("." ++ target)

/-- Module rows in tree order, each with its depth: from the roots, or from one module. -/
def moduleOrder (v : View) (from? : Option Name := none) : Array (Name × Nat) := Id.run do
  let roots := match from? with
    | some m => #[m]
    | none => v.rootModules
  let mut out := #[]
  let mut stack : List (Name × Nat) := roots.toList.map (·, 0)
  while true do
    match stack with
    | [] => break
    | (m, d) :: rest =>
      out := out.push (m, d)
      stack := (v.children.getD m #[]).toList.map (·, d + 1) ++ rest
  return out

def noCacheWarning (v : View) : IO Unit := do
  if v.cache.isNone then
    IO.eprintln "warning: no cache; every planned node reads as open, and there are no declarations"

/-- A module by its module name, or by an unambiguous trailing part of it. Says why when nothing
matches or several do. -/
def resolveModule (v : View) (target : String) : IO (Option Name) := do
  if let some m := v.modules.find? (·.toString == target) then return some m
  match v.modules.filter (namedBy · target) with
  | #[m] => return some m
  | #[] => IO.eprintln s!"no module named '{target}'"; return none
  | hits =>
    IO.eprintln s!"'{target}' is ambiguous:"
    for m in hits do IO.eprintln s!"  {m}"
    return none

/-- The declarations of the project, and the planned nodes' ids. -/
def allIds (v : View) : Array Name :=
  v.declIds.filter (fun id => (v.decl[id]?.map (·.declaration)).getD false) ++
    (sortNames (v.plan.nodes.fold (init := #[]) fun a id _ => a.push id)).filter
      fun id => !((v.decl[id]?.map (·.declaration)).getD false)

-- ## status

/-- What a row says: done for the subtree; ready or blocked for the module's own planned nodes;
else nothing. -/
def View.moduleState (v : View) (m : Name) : String :=
  if v.moduleDone m then "done"
  else if v.moduleReady m then "ready"
  else if !(v.ownWork m).isEmpty then "blocked"
  else ""

private def countsJson (c : View.Counts) (d : View.DeclCounts) : List (String × Json) := [
  ("proved", c.proved), ("stated", c.stated), ("open", c.open), ("axioms", c.axioms),
  ("wrong", c.wrong), ("declarations", d.total), ("definitions", d.definitions),
  ("theorems", d.theorems)]

def moduleJson (v : View) (m : Name) : Json :=
  let parent := if m.getPrefix.isAnonymous then none else some m.getPrefix.toString
  Json.mkObj ([("module", toJson m.toString), ("parent", toJson parent)] ++
    countsJson (v.counts m) (v.declCounts m) ++
    [("done", toJson (v.moduleDone m)), ("ready", toJson (v.moduleReady m))])

def status (v : View) (module? : Option String) (json : Bool) : IO UInt32 := do
  let mut from? : Option Name := none
  if let some m := module? then
    let some r ← resolveModule v m | return 1
    from? := some r
  let rows := moduleOrder v from?
  let (c, d) := match from? with
    | some m => (v.counts m, v.declCounts m)
    | none => (v.totals, v.declTotals)
  if json then
    let regs := (v.cache.map (·.regressions)).getD #[]
    IO.println (Json.mkObj [("modules", toJson (rows.map (moduleJson v ·.1))),
      ("totals", Json.mkObj (countsJson c d)), ("regressions", toJson regs)]).pretty
    return 0
  noCacheWarning v
  IO.println s!"{pad "module" 40} {pad "proved" 7} {pad "stated" 7} {pad "open" 6} {pad "wrong" 6} {pad "axioms" 7} {pad "decls" 7} state"
  for (m, depth) in rows do
    let c := v.counts m
    -- the top row in full, the rows under it by the last component: the indentation says the rest
    let label := if depth == 0 then m.toString else "".pushn ' ' (2 * depth) ++ m.componentsRev.head!.toString
    IO.println s!"{pad label 40} {pad (toString c.proved) 7} {pad (toString c.stated) 7} {pad (toString c.open) 6} {pad (toString c.wrong) 6} {pad (toString c.axioms) 7} {pad (toString (v.declCounts m).total) 7} {v.moduleState m}"
  IO.println s!"\nplanned nodes: {c.total} ({c.proved} proved, {c.stated} stated, {c.open} open, \
    {c.wrong} wrong, {c.axioms} axioms)"
  IO.println (declSummary d)
  -- wrong planned nodes and regressions
  let inScope (m : Name) := match from? with
    | some f => f.isPrefixOf m
    | none => true
  let wrongs := v.plan.nodes.toArray.filterMap fun (_, n) =>
    if let some w := n.wrong then (if inScope n.module then some (n, w) else none) else none
  if !wrongs.isEmpty then
    IO.println "\nwrong:"
    for (n, w) in wrongs.qsort (·.1.id.toString < ·.1.id.toString) do
      IO.println s!"  {n.id}  ({n.module}): {firstLine w}"
  if let some c := v.cache then
    if !c.regressions.isEmpty then
      IO.println "\nregressed since the previous check:"
      for r in c.regressions do
        IO.println s!"  {r.id}: {r.before} → {r.after}"
  if !v.plan.errors.isEmpty then
    IO.println s!"\n{v.plan.errors.size} plan error(s); run `tracker lint`."
  return 0

-- ## ready

def ready (v : View) (json : Bool) : IO UInt32 := do
  let modules := v.plan.modules.filter fun mp => v.moduleReady mp.module
  if json then
    IO.println (toJson (modules.map fun mp =>
      Json.mkObj [("module", mp.module.toString), ("desc", v.moduleDesc mp.module),
        ("nodes", toJson (mp.nodes.filterMap fun n =>
          if v.state n.id != .proved then some (n.id.toString) else none))])).pretty
    return 0
  noCacheWarning v
  if modules.isEmpty then
    IO.println "no ready modules"
    return 0
  for mp in modules do
    let c := v.countNodes mp.nodes
    let desc := firstLine (v.moduleDesc mp.module)
    IO.println (if desc.isEmpty then mp.module.toString else s!"{mp.module}  — {desc}")
    IO.println s!"  {c.open} open, {c.stated} stated, {c.proved} proved"
    for n in mp.nodes do
      if v.state n.id != .proved then
        IO.println s!"    {pad (v.state n.id).toString 7} {v.plan.shortId n}  — {firstLine (v.descOf n.id)}"
  return 0

-- ## show

private def depLine (v : View) (d : Name) (tag : String) : String :=
  let sig := match v.decl[d]? with
    | some i => if i.signature.isEmpty then "" else "\n" ++ indent i.signature 6
    | none => ""
  s!"  {pad (v.state d).toString 7} {d}{tag}{sig}"

/-- Where a declaration is, its signature, and its axioms when they are not the standard ones. -/
private def showDeclInfo (d : DeclInfo) : IO Unit := do
  if d.found then
    IO.println s!"  at {d.module.map (·.toString) |>.getD "?"}:{d.line.map toString |>.getD "?"}"
    if !d.signature.isEmpty then IO.println (indent d.signature 4)
    if !d.axiomsOk then IO.println s!"  axioms: {d.axioms}"

def showNode (v : View) (n : Node) : IO Unit := do
  IO.println s!"{n.id}  [{v.kindName n.id}, {v.state n.id}]  planned in module {n.module}"
  let desc := v.descOf n.id
  if desc.isEmpty then IO.println "  (no description: no desc in the plan and no doc comment)"
  else IO.println (indent desc)
  if v.hasDoc n.id then
    if let some d := n.desc then IO.println (indent s!"(from the doc comment; the plan's desc is superseded: {firstLine d})")
  if let some s := n.source then IO.println s!"  source: {s}"
  if let some w := n.wrong then IO.println s!"  wrong: {w}"
  if let some d := n.deprecated then IO.println s!"  deprecated: {d}"
  if let some d := v.decl[n.id]? then showDeclInfo d
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

/-- A declaration no plan names: what the library says about it, and where it sits among the
declarations and planned nodes. -/
def showDecl (v : View) (d : DeclInfo) : IO Unit := do
  let m := d.module.map (·.toString) |>.getD "?"
  IO.println s!"{d.id}  [{v.kindName d.id}, {v.state d.id}]  in module {m}, unplanned"
  match d.doc with
  | some doc => IO.println (indent doc)
  | none => IO.println "  (no doc comment)"
  showDeclInfo d
  if !d.uses.isEmpty then
    IO.println "  planned nodes it uses:"
    for u in d.uses do IO.println (depLine v u "")
  let refs := v.refsOf d.id
  if !refs.isEmpty then IO.println s!"  refers to: {refs}"
  let users := match v.declIds.findIdx? (· == d.id) with
    | some i => v.declIds.filter fun u => ((v.decl[u]?.map fun (e : DeclInfo) => e.refs.contains i).getD false)
    | none => #[]
  if !users.isEmpty then IO.println s!"  referred to by: {users}"

def showModule (v : View) (m : Name) : IO Unit := do
  let c := v.counts m
  let d := v.declCounts m
  let st := v.moduleState m
  let tags := (if st.isEmpty then [] else [st]) ++
    (if v.moduleExists m then [] else ["does not exist yet"]) ++
    (if (v.plan.modulePlan? m).isSome then [] else ["no module plan"])
  IO.println (if tags.isEmpty then m.toString else s!"{m}  [{", ".intercalate tags}]")
  if let some ns := (v.plan.modulePlan? m).bind (·.namespace) then IO.println s!"  namespace: {ns}"
  if c.total > 0 then
    IO.println s!"  planned nodes: {c.proved} proved, {c.stated} stated, {c.open} open, {c.wrong} wrong, {c.axioms} axioms"
  IO.println s!"  {declSummary d}"
  let desc := v.moduleDesc m
  if !desc.isEmpty then
    IO.println ""
    IO.println (indent desc)
    if (v.moduleDoc? m).isSome then
      if let some pd := (v.plan.modulePlan? m).bind (·.desc) then
        IO.println (indent s!"(from the module's doc comment; the plan's desc is superseded: {firstLine pd})")
  let kids := v.children.getD m #[]
  if !kids.isEmpty then
    IO.println "\nmodules:"
    for k in kids do
      let kc := v.counts k
      let planned := if kc.total > 0 then s!"{kc.proved}/{kc.total} proved, " else ""
      IO.println s!"  {pad k.toString 40} {planned}{plural (v.declCounts k).total "declaration"}"
  let nodes := v.ownNodes m
  if !nodes.isEmpty then
    IO.println "\nplanned nodes:"
    for n in nodes do
      IO.println s!"  {pad (v.state n.id).toString 7} {pad (v.kindName n.id) 10} {v.plan.shortId n}"
      IO.println (indent (v.descOf n.id) 20)
      if let some w := n.wrong then IO.println (indent s!"wrong: {w}" 20)
      if let some dep := n.deprecated then IO.println (indent s!"deprecated: {dep}" 20)
  let outside := v.outsideDeps m
  if !outside.isEmpty then
    IO.println "\noutside dependencies:"
    for dep in outside do IO.println (depLine v dep "")

/-- A planned node, or else a declaration, by its exact id. -/
private def showId (v : View) (id : Name) : IO Bool := do
  if let some n := v.plan.node? id then
    showNode v n
    return true
  if let some d := v.decl[id]? then
    if d.declaration then
      showDecl v d
      return true
  return false

def «show» (v : View) (target : String) : IO UInt32 := do
  noCacheWarning v
  let ids := allIds v
  -- exact matches first: a module name and an id may coincide, and then both are shown
  let module? := v.modules.find? (·.toString == target)
  let id? := ids.find? (·.toString == target)
  if module?.isSome || id?.isSome then
    if let some m := module? then showModule v m
    if let some id := id? then
      if module?.isSome then IO.println ""
      discard <| showId v id
    return 0
  -- else a trailing part of a module name (`Odd` for `Numbers.Odd`) or of an id
  let modules := v.modules.filter (namedBy · target)
  let hits := ids.filter (namedBy · target)
  match modules, hits with
  | #[m], #[] => showModule v m; return 0
  | #[], #[id] => discard <| showId v id; return 0
  | #[], #[] => IO.eprintln s!"no module, planned node or declaration named '{target}'"; return 1
  | _, _ =>
    IO.eprintln s!"'{target}' is ambiguous:"
    for m in modules do IO.eprintln s!"  module {m}"
    for id in hits do IO.eprintln s!"  {id}"
    return 1

-- ## lint

def lint (v : View) : IO UInt32 := do
  let mut errors : Array String := v.plan.errors
  let mut warnings : Array String := #[]
  if let some cyc := v.suggestedCycle then
    errors := errors.push s!"cycle among suggested dependencies: {String.intercalate " → " (cyc.map (·.toString))}"
  for mp in v.plan.modules do
    let p := mp.path
    -- the module's description: its plan's `desc` until the module has a doc comment
    if let some d := mp.desc then
      if isBlank d then errors := errors.push s!"{p}: empty desc"
    if v.cache.isSome then
      let exists_ := v.moduleExists mp.module
      let hasDoc := (v.moduleDoc? mp.module).isSome
      if !exists_ && mp.desc.isNone then
        errors := errors.push s!"{p}: the module does not exist yet and its plan has no desc"
      if exists_ && !hasDoc && mp.desc.isNone then
        warnings := warnings.push s!"{p}: neither a desc nor a module doc comment"
      if hasDoc && mp.desc.isSome then
        warnings := warnings.push s!"{p}: desc is superseded by the module's doc comment; remove it"
    for n in mp.nodes do
      let at_ := s!"{p}:{n.line}"
      if let some w := n.wrong then
        if isBlank w then errors := errors.push s!"{at_}: {n.id} is marked wrong without a reason"
      -- deprecation is hand-set and read nowhere else: lint is where it surfaces, node and users
      if let some d := n.deprecated then
        if isBlank d then
          errors := errors.push s!"{at_}: {n.id} is marked deprecated without a reason"
        else warnings := warnings.push s!"{at_}: {n.id} is deprecated: {firstLine d}"
      else
        for d in n.deps ++ (v.effDeps n.id).filter (!n.deps.contains ·) do
          if ((v.plan.node? d).bind (·.deprecated)).isSome then
            warnings := warnings.push s!"{at_}: {n.id} depends on the deprecated {d}"
      -- descriptions: the plan's `desc` until there is a doc comment, then the doc comment
      if let some d := n.desc then
        if isBlank d then errors := errors.push s!"{at_}: {n.id} has an empty desc"
      if v.cache.isSome then
        let attached := (v.decl[n.id]?.map (·.found)).getD false
        if !attached && n.desc.isNone then
          errors := errors.push s!"{at_}: {n.id} is open and has no desc"
        if attached && !v.hasDoc n.id && n.desc.isNone then
          warnings := warnings.push s!"{at_}: {n.id} has neither a desc nor a doc comment"
        if v.hasDoc n.id && n.desc.isSome then
          warnings := warnings.push s!"{at_}: {n.id}: desc is superseded by its doc comment; remove it"
        if v.state n.id == .proved && !n.deps.isEmpty then
          warnings := warnings.push s!"{at_}: {n.id}: deps is superseded by the real dependencies; remove it"
        if n.kind.isNone && !attached then
          errors := errors.push s!"{at_}: {n.id} is open and has no kind"
      if let some d := v.decl[n.id]? then
        if d.found then
          match n.kind with
          | some .theorem =>
            if !d.isTheorem && !d.isAxiom then
              warnings := warnings.push s!"{at_}: {n.id} is planned as a theorem but the declaration is not one"
            else
              warnings := warnings.push s!"{at_}: {n.id}: kind is superseded by the declaration; remove it"
          | some .definition =>
            if d.isTheorem then
              warnings := warnings.push s!"{at_}: {n.id} is planned as a definition but the declaration is a theorem"
            else
              warnings := warnings.push s!"{at_}: {n.id}: kind is superseded by the declaration; remove it"
          | none => pure ()
          if d.isAxiom then
            errors := errors.push s!"{at_}: {n.id} is an axiom"
          if let some dm := d.module then
            if dm != mp.module then
              warnings := warnings.push s!"{at_}: {n.id} is in module {dm}, not in module {mp.module}"
  for e in errors do IO.println s!"error: {e}"
  for w in warnings do IO.println s!"warning: {w}"
  if errors.isEmpty && warnings.isEmpty then IO.println "ok"
  return if errors.isEmpty then 0 else 1

-- ## graph

/-- What `graph` draws: the modules of the tree under `under?` (all of them without it), and in
those modules the planned nodes, with `all` every declaration too. -/
private def graphScope (v : View) (under? : Option Name) (all : Bool) : Array Name × Array Name :=
  let modules := match under? with
    | some m => v.subtree m
    | none => v.modules
  let inScope : Std.HashSet Name := modules.foldl (init := {}) (·.insert ·)
  let ids := (if all then allIds v else sortNames (v.plan.nodes.fold (init := #[]) fun a id _ => a.push id))
    |>.filter fun id => (v.moduleOf? id).any inScope.contains
  (modules, ids)

/-- The edges out of one node: its real dependencies — among planned nodes, or with `all` among
every node — and a planned node's suggested ones. -/
private def graphEdges (v : View) (all : Bool) (id : Name) : Array (Name × Bool × Bool) :=
  let real := if all then v.refsOf id else v.realDeps id
  let sugg := ((v.plan.node? id).map (·.deps)).getD #[]
  (real ++ sugg.filter (!real.contains ·)).map fun d => (d, real.contains d, sugg.contains d)

def graphJson (v : View) (under? : Option Name) (all : Bool) : Json :=
  let (modules, ids) := graphScope v under? all
  let moduleJson := modules.map fun m => Json.mkObj [
    ("module", toJson m.toString),
    ("parent", toJson (if m.getPrefix.isAnonymous then none else some m.getPrefix.toString)),
    ("desc", toJson (v.moduleDesc m)), ("exists", toJson (v.moduleExists m)),
    ("plan", toJson (v.plan.modulePlan? m).isSome),
    ("done", toJson (v.moduleDone m)), ("ready", toJson (v.moduleReady m))]
  let nodeJson := ids.map fun id =>
    let n? := v.plan.node? id
    Json.mkObj [
      ("id", toJson id.toString), ("module", toJson ((v.moduleOf? id).map toString)),
      ("planned", toJson n?.isSome), ("kind", toJson ((v.kindOf id).map toString)),
      ("state", toJson (v.state id).toString), ("desc", toJson (v.descOf id)),
      ("source", toJson (n?.bind (·.source))), ("wrong", toJson (n?.bind (·.wrong))),
      ("deprecated", toJson (n?.bind (·.deprecated)))]
  let edges := ids.flatMap fun id => (graphEdges v all id).map fun (d, real, sugg) =>
    Json.mkObj [("from", toJson id.toString), ("to", toJson d.toString),
      ("real", toJson real), ("suggested", toJson sugg)]
  Json.mkObj [("modules", toJson moduleJson), ("nodes", toJson nodeJson), ("edges", toJson edges)]

private def dotEscape (s : String) : String :=
  s.replace "\"" "\\\""

def graphDot (v : View) (under? : Option Name) (all : Bool) : String := Id.run do
  let (_, ids) := graphScope v under? all
  let inScope : Std.HashSet Name := ids.foldl (init := {}) (·.insert ·)
  let mut byModule : Std.HashMap Name (Array Name) := {}
  for id in ids do
    if let some m := v.moduleOf? id then byModule := byModule.insert m ((byModule.getD m #[]).push id)
  let mut out := "digraph tracker {\n  rankdir=BT;\n  node [shape=box, fontsize=10];\n"
  for m in sortNames (byModule.keys.toArray) do
    out := out ++ s!"  subgraph \"cluster_{m}\" \{\n    label=\"{dotEscape m.toString}\";\n"
    for id in byModule.getD m #[] do
      let color := match v.state id with
        | .proved => "palegreen" | .stated => "khaki" | .wrong => "lightcoral"
        | .axioms => "orange" | .«open» => "white"
      let (label, shape) := match v.plan.node? id with
        | some n => (v.plan.shortId n, "")
        | none => (id.componentsRev.head!.toString, ", shape=ellipse, fontsize=8")
      out := out ++ s!"    \"{id}\" [label=\"{dotEscape label}\", style=filled, fillcolor={color}{shape}];\n"
    out := out ++ "  }\n"
  for id in ids do
    for (d, real, _) in graphEdges v all id do
      if inScope.contains d then
        out := out ++ (if real then s!"  \"{id}\" -> \"{d}\";\n" else s!"  \"{id}\" -> \"{d}\" [style=dashed];\n")
  out := out ++ "}\n"
  return out

def graph (v : View) (under? : Option String) (all dot : Bool) : IO UInt32 := do
  let mut under : Option Name := none
  if let some m := under? then
    let some r ← resolveModule v m | return 1
    under := some r
  if dot then IO.print (graphDot v under all)
  else IO.println (graphJson v under all).pretty
  return 0

end Tracker
