import Tracker.Types
import Tracker.Plan

/-!
# The graph

Everything computed from the plan and the cache: node states, effective dependencies, readiness,
group roll-ups, and cycle detection on the suggestions.
-/

open Lean

namespace Tracker

/-- The plan and cache joined: what every command reads. -/
structure View where
  plan : Plan
  cache : Option Cache
  decl : Std.HashMap Name DeclInfo := {}
  states : Std.HashMap Name NodeState := {}
  /-- Real dependencies from the cache, restricted to tracked ids. -/
  real : Std.HashMap Name (Array Name) := {}
  /-- Effective dependencies: suggested while open, real once proved, both in between. -/
  eff : Std.HashMap Name (Array Name) := {}
  /-- Reverse of `eff`. -/
  dependents : Std.HashMap Name (Array Name) := {}
  /-- Groups by parent. -/
  children : Std.HashMap String (Array String) := {}

/-- The state of a node given what the cache knows about it. -/
def nodeState (n : Node) (d : Option DeclInfo) : NodeState :=
  if n.wrong.isSome then .wrong
  else match d with
    | none => .«open»
    | some d =>
      if !d.found then .«open»
      else if d.hasSorry then .stated
      else if d.isAxiom || !d.axiomsOk then .axioms
      else .proved

private def dedup (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

def mkView (plan : Plan) (cache : Option Cache) : View := Id.run do
  let mut v : View := { plan, cache }
  if let some c := cache then
    for d in c.decls do
      v := { v with decl := v.decl.insert d.id d }
  for (id, n) in plan.nodes.toArray do
    let d := v.decl[id]?
    let st := nodeState n d
    v := { v with states := v.states.insert id st }
    let real := (d.map (·.uses)).getD #[] |>.filter plan.nodes.contains
    let eff := match st with
      | .«open» => n.deps
      | .proved | .axioms => real
      | .stated | .wrong => dedup (n.deps ++ real)
    v := { v with real := v.real.insert id real, eff := v.eff.insert id eff }
  for (id, deps) in v.eff.toArray do
    for d in deps do
      v := { v with dependents := v.dependents.insert d ((v.dependents.getD d #[]).push id) }
  for g in plan.groups do
    if let some p := g.parent then
      v := { v with children := v.children.insert p ((v.children.getD p #[]).push g.name) }
  return v

namespace View

def state (v : View) (id : Name) : NodeState := v.states.getD id .«open»
def effDeps (v : View) (id : Name) : Array Name := v.eff.getD id #[]
def realDeps (v : View) (id : Name) : Array Name := v.real.getD id #[]

/-- A node is ready when it is not yet proved and every effective dependency is proved. -/
def nodeReady (v : View) (id : Name) : Bool :=
  match v.state id with
  | .«open» | .stated => (v.effDeps id).all fun d => v.state d == .proved
  | _ => false

/-- The group and all its descendants. -/
partial def subtree (v : View) (name : String) : Array String := Id.run do
  let mut out := #[name]
  let mut queue := v.children.getD name #[]
  while h : queue.size > 0 do
    let g := queue[0]
    queue := queue.extract 1 queue.size
    out := out.push g
    queue := queue ++ v.children.getD g #[]
  return out

/-- Nodes of a group, including descendant groups. -/
def groupNodes (v : View) (name : String) : Array Node :=
  (v.subtree name).flatMap fun g => match v.plan.group? g with
    | some g => g.nodes
    | none => #[]

structure Counts where
  «open» : Nat := 0
  stated : Nat := 0
  proved : Nat := 0
  axioms : Nat := 0
  wrong : Nat := 0
  deriving Inhabited

def Counts.total (c : Counts) : Nat := c.open + c.stated + c.proved + c.axioms + c.wrong

def counts (v : View) (name : String) : Counts :=
  (v.groupNodes name).foldl (init := {}) fun c n =>
    match v.state n.id with
    | .«open» => { c with «open» := c.open + 1 }
    | .stated => { c with stated := c.stated + 1 }
    | .proved => { c with proved := c.proved + 1 }
    | .axioms => { c with axioms := c.axioms + 1 }
    | .wrong => { c with wrong := c.wrong + 1 }

/-- Done when every node in the subtree is proved (and there is at least one). -/
def groupDone (v : View) (name : String) : Bool :=
  let ns := v.groupNodes name
  !ns.isEmpty && ns.all fun n => v.state n.id == .proved

/-- Dependencies of the subtree's nodes that lie outside the subtree, with their states. -/
def outsideDeps (v : View) (name : String) : Array Name := Id.run do
  let inside : Std.HashSet Name := (v.groupNodes name).foldl (init := {}) fun s n => s.insert n.id
  let mut out := #[]
  for n in v.groupNodes name do
    for d in v.effDeps n.id do
      unless inside.contains d || out.contains d do out := out.push d
  return out

/-- Ready when not done and every outside dependency is proved. -/
def groupReady (v : View) (name : String) : Bool :=
  !v.groupDone name && (v.groupNodes name).size > 0 &&
    (v.outsideDeps name).all fun d => v.state d == .proved

/-- A cycle among suggested dependencies, if any (as the list of ids on it). -/
partial def suggestedCycle (v : View) : Option (List Name) := Id.run do
  -- 0 = unvisited, 1 = on stack, 2 = done
  let mut color : Std.HashMap Name Nat := {}
  let mut found : Option (List Name) := none
  for (id, _) in v.plan.nodes.toArray do
    if found.isSome then break
    if color.getD id 0 == 0 then
      let (c, f) := go v color [] id
      color := c
      found := f
  return found
where
  go (v : View) (color : Std.HashMap Name Nat) (stack : List Name) (id : Name) :
      Std.HashMap Name Nat × Option (List Name) := Id.run do
    let mut color := color.insert id 1
    let stack := id :: stack
    let deps := match v.plan.nodes[id]? with | some n => n.deps | none => #[]
    for d in deps do
      match color.getD d 0 with
      | 1 => return (color, some (d :: stack.takeWhile (· != d) ++ [d]).reverse)
      | 0 =>
        let (c, f) := go v color stack d
        color := c
        if f.isSome then return (color, f)
      | _ => pure ()
    return (color.insert id 2, none)

end View

end Tracker
