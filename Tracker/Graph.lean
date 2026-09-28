import Tracker.Types
import Tracker.Plan

/-!
# The graph

Everything computed from the plan and the cache: states, real and effective dependencies,
readiness, the module tree and its roll-ups, and cycle detection on the suggestions. The concepts
are those of the README's Concepts section.
-/

open Lean

namespace Tracker

/-- The plan and cache joined: what every command reads. -/
structure View where
  plan : Plan
  cache : Option Cache
  /-- The cache's entries: the declarations and the planned declarations' ids at check time. -/
  entries : Array CacheEntry := #[]
  /-- The index in `entries` of each id. -/
  index : Std.HashMap Name Nat := {}
  /-- The module names of `Cache.modules`, which `CacheEntry.module` indexes. -/
  entryModules : Array Name := #[]
  /-- The state of every planned declaration. -/
  states : Std.HashMap Name NodeState := {}
  /-- Real dependencies of the planned declarations, derived from the entries' `refs`. -/
  real : Std.HashMap Name (Array Name) := {}
  /-- Effective dependencies: suggested while open, real once proved, both in between. -/
  eff : Std.HashMap Name (Array Name) := {}
  /-- Reverse of `eff`. -/
  dependents : Std.HashMap Name (Array Name) := {}
  /-- The project's compiled modules, by module name. -/
  compiled : Std.HashMap Name ModuleRec := {}
  /-- The module name of every module of the tree, sorted. -/
  modules : Array Name := #[]
  /-- The modules directly under each module of the tree, sorted. -/
  children : Std.HashMap Name (Array Name) := {}
  /-- The ids of the declarations of the project, by the module name of the module they are in. -/
  moduleDecls : Std.HashMap Name (Array Name) := {}

/-- The state of a planned declaration: its declaration's, unless it is marked wrong. -/
def nodeState (n : Node) (e : Option CacheEntry) : NodeState :=
  if n.wrong.isSome then .wrong else (e.map (·.state)).getD .«open»

private def dedup (xs : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

/-- The module names above a module name: `Numbers` for `Numbers.Odd`. -/
private def modulesAbove : Name → List Name
  | .str p _ | .num p _ => if p.isAnonymous then [] else p :: modulesAbove p
  | .anonymous => []

/--
The planned entries reachable from entry `i` through unplanned ones, memoized: the real
dependencies at the grain of planned declarations, from the finest grain `refs` records. Sound
because `refs` is acyclic.
-/
private partial def plannedReach (entries : Array CacheEntry) (planned : Array Bool) (i : Nat) :
    StateM (Std.HashMap Nat (Array Nat)) (Array Nat) := do
  if let some out := (← get)[i]? then return out
  modify (·.insert i #[])
  let mut acc : Std.HashSet Nat := {}
  for r in (entries[i]?.map (·.refs)).getD #[] do
    if planned[r]?.getD false then acc := acc.insert r
    else acc := acc.insertMany (← plannedReach entries planned r)
  let out := acc.toArray
  modify (·.insert i out)
  return out

def mkView (plan : Plan) (cache : Option Cache) : View := Id.run do
  let mut v : View := { plan, cache }
  let mut inTree : Std.HashSet Name := plan.modules.foldl (init := {}) (·.insert ·.module)
  if let some c := cache then
    v := { v with
      entries := c.entries
      index := c.entries.foldl (init := {}) fun m e => m.insert e.id m.size
      entryModules := c.modules.map (·.name) }
    for m in c.modules do
      if m.olean.isSome then
        v := { v with compiled := v.compiled.insert m.name m }
        inTree := inTree.insert m.name
    for e in c.entries do
      if e.declaration then
        if let some m := e.module >>= (v.entryModules[·]?) then
          v := { v with moduleDecls := v.moduleDecls.insert m ((v.moduleDecls.getD m #[]).push e.id) }
  -- real dependencies of the planned declarations, through the unplanned entries
  let planned := v.entries.map fun e => plan.nodes.contains e.id
  let mut memo : Std.HashMap Nat (Array Nat) := {}
  for (id, n) in plan.nodes.toArray do
    let e := v.index[id]? >>= (v.entries[·]?)
    let st := nodeState n e
    v := { v with states := v.states.insert id st }
    let mut real : Array Name := #[]
    if let some i := v.index[id]? then
      let mut acc : Std.HashSet Nat := {}
      for r in (e.map (·.refs)).getD #[] do
        if planned[r]?.getD false then acc := acc.insert r
        else
          let (out, memo') := (plannedReach v.entries planned r).run memo
          memo := memo'
          acc := acc.insertMany out
      real := sortNames ((acc.erase i).toArray.filterMap fun j => v.entries[j]?.map (·.id))
    let eff := match st with
      | .«open» => n.deps
      | .proved | .axioms => real
      | .stated | .wrong => dedup (n.deps ++ real)
    v := { v with real := v.real.insert id real, eff := v.eff.insert id eff }
  for (id, deps) in v.eff.toArray do
    for d in deps do
      v := { v with dependents := v.dependents.insert d ((v.dependents.getD d #[]).push id) }
  -- the module tree: every module there is, and every module name above one
  for m in inTree.toArray do
    inTree := inTree.insertMany (modulesAbove m)
  let modules := sortNames inTree.toArray
  let mut children : Std.HashMap Name (Array Name) := {}
  for m in modules do
    let p := m.getPrefix
    if !p.isAnonymous then children := children.insert p ((children.getD p #[]).push m)
  return { v with modules, children }

namespace View

/-- The cache's entry for an id, if it has one. -/
def entry? (v : View) (id : Name) : Option CacheEntry := v.index[id]? >>= (v.entries[·]?)

/-- The module name of the module an entry is in. -/
def entryModule? (v : View) (e : CacheEntry) : Option Name := e.module >>= (v.entryModules[·]?)

/-- Whether an id is a planned declaration's. -/
def isPlanned (v : View) (id : Name) : Bool := v.plan.nodes.contains id

/-- Whether an id is a declaration's. -/
def isDeclaration (v : View) (id : Name) : Bool := (v.entry? id).any (·.declaration)

/-- The state of a declaration, planned or not. -/
def state (v : View) (id : Name) : NodeState :=
  v.states.getD id (((v.entry? id).map (·.state)).getD .«open»)

/-- Whether the declaration has a doc comment, which then supersedes the plan's `desc`. -/
def hasDoc (v : View) (id : Name) : Bool := ((v.entry? id).bind (·.doc)).isSome

/-- The kind in force: the declaration's once it exists, else the plan's `kind`. -/
def kindOf? (v : View) (id : Name) : Option String :=
  match (v.entry? id).bind (·.kind) with
  | some k => some k.toString
  | none => ((v.plan.node? id).bind (·.kind)).map toString

def kindName (v : View) (id : Name) : String := (v.kindOf? id).getD "?"

/-- The description in force: the doc comment once there is one, else the plan's `desc`. -/
def descOf (v : View) (id : Name) : String :=
  match (v.entry? id).bind (·.doc) with
  | some d => d
  | none => ((v.plan.node? id).bind (·.desc)).getD ""

def effDeps (v : View) (id : Name) : Array Name := v.eff.getD id #[]
def realDeps (v : View) (id : Name) : Array Name := v.real.getD id #[]

/-- The entries an entry refers to, through the other constants of the project. -/
def refsOf (v : View) (id : Name) : Array Name :=
  ((v.entry? id).map (·.refs)).getD #[] |>.filterMap fun i => v.entries[i]?.map (·.id)

/-- The planned declarations an unplanned entry leads to, through other unplanned entries. -/
def plannedUses (v : View) (id : Name) : Array Name :=
  match v.index[id]? with
  | none => #[]
  | some i =>
    let planned := v.entries.map fun e => v.plan.nodes.contains e.id
    sortNames (((plannedReach v.entries planned i).run' {}).filterMap fun j => v.entries[j]?.map (·.id))

/-- The entries that refer to an entry. -/
def referrersOf (v : View) (id : Name) : Array Name :=
  match v.index[id]? with
  | some i => v.entries.filterMap fun e => if e.refs.contains i then some e.id else none
  | none => #[]

/-- The module name of the module a declaration, planned or not, is in: for a planned
declaration, the module whose plan names it. -/
def moduleOf? (v : View) (id : Name) : Option Name :=
  match v.plan.node? id with
  | some n => some n.module
  | none => (v.entry? id).bind v.entryModule?

/-- A planned declaration is ready when it is not yet proved and every effective dependency is
proved. -/
def nodeReady (v : View) (id : Name) : Bool :=
  match v.state id with
  | .«open» | .stated => (v.effDeps id).all fun d => v.state d == .proved
  | _ => false

/-- The modules without a module above them, sorted. -/
def rootModules (v : View) : Array Name :=
  v.modules.filter (·.getPrefix.isAnonymous)

/-- The module and every module under it. -/
partial def subtree (v : View) (m : Name) : Array Name := Id.run do
  let mut out := #[]
  let mut stack := [m]
  while true do
    match stack with
    | [] => break
    | x :: rest =>
      out := out.push x
      stack := (v.children.getD x #[]).toList ++ rest
  return out

/-- The planned declarations of a module's own plan. -/
def ownNodes (v : View) (m : Name) : Array Node :=
  (v.plan.modulePlan? m).map (·.nodes) |>.getD #[]

/-- The planned declarations of a module and of every module under it. -/
def subtreeNodes (v : View) (m : Name) : Array Node := (v.subtree m).flatMap v.ownNodes

/-- A module's own planned declarations that can be worked on: open or stated. -/
def ownWork (v : View) (m : Name) : Array Node :=
  (v.ownNodes m).filter fun n => match v.state n.id with
    | .«open» | .stated => true
    | _ => false

/-- Whether a module exists: it is one of the compiled modules of the project. -/
def moduleExists (v : View) (m : Name) : Bool := v.compiled.contains m

/-- The module's doc comment, which then supersedes its plan's `desc`. -/
def moduleDoc? (v : View) (m : Name) : Option String := v.compiled[m]?.bind (·.doc)

/-- The description in force: the module's doc comment once there is one, else its plan's `desc`. -/
def moduleDesc (v : View) (m : Name) : String :=
  match v.moduleDoc? m with
  | some d => d
  | none => ((v.plan.modulePlan? m).bind (·.desc)).getD ""

/-- Counts of planned declarations by state. -/
structure Counts where
  «open» : Nat := 0
  stated : Nat := 0
  proved : Nat := 0
  axioms : Nat := 0
  wrong : Nat := 0
  deriving Inhabited

def Counts.total (c : Counts) : Nat := c.open + c.stated + c.proved + c.axioms + c.wrong

def countNodes (v : View) (ns : Array Node) : Counts :=
  ns.foldl (init := {}) fun c n =>
    match v.state n.id with
    | .«open» => { c with «open» := c.open + 1 }
    | .stated => { c with stated := c.stated + 1 }
    | .proved => { c with proved := c.proved + 1 }
    | .axioms => { c with axioms := c.axioms + 1 }
    | .wrong => { c with wrong := c.wrong + 1 }

/-- Planned declaration counts over a module and every module under it. -/
def counts (v : View) (m : Name) : Counts := v.countNodes (v.subtreeNodes m)

/-- Planned declaration counts over the whole plan. -/
def totals (v : View) : Counts := v.countNodes (v.plan.modules.flatMap (·.nodes))

/-- Counts of declarations by kind. -/
structure DeclCounts where
  definitions : Nat := 0
  theorems : Nat := 0
  deriving Inhabited

def DeclCounts.total (c : DeclCounts) : Nat := c.definitions + c.theorems

def countDecls (v : View) (ids : Array Name) : DeclCounts :=
  ids.foldl (init := {}) fun c id =>
    if ((v.entry? id).bind (·.kind)) == some .theorem then { c with theorems := c.theorems + 1 }
    else { c with definitions := c.definitions + 1 }

/-- Declaration counts over a module and every module under it. -/
def declCounts (v : View) (m : Name) : DeclCounts :=
  v.countDecls ((v.subtree m).flatMap (v.moduleDecls.getD · #[]))

/-- Declaration counts over the whole project. -/
def declTotals (v : View) : DeclCounts :=
  v.countDecls (v.moduleDecls.fold (init := #[]) fun a _ ids => a ++ ids)

/-- Done when every planned declaration in and under the module is proved (and there is at least
one). -/
def moduleDone (v : View) (m : Name) : Bool :=
  let ns := v.subtreeNodes m
  !ns.isEmpty && ns.all fun n => v.state n.id == .proved

/-- Dependencies of the module's workable planned declarations that are not its own planned
declarations. -/
def outsideDeps (v : View) (m : Name) : Array Name := Id.run do
  let inside : Std.HashSet Name := (v.ownNodes m).foldl (init := {}) fun s n => s.insert n.id
  let mut out := #[]
  for n in v.ownWork m do
    for d in v.effDeps n.id do
      unless inside.contains d || out.contains d do out := out.push d
  return out

/--
Ready when the module has open or stated planned declarations of its own and every dependency of
those outside the module is proved: the module can be worked on now.
-/
def moduleReady (v : View) (m : Name) : Bool :=
  !(v.ownWork m).isEmpty && (v.outsideDeps m).all fun d => v.state d == .proved

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
