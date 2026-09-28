import Lean

/-!
# Types

The plan (hand-written intent, read from TOML module plans) and the cache (derived state, written
by `tracker check`). Nothing here is computed; see `Tracker.Graph` for that.
-/

open Lean

namespace Tracker

/-- A 64-bit hash as hex, the form Lake's `.olean.hash` files use. -/
def hex (h : UInt64) : String := String.ofList (Nat.toDigits 16 h.toNat)

/-- Without leading and trailing whitespace. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Sort names by their printed form, printing each once rather than twice per comparison. -/
def sortNames (ns : Array Name) : Array Name :=
  (ns.map fun n => (n.toString, n)).qsort (·.1 < ·.1) |>.map (·.2)

/-- A planned node, or a declaration, is a definition or a theorem. -/
inductive NodeKind where
  | definition
  | theorem
  deriving BEq, Repr, Inhabited, DecidableEq

namespace NodeKind

def toString : NodeKind → String
  | .definition => "definition"
  | .theorem => "theorem"

instance : ToString NodeKind := ⟨NodeKind.toString⟩

def parse? : String → Option NodeKind
  | "definition" | "def" => some .definition
  | "theorem" | "thm" | "lemma" => some .theorem
  | _ => none

end NodeKind

/-- A planned node: one `[[node]]` entry of a module plan, after id resolution. -/
structure Node where
  /-- The fully qualified Lean identifier the declaration has or will have. -/
  id : Name
  /-- Definition or theorem, until the declaration exists and says so itself. -/
  kind : Option NodeKind := none
  /-- The natural-language statement, until the declaration has a doc comment. -/
  desc : Option String := none
  /-- Suggested dependencies, resolved to planned node ids. -/
  deps : Array Name := #[]
  /-- Where the statement comes from, e.g. `Textbook, Theorem 1.2`. -/
  source : Option String := none
  /-- Set by hand when the statement was found false or unprovable as stated. -/
  wrong : Option String := none
  /-- Set by hand when the node is on its way out: why, and what to use instead. -/
  deprecated : Option String := none
  /-- The module name of the module plan that names this node. -/
  module : Name := .anonymous
  /-- Line of the `[[node]]` header in the module plan, for messages. -/
  line : Nat := 0
  /-- The id as written, before namespace resolution. -/
  rawId : String := ""
  /-- The dependencies as written, before resolution. -/
  rawDeps : Array String := #[]
  deriving Inhabited

/--
A module plan: one TOML file under the plan directory, the plan for one module. The file sits
where the module's source file sits under the project root: the plan of the module named
`Numbers.Odd`, whose source is `Numbers/Odd.lean`, is `Numbers/Odd.toml`.
-/
structure ModulePlan where
  /-- The module name, as `import` writes it: `Numbers.Odd`. -/
  module : Name
  /-- Ids in the module plan are resolved relative to this namespace. -/
  «namespace» : Option Name := none
  /-- What the module is for, until it exists and has a doc comment. -/
  desc : Option String := none
  nodes : Array Node := #[]
  /-- The module plan's file. -/
  path : System.FilePath := ""
  deriving Inhabited

/-- The module name a module plan's file stands for, from the file's path components under the
plan directory without `.toml`: `Numbers.Odd` for `["Numbers", "Odd"]`. -/
def planModuleName (components : List String) : Name :=
  components.foldl Name.str .anonymous

/-- Every module plan, with indexes. `errors` collects everything that went wrong while loading. -/
structure Plan where
  modules : Array ModulePlan := #[]
  /-- The planned nodes by id. -/
  nodes : Std.HashMap Name Node := {}
  /-- The index in `modules` of each module plan, by module name. -/
  moduleIdx : Std.HashMap Name Nat := {}
  errors : Array String := #[]
  /-- A hash of every module plan's file path and content, by which a cache knows it is stale. -/
  hash : String := ""

/-- The plan of a module, by module name, if it has one. -/
def Plan.modulePlan? (p : Plan) (m : Name) : Option ModulePlan :=
  p.moduleIdx[m]? >>= fun i => p.modules[i]?

def Plan.node? (p : Plan) (id : Name) : Option Node := p.nodes[id]?

/-- The state of a planned node or a declaration, derived from the compiled library except for
`wrong`. -/
inductive NodeState where
  /-- The id does not resolve; the node is a plan. -/
  | «open»
  /-- The declaration exists and depends on `sorry`. -/
  | stated
  /-- The declaration exists, no `sorry`, standard axioms only. -/
  | proved
  /-- The declaration exists and depends on an axiom outside the standard three. -/
  | axioms
  /-- The `wrong` field is set. -/
  | wrong
  deriving BEq, Repr, Inhabited, DecidableEq

namespace NodeState

def toString : NodeState → String
  | .«open» => "open"
  | .stated => "stated"
  | .proved => "proved"
  | .axioms => "axioms"
  | .wrong => "wrong"

instance : ToString NodeState := ⟨NodeState.toString⟩

def parse? : String → Option NodeState
  | "open" => some .«open»
  | "stated" => some .stated
  | "proved" => some .proved
  | "axioms" => some .axioms
  | "wrong" => some .wrong
  | _ => none

/-- Progress order, for regression detection. `wrong` is outside the order. -/
def rank : NodeState → Nat
  | .«open» => 0
  | .stated => 1
  | .axioms => 2
  | .proved => 3
  | .wrong => 0

end NodeState

/--
What `tracker check` learned about one id: a declaration of the project, or a planned node's id
(which then may not resolve, or may resolve outside the project).
-/
structure DeclInfo where
  id : Name
  /-- Whether it is one of the project's declarations, and not only a planned node's id. -/
  declaration : Bool := false
  found : Bool := false
  /-- The module name of the module the declaration is in. -/
  module : Option Name := none
  line : Option Nat := none
  isTheorem : Bool := false
  isAxiom : Bool := false
  hasSorry : Bool := false
  axioms : Array Name := #[]
  axiomsOk : Bool := false
  /-- Planned nodes reachable from the declaration through unplanned constants of the project:
  its real dependencies, when it is a planned node. -/
  uses : Array Name := #[]
  /-- Declarations and planned nodes reachable from the declaration through the other constants
  of the project, as indexes into `Cache.decls`. -/
  refs : Array Nat := #[]
  signature : String := ""
  /-- The declaration's doc comment, which supersedes the plan's `desc`. -/
  doc : Option String := none
  deriving ToJson, FromJson, Inhabited

structure StateRec where
  id : Name
  state : String
  deriving ToJson, FromJson, Inhabited

structure Regression where
  id : Name
  before : String
  after : String
  deriving ToJson, FromJson, Inhabited

/-- Bumped whenever the cache's meaning changes; a cache of another version is stale. -/
def cacheVersion : Nat := 4

/-- One compiled module of the project, fingerprinted at check time. -/
structure ModuleRec where
  module : Name
  /-- The olean the module was read from. -/
  olean : String
  /-- Its fingerprint: Lake's `.olean.hash` beside it, else a hash of the file. -/
  hash : String
  /-- The first `/-! … -/` block of the module, which supersedes the module plan's `desc`. -/
  doc : Option String := none
  deriving ToJson, FromJson, Inhabited

/-- The check cache, `.lake/tracker/check.json` under the project root. -/
structure Cache where
  version : Nat := cacheVersion
  roots : Array Name := #[]
  loadExts : Bool := true
  /-- `Plan.hash` of the plan the check ran against. -/
  planHash : String := ""
  modules : Array ModuleRec := #[]
  /-- Every declaration of the project, and every planned node's id, sorted by id. -/
  decls : Array DeclInfo := #[]
  /-- The state of every planned node. -/
  states : Array StateRec := #[]
  regressions : Array Regression := #[]
  deriving ToJson, FromJson, Inhabited

/-- The standard axioms a proved node may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

end Tracker
