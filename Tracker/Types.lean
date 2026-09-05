import Lean

/-!
# Types

The plan (hand-written intent, read from TOML group files) and the cache (derived state, written
by `tracker check`). Nothing here is computed; see `Tracker.Graph` for that.
-/

open Lean

namespace Tracker

/-- A 64-bit hash as hex, the form Lake's `.olean.hash` files use. -/
def hex (h : UInt64) : String := String.ofList (Nat.toDigits 16 h.toNat)

/-- Without leading and trailing whitespace. -/
def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- A node is a definition or a theorem. -/
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

/-- One `[[node]]` entry of a group file, after id resolution. -/
structure Node where
  /-- The fully qualified Lean identifier the declaration has or will have. -/
  id : Name
  /-- Definition or theorem, until the declaration exists and says so itself. -/
  kind : Option NodeKind := none
  /-- The natural-language statement, until the declaration has a doc comment. -/
  desc : Option String := none
  /-- Suggested dependencies, resolved to node ids. -/
  deps : Array Name := #[]
  /-- Where the statement comes from, e.g. `Textbook, Theorem 1.2`. -/
  source : Option String := none
  /-- Set by hand when the statement was found false or unprovable as stated. -/
  wrong : Option String := none
  /-- The group (file stem) this node belongs to. -/
  group : String := ""
  /-- Line of the `[[node]]` header in the group file, for messages. -/
  line : Nat := 0
  /-- The id as written, before namespace resolution. -/
  rawId : String := ""
  /-- The dependencies as written, before resolution. -/
  rawDeps : Array String := #[]
  deriving Inhabited

/-- One group file: the plan for one module. -/
structure Group where
  /-- The file's path under the plan directory without `.toml`, with `/` between components,
  which is the module's path too: `Numbers/Odd` for `Numbers/Odd.toml`, the plan for
  `Numbers.Odd`. How the group is referred to everywhere. The directory of the same name beside
  the file holds the group's children. -/
  name : String
  /-- Ids inside the group are resolved relative to this namespace. -/
  «namespace» : Option Name := none
  /-- What the module is for, until it exists and has a doc comment. -/
  desc : Option String := none
  nodes : Array Node := #[]
  path : System.FilePath := ""
  deriving Inhabited

/-- The module a group is the plan for: `Numbers.Odd` for `Numbers/Odd`. -/
def Group.module (g : Group) : Name :=
  (g.name.splitOn "/").foldl (fun n c => Name.str n c) Name.anonymous

/-- All groups, with indexes. `errors` collects everything that went wrong while loading. -/
structure Plan where
  groups : Array Group := #[]
  nodes : Std.HashMap Name Node := {}
  groupIdx : Std.HashMap String Nat := {}
  errors : Array String := #[]
  /-- A hash of every group file's name and content, by which a cache knows it is stale. -/
  hash : String := ""

def Plan.group? (p : Plan) (name : String) : Option Group :=
  p.groupIdx[name]? >>= fun i => p.groups[i]?

def Plan.node? (p : Plan) (id : Name) : Option Node := p.nodes[id]?

/-- The last component of a group name: `odd` for `numbers/odd`. -/
def groupStem (name : String) : String := (name.splitOn "/").getLastD name

/-- The name of the directory a group file sits in: `numbers` for `numbers/odd`, none at the top. -/
def groupEnclosing? (name : String) : Option String :=
  match (name.splitOn "/").dropLast with
  | [] => none
  | parts => some (String.intercalate "/" parts)

/-- The group whose directory holds `name`, when its file exists: `numbers` for `numbers/odd`. -/
def Plan.parent? (p : Plan) (name : String) : Option String :=
  (groupEnclosing? name).filter p.groupIdx.contains

/-- The state of a node, derived from the compiled library except for `wrong`. -/
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

/-- What `tracker check` learned about one id. -/
structure DeclInfo where
  id : Name
  found : Bool := false
  module : Option Name := none
  line : Option Nat := none
  isTheorem : Bool := false
  isAxiom : Bool := false
  hasSorry : Bool := false
  axioms : Array Name := #[]
  axiomsOk : Bool := false
  /-- Tracked ids reachable from the declaration through untracked project constants. -/
  uses : Array Name := #[]
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
def cacheVersion : Nat := 3

/-- One compiled module of the project, fingerprinted at check time. -/
structure ModuleRec where
  module : Name
  /-- The olean the module was read from. -/
  olean : String
  /-- Its fingerprint: Lake's `.olean.hash` beside it, else a hash of the file. -/
  hash : String
  /-- The first `/-! … -/` block of the module, which supersedes the group's `desc`. -/
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
  decls : Array DeclInfo := #[]
  states : Array StateRec := #[]
  regressions : Array Regression := #[]
  deriving ToJson, FromJson, Inhabited

/-- The standard axioms a proved node may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

end Tracker
