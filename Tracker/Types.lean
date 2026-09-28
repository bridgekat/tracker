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

/-- What a declaration is, read from the compiled library. -/
inductive DeclKind where
  | definition
  | theorem
  | axiom
  deriving BEq, Repr, Inhabited, DecidableEq

namespace DeclKind

def toString : DeclKind → String
  | .definition => "definition"
  | .theorem => "theorem"
  | .axiom => "axiom"

instance : ToString DeclKind := ⟨DeclKind.toString⟩

def parse? : String → Option DeclKind
  | "definition" => some .definition
  | "theorem" => some .theorem
  | "axiom" => some .axiom
  | _ => none

end DeclKind

/-- An object of the fields that are present: a field at its default is left out. -/
def objOmitting (fields : List (String × Option Json)) : Json :=
  Json.mkObj (fields.filterMap fun (k, v) => v.map (k, ·))

/-- `some` unless the array is empty. -/
def nonEmpty? (a : Array α) : Option (Array α) := if a.isEmpty then none else some a

/-- The standard axioms a proved node may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/--
One entry of the cache: a declaration of the project, or a planned node's id, which may not
resolve or may resolve to something that is not a declaration (outside the project, private, or
generated).
-/
structure CacheEntry where
  id : Name
  /-- Whether it is one of the project's declarations, and not only a planned node's id. -/
  declaration : Bool := true
  /-- What the id resolves to; none when it does not resolve. -/
  kind : Option DeclKind := none
  /-- The index in `Cache.modules` of the module it is in. -/
  module : Option Nat := none
  line : Option Nat := none
  /-- The axioms it rests on, when they are not all standard ones; empty when they are. -/
  axioms : Array Name := #[]
  /-- The entries reachable from it through the other constants of the project, as indexes into
  `Cache.entries`: its real dependencies at the finest grain. -/
  refs : Array Nat := #[]
  signature : String := ""
  /-- The doc comment, which supersedes a planned node's `desc`. -/
  doc : Option String := none
  deriving Inhabited

namespace CacheEntry

def found (e : CacheEntry) : Bool := e.kind.isSome
def hasSorry (e : CacheEntry) : Bool := e.axioms.contains ``sorryAx

/-- Its state from the compiled library alone: open when it does not resolve. -/
def state (e : CacheEntry) : NodeState :=
  if !e.found then .«open»
  else if e.hasSorry then .stated
  else if e.kind == some .axiom || !e.axioms.isEmpty then .axioms
  else .proved

instance : ToJson CacheEntry where
  toJson e := objOmitting [
    ("id", some (toJson e.id)),
    ("declaration", if e.declaration then none else some (toJson false)),
    ("kind", e.kind.map (toJson ·.toString)),
    ("module", e.module.map toJson), ("line", e.line.map toJson),
    ("axioms", (nonEmpty? e.axioms).map toJson), ("refs", (nonEmpty? e.refs).map toJson),
    ("signature", if e.signature.isEmpty then none else some (toJson e.signature)),
    ("doc", e.doc.map toJson)]

instance : FromJson CacheEntry where
  fromJson? j := do
    let opt {α} [FromJson α] (k : String) : Except String (Option α) :=
      match j.getObjVal? k with
      | .ok v => some <$> fromJson? v
      | .error _ => pure none
    let kind ← match ← opt (α := String) "kind" with
      | some s => match DeclKind.parse? s with
        | some k => pure (some k)
        | none => throw s!"unknown kind '{s}'"
      | none => pure none
    return {
      id := ← j.getObjValAs? Name "id"
      declaration := (← opt "declaration").getD true
      kind, module := ← opt "module", line := ← opt "line"
      axioms := (← opt "axioms").getD #[], refs := (← opt "refs").getD #[]
      signature := (← opt "signature").getD "", doc := ← opt "doc" }

end CacheEntry

structure Regression where
  id : Name
  before : String
  after : String
  deriving ToJson, FromJson, Inhabited

/-- Bumped whenever the cache's meaning changes; a cache of another version is stale. -/
def cacheVersion : Nat := 5

/-- A module an entry is in. The project's modules are fingerprinted at check time; a module
outside the project is only named. -/
structure ModuleRec where
  /-- The module name. -/
  name : Name
  /-- For a module of the project: the olean it was read from. -/
  olean : Option String := none
  /-- For a module of the project: its fingerprint, Lake's `.olean.hash` beside the olean, else
  a hash of the olean. -/
  hash : Option String := none
  /-- The first `/-! … -/` block of the module, which supersedes the module plan's `desc`. -/
  doc : Option String := none
  deriving ToJson, FromJson, Inhabited

/--
The check cache, `.lake/tracker/check.json` under the project root. It records what the compiled
library says and nothing the plan says, so that editing a module plan needs no new check unless it
names ids the cache has not resolved.
-/
structure Cache where
  version : Nat := cacheVersion
  roots : Array Name := #[]
  loadExts : Bool := true
  /-- The project's modules, sorted by module name, then any other module an entry is in. -/
  modules : Array ModuleRec := #[]
  /-- Every declaration of the project, and every planned node's id at check time, sorted by id. -/
  entries : Array CacheEntry := #[]
  /-- The planned nodes whose state went down at the check that wrote the cache. -/
  regressions : Array Regression := #[]
  deriving ToJson, FromJson, Inhabited

end Tracker
