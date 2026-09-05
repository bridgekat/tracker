import Lean
import Lake.Toml

/-!
# TOML helpers

Thin wrappers around `Lake.Toml`: load a file, run a decoder, and report errors with positions.
-/

open Lean Lake Lake.Toml

namespace Tracker.Toml

structure Loaded where
  table : Table
  ictx : Parser.InputContext

/-- Parse a TOML file. Parse errors come back as one string with positions. -/
def load (path : System.FilePath) : IO (Except String Loaded) := do
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  match ← (loadToml ictx).toBaseIO with
  | .ok t => return .ok { table := t, ictx }
  | .error log =>
    let msgs ← log.toList.mapM fun m => do
      let text ← m.data.toString
      pure s!"{m.pos.line}:{m.pos.column}: {text}"
    return .error (String.intercalate "; " msgs)

def lineOf (ictx : Parser.InputContext) (ref : Syntax) : Nat :=
  match ref.getPos? with
  | some p => (ictx.fileMap.toPosition p).line
  | none => 0

def posOf (ictx : Parser.InputContext) (ref : Syntax) : String :=
  match ref.getPos? with
  | some p =>
    let pos := ictx.fileMap.toPosition p
    s!"{pos.line}:{pos.column}"
  | none => "?"

/-- Record an error and abort the decoder. -/
def fail (ref : Syntax) (msg : String) : EDecodeM α :=
  fun errs => .error () (errs.push { ref, msg })

/-- Record an error and go on. -/
def report (ref : Syntax) (msg : String) : EDecodeM Unit :=
  fun errs => .ok () (errs.push { ref, msg })

/-- An error for every key of the table that is not a known one, at the key's value. -/
def unknownKeys (t : Table) (known : List Name) (hint : String) : EDecodeM Unit := do
  for k in t.keys do
    unless known.contains k do
      let ref := ((t.find? k).map (·.ref)).getD Syntax.missing
      report ref s!"unknown key '{k}' ({hint})"

/-- Run a decoder, keeping its errors but continuing with `none` on failure. -/
def recover (x : EDecodeM α) : EDecodeM (Option α) := fun s =>
  match x s with
  | .ok a s' => .ok (some a) s'
  | .error _ s' => .ok none s'

/-- Run a decoder: its errors as strings prefixed with `line:col`, and its result if it has one. -/
def run (ictx : Parser.InputContext) (x : EDecodeM α) : Array String × Option α :=
  let render (errs : Array DecodeError) := errs.map fun e => s!"{posOf ictx e.ref}: {e.msg}"
  match x.run #[] with
  | .ok a errs => (render errs, some a)
  | .error _ errs => (render errs, none)

def str? (t : Table) (k : Name) : EDecodeM (Option String) := do
  match t.find? k with
  | none => pure none
  | some v => some <$> v.decodeString

def str (t : Table) (k : Name) (ref : Syntax) : EDecodeM String := do
  match t.find? k with
  | none => fail ref s!"missing field '{k}'"
  | some v => v.decodeString

def name? (t : Table) (k : Name) : EDecodeM (Option Name) := do
  match t.find? k with
  | none => pure none
  | some v => some <$> v.decodeName

def strArray? (t : Table) (k : Name) : EDecodeM (Array String) := do
  match t.find? k with
  | none => pure #[]
  | some v => (← v.decodeValueArray).mapM (·.decodeString)

/-- An array of tables, each with the syntax of its header for messages. -/
def tables (t : Table) (k : Name) : EDecodeM (Array (Table × Syntax)) := do
  match t.find? k with
  | none => pure #[]
  | some v => (← v.decodeValueArray).mapM fun v => do pure (← v.decodeTable, v.ref)

end Tracker.Toml
