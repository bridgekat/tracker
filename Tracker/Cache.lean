import Tracker.Types

/-!
# The check cache

`tracker check` writes `.lake/tracker/check.json` under the project root; everything else reads
it. It is never committed.
-/

open Lean

namespace Tracker

def cachePath (root : System.FilePath) : System.FilePath :=
  root / ".lake" / "tracker" / "check.json"

def readCache (root : System.FilePath) : IO (Option Cache) := do
  let p := cachePath root
  unless ← p.pathExists do return none
  let s ← IO.FS.readFile p
  match Json.parse s >>= fromJson? with
  | .ok c => return some c
  | .error e =>
    IO.eprintln s!"warning: could not read {p}: {e}"
    return none

def writeCache (root : System.FilePath) (c : Cache) : IO Unit := do
  let p := cachePath root
  if let some d := p.parent then IO.FS.createDirAll d
  IO.FS.writeFile p ((toJson c).pretty ++ "\n")

end Tracker
