import Tracker.Types

/-!
# The check cache

A check writes `.lake/tracker/check.json` under the project root; every command reads it, after
making sure it is fresh. It is never committed. Freshness is judged by content hashes alone, of
the plan files, of the project's oleans, and of the check's inputs; never by timestamps.
-/

open Lean

namespace Tracker

def cachePath (root : System.FilePath) : System.FilePath :=
  root / ".lake" / "tracker" / "check.json"

/-- The cache on disk, if there is one and it reads; one of another format reads as none. -/
def readCache (root : System.FilePath) : IO (Option Cache) := do
  let p := cachePath root
  unless ← p.pathExists do return none
  let s ← IO.FS.readFile p
  match Json.parse s >>= fromJson? with
  | .ok c => return some c
  | .error _ => return none

/-- Write the cache through a temporary file, so that a concurrent reader never sees half of it. -/
def writeCache (root : System.FilePath) (c : Cache) : IO Unit := do
  let p := cachePath root
  if let some d := p.parent then IO.FS.createDirAll d
  let text := (toJson c).pretty ++ "\n"
  let tmp := p.addExtension "tmp"
  IO.FS.writeFile tmp text
  try
    if ← p.pathExists then IO.FS.removeFile p
    IO.FS.rename tmp p
  catch _ =>
    IO.FS.writeFile p text
    try IO.FS.removeFile tmp catch _ => pure ()

/-- A hash of a file's bytes, or none when there is no file. -/
def fileHash? (p : System.FilePath) : IO (Option String) := do
  unless ← p.pathExists do return none
  return some (hex (← IO.FS.readBinFile p).hash)

/--
The fingerprint of a compiled module: Lake's `.olean.hash` beside the olean when there is one,
which spares reading the olean, else a hash of the olean itself. None when the olean is missing.
-/
def oleanFingerprint (olean : System.FilePath) : IO (Option String) := do
  let h := olean.addExtension "hash"
  if ← h.pathExists then
    let s := String.ofList ((← IO.FS.readFile h).toList.filter Char.isAlphanum)
    if !s.isEmpty then return some s
  fileHash? olean

/--
Why the cache cannot be answered from, empty when it can: compare it with the plan, the
options, and the project's oleans as they are now. An edit that has not been built is
invisible here, as everywhere in the tracker, which reads oleans and never builds.
-/
def staleness (plan : Plan) (cache : Option Cache) (roots : Array Name) (loadExts : Bool) :
    IO (Array String) := do
  let some c := cache | return #["no cache"]
  let mut stale : Array String := #[]
  if c.version != cacheVersion then stale := stale.push "cache format changed"
  let byName (a : Array Name) := a.qsort (·.toString < ·.toString)
  if byName c.roots != byName roots then stale := stale.push "root modules changed"
  if c.loadExts != loadExts then stale := stale.push "options changed"
  if c.planHash != plan.hash then stale := stale.push "plan changed"
  let mut rebuilt : Array String := #[]
  for m in c.modules do
    match ← oleanFingerprint (System.FilePath.mk m.olean) with
    | none => rebuilt := rebuilt.push s!"{m.module} (olean missing)"
    | some h => if h != m.hash then rebuilt := rebuilt.push m.module.toString
  if !rebuilt.isEmpty then
    let more := if rebuilt.size > 3 then s!", … ({rebuilt.size} in all)" else ""
    stale := stale.push s!"rebuilt: {", ".intercalate (rebuilt.toList.take 3)}{more}"
  return stale

end Tracker
