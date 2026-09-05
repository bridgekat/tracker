import Tracker
import Lake.Toml

open Lean Tracker

/-- Parsed command line: positionals and `--flag[=value]` / `--flag value` options. -/
structure Args where
  positional : Array String := #[]
  flags : Std.HashMap String String := {}

def valueFlags : List String := ["dir", "root", "roots", "under"]

def parseArgs (args : List String) : Args := Id.run do
  let mut a : Args := {}
  let mut rest := args
  while true do
    match rest with
    | [] => break
    | arg :: tl =>
      rest := tl
      if arg.startsWith "--" then
        let body := String.ofList (arg.toList.drop 2)
        match body.splitOn "=" with
        | [k, v] => a := { a with flags := a.flags.insert k v }
        | _ =>
          if valueFlags.contains body then
            match rest with
            | v :: tl' => a := { a with flags := a.flags.insert body v }; rest := tl'
            | [] => a := { a with flags := a.flags.insert body "" }
          else a := { a with flags := a.flags.insert body "" }
      else a := { a with positional := a.positional.push arg }
  return a

def usage : String := "\
tracker — progress tracker for Lean formalization projects

usage: tracker [--root DIR] [--dir DIR] [--roots A,B] [--no-exts] [--no-check] <command> [args]

  check [--force]                   make the cache fresh: import the project, resolve every id
  status [group] [--json]           counts per group, rolled up through parents; regressions
  ready [--json]                    groups whose outside dependencies are all proved
  show <group|id>                   the brief for a group, or everything about one node
  lint                              plan errors, cycles, placement and kind mismatches
  graph [--under G] [--dot]         the graph as JSON (default) or Graphviz DOT

Every command checks first when the cache is stale, that is when the plan, the project's
oleans, the root modules or the options changed since it was written.

  --root DIR   project root (default: current directory)
  --dir DIR    directory of group files (default: <root>/tracker)
  --roots A,B  root modules to import (default: lean_lib names in lakefile.toml, else the cache's)
  --no-exts    skip the imported modules' initializers; printed signatures lose their notation
  --no-check   answer from the cache as it is, even if stale"

def commands : List String := ["check", "status", "ready", "show", "lint", "graph"]

/-- Root modules from the project's `lakefile.toml`. -/
def rootsFromLakefile (root : System.FilePath) : IO (Array Name) := do
  let p := root / "lakefile.toml"
  unless ← p.pathExists do return #[]
  match ← Tracker.Toml.load p with
  | .error _ => return #[]
  | .ok l =>
    match Tracker.Toml.run l.ictx (do
        let ts ← Tracker.Toml.tables l.table `lean_lib
        ts.filterMapM fun (t, _) => Tracker.Toml.name? t `name) with
    | (_, some names) => return names
    | _ => return #[]

/--
The cache to answer from, and whether a check ran for it. Fresh on disk: that one. Stale, or
`force`: a check run now, unless the plan has errors or there are no roots, in which case
`check` fails and the other commands say so and answer from what is there. `useStale` never
checks.
-/
unsafe def freshCache (root : System.FilePath) (plan : Plan) (previous : Option Cache)
    (roots : Array Name) (loadExts isCheck force useStale : Bool) :
    IO (Except UInt32 (Option Cache × Bool)) := do
  let stale ← staleness plan previous roots loadExts
  let mut cache := previous
  let mut ran := false
  let why := ", ".intercalate stale.toList
  if useStale then
    if previous.isSome && !stale.isEmpty then
      IO.eprintln s!"warning: the cache is stale ({why}); answering from it anyway"
  else if force || !stale.isEmpty then
    let blocked :=
      if !plan.errors.isEmpty then some "the plan has errors; run `tracker lint`"
      else if roots.isEmpty then some "no root modules; pass --roots A,B or add a lean_lib to lakefile.toml"
      else none
    match blocked with
    | some b =>
      if isCheck then
        for e in plan.errors do IO.eprintln s!"error: {e}"
        IO.eprintln b
        return .error 1
      let what := if previous.isNone then "missing" else s!"stale ({why})"
      IO.eprintln s!"warning: the cache is {what} and cannot be refreshed: {b}"
    | none =>
      IO.eprintln (if force then "checking" else if previous.isNone then "no cache; checking"
        else s!"cache stale ({why}); checking")
      let c ← runCheck plan roots loadExts previous
      writeCache root c
      cache := some c
      ran := true
      if !isCheck && !c.regressions.isEmpty then
        IO.eprintln "regressed since the previous check:"
        for r in c.regressions do IO.eprintln s!"  {r.id}: {r.before} → {r.after}"
  return .ok (cache, ran)

unsafe def run (a : Args) : IO UInt32 := do
  let root : System.FilePath := (a.flags.get? "root").getD "."
  let dir : System.FilePath := match a.flags.get? "dir" with
    | some d => d
    | none => root / "tracker"
  let some cmd := a.positional[0]? | IO.println usage; return 2
  if cmd == "help" || a.flags.contains "help" then IO.println usage; return 0
  unless commands.contains cmd do
    IO.eprintln s!"unknown command '{cmd}'\n"
    IO.println usage
    return 2
  if cmd == "show" && a.positional[1]?.isNone then
    IO.eprintln "show: give a group name or a node id"; return 2
  let plan ← loadPlan dir
  let previous ← readCache root
  let roots ← match a.flags.get? "roots" with
    | some r => pure (r.splitOn "," |>.filter (!·.isEmpty) |>.map String.toName |>.toArray)
    | none => rootsFromLakefile root
  let roots := if roots.isEmpty then (previous.map (·.roots)).getD #[] else roots
  let loadExts := !a.flags.contains "no-exts"
  let (cache?, ran) ← match ← freshCache root plan previous roots loadExts (cmd == "check")
      (a.flags.contains "force") (a.flags.contains "no-check") with
    | .error code => return code
    | .ok r => pure r
  let v := mkView plan cache?
  match cmd with
  | "check" =>
    let some cache := cache? | IO.eprintln "no cache"; return 1
    let c := plan.groups.foldl (init := ({} : View.Counts)) fun acc g =>
      if (plan.parent? g.name).isNone then
        let gc := v.counts g.name
        { «open» := acc.open + gc.open, stated := acc.stated + gc.stated, proved := acc.proved + gc.proved,
          axioms := acc.axioms + gc.axioms, wrong := acc.wrong + gc.wrong }
      else acc
    let tail := if ran then s!"cache written to {cachePath root}" else "cache is fresh (--force checks anyway)"
    IO.println s!"{c.proved} proved, {c.stated} stated, {c.open} open, {c.wrong} wrong, {c.axioms} axioms; {tail}"
    if ran && !cache.regressions.isEmpty then
      IO.println "regressed since the previous check:"
      for r in cache.regressions do IO.println s!"  {r.id}: {r.before} → {r.after}"
    return 0
  | "status" => status v a.positional[1]? (a.flags.contains "json")
  | "ready" => ready v (a.flags.contains "json")
  | "show" =>
    let some target := a.positional[1]? | return 2
    «show» v target
  | "lint" => lint v
  | "graph" => graph v (a.flags.get? "under") (a.flags.contains "dot")
  | _ => return 2

unsafe def main (argv : List String) : IO UInt32 := do
  try run (parseArgs argv)
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
