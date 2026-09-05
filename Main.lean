import Tracker
import Lake.Toml

open Lean Tracker

/-- Parsed command line: positionals and `--flag[=value]` / `--flag value` options. -/
structure Args where
  positional : Array String := #[]
  flags : Std.HashMap String String := {}

def valueFlags : List String := ["dir", "root", "kind", "roots", "under"]

def parseArgs (args : List String) : Args := Id.run do
  let mut a : Args := {}
  let mut rest := args
  while true do
    match rest with
    | [] => break
    | arg :: tl =>
      rest := tl
      if arg.startsWith "--" then
        let body := String.mk (arg.toList.drop 2)
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

usage: tracker [--root DIR] [--dir DIR] <command> [args]

  check [--roots A,B] [--no-exts]   import the project, resolve every id, write the cache
  status [group] [--json]           counts per group, rolled up through parents; regressions
  ready [--kind K | --all] [--json] groups whose outside dependencies are all proved
  show <group|id>                   the brief for a group, or everything about one node
  lint                              plan errors, cycles, placement and kind mismatches
  graph [--under G] [--dot]         the graph as JSON (default) or Graphviz DOT

  --root DIR   project root (default: current directory)
  --dir DIR    directory of group files (default: <root>/tracker)
  --roots A,B  root modules to import for `check` (default: lean_lib names in lakefile.toml)"

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

unsafe def run (a : Args) : IO UInt32 := do
  let root : System.FilePath := (a.flags.get? "root").getD "."
  let dir : System.FilePath := match a.flags.get? "dir" with
    | some d => d
    | none => root / "tracker"
  let some cmd := a.positional[0]? | IO.println usage; return 2
  if cmd == "help" || a.flags.contains "help" then IO.println usage; return 0
  let plan ← loadPlan dir
  match cmd with
  | "check" =>
    if !plan.errors.isEmpty then
      for e in plan.errors do IO.eprintln s!"error: {e}"
      IO.eprintln "fix the plan before checking"
      return 1
    let roots ← match a.flags.get? "roots" with
      | some r => pure (r.splitOn "," |>.filter (!·.isEmpty) |>.map String.toName |>.toArray)
      | none => rootsFromLakefile root
    if roots.isEmpty then
      IO.eprintln "no root modules: pass --roots A,B or add a lean_lib to lakefile.toml"
      return 1
    let previous ← readCache root
    let cache ← runCheck root plan roots (loadExts := !a.flags.contains "no-exts") previous
    writeCache root cache
    let v := mkView plan (some cache)
    let c := plan.groups.foldl (init := ({} : View.Counts)) fun acc g =>
      if g.parent.isNone then
        let gc := v.counts g.name
        { «open» := acc.open + gc.open, stated := acc.stated + gc.stated, proved := acc.proved + gc.proved,
          axioms := acc.axioms + gc.axioms, wrong := acc.wrong + gc.wrong }
      else acc
    IO.println s!"{c.proved} proved, {c.stated} stated, {c.open} open, {c.wrong} wrong, {c.axioms} axioms; cache written to {cachePath root}"
    if !cache.regressions.isEmpty then
      IO.println "regressed since the previous check:"
      for r in cache.regressions do IO.println s!"  {r.id}: {r.before} → {r.after}"
    return 0
  | "status" =>
    let v := mkView plan (← readCache root)
    status v a.positional[1]? (a.flags.contains "json")
  | "ready" =>
    let v := mkView plan (← readCache root)
    ready v (a.flags.get? "kind") (a.flags.contains "all") (a.flags.contains "json")
  | "show" =>
    let some target := a.positional[1]? | IO.eprintln "show: give a group name or a node id"; return 2
    let v := mkView plan (← readCache root)
    «show» v target
  | "lint" =>
    let v := mkView plan (← readCache root)
    lint v
  | "graph" =>
    let v := mkView plan (← readCache root)
    graph v (a.flags.get? "under") (a.flags.contains "dot")
  | _ =>
    IO.eprintln s!"unknown command '{cmd}'\n"
    IO.println usage
    return 2

unsafe def main (argv : List String) : IO UInt32 := do
  try run (parseArgs argv)
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
