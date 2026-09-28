# tracker

A progress tracker for Lean formalization projects.

- **The plan** is a set of small TOML files naming the definitions and theorems that should exist.
- **The progress** is read from the compiled library (`.olean` files).

It answers what an orchestrator and its sub-agents need to know: what is proved, what is ready to
work on, what a task depends on, and what changed since last time.

## Setup

The tracker reads the project's oleans, so it must build on the project's toolchain. Add it as a
git submodule, so this README is in the tree for agents and its version is pinned with the project:

```
git submodule add https://github.com/bridgekat/tracker tools/tracker
```

```toml
# lakefile.toml
[[require]]
name = "tracker"
path = "tools/tracker"
```

```
lake build                 # the tracker reads oleans and never builds: build first
lake exe tracker init      # no plan yet? write a first one from the existing declarations
lake exe tracker check     # import the project, resolve every id, write the cache
lake exe tracker status
```

Add one line to the project's agent instructions: read `tools/tracker/README.md` before touching
the plan.

Alternatives:
- A `git = "…"` require works too; Lake keeps the clone under `.lake/packages/tracker/`.
- A clone built anywhere runs from the project root, with no `require`, as
  `lake env path/to/tracker/.lake/build/bin/tracker …`.

Either way the toolchain's `bin` must be on the path, since the tracker links Lean's shared library.

`examples/` is a small self-contained project whose plan (`examples/plans/`) exercises every state
and every lint: `cd examples && lake build && lake exe tracker check && lake exe tracker lint`.

## Commands

```
tracker [--root DIR] [--dir DIR] [--roots A,B] [--no-exts] [--no-check] <command> [args]

init                         write a first plan from the project's own declarations
check [--force]              make the cache fresh: import the project, resolve every id
status [group] [--json]      counts per group, rolled up through parents; regressions
ready [--json]               groups whose outside dependencies are all proved
show <group | id>            the brief for a group, or everything about one node
lint                         plan errors, cycles, mismatches, deprecations, superseded fields
graph [--under G] [--dot]    the graph as JSON (default) or Graphviz DOT
```

| option | meaning |
|---|---|
| `--root DIR` | project root (default `.`) |
| `--dir DIR` | plan directory (default `<root>/plans`) |
| `--roots A,B` | modules to import (default: the `lean_lib`s in `lakefile.toml`, else the cache's) |
| `--no-exts` | skip the imported modules' initializers; printed signatures lose their notation |
| `--no-check` | answer from the cache as it is, even if stale |

- **Naming.** A group is named by its path under the plan directory (`Numbers/Odd`) or an
  unambiguous trailing part of it (`Odd`). `show` also takes a node id, in full or by an
  unambiguous suffix.
- **Lint.** `lint` exits non-zero on errors, and no check runs while the plan has any.

### Cache

- Lives at `<root>/.lake/tracker/check.json`, and is never committed.
- Every command but `init` refreshes it first when stale: when the plan, the compiled modules, the
  root modules, the options, or the cache format changed. Staleness is judged by content hashes,
  never timestamps.
- `check` is that refresh alone; it does nothing unless the cache is stale or `--force` is given.
- `check` compares with the previous cache and reports every node whose state went down — this is
  how a renamed or broken declaration shows up.
- The tracker never builds, so unbuilt edits are invisible to it.

### `init`

For a project that has Lean but no plan. It refuses unless the plan directory is absent or empty,
writes only plan files, and then checks.

- One group file per compiled module, one node per declaration written there by hand.
- Left out: axioms, private declarations, and anything the elaborator generated (constructors,
  recursors, projections, `deriving` instances, `where` helpers).
- A directory with no module of its own gets a group file with a `TODO` description.

The result is a starting point, not a plan: it names every declaration, where a plan names the ones
that matter. Curate it by hand — drop nodes not worth tracking; `lint` names those left without a
description.

The tracker never edits plan files: `init` creates them where there are none, and nothing else
touches them.

### `graph`

The contract for anything that wants a picture; the tracker itself does not draw. `--under G`
restricts output to a group and its descendants. The JSON is one object with three arrays:

| array | fields |
|---|---|
| `groups` | `name`, `parent`, `desc`, `done`, `ready` |
| `nodes` | `id`, `group`, `kind`, `state`, `desc`, `source`, `wrong`, `deprecated` |
| `edges` | `from`, `to`, `real`, `suggested` |

- An edge means `from` depends on `to`. `real`: read from the proof; `suggested`: written in the
  plan; both may be set.
- A group's `parent` is the group whose directory holds it; its module is its name with `.` for `/`.
- The DOT form has one cluster per group, nodes filled by state, real edges solid, suggested edges
  dashed:

```
lake exe tracker graph --dot --under Numbers | dot -Tsvg -o numbers.svg
```

## Model

### Nodes

A node is a definition or theorem, named by the fully qualified Lean identifier it has or will
have, and described in natural language. It is *attached* once that identifier resolves in the
compiled environment; until then it is a plan.

Optional fields:
- `source` — e.g. a numbered result in a book.
- `wrong` — set by hand when the statement was found false or unprovable as stated; the value says why.
- `deprecated` — set by hand when the node is on its way out; the value says why and what replaces it.

**The declaration supersedes the plan.** The plan's `kind` applies until the declaration exists;
its `desc` until the declaration has a doc comment. From then on the declaration is authoritative
everywhere (`show`, `ready`, `graph`). A finished, documented node needs nothing in the plan but
its id.

**Identity.** Renaming a declaration renames the node. Correcting a statement means editing the
description and the Lean under the same name, or renaming if it deserves a new one. `wrong` is a
state a node passes through, not a new object. `deprecated` is not a state: the node counts as its
declaration says, and `lint` names it and everything still depending on it until the plan drops it.

### Dependencies

Each node lists the nodes its proof is expected to use (`deps`). These are *suggestions*.

| node state | dependencies in force |
|---|---|
| open | the suggestions |
| stated | the suggestions and the real dependencies |
| proved | the real dependencies only |

*Real* dependencies are the tracked ids reachable from the declaration's type and proof through
untracked constants of the project, stopping at tracked ids and at anything outside the project
(Mathlib, core). For a proved node, `show` lists suggestions the proof did not use and real
dependencies never suggested.

The real graph is acyclic by construction; a cycle among suggestions is a lint error.

### States

| state | meaning |
|---|---|
| `open` | the id does not resolve; the node is a plan |
| `stated` | the declaration exists and depends on `sorryAx` |
| `proved` | no `sorry`; axioms within `propext`, `Classical.choice`, `Quot.sound` |
| `axioms` | depends on some other axiom, or is itself an axiom |
| `wrong` | the `wrong` field is set, whatever the declaration says |

A node is *ready* when it is open or stated and every dependency in force is proved.

### Groups

A group is the plan for one module: the nodes that should live in it, and what it is for.

- **Naming.** Its file path under the plan directory is the module path: `Numbers/Odd` plans
  `Numbers.Odd`.
- **Nesting.** Groups nest as modules do: the children of `Numbers` are the files in `Numbers/`
  beside `Numbers.toml`. Counts roll up. A group may stand for a module that is only a directory,
  and a module need not have a group.
- **Description.** The plan's `desc` applies until the module exists and has a `/-! … -/` doc
  comment; then that comment's first block supersedes it.
- **Placement.** For each attached node, `lint` checks that its declaration lives in the group's
  module, so a lemma in the wrong file is reported.
- **Done** when every node in it and under it is proved.
- **Ready** when it has open or stated nodes of its own and all their dependencies outside the
  group are proved: the module can be worked on now.

## Plan files

One TOML file per group, at its module's path under the plan directory. A directory holds the
children of the same-named group file beside it, and that file must exist.

```toml
# plans/Numbers/Odd.toml
namespace = "Numbers"                  # ids below are relative to this; optional
desc = '''
What the module is for, and anything a sub-agent should know before writing it.
'''                                    # until the module has a doc comment

[[node]]
id = "IsOdd.add_odd"                   # the Lean identifier, relative to namespace
kind = "theorem"                       # definition | theorem; until the declaration exists
desc = 'The sum of two odd numbers is even.'   # until a doc comment exists
deps = ["IsOdd", "IsEven", "IsOdd.add_one_even"]   # suggested dependencies; until proved
source = "Textbook, Proposition 1.2"   # optional
# wrong = 'why the statement is false or unprovable as stated'   # optional, hand-set
# deprecated = 'why it is on its way out and what replaces it'   # optional, hand-set
```

| field | required | superseded |
|---|---|---|
| node `kind` | while open | once the declaration exists |
| node `desc` | while open | once the declaration has a doc comment |
| node `deps` | — | once proved |
| group `desc` | while the module does not exist | once the module has a doc comment |

**Ids** resolve like Lean names: relative to the group's `namespace` if set, otherwise as
written; `_root_.` forces an absolute name. A dependency may name a node in any group (tried
relative first, then absolute) and must name a tracked node.

**Aliases**: `def`, `thm`, `lemma` for `kind`; `description` for `desc`. Any other key is an
error, so a misspelt or outdated field cannot pass unnoticed.

**`lint` reports**: fields that can be removed; open nodes or groups missing what they need; a
planned `kind` disagreeing with the declaration; attached nodes or groups with neither `desc` nor
doc comment; deprecated nodes and their dependents.

**Style**: write descriptions as literal strings (`'…'` or `'''…'''`) so `\` and `"` need no
escaping. Append each new node as a block after a blank line, so files merge cleanly under git.

## Workflow

The tracker adds no coordination machinery. It fits one orchestrator merging the work of
sub-agents that each own a git worktree.

**Orchestrator** (on main):
1. `lake build`, `tracker check`, `tracker lint`.
2. `tracker ready` lists groups whose outside dependencies are all proved. Each is one module, so
   no two sub-agents write the same file.
3. For each: a worktree, a branch, and a sub-agent started with `tracker show <group>` — the
   module's description and nodes, plus each dependency's state and signature printed from the
   environment.

**Sub-agent** (in its worktree):
- Writes its module. Proving planned nodes under planned names changes only Lean code; the tracker
  sees progress in the build.
- Edits only its own group's file, and only when the plan changes in its hands: a statement found
  wrong, a rename, a theorem split into clauses, a helper worth tracking.
- Reports anything it learns about other groups instead of editing them.
- Its cache is under the worktree's own `.lake/`, so its `check` describes that worktree only.

**Merging**: plan files and modules from different branches are disjoint and merge cleanly. The
orchestrator rebuilds, runs `check` on main, and reads `status`. A task is done when main's check
says every node is proved, never when a report says so. `lint` on the merged tree catches the rest:
an id two branches both added, a dependency on a node another branch deleted, a declaration in the
wrong module.

**Rules that keep it conflict-free**:
- Additive tasks touch only their own module. The project's root import file is regenerated on
  main, not edited on branches.
- Tasks that change existing declarations (a rename, a restatement of a `wrong` node) run alone.
- Nodes may be merged while `stated`, so a skeleton can be shared before its proofs exist. A
  release is when nothing is stated.
