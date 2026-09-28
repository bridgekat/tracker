# tracker

A progress tracker for Lean formalization projects. The plan is a set of small TOML files naming
the definitions and theorems that should exist; the progress is read from the compiled library.

It answers what an orchestrator and its sub-agents need to know: what is proved, what is ready to
work on, what a task depends on, what changed since last time, and how large the library is.

## Setup

The tracker reads the project's `.olean` files, so it must build on the project's toolchain. Add
it as a git submodule, so this README is in the tree for agents and its version is pinned with the
project:

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
lake build                 # build first: the tracker reads oleans
lake exe tracker check     # import the project and write the cache
lake exe tracker status
```

No plan is needed to start: without a plan directory the plan is empty, and `status`, `show` and
`graph --all` already describe the library. Add one line to the project's agent instructions: read
`tools/tracker/README.md` before touching the plan.

Alternatives:
- A `git = "…"` require works too; Lake keeps the clone under `.lake/packages/tracker/`.
- A clone built anywhere runs from the project root, with no `require`, as
  `lake env path/to/tracker/.lake/build/bin/tracker …`.

Either way the toolchain's `bin` must be on the path, since the tracker links Lean's shared library.

`examples/` is a small self-contained project whose plan exercises every state and every lint:
`cd examples && lake build && lake exe tracker check && lake exe tracker lint`.

## Concepts

### Modules

A *module* is a Lean module of the project (one under the root modules), or one planned to be,
named by its *module name* as `import` writes it: `Numbers.Odd`.

The *module tree* holds every compiled module of the project and every module that has a plan,
arranged by module name: `Numbers.Odd` is under `Numbers`, which is in the tree even if it is
neither compiled nor planned. Counts roll up the tree.

A module is *done* when every planned declaration in and under it is proved, and *ready* when it
has open or stated planned declarations of its own and all their dependencies outside the module
are proved: it can be worked on now.

#### Module plans

A *module plan* says which declarations should live in a module and what the module is for. A
module need not have one, and a module plan may be for a module that does not exist yet. It is a
TOML file under the plan directory, at the path of the module's source file: the plan of
`Numbers.Odd`, whose source is `Numbers/Odd.lean`, is `plans/Numbers/Odd.toml`. Plans are written
by hand; the tracker only reads them. Each planned declaration is a `[[node]]` table: its node in
the dependency graph.

```toml
# plans/Numbers/Odd.toml
namespace = "Numbers"                  # ids below are relative to this; optional
desc = '''
What the module is for, and anything a sub-agent should know before writing it.
'''

[[node]]
id = "IsOdd.add_odd"
kind = "theorem"                       # definition | theorem
desc = 'The sum of two odd numbers is even.'
deps = ["IsOdd", "IsEven", "IsOdd.add_one_even"]   # suggested dependencies
source = "Textbook, Proposition 1.2"   # optional
# wrong = 'why the statement is false or unprovable as stated'   # optional
# deprecated = 'why it is on its way out and what replaces it'   # optional
```

**The library supersedes the plan.** What a plan says — a kind, a description, dependencies — is
what the tracker has until the compiled library says it; from then on the library is
authoritative everywhere, and the plan's copy is superseded and can be removed:

| field | required | superseded |
|---|---|---|
| `[[node]]` `kind` | while open | once the declaration exists |
| `[[node]]` `desc` | while open | once the declaration has a doc comment |
| `[[node]]` `deps` | — | once proved, by the real dependencies |
| module `desc` | while the module does not exist | once the module has a `/-! … -/` doc comment, by its first block |

A finished, documented planned declaration needs nothing in the plan but its id.

**Ids** resolve like Lean names: relative to the module plan's `namespace` if set, otherwise as
written; `_root_.` forces an absolute id. The namespace is a namespace of ids, not a module name.
A dependency may name a planned declaration of any module plan (tried relative first, then
absolute).

**Aliases**: `def`, `thm`, `lemma` for `kind`; `description` for `desc`. Any other key is an
error, so a misspelt or outdated field cannot pass unnoticed.

**Style**: write descriptions as literal strings (`'…'` or `'''…'''`) so `\` and `"` need no
escaping. Append each new planned declaration as a block after a blank line, so files merge
cleanly under git.

### Declarations

A *declaration* is a definition, inductive type or theorem written in one of the project's
modules. Left out, and looked through by every search: axioms, private declarations, and whatever
the elaborator generated instead of someone writing it — constructors, recursors, projections,
`deriving` instances, `where` helpers, equation lemmas.

An *id* is the fully qualified name of a declaration: `Numbers.IsOdd.add_odd`. Ids and module
names look alike but are unrelated: a module name says where code is, an id names one declaration,
and its namespace need not match its module name. The module tree follows module names only.

#### Planned declarations

A *planned declaration* is one a module plan names, by the id it has or will have, and describes
in natural language; it may not exist yet. A planned declaration is a key node in the dependency
graph. Which declarations are planned is a judgement — the book's numbered results, the key
definitions and theorems, not every helper; the rest are *unplanned*.

Renaming a declaration renames the planned declaration. Correcting a statement means editing the
description and the Lean under the same id, or renaming if it deserves a new one. A planned
declaration may be marked `wrong` (its statement was found false or unprovable as stated), a state
it passes through, or `deprecated` (it is on its way out), which is no state at all: it counts as
its declaration says, and `lint` names it and everything still depending on it until the plan
drops it.

#### States

Every declaration has a state, read from the compiled library:

| state | meaning |
|---|---|
| `open` | the id does not resolve; the planned declaration does not exist yet |
| `stated` | the declaration exists and depends on `sorryAx` |
| `proved` | no `sorry`; axioms within `propext`, `Classical.choice`, `Quot.sound` |
| `axioms` | depends on some other axiom, or is itself an axiom |
| `wrong` | the planned declaration is marked `wrong`, whatever the declaration says |

A planned declaration is *attached* once its id resolves. It is *ready* when it is open or stated
and every dependency in force is proved.

#### Dependencies

A module plan lists, for each planned declaration, the planned declarations its proof is expected
to use: its *suggested* dependencies. Its *real* dependencies are the planned declarations
reachable from its type and proof through the other constants of the project, unplanned
declarations included, stopping at planned declarations and at anything outside the project
(Mathlib, core).

| state | dependencies in force |
|---|---|
| open | the suggested ones |
| stated | the suggested and the real ones |
| proved | the real ones only |

The real graph is acyclic by construction; a cycle among suggestions is a lint error.

## Commands

```
tracker [--root DIR] [--dir DIR] [--roots A,B] [--no-exts] [--no-check] <command> [args]

check [--force]                    make the cache fresh: import the project, resolve every id
status [module] [--json]           counts per module, rolled up the module tree; regressions
ready [--json]                     modules whose outside dependencies are all proved
show <module | id>                 a module's brief, or everything about one declaration
lint                               plan errors, cycles, mismatches, deprecations, superseded fields
graph [--under M] [--all] [--dot]  the dependency graph of the planned declarations (with --all,
                                   of every declaration) as JSON or Graphviz DOT
```

| option | meaning |
|---|---|
| `--root DIR` | project root (default `.`) |
| `--dir DIR` | plan directory (default `<root>/plans`) |
| `--roots A,B` | root modules to import (default: the `lean_lib`s in `lakefile.toml`, else the cache's) |
| `--no-exts` | skip the imported modules' initializers; printed signatures lose their notation |
| `--no-check` | answer from the cache as it is, even if stale |

A module is named on the command line by its module name (`Numbers.Odd`) or an unambiguous
trailing part of it (`Odd`); a declaration, planned or not, by its id, likewise. When a module
name and an id are both exactly the argument, `show` shows both.

### `status`

One row per module of the module tree: counts of its planned declarations by state and of all its
declarations, rolled up through the modules under it, and whether it is `done`, `ready` or
`blocked`. Then totals — planned declarations by state, all declarations as definitions and
theorems — the planned declarations marked `wrong`, and the regressions of the last check.

### `show`

- **A module**: its state and counts, its description, the modules directly under it, its planned
  declarations with descriptions, and their dependencies outside the module with state and
  signature — the brief for a sub-agent writing the module. Unplanned declarations are counted,
  not listed.
- **A planned declaration**: its kind, state, description, source, marks, location and signature;
  its dependencies in force, each tagged as suggested, real or both; suggestions the proof did
  not use; and the planned declarations that need it.
- **An unplanned declaration**: its kind, state, doc comment, location and signature; the planned
  declarations it uses; and the declarations it refers to and is referred to by.

### `lint`

Reports, as errors: module plans that do not parse, unknown keys or kinds, duplicate ids,
dependencies that name no planned declaration or the declaration itself, cycles among
suggestions, open planned declarations without `kind` or `desc`, module plans of modules that do
not exist without `desc`, blank `desc`, `wrong` or `deprecated` values, planned declarations
that are axioms. As warnings: superseded fields that can be removed, a planned `kind` disagreeing
with the declaration, planned declarations and modules with neither `desc` nor doc comment, a
planned declaration in another module than the one whose plan names it, deprecated planned
declarations and their dependents. It exits non-zero on errors, and no check runs while the plan
has any.

### `graph`

The dependency graph, the contract for anything that wants a picture; the tracker itself does not
draw. Its nodes are the planned declarations, and with `--all` every declaration. `--under M`
restricts it to a module and the modules under it. The JSON is compact: one object with two
tables, whose entries refer to each other by index (position in the table). A field at its
default — `false`, empty, or absent — is left out.

| table | fields |
|---|---|
| `modules` | `name`, `parent`, `desc`, `exists`, `plan`, `done`, `ready` |
| `nodes` | `id`, `module`, `planned`, `kind`, `state`, `desc`, `source`, `wrong`, `deprecated`, `deps`, `suggested` |

- `modules` holds every module of the module tree in scope. `parent` is the module one level up,
  when that is in scope; `exists` says whether the module is compiled, `plan` whether it has a
  module plan.
- A node's `module` is, for a planned declaration, the module whose plan names it, else the
  module the declaration is in.
- `deps` are the node's real dependencies and `suggested` its suggested ones; a node may be in
  both, and nodes outside the scope are left out of both. Without `--all`, `deps` are real
  dependencies as [defined above](#dependencies). With `--all`, they run between declarations
  directly, planned or not, passing only through the constants that are neither (auxiliary and
  private ones); the planned-level ones follow from these by the same rule.
- `desc` is the description in force: the doc comment, else the plan's `desc`.
- The DOT form has one cluster per module, nodes filled by state (unplanned declarations as small
  ellipses), real dependencies as solid edges, suggested ones dashed:

```
lake exe tracker graph --dot --under Numbers | dot -Tsvg -o numbers.svg
```

## Cache

A check writes `<root>/.lake/tracker/check.json`, which is never committed. It records the
compiled library and nothing the plan says: every declaration, and every id the plan named when the
check ran, with kind, module, location, signature, doc comment, nonstandard axioms, and the
entries each refers to.

- **Freshness.** Every command refreshes the cache first when it is stale: when the compiled
  modules, the root modules, the options or the cache format changed, or the plan names an id the
  cache has not resolved. Editing a module plan otherwise needs no check. Staleness is judged by
  content hashes, never timestamps; the tracker never builds, so an edit that is not built is
  invisible to it.
- **`check`** is that refresh alone; it does nothing unless the cache is stale or `--force` is
  given.
- **Regressions.** A check compares with the previous cache and reports every planned declaration
  whose state went down; this is how a renamed or broken declaration shows up.
- **Format.** Compact JSON: ids and module names are written once, in an `entries` and a
  `modules` table, and referred to by index; fields at their default are left out; real
  dependencies are not stored but derived when the cache is read.

## Workflow

The tracker adds no coordination machinery. It fits one orchestrator merging the work of
sub-agents that each own a git worktree.

**Orchestrator** (on main):
1. `lake build`, `tracker check`, `tracker lint`.
2. `tracker ready` lists the modules that can be worked on now. No two sub-agents write the same
   module.
3. For each: a worktree, a branch, and a sub-agent started with the output of
   `tracker show <module>`.

**Sub-agent** (in its worktree):
- Writes its module. Proving planned declarations under their planned ids changes only Lean code;
  the tracker sees progress in the build.
- Edits only its own module's plan, and only when the plan changes in its hands: a statement
  found wrong, a rename, a theorem split into clauses, a helper worth planning.
- Reports anything it learns about other modules instead of editing their plans.
- Its cache is under the worktree's own `.lake/`, so its checks describe that worktree only.

**Merging**: module plans and modules from different branches are disjoint and merge cleanly. The
orchestrator rebuilds, runs `check` on main, and reads `status`. A task is done when main's check
says every planned declaration is proved, never when a report says so. `lint` on the merged tree
catches the rest: an id two branches both planned, a dependency on a planned declaration another
branch deleted, a declaration in the wrong module.

**Rules that keep it conflict-free**:
- Additive tasks touch only their own module. The project's root import file is regenerated on
  main, not edited on branches.
- Tasks that change existing declarations (a rename, a restatement of a `wrong` planned
  declaration) run alone.
- Planned declarations may be merged while `stated`, so a skeleton can be shared before their
  proofs exist. A release is when nothing is stated.
