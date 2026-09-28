# tracker

A progress tracker for Lean formalization projects.

- **The plan** is a set of small TOML files, one *module plan* per module, naming the definitions
  and theorems that should exist: the *planned nodes*.
- **The progress** is read from the compiled library (`.olean` files), along with every other
  *declaration* of the project.

It answers what an orchestrator and its sub-agents need to know: what is proved, what is ready to
work on, what a task depends on, what changed since last time, and how large the library is.

## Terms

| term | meaning |
|---|---|
| module | a Lean module of the project, named by its **module name** as `import` writes it: `Numbers.Odd` |
| module plan | the TOML file that plans one module, at the path of the module's source file: `plans/Numbers/Odd.toml` |
| planned node | a definition or theorem a module plan names, whether or not its declaration exists yet |
| declaration | a definition, inductive type or theorem written in one of the project's modules (see [Declarations](#declarations)) |
| id | the fully qualified name of a planned node or a declaration: `Numbers.IsOdd.add_odd` |

Module names and ids look alike, but they are different things: a module name says where code is
(and so where a module plan is), an id names one declaration in the environment, and its namespace
need not match its module name. The tracker never treats one as the other.

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
lake exe tracker check     # import the project, collect declarations, resolve every id
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

`examples/` is a small self-contained project whose plan (`examples/plans/`) exercises every state
and every lint: `cd examples && lake build && lake exe tracker check && lake exe tracker lint`.

## Commands

```
tracker [--root DIR] [--dir DIR] [--roots A,B] [--no-exts] [--no-check] <command> [args]

check [--force]                    make the cache fresh: import the project, resolve every id
status [module] [--json]           counts per module, rolled up the module tree; regressions
ready [--json]                     modules whose outside dependencies are all proved
show <module | id>                 a module's brief, or everything about one planned node or
                                   declaration
lint                               plan errors, cycles, mismatches, deprecations, superseded fields
graph [--under M] [--all] [--dot]  the planned nodes (with --all, every declaration) as JSON or
                                   Graphviz DOT
```

| option | meaning |
|---|---|
| `--root DIR` | project root (default `.`) |
| `--dir DIR` | plan directory (default `<root>/plans`) |
| `--roots A,B` | root modules to import (default: the `lean_lib`s in `lakefile.toml`, else the cache's) |
| `--no-exts` | skip the imported modules' initializers; printed signatures lose their notation |
| `--no-check` | answer from the cache as it is, even if stale |

- **Naming.** A module is named by its module name (`Numbers.Odd`) or an unambiguous trailing part
  of it (`Odd`); a planned node or a declaration by its id, likewise. When a module name and an id
  are both exactly the argument, `show` shows both.
- **Lint.** `lint` exits non-zero on errors, and no check runs while the plan has any.

### `status`

One row per module of the module tree, with counts of its planned nodes by state and of its
declarations, rolled up through the modules under it, and the module's state (`done`, `ready`,
`blocked`). Totals follow: planned nodes by state, and declarations as definitions and theorems.
Then the planned nodes marked `wrong`, and regressions since the previous check.

### `show`

- **A module**: its states and counts, its description, the modules directly under it, its
  planned nodes with descriptions, and the dependencies of those outside the module with their
  signatures — the brief for a sub-agent writing the module. Unplanned declarations are counted,
  not listed, to keep the brief short.
- **A planned node**: its kind, state, description, source, marks, location and signature, its
  dependencies with how each is known, suggestions the proof did not use, and the planned nodes
  that need it.
- **An unplanned declaration**: its kind, state, doc comment, location and signature, the planned
  nodes it uses, and the declarations it refers to and is referred to by.

### Cache

- Lives at `<root>/.lake/tracker/check.json`, and is never committed.
- Holds every declaration and every planned node's id, with signatures, doc comments and real
  dependencies, so its size grows with the library, not with the plan.
- Every command refreshes it first when stale: when the module plans, the compiled modules, the
  root modules, the options, or the cache format changed. Staleness is judged by content hashes,
  never timestamps.
- `check` is that refresh alone; it does nothing unless the cache is stale or `--force` is given.
- `check` compares with the previous cache and reports every planned node whose state went down —
  this is how a renamed or broken declaration shows up. Unplanned declarations are not compared.
- The tracker never builds, so unbuilt edits are invisible to it.

The tracker never writes a module plan: the plan is written by hand, and is the one thing the
tracker only reads.

### `graph`

The contract for anything that wants a picture; the tracker itself does not draw. `--under M`
restricts output to a module and the modules under it. `--all` adds every declaration to the
planned nodes. The JSON is one object with three arrays:

| array | fields |
|---|---|
| `modules` | `module`, `parent`, `desc`, `exists`, `plan`, `done`, `ready` |
| `nodes` | `id`, `module`, `planned`, `kind`, `state`, `desc`, `source`, `wrong`, `deprecated` |
| `edges` | `from`, `to`, `real`, `suggested` |

- `modules` holds every module of the module tree in scope. `parent` is the module name one level
  up; `exists` says whether the module is compiled, `plan` whether it has a module plan.
- A node's `module` is the module whose plan names it for a planned node, else the module the
  declaration is in; `planned` says which.
- An edge means `from` depends on `to`. `real`: read from the compiled library; `suggested`:
  written in the plan; both may be set.
  - Without `--all`, real edges run between planned nodes, passing through unplanned
    declarations (see [Dependencies](#dependencies)).
  - With `--all`, real edges run between declarations and planned nodes directly, passing only
    through what is neither (auxiliary and private constants). Planned-level edges follow from
    these by the same rule.
- The DOT form has one cluster per module, nodes filled by state (unplanned declarations as small
  ellipses), real edges solid, suggested edges dashed:

```
lake exe tracker graph --dot --under Numbers | dot -Tsvg -o numbers.svg
```

## Model

### Declarations

A declaration is a definition, inductive type or theorem written in one of the project's modules
(those under the root modules). Left out, and looked through by every search: axioms, private
declarations, and whatever the elaborator generated instead of someone writing it — constructors,
recursors, projections, `deriving` instances, `where` helpers, equation lemmas. Declarations are
what `status` counts and what `graph --all` draws.

### Planned nodes

A planned node is a definition or theorem that matters, named by the id its declaration has or
will have, and described in natural language. It is *attached* once that id resolves in the
compiled library; until then it is *open*, a plan. Which declarations become planned nodes is a
judgement: the book's numbered results, the key definitions and theorems — not every helper.

Optional fields:
- `source` — e.g. a numbered result in a book.
- `wrong` — set by hand when the statement was found false or unprovable as stated; the value says why.
- `deprecated` — set by hand when the node is on its way out; the value says why and what replaces it.

**The declaration supersedes the plan.** The plan's `kind` applies until the declaration exists;
its `desc` until the declaration has a doc comment. From then on the declaration is authoritative
everywhere (`show`, `ready`, `graph`). A finished, documented planned node needs nothing in the
plan but its id.

**Identity.** Renaming a declaration renames the planned node. Correcting a statement means
editing the description and the Lean under the same id, or renaming if it deserves a new one.
`wrong` is a state a planned node passes through, not a new object. `deprecated` is not a state:
the node counts as its declaration says, and `lint` names it and everything still depending on it
until the plan drops it.

### Dependencies

Each planned node lists the planned nodes its proof is expected to use (`deps`). These are
*suggestions*.

| state | dependencies in force |
|---|---|
| open | the suggestions |
| stated | the suggestions and the real dependencies |
| proved | the real dependencies only |

*Real* dependencies are the planned nodes reachable from the declaration's type and proof through
the other constants of the project, unplanned declarations included, stopping at planned nodes and
at anything outside the project (Mathlib, core). For a proved node, `show` lists suggestions the
proof did not use and real dependencies never suggested.

The real graph is acyclic by construction; a cycle among suggestions is a lint error.

### States

Planned nodes and declarations alike:

| state | meaning |
|---|---|
| `open` | the id does not resolve; the planned node is a plan |
| `stated` | the declaration exists and depends on `sorryAx` |
| `proved` | no `sorry`; axioms within `propext`, `Classical.choice`, `Quot.sound` |
| `axioms` | depends on some other axiom, or is itself an axiom |
| `wrong` | the planned node's `wrong` field is set, whatever the declaration says |

A planned node is *ready* when it is open or stated and every dependency in force is proved.

### Modules

- **The module tree.** Every compiled module of the project and every module with a module plan,
  arranged by module name: `Numbers.Odd` is under `Numbers`, which is in the tree even if it is
  neither compiled nor planned. Counts roll up the tree. The tree follows module names only; the
  namespaces of ids play no part in it.
- **Module plans.** A module need not have a plan, and a module plan may be for a module that does
  not exist yet.
- **Description.** The module plan's `desc` applies until the module exists and has a
  `/-! … -/` doc comment; then that comment's first block supersedes it.
- **Placement.** For each attached planned node, `lint` checks that its declaration is in the
  module whose plan names it, so a lemma in the wrong file is reported.
- **Done** when every planned node in it and under it is proved.
- **Ready** when it has open or stated planned nodes of its own and all their dependencies outside
  the module are proved: the module can be worked on now.

## Module plans

One TOML file per planned module, at the path of the module's source file under the plan
directory: the plan of `Numbers.Odd`, whose source is `Numbers/Odd.lean`, is `plans/Numbers/Odd.toml`.

```toml
# plans/Numbers/Odd.toml
namespace = "Numbers"                  # ids below are relative to this; optional
desc = '''
What the module is for, and anything a sub-agent should know before writing it.
'''                                    # until the module has a doc comment

[[node]]
id = "IsOdd.add_odd"                   # the id, relative to namespace
kind = "theorem"                       # definition | theorem; until the declaration exists
desc = 'The sum of two odd numbers is even.'   # until a doc comment exists
deps = ["IsOdd", "IsEven", "IsOdd.add_one_even"]   # suggested dependencies; until proved
source = "Textbook, Proposition 1.2"   # optional
# wrong = 'why the statement is false or unprovable as stated'   # optional, hand-set
# deprecated = 'why it is on its way out and what replaces it'   # optional, hand-set
```

| field | required | superseded |
|---|---|---|
| `[[node]]` `kind` | while open | once the declaration exists |
| `[[node]]` `desc` | while open | once the declaration has a doc comment |
| `[[node]]` `deps` | — | once proved |
| module `desc` | while the module does not exist | once the module has a doc comment |

**Ids** resolve like Lean names: relative to the module plan's `namespace` if set, otherwise as
written; `_root_.` forces an absolute id. The namespace is a namespace of ids, not a module name.
A dependency may name a planned node of any module plan (tried relative first, then absolute) and
must name a planned node.

**Aliases**: `def`, `thm`, `lemma` for `kind`; `description` for `desc`. Any other key is an
error, so a misspelt or outdated field cannot pass unnoticed.

**`lint` reports**: fields that can be removed; open planned nodes, or module plans of modules that
do not exist, missing what they need; a planned `kind` disagreeing with the declaration; planned
nodes and modules with neither `desc` nor doc comment; misplaced planned nodes; deprecated planned
nodes and their dependents.

**Style**: write descriptions as literal strings (`'…'` or `'''…'''`) so `\` and `"` need no
escaping. Append each new planned node as a block after a blank line, so files merge cleanly under
git.

## Workflow

The tracker adds no coordination machinery. It fits one orchestrator merging the work of
sub-agents that each own a git worktree.

**Orchestrator** (on main):
1. `lake build`, `tracker check`, `tracker lint`.
2. `tracker ready` lists modules whose outside dependencies are all proved. No two sub-agents
   write the same module.
3. For each: a worktree, a branch, and a sub-agent started with `tracker show <module>` — the
   module's description and planned nodes, plus each dependency's state and signature printed
   from the compiled library.

**Sub-agent** (in its worktree):
- Writes its module. Proving planned nodes under their planned ids changes only Lean code; the
  tracker sees progress in the build.
- Edits only its own module's plan, and only when the plan changes in its hands: a statement
  found wrong, a rename, a theorem split into clauses, a helper worth planning.
- Reports anything it learns about other modules instead of editing their plans.
- Its cache is under the worktree's own `.lake/`, so its `check` describes that worktree only.

**Merging**: module plans and modules from different branches are disjoint and merge cleanly. The
orchestrator rebuilds, runs `check` on main, and reads `status`. A task is done when main's check
says every planned node is proved, never when a report says so. `lint` on the merged tree catches
the rest: an id two branches both planned, a dependency on a planned node another branch deleted,
a declaration in the wrong module.

**Rules that keep it conflict-free**:
- Additive tasks touch only their own module. The project's root import file is regenerated on
  main, not edited on branches.
- Tasks that change existing declarations (a rename, a restatement of a `wrong` planned node) run
  alone.
- Planned nodes may be merged while `stated`, so a skeleton can be shared before its proofs exist.
  A release is when nothing is stated.
