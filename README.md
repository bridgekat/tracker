# tracker

A progress tracker for Lean formalization projects. The plan is a set of small TOML files naming
the definitions and theorems that should exist; the progress is read from the compiled library.
The tracker answers the questions an orchestrator and its sub-agents ask: what is proved, what is
ready to work on, what a task depends on, and what changed since last time.

## Get started

The tracker reads the project's `.olean` files, so it must build on the project's toolchain
(`lean-toolchain` here is the version it is currently pinned to). Add it to the project's
`lakefile.toml` and run it with `lake exe`, which gives it the project's search path:

```toml
[[require]]
name = "tracker"
git = "https://github.com/bridgekat/tracker"
```

```
lake build                 # the tracker reads oleans, so build first
lake exe tracker check     # import the project, resolve every id, write the cache
lake exe tracker status    # every command does the same first when the cache is stale
```

The built executable also runs without the `require`, from the project root, as
`lake env path/to/tracker/.lake/build/bin/tracker …`. Either way it needs the toolchain's `bin`
on the path, because it links Lean's shared library.

`examples/` is a small self-contained project with a plan over it, exercising every state and
every lint:

```
cd examples
lake build
lake exe tracker check
lake exe tracker status
lake exe tracker lint
```

### Usage

```
tracker [--root DIR] [--dir DIR] [--roots A,B] [--no-exts] [--no-check] <command> [args]

check [--force]                   make the cache fresh: import the project, resolve every id
status [group] [--json]           counts per group, rolled up through parents; regressions
ready [--json]                    groups whose outside dependencies are all proved
show <group | id>                 the brief for a group, or everything about one node
lint                              plan errors, cycles, placement and kind mismatches, superseded fields
graph [--under G] [--dot]         the graph as JSON (default) or Graphviz DOT
```

`--root` is the project root (default `.`); `--dir` is the directory of plan files (default
`<root>/tracker`). A check imports the `lean_lib` roots of the project's `lakefile.toml` unless
`--roots` says otherwise, and runs the imported modules' initializers so that printed signatures
carry their notation; `--no-exts` skips that. A group is named by its path under the plan
directory, `Numbers/Odd`, or by an unambiguous trailing part of it, `Odd`; `show` also takes a
node id, in full or by an unambiguous suffix. `lint` exits non-zero on errors, and no check runs
while the plan has any.

The cache is `<root>/.lake/tracker/check.json`. It is never committed, and the tracker never
edits plan files. Every command checks first when the cache is stale: when the plan, the
project's compiled modules, the root modules, the options, or the cache format changed since it
was written, all judged by content hashes and never by timestamps. `check` is that step alone,
and does nothing unless the cache is stale or `--force` is given; `--no-check` answers from the
cache as it is. The tracker reads oleans and never builds, so an edit that has not been built is
invisible to it: build first.

### Exports

`graph` is the contract for anything that wants a picture; the tracker itself does not draw.
`--under G` restricts the output to a group and its descendants. The JSON is one object with
three arrays:

| array | fields |
|---|---|
| `groups` | `name`, `parent`, `desc`, `done`, `ready` |
| `nodes` | `id`, `group`, `kind`, `state`, `desc`, `source`, `wrong` |
| `edges` | `from`, `to`, `real`, `suggested` |

An edge means `from` depends on `to`; `real` is set when the dependency was read from the proof,
`suggested` when it was written in the plan, and both can be set. A group's `parent` is the group
whose directory holds it, and its module is its name with `.` for `/`. The DOT form has one
cluster per group, nodes filled by state, real edges solid and suggested edges dashed:

```
lake exe tracker graph --dot --under Numbers | dot -Tsvg -o numbers.svg
```

## Plan graph

### Nodes

A node is a definition or a theorem. It is named by the fully qualified Lean identifier the
declaration has or will have, and described in natural language. The node is *attached* once
that identifier resolves in the compiled environment; until then it is a plan. A node may cite
a `source`, such as a numbered result in a book, and may be marked `wrong` by hand when its
statement was found false or unprovable as stated.

The kind and the description follow the same rule as the dependencies below: the plan's `kind`
and `desc` are what the tracker has until the declaration exists and, for the description, carries
a doc comment; from then on the declaration says whether it is a theorem, the doc comment is the
description everywhere (`show`, `ready`, `graph`), and the plan's copies are superseded. A
finished, documented node needs nothing in the plan but its id.

Renaming a declaration is renaming the node. Correcting a statement is editing the description
and the Lean under the same name, or renaming if the corrected statement deserves a new name.
"Wrong" is a state a node passes through, not a new object.

### Dependencies

Each node lists the nodes its proof is expected to use. That list is a suggestion: while the
node is open it is all the tracker has, and readiness is judged by it. Once the node is proved,
its dependencies are read off the declaration instead: the tracked ids reachable from its type
and proof through untracked constants of the project, stopping at tracked ids and at anything
outside the project (Mathlib, core). The suggestion is then ignored, and `show` says which
suggestions the proof did not use and which real dependencies were never suggested. While a
node is only stated, both are in force.

The real graph is acyclic by construction. A cycle among suggestions is a lint error.

### States

| state | meaning |
|---|---|
| `open` | the id does not resolve; the node is a plan |
| `stated` | the declaration exists and depends on `sorryAx` |
| `proved` | the declaration exists, no `sorry`, axioms within `propext`, `Classical.choice`, `Quot.sound` |
| `axioms` | the declaration exists and depends on some other axiom, or is itself an axiom |
| `wrong` | the `wrong` field is set, whatever the declaration says |

A node is *ready* when it is open or stated and every dependency in force is proved. `check`
compares with the previous cache and reports every node whose state went down, which is how a
renamed or broken declaration shows up.

### Groups

A group is the plan for one module: the nodes that should live in it, and what it is for. It is
named by its file's path under the plan directory, which is the module's path too: `Numbers/Odd`
is the plan for `Numbers.Odd`. Groups nest as modules do, the children of `Numbers` being the
group files in `Numbers/` beside `Numbers.toml`, and counts roll up. A group may stand for a
module that is only a directory, and a module need not have a group.

The description follows the rule of a node's: the plan's `desc` is what the tracker has until
the module exists and has a `/-! … -/` doc comment, whose first block is then the description
everywhere, and the plan's copy is superseded. Once a node is attached, `lint` compares the
module the environment records for it with the group's, so a lemma that landed in the wrong
file is reported without anyone looking for it.

A group is *done* when every node in it and under it is proved, and *ready* when it has open
or stated nodes of its own and every dependency of those outside the group is proved: the
module can be worked on now. `ready` lists the ready groups.

## Plan files

One TOML file per group, under the plan directory, at its module's path: `Numbers/Odd.toml` is
the group `Numbers/Odd`, the plan for `Numbers.Odd`, and a child of `Numbers.toml`. A directory
holds the children of the group file of the same name beside it, and must have one.

```toml
# tracker/Numbers/Odd.toml
namespace = "Numbers"                  # ids below are relative to this; optional
desc = '''
What the module is for, and anything a sub-agent should know before writing it.
'''                                    # until the module has a doc comment

[[node]]
id = "IsOdd.add_odd"                   # the Lean identifier, relative to namespace
kind = "theorem"                       # definition | theorem; until the declaration exists
desc = 'The sum of two odd numbers is even.'   # until a doc comment exists
deps = ["IsOdd", "IsEven", "IsOdd.add_one_even"]   # suggested dependencies, by id; until proved
source = "Textbook, Proposition 1.2"   # optional
# wrong = 'why the statement is false or unprovable as stated'   # optional, hand-set
```

`kind` and `desc` are required while the node is open; `kind` is superseded once the
declaration exists, `desc` once it has a doc comment, and `deps` once the node is proved. The
group's `desc` is required while its module does not exist, and superseded once the module has
a doc comment. `lint` says when each can be removed, when an open node or group lacks what it
needs, when a planned kind disagrees with the declaration, and when an attached node or group
has neither a `desc` nor a doc comment. Ids resolve like Lean names: relative to the group's
`namespace` if it has one, otherwise as written, and `_root_.` forces an absolute name. A dependency may name a node of any group,
relative first and then absolute, and must name a tracked node. `def`, `thm` and `lemma` are
accepted for `kind`, and `description` for `desc`.

Write descriptions as literal strings (`'…'` or `'''…'''`), so that `\` and `"` need no
escaping. A new node is a block appended after a blank line, which is why the files merge
cleanly under git. `examples/tracker/` is the plan of the example project.

## Workflow

The tracker adds no coordination machinery; it fits the usual arrangement of one orchestrator
merging the work of sub-agents that each own a git worktree.

**The orchestrator**, on the main branch: `lake build`, `tracker check`, `tracker lint`. Then
`tracker ready` for the groups whose outside dependencies are all proved; each is one module,
so no two sub-agents write the same file. For each, a worktree and a branch, and a sub-agent
started with the output of `tracker show <group>`: the module's description and nodes, and for
every dependency its state and its signature printed from the environment rather than copied
by hand.

**A sub-agent**, in its worktree: writes its module, and may edit only its own group's file,
usually not at all. Proving the planned nodes under their planned names changes
only Lean code; the tracker sees the progress in the build. It touches the file when the plan
changes in its hands: a statement found wrong, a rename, a theorem split into clauses, a helper
worth tracking. Anything it learns about other groups goes in its report. The cache is under the
worktree's own `.lake/`, so its `check` describes its worktree and nothing else.

**Merging**: plan files changed on different branches are disjoint and merge cleanly; so do the
modules. The orchestrator then rebuilds, runs `check` on main, and reads `status`. A task is
done when main's check says every node is proved, never when a report does. `lint` on the
merged tree catches the rest: an id two branches both added, a dependency on a node another
branch deleted, a declaration that landed in the wrong module.

Three rules keep this conflict-free. Additive tasks touch only their own module, and the
project's root import file is regenerated on main rather than edited on branches. Tasks that
change existing declarations, a rename or a restatement of a node marked `wrong`, run alone.
Nodes may be merged while still `stated`, so that a skeleton can be shared before its proofs
exist; a release is when nothing is stated.
