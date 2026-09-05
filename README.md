# tracker

A progress tracker for Lean formalization projects. It keeps a plan of definitions and theorems
as small TOML files, computes how far the plan has got from the compiled library, and answers the
questions an orchestrator and its sub-agents ask: what is proved, what is ready to work on, what a
task depends on, and what changed.

Nothing about progress is written by hand. A node is named by the Lean identifier it has or will
have; once that identifier exists, its state (stated with `sorry`, proved, or depending on a
non-standard axiom) and its real dependencies are read from the environment. Before it exists,
hand-written suggestions stand in.

## Using it in a project

Add the tracker to the project's `lakefile.toml` and run it with `lake exe`, so that it inherits
the project's search path and can import the project's modules:

```toml
[[require]]
name = "tracker"
path = "../tracker"        # or git = "…"
```

```
lake build                 # the tracker reads .olean files, so build first
lake exe tracker check     # import the project, resolve every id, write the cache
lake exe tracker status    # counts per group, rolled up through parents
lake exe tracker ready     # tasks whose outside dependencies are all proved
lake exe tracker show <group | id>
lake exe tracker lint
lake exe tracker graph [--dot]
```

Without the `require`, the built executable also runs under `lake env` from the project root:
`lake env path/to/tracker/.lake/build/bin/tracker check`. It links against Lean's shared library,
so it needs the toolchain's `bin` on the path either way.

Group files live in `<project>/tracker/` by default (`--dir` overrides). The cache is written to
`<project>/.lake/tracker/check.json` and is never committed. The tracker never edits group files.

Options: `--root DIR` (project root, default `.`), `--dir DIR` (group files), `--roots A,B`
(modules to import for `check`; default: the `lean_lib` names in `lakefile.toml`), `--no-exts`
(skip running the imported modules' initializers), `--json` on `status` and `ready`, `--kind K`
or `--all` on `ready`, `--under G` on `graph`.

## Group files

One TOML file per group. A group is a set of nodes: a `task` handed to one sub-agent, a `section`
or `chapter` of a book, a `module`, or any other word; the tracker treats every kind alike. A
group is *done* when all its nodes are proved and *ready* when every dependency of its nodes
outside the group is proved. Groups nest through `parent`, and status rolls up.

```toml
kind = "task"                                   # default "task"
title = "Conjugates of improper functions"
parent = "duality"                              # optional
module = "Tdaf.Analysis.Convex.Duality.Improper"  # where the declarations should live; optional
namespace = "Tdaf.ConvexAnalysis"               # ids below are relative to this; optional
notes = '''
Anything a sub-agent should read before starting.
'''

[[node]]
id = "conj_eq_top_of_exists_eq_bot"             # the Lean identifier, relative to namespace
kind = "theorem"                                # definition | theorem
desc = 'If f takes the value -∞ anywhere, then f* is identically +∞.'
deps = ["conj", "conj_bot"]                     # suggested dependencies, by id
source = "Rockafellar, §12"                     # optional
# wrong = 'why the statement is false or unprovable as stated'   # optional, hand-set
```

Ids resolve like Lean names: relative to the group's `namespace` if it has one, else as written;
`_root_.` forces an absolute name. A dependency may name a node of any group; relative first,
then absolute.

Use literal strings (`'…'`) for descriptions, so that `\` and `"` need no escaping.

## States

| state | meaning |
|---|---|
| `open` | the id does not resolve; the node is a plan |
| `stated` | the declaration exists and depends on `sorryAx` |
| `proved` | the declaration exists, no `sorry`, axioms within `propext`, `Classical.choice`, `Quot.sound` |
| `axioms` | the declaration exists and depends on some other axiom, or is itself an axiom |
| `wrong` | the `wrong` field is set, whatever the declaration says |

`deps` is a suggestion. While a node is open it is all the tracker has, and readiness is judged
by it. Once the node is proved, dependencies are read off the declaration: the tracked ids
reachable from its type and proof through untracked constants of the project, stopping at
tracked ids and at anything outside the project. The suggestion is then ignored; `show` says
which suggestions the proof did not use and which real dependencies were not suggested. While a
node is only stated, both are shown.

`check` compares with the previous cache and reports every node whose state went down, which is
how a renamed declaration shows up.

`lint` reports: plan errors (unparsable files, missing fields, unknown kinds, unknown or self
dependencies, duplicate ids, missing parents), cycles among suggestions, empty descriptions,
`wrong` without a reason, and, once checked, nodes planned as theorems that are not, nodes that
are axioms, and declarations that live in a module other than their group's.

## Graph exports

`tracker graph` is the contract for anything that wants a picture; the tracker itself does not
draw. `--under G` restricts the output to a group and its descendants, which is the only way a
layout stays readable past a few hundred nodes.

JSON (the default) is one object with three arrays:

| array | fields |
|---|---|
| `groups` | `name`, `kind`, `title`, `parent`, `module`, `done`, `ready` |
| `nodes` | `id`, `group`, `kind`, `state`, `desc`, `source`, `wrong` |
| `edges` | `from`, `to`, `real`, `suggested` |

An edge means `from` depends on `to`. `real` is set when the dependency was read from the
proof, `suggested` when it was written in `deps`; both can be set.

DOT (`--dot`) has one cluster per group, nodes filled by state (green proved, yellow stated, red
wrong, orange axioms, white open), real edges solid and suggested edges dashed. Render it with
Graphviz:

```
lake exe tracker graph --dot --under rockafellar-part3 | dot -Tsvg -o part3.svg
```

## Layout

```
Tracker/Types.lean      Node, Group, Plan, NodeState, DeclInfo, Cache
Tracker/Toml.lean       Lake.Toml wrappers: load, decode with positions
Tracker/Plan.lean       read a directory of groups, resolve ids and dependencies
Tracker/Graph.lean      states, effective dependencies, readiness, roll-ups, cycles
Tracker/Check.lean      import the project and resolve every id (the only Lean-environment code)
Tracker/Cache.lean      read and write .lake/tracker/check.json
Tracker/Commands.lean   status, ready, show, lint, graph
Main.lean               the CLI
examples/tdaf/          a small plan over the tdaf library, for trying the commands
```

The tracker must build on the same toolchain as the project it checks, because it reads the
project's `.olean` files.
