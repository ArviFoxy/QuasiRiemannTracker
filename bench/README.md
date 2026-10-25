# Proof size benchmark

The Pareto tab plots each bound against the size of its proof. This directory
measures that size: how much compile work each submission's proof takes.

## What is measured

- The modules of a submission are the ones the verifier compiles: the import
  closure of `Candidate.Main`, including the OpenAI baseline and any other
  submission it depends on. `plan.mjs` lists them with the verifier's own
  dependency code.
- Each module is compiled once with `lean -j1`, from scratch. Its cost is the CPU
  time (user plus system) of that process, less the time Lean's profiler reports
  for importing dependencies and starting up, and less what a file with no
  content costs beyond that. Every file pays those fixed prices, about four
  seconds here however small it is, so counting them would make the cost a
  function of how a proof is split into files. The cost of an empty file is read
  from the data: it is the median over submissions of their `Candidate.Main`,
  a few lines that only re-export the bound.
- A submission's cost is the sum over its modules. Mathlib and the pinned
  libraries are prebuilt, as in verification, and are not counted. Peak memory is
  the largest resident set of any one compile, which includes the memory-mapped
  libraries every compile loads.
- Compile only. Lean's own kernel already checks every declaration while
  compiling, and the kernel replays that follow in verification measure the
  checkers more than the proof.
- Modules that several submissions share are compiled and measured once. A module
  is identified by its source and the identities of its dependencies, as in the
  verifier's build cache, so a changed module is measured again with everything
  that imports it.

CPU time is used instead of wall-clock time because it does not depend on the
number of cores or on how a proof's modules are arranged. Source length is
recorded for comparison, but it is easy to change without changing the proof.

## Alive code

The size that the Pareto tab opens on does not need the compile cost at all. It is
the Lean code the proof needs, gzipped, as a stand-in for how much has to be said
to prove the bound.

Starting from `Candidate.bound`, a declaration is **alive** if the proof mentions
it, or something alive does. That is every constant named in the type or the value
of an alive declaration, the constructors of an alive inductive type, and the
declarations defined together with an alive one. A declaration that nothing alive
mentions is **dead**: an unused lemma, a helper nobody calls, a whole file that no
alive declaration lives in. The alive code of a submission is

- the text of every alive declaration, and
- the rest of each file that holds one: imports, namespaces, `open` and `variable`
  lines, notation, macros and tactics, which cannot be told apart from what an
  alive declaration uses, so they all count, except that a namespace or section
  that held nothing but dead declarations goes with them, as do `#print`, `#check`,
  `#eval` and `example`, which leave nothing behind, and
- definitions that deal in Lean's own syntax and meta types (`Lean.*`) in such
  files, which is where tactics keep their helpers,

in build order, without comments and with whitespace collapsed (the same
`active-source.mjs` as above), then gzipped at level 9. Mathlib and the pinned
libraries are not counted. Dead declarations are cut out by the position Lean
recorded for them, so renaming, reformatting or commenting changes nothing, and
neither does adding code that the proof does not use.

How it is worked out, in three steps that can be repeated separately:

1. `measure.py run` compiles every module. When a submission is finished,
   `alive/Dump.lean` reads the compiled `.olean` files as data and writes the
   declaration graph of each module that has none (`dumps/<module key>.json.gz`):
   every constant with its kind, its position in the source, and the constants of
   the same submission that its type and value mention. Nothing is elaborated or
   executed. The compiled modules that no unfinished submission builds on are then
   deleted, so disk use follows the work in progress, not everything compiled.
   `measure.py dump ID` redoes this for a submission that is still compiled.
2. `node --max-old-space-size=8192 bench/alive.mjs` follows the graph from the
   root, cuts the dead declarations out of the sources, and writes
   `alive/<id>.json` (the sizes) and `alive/<id>.txt.gz` (the text, to read).
   It needs only the graphs and the sources, not the compiled modules.
3. `aggregate.py` copies the sizes into `metrics/`.

What this still counts, and does not:

- Alive code is judged by the text of the declarations, not by the proof terms
  they elaborate to. A proof by `decide` or `native_decide` is short however large
  the computation is.
- A file with no alive declaration is left out even if it holds notation that an
  alive file uses.
- Auxiliary constants (proofs lifted out of a theorem, equation lemmas) have no
  position of their own and belong to the declaration whose name they extend.
- The size can differ by a few bytes between zlib versions.

## Reachable modules

`plan.mjs` also measures the files themselves, without compiling anything. The
active source of a submission is the text of the modules above, in the order the
verifier builds them, with block comments (they nest in Lean) and line comments
removed, string and character literals kept as written, and whitespace within a
line collapsed. Blank lines are dropped. Its gzip size at level 9 is recorded as
`gzip_bytes` and its length as `active_bytes`. This counts whole modules that the
proof imports, including the declarations in them that nothing needs, so it is
always at least the alive code.

## Checks on each measurement

Lean reports where a run spent its time. The phases other than import and startup
should add up to the CPU time left after subtracting those two, give or take the
process teardown (about 0.13 s). A run where they disagree, because a file was read
cold or the machine was busy, is repeated, and the closest agreement is kept.
Time the main thread spends blocked on tasks repeats work Lean attributes to the
task, so it is left out of the sum.

Running several compiles at once adds system time while a file imports its
dependencies, which is subtracted with the import, so the same module costs the
same alone or alongside others. `metrics/profile.json` records the machine, the
toolchain, the cost of an empty file and the spread of repeated measurements.

## Reproduce

Needs Linux with root, `git`, `node`, `zstd`, `unshare` and `setpriv`, and about
25 GB of disk. Compiles run as an unprivileged user (`qrhbench`) without network
access and with an empty environment, because submitted Lean is untrusted code.
That user must be able to read `QRH_BENCH_ROOT` (default `.bench/`), so keep it
outside directories closed to other users.

```sh
python3 bench/setup.py                  # Lean 4.34.1, pinned packages, Mathlib cache
python3 bench/measure.py stats          # unique work across submissions
python3 bench/measure.py run            # resumable; touch $QRH_BENCH_ROOT/STOP to pause
python3 bench/measure.py status
node --max-old-space-size=8192 bench/alive.mjs   # alive code of the finished submissions
python3 bench/aggregate.py              # writes ../metrics/
```

`setup.py` mirrors `verifier/actions/setup.py` (same pins and package patches)
without the sandbox or the kernels. `measure.py run` appends one record per
compile to `measurements.jsonl`, including repeats and a few canary modules that
are remeasured through the run to show drift. `aggregate.py` turns the records
into `metrics/<result-id>.json`, each bound to the submission's source tree, and
`metrics/profile.json`. Compare costs only within one profile.

A new submission needs only its own modules measured: run `measure.py run <id>`
and `aggregate.py` again. Website builds ignore metrics whose sources have since
changed.
