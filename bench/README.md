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

## Source size

`plan.mjs` also measures the code itself, without compiling anything. The active
source of a submission is the text of the modules above, in the order the verifier
builds them, with block comments (they nest in Lean) and line comments removed,
string and character literals kept as written, and whitespace within a line
collapsed. Blank lines are dropped. Its gzip size at level 9 is recorded as
`gzip_bytes` and its length as `active_bytes`. Compression takes out repetition, so
generated or copied lines add little, while text that has to be said once adds
its full length.

This counts whole modules that the proof imports. A declaration that nothing uses
inside such a module still counts; telling those apart needs the compiled
modules. The size can differ by a few bytes between zlib versions.

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
