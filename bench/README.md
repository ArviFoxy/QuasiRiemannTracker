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
  for importing dependencies and starting up. Every file pays that fixed price,
  about four seconds here however small it is, so counting it would make the cost
  a function of how a proof is split into files.
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

## Checks on each measurement

Lean reports where a run spent its time. The phases other than import and startup
should add up to the CPU time left after subtracting those two, give or take the
process teardown (about 0.13 s). A run where they disagree, because a file was read
cold or the machine was busy, is repeated, and the closest agreement is kept.
Time the main thread spends blocked on tasks repeats work Lean attributes to the
task, so it is left out of the sum.

The first measurements show how small the effect of running three compiles at once
is: the same modules cost the same alone or together, once import time is removed.
`metrics/profile.json` records the machine, the toolchain and the spread of
repeated measurements.

What this measure still counts: Lean's interpreter also runs the initializers of
imported modules when a file starts, about half a second per file, and that is
not separated from the interpreter work a proof does.

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
