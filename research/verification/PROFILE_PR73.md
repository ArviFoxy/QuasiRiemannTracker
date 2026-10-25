# Why PR 73 cannot pass the hosted admission check, with numbers (2026-10-25)

## The hosted budget

The limits come from upstream `verifier/standard/replay.py`, `worker_resources.py` and
`.github/workflows/pr-admission.yml`.

- **Runner.** A GitHub `ubuntu-24.04` runner: 4 vCPU, 16 GB.
  - `worker_capacity` gives 4 Lean threads.
  - It gives **1 kernel job** (`min(3, threads, 0.75·mem/8 GiB)`), so Comparator + Lean default +
    nanoda + con-ron run one after another.
- **Time limits.**
  - Shared deadline: 10800 s, i.e. 3 h for compile + export + kernels.
  - Each module: 1800 s. Each export: 600 s. The judge (all kernels): 3600 s.
  - The step timeout is 185 min, so the job dies at about 3h05m with exit code 1.
- **Memory.** The sandbox allows 75% (high) and 85% (max) of RAM, about 12–13.6 GB.

## Upstream history

Every result since PR #63 was verified offline by the maintainer, with raised budgets: shared
3h → 6–12 h, judge 1h → 2–8 h. On their 16-thread / 192 GiB worker, with the three kernels in
parallel, the receipts in `verifier/standard/receipts/*/phases.json` show:

| PR | compile | kernel stage |
|---|---|---|
| #43 | 80 min | 20 min |
| #63 | 94 min | 30 min |
| #64 | 52 min | 18 + 50 min (retry with con-ron --jobs=1) |
| #66 | 103 min | 42 min |
| #68 | 61 min | 34 min |
| #70 | 73 min | 65 min |
| #71 | 67 min | 54 min (con-ron: 176,518 declarations) |

A manual hosted run on `main` fails the same way. The hosted check cannot pass for the current
state of the art.

## Our closure

Measured on this 4-core / 15 GB machine, which is the same class as the hosted runner.

- **Export.** `lean4export` of `Candidate.bound` + `Candidate.bound_sharp`: **511 s**
  (hosted limit 600 s), **4.3 GB**, peak RSS **12.3 GB** (hosted cap about 12–13.6 GB).
- **Closure.** 157,350 constants. #71 had 176,518, so ours is about 11% smaller.
- **Kernels.**
  - nanoda: **20 min** wall on 4 threads for the whole proof (earlier session, streamed).
  - con-ron: see below.
  - Comparator's Lean replay: not run here.

**Attribution** of export bytes (each declaration is charged the new terms it introduces;
`attribute.py`, module map from `ModuleOf.lean`):

| development | constants | export MB | share |
|---|---|---|---|
| hailey-collet-1252270103 (dependency) | 26,605 | 2336 | 54.1% |
| openai-baseline | 26,706 | 836 | 19.4% |
| Mathlib | 88,090 | 804 | 18.6% |
| arvi-repeated-marks (ours) | 5,289 | 290 | 6.7% |
| Lean core, PNT+, Batteries, other | 8,432 | 49 | 1.1% |

**The largest single terms are Collet's analytic theorems**, not finite certificates:
- `…Cycle63InitialMass.actual_main_low_physical_bins._proof_2`: 88 MB;
- `…SelectedLowSourceMissingBins.global_selected_low_positive_family_missing_bins`: 83 MB;
- `…SelectedLowSourceReindex.global_selected_low_positive_family_injective`: 80 MB;
- `…SelectedLowBufferedSource…`: 56 MB;
- `…SelectedRegularLowSource…`: 52 MB.

These are long tactic proofs with 30-line statements, so proof by reflection cannot shrink them.
Our largest term is `highGateReal_affine` at 24 MB.

## Conclusion

- **No change to our own code can make the hosted check pass.**
  - Deleting all of it would remove 7% of the export.
  - The export time and memory are already at the hosted limits because of the dependency and
    the baseline.
  - The kernel stage needs three sequential kernels on 4 threads within one hour. nanoda alone
    takes 20 of those minutes.
- **What would fix it is upstream:**
  - **Incremental kernel verification.** Re-check only declarations that are not already in an
    admitted, verified export, keyed by declaration hash. Our delta is about 7% of the bytes.
  - Or bigger hosted runners, so the kernels can run in parallel.
- **A lighter path for a future submission:** a base that does not import Collet's admission
  framework would roughly halve the export. That would mean re-implementing the source-step
  infrastructure our chain uses (seed step, selected-source families), which is a large project.
- **Practical route now:** the maintainer's offline verification, as for #63–#71. Our closure
  is smaller than #71's, which passed offline in 67 + 54 min.
