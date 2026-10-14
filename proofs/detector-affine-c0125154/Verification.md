# Verification and reproduction

## Local Lean compilation

The whole candidate was compiled locally against the tracker's pinned environment. That is 219 modules:

* the 193 Cycle61 bundles, 14 of them changed;
* the pieces of the unchanged bundles `B167` and `B176`, split for the replay time limit (see below);
* `Main.lean`;
* ten new `Affine/` modules.

**Environment**

* Lean 4.34.1 (standalone release; SHA256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`).
* The `verifier/standard` lake manifest: Mathlib, PrimeNumberTheoremAnd and rellich-kondrachov, with OpenAI/math's Lean 4.34.1 compatibility patches.
* OpenAI/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
* All 2,923 protected OAI modules were built from source with `lake build`.
* Candidate modules were compiled one file at a time in dependency order with `lake env lean` (`scripts/build_oai.sh`, `scripts/setup_env.sh`).

**Result**

All 219 modules compiled without errors.

* The sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `extern`.
* A final pass found every module up to date with its source and imports.

 The final checks report only the three standard axioms:

```
'Candidate.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle61.FinalAssembly.beta_le_rational' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle61Verification.allDirichlet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle61Verification.zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle61Verification.allHecke' depends on axioms: [propext, Classical.choice, Quot.sound]
'Cycle61Verification.zetaTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Candidate.bound` states non-vanishing for `(437423 / 500000 : ℝ) < s.re`. The transcripts are in [`verification/`](verification/).

**Tracker preparation, run locally**

The tracker's own `verifier/standard/prepare.mjs` (repository base `43cc0ac`) was run on a snapshot of the submission. It accepted the file set (219 Lean modules, within the size limits) and generated the canonical `Challenge.lean` and `Solution.lean` for 437423/500000. `Solution.lean` compiles against the candidate:

```
'QRH.canonical_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The PR body passes the tracker's own checks:

* `parseDeclaration`;
* `parseSubmissionMetadata`;
* `validateDecimalApproximation`, against both 874861/1000000 (Cycle61) and 4374299/5000000 (`gao-cycle61-plane-20261013`);
* `classifyChanges`, which gives a proof-only PR with no maintenance paths.

**Per-module time and the 600-second replay limit**

* **Measurements.** Wall-clock compile times are in [`verification/module-wall-seconds.json`](verification/module-wall-seconds.json). They were measured on a 4-core 2.1 GHz Xeon VM, with up to three modules in parallel.
* **Why the split.** Unsplit, the Cycle61 bundles `B167` and `B176` took 1130 s and 904 s here, so they are split.
  * `B167`: one module per original source section. Section 1 is further split at declaration boundaries into `B167Part1A`–`1D`.
  * `B176`: one module per section. Section 2 is further split into `B176Part2A`–`2C`.
  * Declarations, statements and proofs are unchanged.
* **Slowest modules.**

  | module | local time | contents |
  |---|---|---|
  | `B176Part2B` | 580–588 s | the single theorem `actual_geometry_main_all_height_coarse_family` |
  | `B167Part1C` | 497 s | the single theorem `actual_geometry_low_paid_fields` |

  Both are single Cycle61 declarations and cannot be split further without changing the proofs. Every other module took under 500 s.
* **Expected margin.** The tracker's replay runs on GitHub `ubuntu-24.04` runners, which are typically faster single-threaded than this VM. The upstream submission `gao-cycle61-plane-20261013`, which was accepted, also has each of these two theorems whole in one module.

The machine had four cores and 15 GiB of memory. The largest bundles (B155, B167, B173, B180) peaked at about 9 GiB resident memory each.

To reproduce:

1. Clone OpenAI/math at the pinned revision into `/home/user/leanbuild/openai-math`. The scripts use absolute paths under `/home/user/leanbuild`, so adjust them for another location.
2. Run `scripts/setup_env.sh`, which needs `zstd`.
3. Copy `scripts/oai_targets.txt` (the 375 direct OAI imports, produced by `scripts/closure.py`) to `/home/user/leanbuild/`, then run `scripts/build_oai.sh`.
4. Link `submissions/detector-affine-c0125154/src/Candidate` into the project as `Candidate`.
5. Run `python3 scripts/compile_candidate.py 2 Candidate.Main`. It compiles each module with `scripts/lc.sh`, in dependency order.

## What this does and does not establish

* This is a local compilation. It is not the tracker's Comparator plus three-kernel replay. Exact-head acceptance needs the tracker's own check on the submitted commit.
* The exact arithmetic is reproduced independently by [`arithmetic/rational-check.py`](arithmetic/README.md). The Lean files contain the same certificates, checked by `norm_num`.
* Submission limits:
  * 219 Lean files (under 256);
  * about 7.9 MB in total (under 10 MB);
  * largest file 0.72 MB (under 2 MB);
  * only `src/Candidate/**/*.lean`.
