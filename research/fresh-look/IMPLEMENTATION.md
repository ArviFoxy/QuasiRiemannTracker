# Implementation notes: REPORT items #2 and #4 in Lean

Status: **both done and built** (2026-10-30). Lean project `/home/user/lean-env/qrh` (toolchain 4.34.1). Sources are
edited there; the three files below are also copied into the repo mirror `research/lean/arvi_selected_leaf/`
(working tree only, nothing committed). Nothing under `R1/`, `arvi_return_tuning/` or `arvi_density/Return*` was edited.

Files changed or created (all in `Submissions/arvi_selected_leaf/`):

| file | state | what |
|---|---|---|
| `Curve.lean` | edited | Task A: `sA := 1/1000`, domain `Icc (401/200) (5143/2000)`, step `1/200000`; `sK` unchanged; gates by `linarith only`; imports `NativeStart` |
| `NativeStart.lean` | new | self-contained `Native.curve_induction` and `Native.native_end` (same proofs as `arvi_ode_shape`, without the density chain) |
| `Final.lean` | new | Task B: `beta_le_theta`, `dirichlet_nonvanishing_e5` (no R1 hypothesis) |
| `Gates.lean` | unchanged | `E5Gates` is generic in `a`, `K` |

## Task A: the E5 line down to Lambda = 401/200 (REPORT #2)

Constants: budget `sB = 99999/100000`, cap `c(Λ) = 1/10 + 3/50 (5143/2000 - Λ)`, `sA = 1/1000`, `sK = 501/1000`,
domain `[401/200, 5143/2000]`, step `1/200000`; end cap `c(401/200) = 13399/100000`.

```
theorem e5_sources (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (401/200 : ℝ) (5143/2000), GlobalSource sB Λ (sCap Λ)
theorem e5_end (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (401/200) (1/10 + 3/50 * (5143/2000 - 401/200))      -- cap = 13399/100000
```

Exact gate check (`scripts/e5gates.py`, Fractions): `Lend 401/200, a = 1/1000, K = 501/1000, h0 = 1/200000`: all gates
PASS, tightest retention 5.17e-7, cap 2.60e-5, principal 5e-4. The Lean proof (`e5_gates`) proves the same gates
symbolically for every `Λ₀, Λ` of the domain with `0 < Λ₀ - Λ ≤ 1/200000`; the worst case is `retention`, a linear
inequality with margin about `1e-6` (`linarith only [a0, hle]`), and `cap`, which needs the two product facts of
`cap_gate_aux`.

Proof style (compile time): the old `nlinarith` calls (about 1.5 s) are replaced by `linarith only [...]` and four small
lemmas (`sCap_ge`, `sCap_le`, `sCap_step`, `cap_gate_aux`). Elaboration of `Curve.lean` is now well under 2 s (profiler
sum about 2 s, wall difference to an import-only file about 0.4 s); every single tactic call is under 60 ms.

## Task B: the final theorem without the density chain (REPORT #4)

`Final.lean` imports `Curve`, `R1.Cap` and `arvi_return_tuning.Endpoint` and nothing else. R1 is discharged by
`selectedRootEnergy sK (by unfold sK; norm_num) (by unfold sK; norm_num)` (`sK = 501/1000`).

```
theorem selectedRootEnergy_sK : SelectedRootEnergy sK
theorem e5_end_cap (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (401/200) (13399/100000)
theorem beta_le_theta_of_R1 (hR1 : SelectedRootEnergy sK) : HeckeZeroSupremum.beta ≤ 43670599/50000000
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ (43670599/50000000 : ℝ)
theorem dirichlet_nonvanishing_e5 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43670599 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0
```
(all in `QRH.ArviSelectedLeaf`; `HeckeZeroSupremum = OAI.SevenEighths.HeckeZeroSupremum`.)
`#print axioms` of `beta_le_theta`, `dirichlet_nonvanishing_e5`, `e5_end`, `e5_sources`, `Native.native_end` and of R1
(`selectedRootEnergy`): `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`, `native_decide`.

The return side needed nothing: `arvi_return_tuning.Endpoint.beta_le_theta_of_sources` / `dirichlet_of_sources` already take
both the count face and the physical face as `G(99999/100000, 401/200, 13399/100000)` (theta = 43670599/50000000), which
is `e5_end` after `1/10 + 3/50 (5143/2000 - 401/200) = 13399/100000` (one `norm_num` in `e5_end_cap`).

### Import closure (local modules = `Submissions.*` and `Candidate.*`)

`Final`'s total import count from Lean's environment is 15247 modules (10763 outside the project); the project-module
counts below match the script `closure.py` (scratchpad, parses `import` lines) exactly.

| | local modules | local olean MB | local source MB |
|---|---|---|---|
| previous record `arvi_density.FinalF50` (ChainF50 + merged return) | 4918 | 3564 | 51.9 |
| `arvi_selected_leaf.Final` | 4484 | 2653 | 41.1 |
| change | -434 | -911 (-26 %) | -10.8 |

Left the closure (596 modules, 1032 MB olean, 13.0 MB source): `ChainF50` 130 (6.1 MB), `arvi_density/Density/*` 15,
`arvi_density/Source/Hybrid*` 2, `density_split_fine_chain` (ChainK15 and `HybridK15_*`) 48 (3.1 MB), 319 Collet modules
(among them the 13 `PR67Source/Cycle63/Density/*` and `LocalMoment`), 46 modules of the merged `arvi_density/Return`
(`Rows/*`, windows, schedule), 34 repeated-marks modules. Entered (162 modules, 121 MB): R1 and the selected leaf
(`Candidate.Local` 114, `arvi_selected_leaf` 33) and `arvi_return_tuning` 15. What remains of `arvi_density`: `Return` 14 and `ReturnD` 119
modules, no `ChainF50`, no `Density/*`, no `Source/Hybrid*`. The only `Source/Hybrid*` left are Sil's own four
(`sil_density_split_20261026/Source/Hybrid{Gates,Certificates,CertificatesFirst,CertificatesSecond}`), imported by Sil's
`CubeFree.Assembly.Leaves`, i.e. part of the native step engine (they are in the previous record's closure too).

### Build and compile times

`lake build Submissions.arvi_selected_leaf.Final` (everything else up to date): Build completed successfully, 13428 jobs
(R1, the return and the three files). `lake build Submissions.arvi_selected_leaf.Curve` alone is 12947 jobs now against
13313 before the change (-366 modules: the density chain behind `arvi_ode_shape.Induction`). Module times printed by lake
for a rebuild:
`NativeStart` 6.2 s, `Curve` 8.2 s, `Final` 6.8 s (one later rebuild of `Final` took 21 s while other builds ran). Standalone
`lean` runs, median of 5 on an idle machine (wall, includes loading the import closure, about 6.9 s):

| file | median wall | import-only baseline |
|---|---|---|
| previous `Curve.lean` (a = 1/250, imports `arvi_ode_shape.NativeCurve`) | 11.6 s | about 7.5 s |
| new `Curve.lean` | 7.3 s | 6.9 s |
| `NativeStart.lean` | 5.9 s | |
| `Final.lean` | 6.8 s | 6.9 s |

The elaboration itself is about 2 s or less for each of `Curve` and `NativeStart` and under 0.2 s for `Final`; the rest is
loading the oleans. `lake build --no-build` on `Final` reports "All targets up-to-date".

## Decisions and caveats

1. **`ArviOdeShape.native_end` cannot be imported lightly.** `arvi_ode_shape/NativeCurve.lean` imports
   `arvi_ode_shape/Induction.lean` only for `curve_induction`, and `Induction.lean` imports
   `arvi_density.Density.StepMarked` only to get `GlobalSource` into the statement of `ode_inequality_estimate`. So `Curve`
   (and anything importing `native_end`) pulled in 17 `arvi_density` modules (`Density/*`, `Source/HybridGates*`) and about
   320 Collet modules for nothing. I did not touch `arvi_ode_shape` (an edit of `Induction.lean` was refused by the
   permission layer: shared package outside the brief). Instead `NativeStart.lean` carries a copy of `curve_induction`
   and of the native line with the same proofs (`Native.native_end` and `ArviOdeShape.native_end` are the same
   proposition: `example : @Native.native_end = @ArviOdeShape.native_end := rfl` checks).
2. **The one-line alternative (validated on a scratch copy, not applied):** in `arvi_ode_shape/Induction.lean` replace
   `import Submissions.arvi_density.Density.StepMarked` by
   `import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract` (where `GlobalSource` is defined).
   The scratch copy compiles (4.6 s), and the closure of `NativeCurve` then has 0 `arvi_density` modules. With that edit
   `NativeStart.lean` can be deleted and `Curve.lean` can import `Submissions.arvi_ode_shape.NativeCurve` and use
   `ArviOdeShape.native_end`, `ArviOdeShape.curve_induction` (identical statements). `Shape.lean` and `Final.lean` of
   `arvi_ode_shape` would need a rebuild (they import `Induction`).
3. **Collateral of the return retune (not mine):** per `research/return-tuning/E5_LEAN_RETUNE.md` section 6,
   `arvi_density/FinalF50.lean`, `arvi_ode_shape/Final.lean` and the old merged `Return/Rows/*` no longer compile against the
   new constants. The closure numbers for `FinalF50` are therefore taken from its static import graph (the previous record's
   modules); only `Return.Rows.Admission01.olean` of that closure is missing in the build directory now.
4. **Stale target after a dependency rebuild:** `Final` was built at 01:20; `arvi_return_tuning.Endpoint` was rebuilt at 01:23
   by its owner, so lake reported `Final` out of date (its oleans are newer than `Final`'s); `Final` was rebuilt and is
   up to date. Any further rebuild of the return makes `Final` stale again until `lake build` is repeated (it costs one
   elaboration of `Final`, a few seconds).
5. **Stray file:** `/CmpNative.lean` (0 bytes, filesystem root) was created by a mistyped command of mine (unset shell
   variable). Removing it was blocked by the safety check, so it is still there; `rm /CmpNative.lean` deletes it.

## Reproduce

```
export PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH
python3 research/fresh-look/scripts/e5gates.py
cd /home/user/lean-env/qrh && lake build Submissions.arvi_selected_leaf.Curve Submissions.arvi_selected_leaf.Final
lake build --no-build Submissions.arvi_selected_leaf.Final      # All targets up-to-date
```

## Possible next steps

- Apply the one-line `Induction.lean` import change and delete `NativeStart.lean` (decision 2).
- REPORT #2' (stretch): `e5gates.py` already passes `Lend 2001/1000, a = 1/10000, K = 5001/10000, h0 = 1e-7`; R1 covers
  `K = 5001/10000` (`selectedRootEnergy` holds for `K ∈ [0.500001, 3/4]`), so the line could be extended by changing the
  same constants in `Curve.lean` (the `cap_gate_aux` bounds and the retention margin are the places to re-check); the
  return would have to be retuned to that face (theta 0.87340648).
- Retire or fix `arvi_density/FinalF50`, `arvi_ode_shape/Final` and the stale merged `Return/Rows/*` (decision 3).
