# Implementation notes: REPORT items #2 and #4 in Lean

Lean project: `/home/user/lean-env/qrh` (toolchain 4.34.1). Sources edited there; the repo mirror
`research/lean/arvi_selected_leaf/` is synced at the end (no commit).

## Status log

- (start) State found: `Curve.lean` still at the E5 end (sA = 1/250, domain Icc (101/50) (5143/2000), step 1/100000);
  no `Final.lean`; no previous notes. `arvi_return_tuning/Endpoint.lean` (other agent) already takes the face
  `G(99999/100000, 401/200, 13399/100000)` (theta = 43670599/50000000).
- `e5gates.py` (exact): all gates PASS for (Lend 401/200, a 1/1000, K 501/1000, h0 1/200000);
  tightest: retention 5.17e-7, cap 2.6e-5, principal 5e-4.

## Finding on the import closure (matters for Task B)

`ArviOdeShape.native_end` lives in `arvi_ode_shape/NativeCurve.lean`, which imports `arvi_ode_shape/Induction.lean`
only for `curve_induction`; `Induction.lean` imports `arvi_density.Density.StepMarked`. So importing `native_end`
(and therefore `arvi_selected_leaf/Curve.lean`) pulls 17 `arvi_density` modules (`Density/*`, `Source/HybridGates*`)
and their Collet dependencies into the closure, although the proof of `native_end` uses none of them.

## Coordinator update (Task B)

R1 is proven and built: `QRH.ArviSelectedLeaf.selectedRootEnergy (K : ℝ) (hK1 : (500001/1000000:ℝ) ≤ K)
(hK2 : K ≤ 3/4) : SelectedRootEnergy K` in `Submissions.arvi_selected_leaf.R1.Cap` (statement at Cap.lean:150).
Final.lean discharges `hR1` with `selectedRootEnergy (501/1000) (by norm_num) (by norm_num)`, so the final theorem has
no R1 hypothesis. `R1.Cap` is imported (closure 3369 local modules, 114 of them `Candidate.Local.Qrh.JointDetector`).
Nothing under `R1/` is edited.

## Decision: native start without touching `arvi_ode_shape`

The clean fix is one line: in `arvi_ode_shape/Induction.lean` replace `import Submissions.arvi_density.Density.StepMarked`
by `import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract` (that is where `GlobalSource` is
defined; `curve_induction` and `ode_inequality_estimate` use nothing else from `StepMarked`). Attempting that edit was
refused by the permission layer (shared package outside the brief), so it is NOT made. Instead a self-contained copy of
`curve_induction` and of the native line is created inside the selected-leaf package
(`Submissions/arvi_selected_leaf/NativeStart.lean`, namespace `QRH.ArviSelectedLeaf.Native`), same proofs, and
`Curve.lean` imports it in place of `arvi_ode_shape.NativeCurve`. If the one-line edit is later allowed, `NativeStart.lean`
can be deleted and `Curve.lean` can import `arvi_ode_shape.NativeCurve` again (identical statements).

## Done: Task A (REPORT #2, E5 line down to Lambda = 401/200)

Files (Lean project `/home/user/lean-env/qrh`):
- `Submissions/arvi_selected_leaf/Curve.lean` (edited): `sA := 1/1000`, domain `Icc (401/200) (5143/2000)`, step
  `1/200000`, `sK := 501/1000` unchanged. Gate proofs rewritten as `linarith only [...]` with three small helpers
  (`sCap_ge`, `sCap_le`, `sCap_step`, `cap_gate_aux`); the old `nlinarith` calls are gone. Imports
  `Submissions.arvi_selected_leaf.NativeStart` instead of `Submissions.arvi_ode_shape.NativeCurve`.
- `Submissions/arvi_selected_leaf/NativeStart.lean` (new): `Native.curve_induction`, `Native.native_end` (copies of
  `ArviOdeShape.curve_induction` / `ArviOdeShape.native_end`, same proofs; gates by `linarith only`).
- `Gates.lean`: unchanged (`E5Gates` is generic in `a`, `K`).

Statements (unchanged shape, new constants):
```
theorem e5_sources (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (401/200 : ℝ) (5143/2000), GlobalSource sB Λ (sCap Λ)
theorem e5_end (hR1 : SelectedRootEnergy sK) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (99999/100000) (401/200) (1/10 + 3/50 * (5143/2000 - 401/200))      -- cap = 13399/100000
```
`e5gates.py` (exact, Fractions): Lend 401/200, a 1/1000, K 501/1000, h0 1/200000 -> all gates PASS; tightest
retention 5.17e-7, cap 2.60e-5, principal 5e-4. The Lean proof checks the same gates symbolically.

Build (lake, all dependencies up to date): NativeStart 6.2 s, Curve 8.2 s (module times as reported by lake; about 7 s
of each is loading the import closure, elaboration is about 1.5 s). `lake env lean Curve.lean` standalone: 7.9-8.9 s versus
12.6-12.8 s for the previous Curve.lean (same machine, 3 rounds).

## Done: Task B (REPORT #4, final theorem without the density chain)

`Submissions/arvi_selected_leaf/Final.lean` (new), imports `Curve`, `R1.Cap`, `arvi_return_tuning.Endpoint`:
- `selectedRootEnergy_sK : SelectedRootEnergy sK` (= `selectedRootEnergy sK ..`)
- `e5_end_cap : ... GlobalSource (99999/100000) (401/200) (13399/100000)`
- `beta_le_theta_of_R1 (hR1 : SelectedRootEnergy sK) : HeckeZeroSupremum.beta ≤ 43670599/50000000`
- `beta_le_theta : HeckeZeroSupremum.beta ≤ 43670599/50000000`
- `dirichlet_nonvanishing_e5 (χ) (hs : 43670599/50000000 < s.re) (hpole) : LFunction χ s ≠ 0`
`#print axioms`: `[propext, Classical.choice, Quot.sound]` for `beta_le_theta`, `dirichlet_nonvanishing_e5`, `e5_end`,
`e5_sources`, `Native.native_end`, `selectedRootEnergy`.
The current `arvi_return_tuning.Endpoint` already takes both faces as `G(99999/100000, 401/200, 13399/100000)`
(theta = 43670599/50000000), so nothing is missing on the return side.

Import closure (local modules, i.e. `Submissions.*` and `Candidate.*`; script `closure.py` in the scratchpad parses
`import` lines):

| | modules | olean MB |
|---|---|---|
| current submission, `arvi_density.FinalF50` | 4918 | 3564 |
| `arvi_selected_leaf.Final` | 4484 | 2653 |

Left the closure (596 modules, 1032 MB): `ChainF50` 130, `arvi_density/Density/*` 15, `arvi_density/Source/Hybrid*` 2,
`density_split_fine_chain` (ChainK15, HybridK15_*) 48, Collet's PR 67 density lemmas (13 `Cycle63/Density` plus
`LocalMoment`; 319 Collet modules in all), the old `Return/Rows/*` and 34 repeated-marks modules. Entered (162
modules, 121 MB): R1 (`Candidate.Local` 114, `arvi_selected_leaf` R1 and others 33) and `arvi_return_tuning` 15.
Remaining `arvi_density` modules: `Return` 14 and `ReturnD` 119 only. Remaining `Source/Hybrid*`: Sil's own four
(`sil_density_split_20261026/Source/Hybrid{Gates,Certificates,CertificatesFirst,CertificatesSecond}`), pulled in by
Sil's `CubeFree.Assembly.Leaves` (part of the native step engine, also in the current submission).
