# Fresh look after E5: what the new faces unlock

Status: numerical (exact rational mirror of the reflective return check, Python, `$SCRATCH/fresh-look/`). Not yet
in Lean. Written by a fresh-look review on 2026-10-30 (no prior context), saved here verbatim in substance.

## 0. Bottom line

θ = 0.87343238 (−7.03e-5 below the E5 retune's 0.87350266) from two return constants, with no new analysis;
two cheap follow-ups give 0.87339298 (−1.10e-4). All θ from the exact mirror (the retune's `mirror2.py` with
three constants as parameters); it reproduces the retune exactly (N = 6324867 passes, N+1 fails, 96 leaves /
366 tests). Reserve 1e-8, all four edges.

The E5 retune is limited not by the faces but by two legacy count-return constants:
- the natural join `naturalM = (1 − 9/2·sMinus)/2 = 0.4325` (`sMinus = 3/100`),
- the plain floor `mMinus = 377/1000`.
Collet's window interface allows both to move (`AdmittedWindow.mHi ∈ [2/5, 1/2)`, `mLo ≥ 0`, per window). The
retune's "floor 0.8734457" is guard 10 (natural tail), built from `sMinus`.

| configuration | θ | vs 0.87350266 |
|---|---|---|
| E5 retune (merged guards, 5 branches, 8 windows) | 0.87350266 | 0 |
| merged guards, unlimited restricted faces, pointwise optimum | 0.87344525 | retune floor |
| **1.** sMinus 3/100 → 27/1000, mMinus 377/1000 → 3/10; E5 end face as is (Λ = 101/50) | **0.87343238** | **−7.03e-5** |
| **2.** + E5 line down to Λ = 401/200 (a = 1/1000) | **0.87341198** | **−9.07e-5** |
| 2′. + line down to Λ = 2001/1000 (a = 1/10000, K = 5001/10000) | 0.87340648 | −9.62e-5 |
| **3.** item 2 + transport floor margin 1/200 → 1/1000, h = 8059999/10⁷ | **0.87339298** | **−1.10e-4** |
| 3′. item 2′ + same | 0.87338708 | −1.16e-4 |

## 1. Read

- E5 brings the face to the architecture's wall (B = 0.99999 to Λ = 2.02; deletion at K ≥ 1/2 needs
  Λ > 6KB/(1+K) → 2B).
- With such a face the return's bookkeeping binds: guard 10 (window value above the tail
  1 − 2δ·naturalM − 2δp·sMinus) and guard 8 (witness above mMinus). With E5 faces the tail crosses the C count at
  δ ≈ 0.543 and meets the old count at δ ≈ 0.566, exactly where the retune binds.
- `count_from_piecewise_moments` (Collet, `Record1252270103Return/CountFromMoments.lean`) accepts any
  mHi ∈ [2/5, 1/2) and mLo ≥ 0; the face only needs slot width min(cap, (B − 2m)/Λ) > ν on [mLo, mHi].
  `FinalWindows.lean` sets `mHi := naturalM` globally; `gen_return86.side_conditions` asks only
  2/5 ≤ naturalM < 1/2 and mMinus ≥ 0.
- Freed, the binding is the interior optimum of the full E5 face (uncapped branch C, newTop, p = 1/2,
  δ* = 0.4522). Sensitivities: count −0.001 → −1.2e-4; Λ −0.01 → −1.4e-5; h +1e-3 → −4e-6; B → 1 and cap: 0.
- No longer levers: PR 93's per-class count (needs 2pδ > 1/2; binding has 0.452); the density curve from the
  E5 end (nearly parallel to the iso-θ direction); the selected norm in the long line; D8a's midpoint rule.

## 2. Opportunities

**#1. Free the natural join and the plain floor (−7.03e-5; trivial Lean).** Raising naturalM makes the tail
≈ 1 − δ; lowering mMinus lets the capped branch reach low δ; the E5 end face serves both pieces. Both constants
must change (either alone fails at 0.87347238). Robust variant with the same θ: sMinus = 1/10000 plus the
literal 11/25 → 1/2 in `upperM` and in unused guard 12. Instance: count face = physical face
(99999/100000, 101/50, 13309/100000), physicalCap = 3/25, numeratorCap = 3/40; windows
⟨.C, 1397/4096, 8189/16384, 0⟩, ⟨.C, 1397/4096, 9517/16384, 3/8⟩, ⟨.capP, 1/16384, 6411/16384, 3/8⟩; edges
1/2/2/40 leaves, newTop 134 tests (depth ≤ 21). Lean: `arvi_density/Return/Constants.lean` (sMinus, mMinus +
E5 constants), `arvi_return_tuning/GuardsQ.lean` (sMinusQ, mMinusQ), `Data.lean`, `Windows.lean`; consumers
(`CountWidth.natural_join_bounds`, `admitted_widths`, `CountDecode.admitted_natural_tail`,
`witnessLower_nonneg`) by norm_num or the guards. Risk: low (a missed consumer).

**#2. Extend the E5 line to Λ = 401/200 (another −2.0e-5; trivial Lean).** In `arvi_selected_leaf/Curve.lean`:
sA := 1/1000, domain Icc (401/200) (5143/2000), step 1/200000, end cap 13399/100000; K and R1 untouched. All
E5Gates fields hold (exact check, `e5gates.py`; tightest retention 5.2e-7, cap 2.6e-5, principal 5e-4; gates
monotone along the line). θ = 0.87341198; windows ⟨.C, 2847/8192, 8189/16384, 0⟩,
⟨.C, 2847/8192, 9507/16384, 3/8⟩, ⟨.capP, 1/16384, 3273/8192, 3/8⟩. Stretch 2′: a = 1/10000, K = 5001/10000,
step 1e-7 reach Λ = 2001/1000 (θ = 0.87340648; needs R1 at K = 5001/10000). Pays only after #1.

**#3. Transport floor margin 1/200 → 1/1000 (another −1.9e-5; moderate Lean, independent of E5).**
`BoundsN.floor_margin` (`arvi_density/ReturnD/TransportGeometry.lean:29`) is the only side condition capping
h; its 1/200 is a budget whose terms total ≈ 1e-10 (`t_padding`). With μ = 1/1000, h → 0.806, all
`gen_return86` side conditions pass (`sidecheck2.py`). θ = 0.87339298 with #1 + #2. Lean: replace 1/200 by μ
in ~9 places (`BoundsN.floor_margin`, `FloorExponent.floor_source_margin`, `htotal` in CubeFloorSaving /
CubeFloorCollected, `hfloorbudget` in HighApproximation / SharedNonfloor / NonfloorTransport,
`TransportParameters.floor_budget` via `t_padding`), rebuild ReturnD (119 modules). Risk: moderate.

**#4. Simplification: final theorem without the density chain; 3-window return.** `ArviOdeShape.native_end`
depends only on PR 76's `face0_source` and Sil's native step, so
`Return.dirichlet_of_sources (fun hβ => e5_end hR1 hβ) (fun hβ => e5_end hR1 hβ)` closes without the chain:
ChainF50 (130 files), `arvi_density/Density/*`, `Source/Hybrid*`, ChainK15 and Collet's PR 67 density lemmas
leave the import closure; `weakC7` and capC become dead code; 3 windows.

## 3. Assumptions

R1 holds as stated; the mirror predicts the Lean kernel (it did exactly on the retune); no consumer of
naturalM/mMinus outside the files listed in #1.

## 4. Afterwards

Binding: the uncapped full-face optimum near δ ≈ 0.453, p = 1/2. Architecture limit (Λ → 2, B → 1): about
0.873405 at the h ceiling, 0.873387 with h = 0.806. Further: better inverse / long lines in the count
(count −0.001 → −1.2e-4); a face with Λ < 2 needs selection below the square-root barrier.

Scripts/logs: `$SCRATCH/fresh-look/` (mirror3.py, cover3.py, exact_run.py, exact_design.py, e5gates.py,
sidecheck2.py, guardscan.py, ...).
