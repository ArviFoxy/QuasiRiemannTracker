# arvi_bank: the engineering limit of the selected-leaf architecture (research bank, not a submission)

Lean prefix `Submissions.arvi_bank`, top namespace `QRH.ArviBank`. It proves

  β ≤ θ = 43669114/50000000 = 0.87338228,

which is 2.97e-5 below the selected-leaf PR #97 (0.87341198). That is not enough for a PR under the 5e-5 rule (bar
0.87336198). The bank exists so that a future lever only needs to find the remaining 2.03e-5.

## What changed relative to `arvi_selected_leaf` (#97)

1. **The line goes further down** (`Curve.lean`, written from `arvi_selected_leaf/Curve.lean`).
   - The selected-leaf native line now runs from `401/200` down to `20001/10000`.
   - Parameters: deletion cut `K = 500001/1000000` (the bottom of R1's range), selected fraction `a = 1/100000`,
     induction step `1/400000000`.
   - End face: `G(99999/100000, 20001/10000, 33571/250000)`.
   - Margins near Λ = 2 (hand-computed; the Lean proof is the actual check): retention ≈ 5e-10, overshoot ≈ 1.8e-4.
2. **The transport is forked** (`ReturnD/`, all 119 modules of `arvi_density/ReturnD`, module prefix renamed).
   Code changes:

   | file | change |
   |---|---|
   | `TransportGeometry.lean` | coarse box `BoundsN`: `h < 81/100` (was `806/1000`), in the structure and in the `Transport` copy of `h_interval`; `floor_margin`: `≤ signal θ − 1/1000` (was `1/200`) |
   | `Transport/TransportParameters.lean` | `floor_budget … ≤ 1/1000` and its two `change` lines (was `1/200`) |
   | `Transport/FinalFixedHigh.lean` | `have hb : h < 81/100` (twice) |
   | `Transport/Transport/{HighApproximation (twice), SharedNonfloor, NonfloorTransport}.lean` | `… + nu + sigma ≤ 1/1000` |
   | `Transport/Transport/{CubeFloorSaving, CubeFloorCollected}.lean` | `… + nu + saving ≤ 1/1000` |
   | `Transport/Transport/FloorExponent.lean` | `signal θ − 1/1000` |

   The budgets are chosen existentially (eventually small), so the smaller floor budget is still met. The namespaces
   are still `QRH.ArviDensity.…`, so `ReturnD/` cannot be imported together with `arvi_density/ReturnD`. The import
   closure of `Final.lean` was checked: no clash.
3. **The return is retuned** (`Return/`, 14 files, and `Tuning/`, 15 files, copied from `arvi_selected_leaf`).
   - c = 6330886/50000000 and h = 8097/10000; the binding newTop edge has an interior minimum near this h.
   - Count and physical faces: both `(99999/100000, 20001/10000, 33571/250000)`.
   - Windows:
     ```
     [⟨.C, 5729/16384, 8189/16384, 0⟩, ⟨.C, 5729/16384, 297/512, 3/8⟩, ⟨.capP, 1/16384, 5971/16384, 1/4⟩]
     ```

## Top theorems (`Final.lean`; both depend only on `propext`, `Classical.choice`, `Quot.sound`)

- `QRH.ArviBank.beta_le_theta : HeckeZeroSupremum.beta ≤ 43669114/50000000`.
- `QRH.ArviBank.dirichlet_nonvanishing_bank`: `L(χ, s) ≠ 0` for every Dirichlet character χ and every
  `Re s > 43669114/50000000`, except at the pole.

## Build

- 150 modules; per-module build times sum to 17.5 min.
- Slowest: `Tuning.EdgeCertificates` 33 s, `ReturnD.PhysicalDirect.Hybrid` 21 s, `Final` 14 s.
- On a warm cache, `lake build Submissions.arvi_bank.Final` ran in 5 min 53 s wall time on 4 cores.
