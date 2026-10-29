# Return retune for the E5 faces (exploratory, not yet in Lean)

Status: numerical (exact rational kernel mirror of the reflective return check, Python). Nothing here is proven
until the Lean return certificates are rebuilt with these constants and R1 (`SelectedRootEnergy (501/1000)`) is
proven. Source: a delegated retune run on 2026-10-29; scripts in `$SCRATCH/retune` (not committed yet).

## Result

- theta = 43675133/50000000 = 0.87350266 (c = 6324867/50000000). Merged record 0.87387234: gain 3.697e-4.
- The cover passes at N = 6324867 and fails at N+1 (least found). Mirror check: the merged constants reproduce
  the merged certificate counts (1/3/3/142 tests) and fail one c-step later.
- h = 1001231/1250000 = 0.8009848 (7-digit floor of the h-ceiling 0.800984897399).
- Floor for these faces: nothing goes below about 0.8734457 (delta 0.566, p 1/2, natural-tail guard 10).

## Constants (merged -> new)

| constant | merged | new |
|---|---|---|
| countCB | 96232839/10^8 | 3913/4000 |
| countCL | 3853/2000 | 101/50 |
| countCap | 9999/10^5 | 21/200 |
| physicalB | 49283557/5e7 | 99999/100000 |
| physicalLambda | 4503/2000 | 101/50 |
| physicalCap | 31/500 | 1097/10000 |
| numeratorCap | 3/50 | 3/40 (needs numeratorCap <= physicalCap) |
| weakC7 offset | 7/4000 | 22/625 |

dm = 19/25, reserve = 1/10^8; mMinus, sMinus, K unchanged. One E5 source G(99999/100000, 101/50, 13309/100000)
(the E5 line at Lambda = 101/50: cap 1/10 + (3/50)(5143/2000 - 101/50) = 0.13309) serves all branches by
monotonicity (B lower, Lambda higher, cap lower).

Branches: C = (3913/4000, 101/50, 21/200); capC = same, capped; weakC7 = (18861/20000, 101/50, 21/200);
capP = (99999/100000, 101/50, 1097/10000), capped. Capped caps must stay below (B - 2 mMinus)/Lambda
(0.1110 for capC, 0.1218 for capP).

Windows (branch, deltaLo, deltaHi, pLo), newTop only:
C 5/12 182/335 1/3 | capC 45/128 3/8 15/32 | weakC7 3/10 199/356 1/3 | capP 17/47 9/20 3/8 |
capP 2/5 13/27 6/13 | capP 2/5 39/79 28/57 | capP 63/128 2031/4096 255/512 | capP 2031/4096 8139/16384 1023/2048.

Coversim: max depth 27 (< 30); newTop 96 leaves / 366 tests. Binding margin -4.3e-7 at newTop (delta 0.543284,
p 1/2, C -> weakC7 handover).

Levers: merged physical face + new count faces 0.873758; + new physical face 0.873703; + numeratorCap 3/40
0.873502.

## Lean changes needed (none made yet)

arvi_density/Return/Constants.lean (c, h, the face constants, numeratorCap, value lemmas), Formulas.lean
(branchB .weakC7), Endpoint.lean (source faces, theta literal), FinalF50.lean; arvi_return_tuning Data.lean,
Windows.lean, Endpoint.lean. Windows/Rows/EdgeCertificates of arvi_density become stale.
