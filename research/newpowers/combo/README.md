# Our marked HIGH leaf against PR 93's joint detector count (2026-10-29)

Model: T-A's continuum chain (`../ta/ode2.py`, HIGH gate with the gain at nu in [q, 3/4], parent = current face)
followed by the exact return toolchain (`../ta/tc`, six branches, box ell < 0.18). Floats on the chain side,
exact on the return side; every number is a model value, not a Lean theorem. Ours alone at floor 1/2: 0.873870999
(the exact certified chain of `research/chain/` gives 0.8738725 with the five-branch return).

## PR 93 (open, Joseph Bebel, 0.87393379)

HIGH rows with slot amplitude delta (`Z^(delta s) <= slotMass`) are counted by
`jointRate(nu, delta) = min(rho(nu), J(nu, delta))`, `J = 3(1-delta)(1-nu)/(3-nu-2 delta)`
(three detector words of lengths r, 2m, r+m), for delta in [1001/2000, 3/4] (`WholeJointCount`: bins b >= 33/40;
an adaptive band nu in [29/50, 13/20] uses `detectorRate`). The cutoff delta > 1/2 is analytic:
`contraction_exponent_range` (the selected-norm iteration) needs it. Their price uses only a linear retained slope
`k(nu) - c` (`c = 17/200`, or `min(9/100, k(q) - 10011/20000)` in the adaptive version).

## Results (floor 1/2 unless stated)

| HIGH count | theta (model) | vs ours alone |
|---|---|---|
| ours alone (repeated marks, K = 8) | 0.873870999 | 0 |
| PR 93's retained-slope price alone, floor 0.65 / adaptive floor 0.58 | 0.873942696 / 0.873918749 | |
| max of the two final prices | 0.873870999 | 0 |
| K = 16, or parent cap 0.12 | 0.873870999 | 0 |
| floor 0.45 (Collet's count holds for a > 51/100) | 0.873868932 | -2.1e-6 |
| **per class: max(our count gain, PR 93's count gain) at each delta = 2 p nu**, PR 93 for nu >= 0.65 | 0.873862522 | -8.5e-6 |
| same, PR 93 for nu >= 0.58 | 0.873857057 | -1.39e-5 |
| same, PR 93 for nu >= 0.5005 (only the delta cutoff) | 0.873855426 | -1.56e-5 |
| same without the delta cutoff (not provable with PR 93's method) | 0.873842355 | -2.86e-5 |

Reading: the two counts are complementary per amplitude class. Ours (inverse cap x plain face facet) binds at the
most marked class p = 1/2; PR 93's J is strongest exactly there (J(nu, nu) = 1 - nu < rho(nu)), but only for
delta > 1/2. Taking the better count per class, not the better final price, is what pays.

## Why the floor is no longer the limit

Below q = 1/2 the chain runs on, but the count face is optimal where the chain slope reaches the return's count
break-even slope (0.0857): L = 1.894 at floor 0.45, for -2.1e-6. Further gains have to lower the slope itself.

Scripts: `combo_ode.py` (price-level combinations), `perclass.py` (per-class combination), `kscan.py`,
`lowfloor.py`; logs `log_*.txt`; results `results/`.
