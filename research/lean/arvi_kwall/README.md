# arvi_kwall: the faces' K ≥ 1/2 wall is a property of the method (research, not a submission)

Lean prefix `Submissions.arvi_kwall`, namespace `QRH.ArviKWall`. One file, `Closure.lean`, Mathlib only; it checks
in about 8 s on a warm cache. Both top theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What it proves

PR 93's selected norm is built from three rules. In log scale (x = log_B of the source length, n(x) = log_B of the
selected norm, rows of norm ≈ B selected at slope δ) they read:

| rule | statement |
|---|---|
| initial bound | n(x) ≤ Θ₆(x) = max(1, x, 5/6 + x/3, 1/3 + 5x/6), the optimal general sextic sieve. PR 93 itself starts from the weaker L + B². |
| amplification by a selected slot block | n(x) ≤ n(y) − δ(y − x) for x ≤ y |
| reflection (Poisson at conductor B²) | n(x) ≤ max(x, x − 1 + n(2 − x)) for 1 ≤ x ≤ 2 |

- `nstar_rules`: for 1/3 ≤ δ < 1/2, the function n*(x) = max(x, 7/6 + δ(x − 1) + (1 − 2δ)·max(x − 1, 0)) obeys all
  three rules, and n*(1) = 7/6.
- `no_balanced_bound_below`: so no argument built from these rules certifies a selected norm below B^{7/6} at the
  balanced point L = B.
- `fixed_point_not_derivable`: in particular the slope-δ fixed point max(x, 1 − δ + δx), which PR 93 reaches for
  δ > 1/2 and which equals B at L = B, does not follow from the rules.

## Why it matters

- The faces' native steps end at Λ = 6KB/(1 + K), which is 2B at K = 1/2. A face below Λ = 2 needs the selected
  leaf at K < 1/2.
- Below slope 1/2 the selection buys nothing at the balanced point, even with the optimal sextic sieve as the
  starting bound. The loss is exactly Θ₆'s excess 1/6 there.
- The reason: one amplify–reflect cycle x = 1 → y → 2 − y → 1 changes the bound at the balanced point by
  (1 − 2δ)(y − 1). That is a gain only if δ > 1/2.
- So moving the wall needs a new direct estimate for the selected rows at L = B: a Guth–Maynard-type operator-norm
  bound on a large-value set of the sextic family. Neither a better start nor more rounds can do it.

## Dilution.lean (RIP program)

- `fixed_point_of_dilution`: the diluted initial bound n(x) ≤ max(1, x, Θ₆(x) − δ) plus amplification gives
  n(x) ≤ 1 − δ + δx on [0, 1] for every δ ≥ 1/6.
- `kwall_is_dilution`: for δ ∈ [1/3, 1/2) both statements hold at once:
  - the undiluted rules admit n(1) = 7/6;
  - the diluted bound forces n(1) ≤ 1.

  So the whole K-wall is the gap between Θ₆ and its dilution on thin row sets.
- Numerics in `../../rip/`: the sextic Gram matrix follows Marchenko–Pastur, and slot large-value sets behave like
  random subsets. So the dilution holds empirically.
