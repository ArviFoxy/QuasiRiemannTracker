# Detector affine capacity: θ = 437423/500000

This note describes how the result differs from Cycle61
([`cycle61-c0125139`](../../cycle61-c0125139/README.md), θ = 874861/1000000). Everything not mentioned here is Cycle61's argument, unchanged. Sections are cited as in the Cycle61 paper.

## 1. Where the gain comes from

The Cycle61 detector count (Cycle25 `DetectorRawFiber`) treats a fiber of plain length `m` and marked weight `w = Σ widths` with three kinds of moment:

* the inverse moments;
* the unmarked plain moment, used when `m ≥ 1/2`;
* the κ-marked plain moment.

The κ-marked moment is available under the capacity constraint

    2m + 6κ·w ≤ 1,          i.e.  w ≤ (1 − 2m)/(6κ).

Cycle61's Theorem 2.2 (`Cycle61Moment.InitialAffineAt`) is an initial affine moment, with Λ = 19312/4787 and B = 14200/14361 − 10⁻⁵. Under the window conditions

    41/100 ≤ m ≤ 44/100,   17/500 ≤ w ≤ 1/25,   2m + Λ·w ≤ B,

it gives the same `U^{1+ε}` bound. Cycle61 used it only in the source row. Inside the window

    m ∈ [m_lo, m_hi],   m_lo = (B − Λ/25)/2 ≈ 0.413704,   m_hi = 847/2000,

the affine capacity `(B − 2m)/Λ` is larger than `(1 − 2m)/(6κ)` for every κ ∈ [κ*, 3/4]. This submission uses Theorem 2.2 inside the detector count as well.

## 2. The new count

Write δ for the row length, `p = q/δ` (`x` in Cycle25), and `V = 5/6 − δ`. Define

    DN = 3 − p − 4p/Λ,   aN = 2 − 4p/Λ,   cN = 1 − 2pB/Λ,
    J_N = V·DN + δ(1−p)·aN,      numT = V·DN + δ(1−p)(aN + cN).

On a fiber with cutoff `t` and inverse length `r`, the affine branch gives the exponent

    affineExp(δ, p, m) = 1 − 2δm − 2δp(B − 2m)/Λ.

At `m = t − r` this equals the inverse exponent `1 − δ(p + (1−p)r)` exactly when

    r = r_N(p, t) = (aN·t + 2pB/Λ − p)/DN.

So the short-branch exponent becomes `shortNew = 1 − δ(p + (1−p)·r_N)`, against the long branch `1 − δ + V(t − 1)`. The two branches balance at

    t_N = numT/J_N,

with common value

    R_New(δ, p) = 1 − δ + V·δ(1−p)·cN/J_N.

`Affine/Arith.lean` proves `short_at_tN`, `long_at_tN` and `max_at_tN`. Unlike Cycle25's `countingR`, `R_New` does not depend on κ.

### Case analysis (`affine_count_bound`)

The fiber estimates give `t − r − γ ≤ m` and `r ≤ t + γ`.

* `r ≥ 1`: the long branch. `r ≥ r_N`: the inverse branch, where `inverse_le_short` applies.
* `r < r_N` forces `m ≥ m_N − γ`, with `m_N = t − r_N(t) ≥ m_lo + γ`. Then:
  * `m ≥ 1/2`: the unmarked branch. Here `r_N ≤ 1` gives `shortNew ≥ 1 − δ`.
  * `m ∈ [m_N − γ, m_hi]`: the affine branch. `affine_antitone` and `affine_shift` move the exponent from `m` to `t − r_N`.
  * `m ≥ m_hi`: the old κ-marked moment, called directly through `plain_marked_count`. The tail certificate shows `oldPlainExp(m_hi; κ) ≤ shortNew(t_N)` for κ ∈ [7/10, 3/4].

    The Cycle25 crossing precondition was needed only to get `m ≥ 1/3 − γ`, and that holds automatically here.

In the affine branch, the per-fiber count calls OAI `plain_fiber_count` with

    κ' = (1 − 2m)/(6z),   z = (B − 2m)/Λ − ν.

Its capacity hypothesis `2m + 6κ'w ≤ 1` is then `w ≤ z`. The marked moment comes from one of two sources:

* if `w ≥ 17/500`, the affine moment;
* if `w < 17/500`, the old κ-moment. This is admissible because `(1 − 6·(3/4)·17/500)/2 = m_hi`.

## 3. Where the new count is used

The new count is used only on the region

    InRegion δ p :=  89/200 ≤ δ ≤ 97/200  ∧  99/200 ≤ p ≤ 1/2,

and only when κ ≥ κ* = 2θ − 1:

    countingR κ δ p := if InRegion δ p ∧ κ* ≤ κ then R_New δ p else countingR0 κ δ p.

`cutoffA` is gated the same way, picking `t_N` or Cycle25's cutoff. Here `countingR0` is Cycle25's `countingR`. Outside the region every Cycle61 statement is unchanged, but it is now proved at the new endpoint.

Inside the region, `Affine/Certificates.lean` gives exact Bernstein certificates, bound in `Affine/Region.lean`, for:

| certificate | statement |
|---|---|
| `regionCutoff`, and the identity for `tN` | 1 ≤ t_N ≤ 3/2 |
| `regionCrossLo`, `regionCrossHi` | 23/37 ≤ r_N(t_N) ≤ 1 |
| `regionPlain` | m_N ≥ m_lo + 1/10000 |
| `regionTail` | old marked exponent at m_hi ≤ shortNew(t_N) for κ ∈ [7/10, 3/4] |
| `regionCompare` | R_New ≤ countingR0 κ* |
| `regionRow` | the final new-h row, at saving 10⁻⁶ |

`regionCompare` and the κ-monotonicity of `countingR0` make every Cycle61 row lemma that only needs an upper bound on the count transfer to `countingR`. The masked amplitude transfer (`Affine/Masked.lean`) needs `countingR` to be antitone in `p`:

* inside the region this is `RNew_antitone`, via an explicit multilinear expression;
* across the region boundary it follows from `regionCompare` plus the κ* gate.

## 4. Endpoint and constants

    θ = 437423/500000 = 0.874846,   c = 62577/500000,   h = 15903/20000,
    ℓ = 62731/375000,   x = 558199/1500000,   y = 690877/1500000,
    κ* = 187423/250000,   d₋ = 15883/20000,   d₊ = 7951500001/10000000000.

With `h ≤ 0.7952`, two Cycle61 design checks stay positive: `slot_upper_gap` (37/1000 − z_max) and `bmax_below_4_25`. The float optimum for θ under that cap is about 0.8748448 (`scripts/fastopt.py`). The rational endpoint 437423/500000 leaves positive margins.

[`arithmetic/rational-check.py`](../arithmetic/rational-check.py) rebuilds the following with exact rationals:

* every Cycle61 scalar design check at the new endpoint;
* the three regenerated row certificates in `Bundles/B021.lean` (`newRow` on the complement of the region, `oldHalf`, `oldJunction`);
* the seven region certificates.

It checks that every coefficient is positive and that the row boxes tile `[0, 3/4] × [0, 1/2]`. It then compares every power polynomial, coefficient matrix and box with the Lean source, character for character.

## 5. Moment supply

`DetectorAffineInput` (`Affine/Moments.lean`) asks for the affine marked moment on every detector fiber. `Affine/Supply.lean` proves it from Cycle61's generic machinery:

1. Every detector dictionary character `η_ℓ = sourceMomentBase … η ℓ` has modulus dividing the fixed bad mask, so it is its own natural row (`naturalRowOf`). Excluding the unit ideal leaves it unchanged (`excluded_one_ofResidue`).
2. `actual_affine_main_uniform_paid`, `actual_affine_error_uniform_paid_of_normalized` and `actual_affine_error_normalized_family` give the paid main and error families. `literal_affine_geometry_budget_of_main_error` and `literal_geometry_initial_affine` then give `InitialAffineAt` at mesh `detectorMesh ε = geometryChosenMesh ε` with loss ε.
3. The detector fiber energy equals the initial energy (`energy_eq`, with θ ≡ 1), as in Cycle25's `weighted_source_batch_plain_marked_fine`.

The polynomial degree in Theorem 2.2 is uniform only over finite families of characters. So the assembly chooses the height τ and the moment degree J for each detector character η:

* `actual_joint_height` (B025);
* `fixed_numerator_of_cells` and `sourceProbe_high_of_finite_numerator_at` (B043, B078).

This is enough because `fixed_source_contract` and `UniformCommonProbe` consume the probe bound one character at a time.
