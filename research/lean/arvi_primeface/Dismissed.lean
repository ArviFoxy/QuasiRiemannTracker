import Mathlib

/-!
# Exponent bookkeeping for routes dismissed in the D1 / K-wall analysis (research file)

All quantities are exponents of `Z` (log scale). `s` is the prime-pool length, `μ` the plain length,
`τ` a pointwise exponent `max|A|² ≤ Z^τ·mean|A|²`. The trivial (pointwise) treatment of the pool loses `s`
(the Λ = 2 face). These lemmas certify the arithmetic behind three dismissals recorded in the journal.

* `holder_loses`: Hölder decoupling with exponent `p ≤ 1/(2s)` (needed for the pool's `2p`-th moment to stay in
  the large sieve's diagonal range) loses at least `2 s μ`, which exceeds the trivial `s` once `μ > 1/2`.
* `interpolation_loses`: Hölder interpolation through a pointwise bound loses `2 s τ`; it beats the trivial `s`
  only if `τ < 1/2` (the bootstrap and Burgess bounds give `τ ≈ 0.69`).
* `bootstrap_rule_loses`: the pointwise bootstrap rule on the plain sums loses `(2β − 1 − δ) m` against the
  dual norm in the binding regime, which is positive when `2β − 1 > δ`.
-/

namespace QRH.ArviPrimeFace

theorem holder_loses {s μ p : ℝ} (hs : 0 < s) (hp : 0 < p) (hp2 : p ≤ 1 / (2 * s)) (hμ : 0 ≤ μ) :
    2 * s * μ ≤ μ / p := by
  have h1 : p * (2 * s) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hp2 (by linarith : (0 : ℝ) ≤ 2 * s)
    rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
  rw [le_div_iff₀ hp]
  nlinarith [mul_le_mul_of_nonneg_left h1 hμ]

theorem holder_worse_than_trivial {s μ : ℝ} (hs : 0 < s) (hμ : 1 / 2 < μ) : s < 2 * s * μ := by
  nlinarith

theorem interpolation_loses {s τ : ℝ} (hs : 0 < s) (hτ : 1 / 2 ≤ τ) : s ≤ 2 * s * τ := by
  nlinarith

theorem bootstrap_rule_loses (β δ γ m s y : ℝ)
    (h1 : s ≤ (1 - δ + γ) * y + δ * s) (h2 : m + s ≤ (1 - δ + γ) * y + δ * (m + s)) :
    ((2 * β - 1) * m + max s ((1 - δ + γ) * y + δ * s)) -
        max (m + s) ((1 - δ + γ) * y + δ * (m + s)) = (2 * β - 1 - δ) * m := by
  rw [max_eq_right h1, max_eq_right h2]
  ring

theorem bootstrap_rule_loss_pos {β δ m : ℝ} (hm : 0 < m) (hβ : δ < 2 * β - 1) :
    0 < (2 * β - 1 - δ) * m := by
  nlinarith

end QRH.ArviPrimeFace

#print axioms QRH.ArviPrimeFace.holder_loses
#print axioms QRH.ArviPrimeFace.bootstrap_rule_loses
