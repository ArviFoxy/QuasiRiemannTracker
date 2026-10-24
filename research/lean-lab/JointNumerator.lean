/-
Joint numerator bound versus Levy's weighted numerator (research/LOG.md,
"Joint numerator bound", 2026-10-24).

Exponents are in base U for one row class at the conductor edge d = h.
* Levy (foundations (223)): Hölder at order 4 over all rows,
    `levy = 3R/4 + 1/4 - q zA/2`, `zA = (B - 2 n₀)/Λ`.
* Joint: Hölder at order 2 with the detector's plain witness `S_m` inside the moment
  (a two-plain product of lengths `n₀, m`, bounded by the same affine face),
    `joint = R/2 + (1 - δ m - 2 q zJ)/2`, `zJ = (B - n₀ - m)/Λ`.
* Plain witness line of the count on that face:
    `P(m) = 1 - 2 δ m - 2 δ p (B - 2m)/Λ`.
With `q = δ p` the two bounds differ by exactly `(R - P(m))/4`, so the joint bound can beat
Levy's only if the class count exceeds the plain line, which the count never does.
Status: proved. Use: closes the "joint numerator" route (no θ gain).
-/
import Mathlib

namespace JointNumerator

/-- Levy's class exponent. -/
noncomputable def levy (R δ p B Λ n₀ : ℝ) : ℝ :=
  3 / 4 * R + 1 / 4 - (δ * p) * ((B - 2 * n₀) / Λ) / 2

/-- The joint (order-2, plain-witness) class exponent. -/
noncomputable def joint (R δ p B Λ n₀ m : ℝ) : ℝ :=
  R / 2 + (1 - δ * m - 2 * (δ * p) * ((B - n₀ - m) / Λ)) / 2

/-- The plain witness line of the count on the affine face `(B, Λ)`. -/
noncomputable def plainLine (δ p B Λ m : ℝ) : ℝ :=
  1 - 2 * δ * m - 2 * δ * p * ((B - 2 * m) / Λ)

theorem levy_sub_joint (R δ p B Λ n₀ m : ℝ) :
    levy R δ p B Λ n₀ - joint R δ p B Λ n₀ m = (R - plainLine δ p B Λ m) / 4 := by
  unfold levy joint plainLine
  ring

/-- The joint bound is never better than Levy's when the class count is at most the plain line. -/
theorem levy_le_joint {R δ p B Λ n₀ m : ℝ} (h : R ≤ plainLine δ p B Λ m) :
    levy R δ p B Λ n₀ ≤ joint R δ p B Λ n₀ m := by
  have := levy_sub_joint R δ p B Λ n₀ m
  linarith

/-- They tie exactly at the crossing `R = P(m)`. -/
theorem levy_eq_joint {R δ p B Λ n₀ m : ℝ} (h : R = plainLine δ p B Λ m) :
    levy R δ p B Λ n₀ = joint R δ p B Λ n₀ m := by
  have h2 := levy_sub_joint R δ p B Λ n₀ m
  have h3 : R - plainLine δ p B Λ m = 0 := by rw [h]; ring
  rw [h3, zero_div] at h2
  linarith

end JointNumerator

/-
The λ test for the long Möbius moment (research/barriers/README.md, round 3).
Sixth-power amplification gives the exponent `(1 + 5t)/6` at length `D = U^t`. A direct estimate
`U + D (U/D)^λ` gives `(1 - λ) t + λ`. For `t > 1` the direct estimate wins iff `λ > 1/6`,
and a gain `g` needs `λ ≥ 1/6 + g/(t - 1)` (at `t = 1.155`, `g = 2.6e-4`: `λ ≥ 0.16834`).
Status: proved.
-/
namespace LambdaTest

theorem direct_sub_amplified (t lam : ℝ) :
    ((1 - lam) * t + lam) - (1 + 5 * t) / 6 = (t - 1) * (1 / 6 - lam) := by
  ring

theorem direct_lt_amplified_iff {t : ℝ} (ht : 1 < t) (lam : ℝ) :
    (1 - lam) * t + lam < (1 + 5 * t) / 6 ↔ 1 / 6 < lam := by
  have h := direct_sub_amplified t lam
  have ht' : 0 < t - 1 := by linarith
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    have : 0 ≤ (t - 1) * (1 / 6 - lam) := mul_nonneg ht'.le (by linarith)
    linarith
  · intro hgt
    have : (t - 1) * (1 / 6 - lam) < 0 := mul_neg_of_pos_of_neg ht' (by linarith)
    linarith

/-- A gain of at least `g` over amplification at length exponent `t > 1`. -/
theorem gain_iff {t : ℝ} (ht : 1 < t) (lam g : ℝ) :
    g ≤ (1 + 5 * t) / 6 - ((1 - lam) * t + lam) ↔ 1 / 6 + g / (t - 1) ≤ lam := by
  have ht' : 0 < t - 1 := by linarith
  have e : (1 + 5 * t) / 6 - ((1 - lam) * t + lam) = (lam - 1 / 6) * (t - 1) := by ring
  rw [e, ← le_sub_iff_add_le', div_le_iff₀ ht']

end LambdaTest
