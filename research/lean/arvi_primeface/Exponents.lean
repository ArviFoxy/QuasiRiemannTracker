import Mathlib

/-!
# Exponent facts behind three research decisions (research file)

* **Label line** (journal "The label line υ = 1/2 is optimal at the binding"). With the Hölder (4/3, 4) price
  `E(υ) = (3/4)dR + d/4 + (1/2 − υ)₊ d + υ y`, the line `υ = 1/2` minimizes `E` iff `d ≥ y`
  (`label_line_optimal`). At the newTop binding (d, y, R, β) = (0.81, 0.47, 0.607, 0.8734), the pointwise
  bootstrap price `P(υ) = dR + (β − υ)d/2 + υ y` stays above Hölder's `E(1/2)` for every `υ ≥ 1 − β`
  (`label_pointwise_worse`).
* **Dunn–Radziwiłł thresholds** (journal "Sharper reading of D–R §9"). With `B = A^b`, the five error terms
  `B^{8/3}`, `(AB)^{7/12}B`, `B^{29/12}A^{−1/12}`, `A^{1/6}B^{5/3}` and the theta main term `A^{2/3}B^{4/3}` are below
  the diagonal `AB` iff `b ≤ 3/5`, `5/7`, `13/17`, `5/4`, `1` respectively; so the whole bound is diagonal exactly
  for `b ≤ 3/5`, i.e. slot cost `5/3` (`dr_diagonal_iff`).
* **K-wall corner** (journal "K-wall corner as a slot-cost statement"): `(1 − δ + γ) + δ X ≤ 1 ↔ γ ≤ δ(1 − X)`.
-/

namespace QRH.ArviPrimeFace

/-- The Hölder price of the label line. -/
noncomputable def labelPrice (d y R υ : ℝ) : ℝ := 3 / 4 * d * R + d / 4 + max 0 (1 / 2 - υ) * d + υ * y

theorem label_line_optimal {d y R : ℝ} (hy : 0 ≤ y) (hdy : y ≤ d) (υ : ℝ) :
    labelPrice d y R (1 / 2) ≤ labelPrice d y R υ := by
  unfold labelPrice
  rcases le_total υ (1 / 2) with h | h
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 / 2 - υ), max_eq_left (by norm_num : (1 / 2 : ℝ) - 1 / 2 ≤ 0)]
    nlinarith [mul_le_mul_of_nonneg_left hdy (by linarith : (0 : ℝ) ≤ 1 / 2 - υ)]
  · rw [max_eq_left (by linarith : (1 / 2 : ℝ) - υ ≤ 0), max_eq_left (by norm_num : (1 / 2 : ℝ) - 1 / 2 ≤ 0)]
    nlinarith [mul_le_mul_of_nonneg_right h hy]

theorem label_pointwise_worse (υ : ℝ) (h1 : 1 - 8734 / 10000 ≤ υ) :
    labelPrice (81 / 100) (47 / 100) (607 / 1000) (1 / 2) <
      81 / 100 * (607 / 1000) + (8734 / 10000 - υ) * (81 / 100) / 2 + υ * (47 / 100) := by
  unfold labelPrice
  rw [max_eq_left (by norm_num : (1 / 2 : ℝ) - 1 / 2 ≤ 0)]
  nlinarith

/-- D–R error terms against the diagonal `AB`, in log scale with `log_A B = b`. -/
theorem dr_diagonal_iff (b : ℝ) :
    (8 / 3 * b ≤ 1 + b ∧ 7 / 12 * (1 + b) + b ≤ 1 + b ∧ 29 / 12 * b - 1 / 12 ≤ 1 + b ∧
      1 / 6 + 5 / 3 * b ≤ 1 + b ∧ 2 / 3 + 4 / 3 * b ≤ 1 + b) ↔ b ≤ 3 / 5 := by
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem dr_slot_cost : (1 : ℝ) / (3 / 5) = 5 / 3 := by norm_num

theorem kwall_corner (δ γ X : ℝ) : (1 - δ + γ) + δ * X ≤ 1 ↔ γ ≤ δ * (1 - X) := by
  constructor <;> intro h <;> nlinarith

end QRH.ArviPrimeFace

#print axioms QRH.ArviPrimeFace.label_line_optimal
#print axioms QRH.ArviPrimeFace.dr_diagonal_iff
