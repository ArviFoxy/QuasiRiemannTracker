/-
The binding balance of the return (research/return-slack/README.md, "Origin of every term").
* Geometry: the marked energy is tight, `x + y + ℓ = 1`, and the conductor edge is `h = 1 + ℓ - x`.
  Then `y = h - 2ℓ`, and the low side `θ = 2/3 + (x + y)/4` equals `11/12 - ℓ/4`.
* At `d = h`, Collet's return exponent (return.tex NR6)
    `E = 1/2 + 13h/75 - y/2 - ℓ/2 - 9h/100 + δ/2 + δp(ℓ - C/2) + (3h/4)R`
  satisfies `E ≤ θ` iff `3ℓ/4 + δ/2 + δp(ℓ - C/2) + (3h/4)R ≤ 5/12 + 5h/12`.
* With the physical capacity `C = (B h - 4ℓ)/Λ`, the left side has `ℓ`-coefficient
  `3/4 + δp + 2δp/Λ`.
Status: proved. Use: bookkeeping of the probe endpoint (no slack; every term is an atom or a
normalization).
-/
import Mathlib

namespace BalanceAlgebra

theorem y_eq {x y ℓ h : ℝ} (hme : x + y + ℓ = 1) (hedge : h = 1 + ℓ - x) : y = h - 2 * ℓ := by
  linarith

theorem theta_low {x y ℓ h : ℝ} (hme : x + y + ℓ = 1) (_hedge : h = 1 + ℓ - x) :
    2 / 3 + (x + y) / 4 = 11 / 12 - ℓ / 4 := by
  linarith

/-- Collet's return exponent at the conductor edge `d = h`. -/
noncomputable def E (h y ℓ δ p C R : ℝ) : ℝ :=
  1 / 2 + 13 * h / 75 - y / 2 - ℓ / 2 - 9 * h / 100 + δ / 2 + δ * p * (ℓ - C / 2) + 3 * h / 4 * R

theorem balance_iff {h ℓ δ p C R : ℝ} :
    E h (h - 2 * ℓ) ℓ δ p C R ≤ 11 / 12 - ℓ / 4 ↔
      3 * ℓ / 4 + δ / 2 + δ * p * (ℓ - C / 2) + 3 * h / 4 * R ≤ 5 / 12 + 5 * h / 12 := by
  unfold E
  constructor <;> intro hle <;> linarith

/-- The left side of the balance, with the physical capacity `C = (B h - 4ℓ)/Λ`. -/
noncomputable def lhs (h ℓ δ p B Λ R : ℝ) : ℝ :=
  3 * ℓ / 4 + δ / 2 + δ * p * (ℓ - ((B * h - 4 * ℓ) / Λ) / 2) + 3 * h / 4 * R

/-- The balance is affine in `ℓ` with slope `3/4 + δp + 2δp/Λ`. -/
theorem lhs_affine_in_ell (h ℓ δ p B Λ R : ℝ) (hΛ : Λ ≠ 0) :
    lhs h ℓ δ p B Λ R =
      (3 / 4 + δ * p + 2 * δ * p / Λ) * ℓ + (δ / 2 - δ * p * B * h / (2 * Λ) + 3 * h / 4 * R) := by
  unfold lhs
  field_simp
  ring

end BalanceAlgebra
