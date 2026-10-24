import Mathlib

/-!
# Algebra behind three findings of 2026-10-24 (see `../LOG.md`, `../chain-ode/README.md`)

1. **The slot contour `z₀` cancels at the binding conductor edge.** Collet's final return
   (first-return.tex FR13) has `13h/75 − 9d/100`. These are `(z₀ − 1/6)h + (1/4 − z₀)d` at
   `z₀ = 17/50`, and their sum at `d = h` is `h/12` for every `z₀`.
2. **The unmarked count.** With the three unmarked witness lines `I(r) = 1 − νr`,
   `P(m) = 1 − 2νm`, `L(t) = 1/6 + (5/6 − ν)t`, the balance `r = ξ`, `m = ξ/2`, `t = r + m`,
   `1 − νξ = L(t)` gives `ξ = 10/(3(5 − 2ν))`, i.e. `ρ(ν) = 1 − 10ν/(15 − 6ν)` (Xu–Sang).
3. **The HIGH gate with a perfect marked gain.** If the gain equals its structural cap `νb`, the
   regular HIGH gate `1 − ρ(ν) − ν(t + b) + G ≥ 0` (amplifier term omitted, as at the crossing)
   becomes `t ≤ 10/(15 − 6ν)`. This is the late source chain's envelope boundary.

All three are exact identities. They locate the binding inputs and give no θ gain.
-/

namespace Lab.ReturnAlgebra

/-- FR13's conductor constants decode with the slot contour `z₀ = 17/50`. -/
theorem fr13_constants : (13 : ℚ)/75 = 17/50 - 1/6 ∧ (9 : ℚ)/100 = 17/50 - 1/4 := by
  constructor <;> norm_num

/-- The `z₀`-dependent part of the return exponent vanishes at `d = h`. -/
theorem z0_cancels (z₀ h : ℝ) : (z₀ - 1/6) * h + (1/4 - z₀) * h = h / 12 := by ring

/-- The unmarked count: the balanced solution of the three-line equation. -/
theorem unmarked_balance (ν : ℝ) (hν : ν < 5/2) :
    let ξ := 10 / (3 * (5 - 2 * ν))
    1 - ν * ξ = 1/6 + (5/6 - ν) * (ξ + ξ / 2) := by
  intro ξ
  have h5 : (5 - 2 * ν) ≠ 0 := by linarith
  have h : (3 * (5 - 2 * ν)) ≠ 0 := mul_ne_zero (by norm_num) h5
  have hξ : ξ * (3 * (5 - 2 * ν)) = 10 := by
    simp only [ξ]; exact div_mul_cancel₀ 10 h
  nlinarith [hξ]

/-- `ρ(ν) = 1 − νξ` equals the Xu–Sang exponent `1 − 10ν/(15 − 6ν)`. -/
theorem rho_formula (ν : ℝ) (hν : ν < 5/2) :
    1 - ν * (10 / (3 * (5 - 2 * ν))) = 1 - 10 * ν / (15 - 6 * ν) := by
  have h2 : (15 - 6 * ν) ≠ 0 := by linarith
  have e : (3 * (5 - 2 * ν)) = 15 - 6 * ν := by ring
  rw [e, mul_div_assoc']
  ring

/-- With the gain at its cap `G = νb`, the HIGH gate is the unmarked envelope bound. -/
theorem perfect_gain_gate (ν t b : ℝ) (hν0 : 0 < ν) (hν : ν < 5/2) :
    0 ≤ 1 - (1 - 10 * ν / (15 - 6 * ν)) - ν * (t + b) + ν * b ↔ t ≤ 10 / (15 - 6 * ν) := by
  have hd : 0 < 15 - 6 * ν := by linarith
  have key : 1 - (1 - 10 * ν / (15 - 6 * ν)) - ν * (t + b) + ν * b
      = ν * (10 / (15 - 6 * ν) - t) := by
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_nonneg_iff_of_pos_left hν0).mp h
    linarith
  · intro h
    exact mul_nonneg hν0.le (by linarith)

/-- At `ν = 1/2` the envelope bound is `t ≤ 5/6`: the late faces (plain length ≈ 0.834 at width
0.042) sit on it. -/
theorem boundary_half : (10 : ℚ) / (15 - 6 * (1/2)) = 5/6 := by norm_num

end Lab.ReturnAlgebra
