import Mathlib

/-!
# Lemma F (cap induction): the algebraic core

Collet's LOW amplifier (feedback.tex NF10–NF13, sources.tex G9–G13). A child face `(B, Λ)` is proved on
a width cell with upper endpoint `b` and mesh `e`; its line value there is `t = B - Λ (b - e)`. With LOW
parent `(B₀, Λ₀)` and density threshold `q`, the amplifier exponent, the amplified width and the
residual gain are

  `a = (q (b + (t - B₀)/Λ₀) + r) / (1 - 6 q B₀/Λ₀)`,  `F = 1 - 6 a`,
  `g = a - q (b + (t - B₀ F)/Λ₀)`,  `z₀ = (B₀ F - t)/Λ₀`.

Lemma F lets a node be its own LOW parent at a smaller cap `c`. This file proves the four identities
that the induction step uses:

* `self_excess`   : with `(B₀, Λ₀) = (B, Λ)` the crossing excess is exactly the mesh `e`;
* `amp_self`      : hence `a = a' := (q e + r)/(1 - 6 q B/Λ)`;
* `gain_self`     : and the residual gain is exactly `r`;
* `guard_iff`     : the weak guard `z₀ ≤ c F` is equivalent to `b - c ≤ 6 a (B/Λ - c) + e`.

The budget identity `B - B + (Λ - Λ) c = 0` is `budget_self`.
-/

namespace Lab.LemmaF

/-- The child's line value at the upper cell endpoint `b` (mesh `e`). -/
def lineAt (B Λ e b : ℝ) : ℝ := B - Λ * (b - e)

/-- The LOW amplifier exponent with LOW parent `(B₀, Λ₀)`. -/
noncomputable def amp (B₀ Λ₀ q r b t : ℝ) : ℝ :=
  (q * (b + (t - B₀) / Λ₀) + r) / (1 - 6 * q * B₀ / Λ₀)

/-- The residual gain left after paying the amplified width. -/
noncomputable def gain (B₀ Λ₀ q b t a : ℝ) : ℝ :=
  a - q * (b + (t - B₀ * (1 - 6 * a)) / Λ₀)

/-- The amplified LOW width. -/
noncomputable def lowWidth (B₀ Λ₀ t a : ℝ) : ℝ := (B₀ * (1 - 6 * a) - t) / Λ₀

theorem budget_self (B Λ c : ℝ) : B - B + (Λ - Λ) * c = 0 := by ring

theorem self_excess (B Λ e b : ℝ) (hΛ : Λ ≠ 0) :
    b + (lineAt B Λ e b - B) / Λ = e := by
  unfold lineAt; field_simp; ring

theorem amp_self (B Λ q r e b : ℝ) (hΛ : Λ ≠ 0) :
    amp B Λ q r b (lineAt B Λ e b) = (q * e + r) / (1 - 6 * q * B / Λ) := by
  unfold amp; rw [self_excess B Λ e b hΛ]

theorem gain_self (B Λ q r e b : ℝ) (hΛ : Λ ≠ 0) (hD : 1 - 6 * q * B / Λ ≠ 0) :
    gain B Λ q b (lineAt B Λ e b) (amp B Λ q r b (lineAt B Λ e b)) = r := by
  set a := amp B Λ q r b (lineAt B Λ e b) with ha_def
  have ha : a * (1 - 6 * q * B / Λ) = q * e + r := by
    rw [ha_def, amp_self B Λ q r e b hΛ]; exact div_mul_cancel₀ _ hD
  have hx : b + (lineAt B Λ e b - B * (1 - 6 * a)) / Λ = e + 6 * a * B / Λ := by
    unfold lineAt; field_simp; ring
  unfold gain; rw [hx]
  linear_combination ha

theorem guard_iff (B Λ e b c a : ℝ) (hΛ : 0 < Λ) :
    lowWidth B Λ (lineAt B Λ e b) a ≤ c * (1 - 6 * a) ↔
      b - c ≤ 6 * a * (B / Λ - c) + e := by
  unfold lowWidth lineAt
  have h1 : (B * (1 - 6 * a) - (B - Λ * (b - e))) / Λ = b - e - 6 * a * (B / Λ) := by
    field_simp; ring
  rw [h1]
  constructor <;> intro h <;> nlinarith

end Lab.LemmaF
