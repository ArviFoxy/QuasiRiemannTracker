/- Copyright (c) 2026 Sil. Apache-2.0.
Abstract weighted common-profile separation (common-profile lemma, Section 1).
Packets `B λ r` indexed by a genuine label fibre over each nonzero row `r` are
dominated by integrals of ONE label-independent coefficient family `A e v r`
against fixed majorants `M e v`. Weighted Cauchy, Tonelli and a bounded fibre
weight reduce the weighted packet sum to the source bound for `A`.
No bound for arbitrary label-dependent coefficient vectors is asserted. -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace QRH.SilDensitySplit.CommonProfile
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- Scalar Cauchy step: an AM–GM bound for every positive weight gives the
product bound. -/
theorem sq_le_of_forall_amgm {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t*a + b/t)/2) : X^2 ≤ a*b := by
  rcases hX.eq_or_lt with hX0 | hXpos
  · rw [← hX0]; nlinarith
  rcases ha.eq_or_lt with ha0 | hapos
  · -- a = 0 forces X = 0
    exfalso
    rcases hb.eq_or_lt with hb0 | hbpos
    · have := h 1 one_pos; rw [← ha0, ← hb0] at this; norm_num at this; linarith
    · have h1 := h (b/X) (div_pos hbpos hXpos)
      rw [← ha0] at h1
      have : b/(b/X) = X := by field_simp
      rw [this] at h1; linarith
  · have h1 := h (X/a) (div_pos hXpos hapos)
    have e1 : X/a*a = X := by field_simp
    have e2 : b/(X/a) = a*b/X := by field_simp
    rw [e1, e2] at h1
    have : X ≤ a*b/X := by linarith
    rw [le_div_iff₀ hXpos] at this
    nlinarith

variable {V : Type*} [MeasurableSpace V] (μ : Measure V)

/-- Weighted Cauchy over finitely many cells and an integral. -/
theorem cauchy_cells {E : Type*} (cells : Finset E) (M f : E → V → ℝ)
    (hM : ∀ e v, 0 ≤ M e v) (hf : ∀ e v, 0 ≤ f e v)
    (hM1 : ∀ e ∈ cells, Integrable (M e) μ)
    (hMf : ∀ e ∈ cells, Integrable (fun v => M e v * f e v) μ)
    (hMf2 : ∀ e ∈ cells, Integrable (fun v => M e v * f e v ^ 2) μ) :
    (∑ e ∈ cells, ∫ v, M e v * f e v ∂μ)^2 ≤
      (∑ e ∈ cells, ∫ v, M e v ∂μ) * ∑ e ∈ cells, ∫ v, M e v * f e v ^ 2 ∂μ := by
  apply sq_le_of_forall_amgm
  · exact Finset.sum_nonneg fun e _ => integral_nonneg fun v => mul_nonneg (hM e v) (hf e v)
  · exact Finset.sum_nonneg fun e _ => integral_nonneg fun v => hM e v
  · exact Finset.sum_nonneg fun e _ => integral_nonneg fun v =>
      mul_nonneg (hM e v) (pow_nonneg (hf e v) 2)
  intro t ht
  have hpt : ∀ e v, M e v * f e v ≤ (t*M e v + M e v * f e v ^ 2 / t)/2 := by
    intro e v
    have key : (t*M e v + M e v * f e v ^ 2 / t)/2 - M e v * f e v
        = M e v * (t - f e v)^2/(2*t) := by field_simp; ring
    have : 0 ≤ M e v * (t - f e v)^2/(2*t) :=
      div_nonneg (mul_nonneg (hM e v) (sq_nonneg _)) (by positivity)
    linarith
  have hint : ∀ e ∈ cells, ∫ v, M e v * f e v ∂μ ≤
      (t*∫ v, M e v ∂μ + (∫ v, M e v * f e v ^ 2 ∂μ)/t)/2 := by
    intro e he
    have hR : Integrable (fun v => (t*M e v + M e v * f e v ^ 2 / t)/2) μ :=
      (((hM1 e he).const_mul t).add ((hMf2 e he).div_const t)).div_const 2
    calc ∫ v, M e v * f e v ∂μ ≤ ∫ v, (t*M e v + M e v * f e v ^ 2 / t)/2 ∂μ :=
          integral_mono (hMf e he) hR (fun v => hpt e v)
      _ = (t*∫ v, M e v ∂μ + (∫ v, M e v * f e v ^ 2 ∂μ)/t)/2 := by
          rw [integral_div, integral_add ((hM1 e he).const_mul t) ((hMf2 e he).div_const t),
            integral_const_mul, integral_div]
  calc ∑ e ∈ cells, ∫ v, M e v * f e v ∂μ
      ≤ ∑ e ∈ cells, (t*∫ v, M e v ∂μ + (∫ v, M e v * f e v ^ 2 ∂μ)/t)/2 :=
        Finset.sum_le_sum hint
    _ = (t*∑ e ∈ cells, ∫ v, M e v ∂μ + (∑ e ∈ cells, ∫ v, M e v * f e v ^ 2 ∂μ)/t)/2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]

/-- The common-profile separation inequality.

* `rows`: the finitely many nonzero physical rows of a fixed envelope;
* `labels r`: the genuine packet labels with that row, with weights `w ≥ 0`
  whose fibre sum is at most `D`;
* `‖B λ r‖ ≤ Σₑ ∫ Mₑ(v) ‖Aₑ(v,r)‖`, where the coefficient family `A` does not
  depend on the label (scalar dependence on `r` is absorbed in the majorant step
  that produces this hypothesis);
* the source bound `Σ_r ‖Aₑ(v,r)‖² ≤ C ω(v) T` for each cell and parameter.

Then `Σ_r Σ_λ w ‖B‖² ≤ D·C·L₀·L_ω·T` with `L₀ = Σₑ∫Mₑ`, `L_ω = Σₑ∫Mₑω`. -/
theorem weighted_separation {E ρ Λ : Type*} (cells : Finset E) (rows : Finset ρ)
    (labels : ρ → Finset Λ) (w : Λ → ρ → ℝ) (B : Λ → ρ → ℂ)
    (M : E → V → ℝ) (A : E → V → ρ → ℂ) (ω : V → ℝ) (D C T : ℝ)
    (hw : ∀ l r, 0 ≤ w l r) (hD0 : 0 ≤ D) (hD : ∀ r ∈ rows, ∑ l ∈ labels r, w l r ≤ D)
    (hM : ∀ e v, 0 ≤ M e v) (hω : ∀ v, 0 ≤ ω v) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hM1 : ∀ e ∈ cells, Integrable (M e) μ)
    (hMω : ∀ e ∈ cells, Integrable (fun v => M e v * ω v) μ)
    (hMA : ∀ e ∈ cells, ∀ r ∈ rows, Integrable (fun v => M e v * ‖A e v r‖) μ)
    (hMA2 : ∀ e ∈ cells, ∀ r ∈ rows, Integrable (fun v => M e v * ‖A e v r‖ ^ 2) μ)
    (hrep : ∀ r ∈ rows, ∀ l ∈ labels r, ‖B l r‖ ≤ ∑ e ∈ cells, ∫ v, M e v * ‖A e v r‖ ∂μ)
    (hsource : ∀ e ∈ cells, ∀ v, ∑ r ∈ rows, ‖A e v r‖ ^ 2 ≤ C * ω v * T) :
    ∑ r ∈ rows, ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤
      D * C * (∑ e ∈ cells, ∫ v, M e v ∂μ) * (∑ e ∈ cells, ∫ v, M e v * ω v ∂μ) * T := by
  set L0 := ∑ e ∈ cells, ∫ v, M e v ∂μ with hL0
  have hL0nn : 0 ≤ L0 := Finset.sum_nonneg fun e _ => integral_nonneg fun v => hM e v
  set I2 : ρ → ℝ := fun r => ∑ e ∈ cells, ∫ v, M e v * ‖A e v r‖ ^ 2 ∂μ with hI2
  have hI2nn : ∀ r, 0 ≤ I2 r := fun r => Finset.sum_nonneg fun e _ =>
    integral_nonneg fun v => mul_nonneg (hM e v) (pow_nonneg (norm_nonneg _) 2)
  -- pointwise packet bound
  have hpacket : ∀ r ∈ rows, ∀ l ∈ labels r, ‖B l r‖ ^ 2 ≤ L0 * I2 r := by
    intro r hr l hl
    have hc := cauchy_cells μ cells M (fun e v => ‖A e v r‖) hM (fun e v => norm_nonneg _)
      hM1 (fun e he => hMA e he r hr) (fun e he => hMA2 e he r hr)
    have hB0 := hrep r hr l hl
    calc ‖B l r‖ ^ 2 ≤ (∑ e ∈ cells, ∫ v, M e v * ‖A e v r‖ ∂μ)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hB0 2
      _ ≤ L0 * I2 r := hc
  -- fibre weights
  have hrow : ∀ r ∈ rows, ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤ D * (L0 * I2 r) := by
    intro r hr
    calc ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤ ∑ l ∈ labels r, w l r * (L0 * I2 r) :=
          Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (hpacket r hr l hl) (hw l r)
      _ = (∑ l ∈ labels r, w l r) * (L0 * I2 r) :=
          (Finset.sum_mul (labels r) (fun l => w l r) (L0 * I2 r)).symm
      _ ≤ D * (L0 * I2 r) :=
          mul_le_mul_of_nonneg_right (hD r hr) (mul_nonneg hL0nn (hI2nn r))
  -- Tonelli and the source bound
  have hsum : ∑ r ∈ rows, I2 r ≤ C * T * ∑ e ∈ cells, ∫ v, M e v * ω v ∂μ := by
    have hswap : ∑ r ∈ rows, I2 r =
        ∑ e ∈ cells, ∫ v, M e v * ∑ r ∈ rows, ‖A e v r‖ ^ 2 ∂μ := by
      rw [hI2]; dsimp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [← integral_finsetSum _ (fun r hr => hMA2 e he r hr)]
      congr 1; ext v; rw [Finset.mul_sum]
    rw [hswap, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    have hInt : Integrable (fun v => M e v * ∑ r ∈ rows, ‖A e v r‖ ^ 2) μ := by
      have : (fun v => M e v * ∑ r ∈ rows, ‖A e v r‖ ^ 2) =
          fun v => ∑ r ∈ rows, M e v * ‖A e v r‖ ^ 2 := by ext v; rw [Finset.mul_sum]
      rw [this]; exact integrable_finsetSum _ fun r hr => hMA2 e he r hr
    calc ∫ v, M e v * ∑ r ∈ rows, ‖A e v r‖ ^ 2 ∂μ ≤ ∫ v, C * T * (M e v * ω v) ∂μ :=
          integral_mono hInt ((hMω e he).const_mul (C*T)) fun v => by
            have := mul_le_mul_of_nonneg_left (hsource e he v) (hM e v)
            nlinarith [hM e v]
      _ = C * T * ∫ v, M e v * ω v ∂μ := integral_const_mul _ _
  calc ∑ r ∈ rows, ∑ l ∈ labels r, w l r * ‖B l r‖ ^ 2 ≤ ∑ r ∈ rows, D * (L0 * I2 r) :=
        Finset.sum_le_sum hrow
    _ = D * L0 * ∑ r ∈ rows, I2 r := by rw [Finset.mul_sum]; ring_nf
    _ ≤ D * L0 * (C * T * ∑ e ∈ cells, ∫ v, M e v * ω v ∂μ) := by
        apply mul_le_mul_of_nonneg_left hsum
        exact mul_nonneg hD0 hL0nn
    _ = D * C * L0 * (∑ e ∈ cells, ∫ v, M e v * ω v ∂μ) * T := by ring

end
end QRH.SilDensitySplit.CommonProfile
