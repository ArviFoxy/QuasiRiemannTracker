/- Copyright (c) 2026 Sil. Apache-2.0.
Row-level tools for the grouped side bound (Seam B, WP-H).

* `positiveSlotRow_rescale`: a positive slot row at ordinary lengths `X₁', X₂'` is the row at
  the dyadic lengths `Y₁, Y₂` with the prefix-dilated profiles `x ↦ W(e^{vᵢ} x)`,
  `vᵢ = log(Yᵢ/Xᵢ')`, times the central factor `√(Y₁Y₂/(X₁'X₂'))` (CF §5: "the per-leaf
  normalisation at its own length").
* `rowTwistedSum_eq_zero_of_small`: an ordinary sum with profile supported in `[a,b]` vanishes
  at a length `X < 1/b` (no nonzero ideal has norm below `1`).
* Finite row supports of ball-weighted lattice sums (`ball_lt_of_ne_zero`,
  `mem_rowNormBall_of_norm_sq_le`). -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.Label
import Submissions.sil_density_split_20261026.CubeFree.Packet.ProfileSeparation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

set_option autoImplicit false

namespace QRH.SilDensitySplit.CubeFree.Packet.Grouped
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_le_one
  ballProfile_one)

local notation "O" => ActualEisensteinCubic.O

/-! ### Dyadic rescaling of the ordinary lengths -/

theorem rowTwistedSum_rescale (η : Character) (m A z : O) (W : 𝓢(ℝ, ℂ)) (t X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y) :
    rowTwistedSum η m A z W t X =
      rowTwistedSum η m A z (ProfileSeparation.dilate W (Real.log (Y / X))) t Y := by
  unfold rowTwistedSum ProfileSeparation.dilate
  congr 1
  funext I
  rw [Real.exp_log (div_pos hY hX)]
  congr 2
  field_simp

theorem positiveSlotRow_rescale {ι : Type*} [Fintype ι] (η : Character) (m A z : O)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁)
    (hY₂ : 0 < Y₂) :
    positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ =
      (Real.sqrt (Y₁ * Y₂ / (X₁ * X₂)) : ℂ) *
        positiveSlotRow η m A z (ProfileSeparation.dilate W₁ (Real.log (Y₁ / X₁)))
          (ProfileSeparation.dilate W₂ (Real.log (Y₂ / X₂))) S β P t Y₁ Y₂ := by
  unfold positiveSlotRow
  rw [← rowTwistedSum_rescale η m A z W₁ t X₁ Y₁ hX₁ hY₁,
    ← rowTwistedSum_rescale η m A z W₂ t X₂ Y₂ hX₂ hY₂]
  have hρ : 0 < Real.sqrt (Y₁ * Y₂ / (X₁ * X₂)) :=
    Real.sqrt_pos.mpr (div_pos (mul_pos hY₁ hY₂) (mul_pos hX₁ hX₂))
  have hsplit : Real.sqrt (Y₁ * Y₂ * ∏ i, P i) =
      Real.sqrt (Y₁ * Y₂ / (X₁ * X₂)) * Real.sqrt (X₁ * X₂ * ∏ i, P i) := by
    rw [← Real.sqrt_mul (div_nonneg (mul_pos hY₁ hY₂).le (mul_pos hX₁ hX₂).le)]
    congr 1
    field_simp
  rw [hsplit, Complex.ofReal_mul, mul_inv]
  have hne : (Real.sqrt (Y₁ * Y₂ / (X₁ * X₂)) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  field_simp

theorem dilate_log_mem (Y X : ℝ) (hX : 0 < X) (h1 : Y / 2 ≤ X) (h2 : X ≤ Y) :
    Real.log (Y / X) ∈ Set.Icc 0 (Real.log 2) := by
  have hY : 0 < Y := hX.trans_le h2
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hX]; linarith
  · apply Real.log_le_log (div_pos hY hX)
    rw [div_le_iff₀ hX]; linarith

theorem rescale_factor_le (Y₁ Y₂ X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h₁ : Y₁ / 2 ≤ X₁) (h₂ : Y₂ / 2 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    Real.sqrt (Y₁ * Y₂ / (X₁ * X₂)) ^ 2 ≤ 4 := by
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg hY₁ hY₂) (mul_pos hX₁ hX₂).le),
    div_le_iff₀ (mul_pos hX₁ hX₂)]
  nlinarith

/-! ### Vanishing of an ordinary sum below the first ideal norm -/

theorem rowTwistedSum_eq_zero_of_small (η : Character) (m A z : O) (W : ℝ → ℂ) (a b : ℝ)
    (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b) (t X : ℝ) (hX : 0 < X)
    (hsmall : b * X < 1) : rowTwistedSum η m A z W t X = 0 := by
  unfold rowTwistedSum
  have hterm : ∀ I : Ideal O, W ((Ideal.absNorm I : ℝ) / X) = 0 := by
    intro I
    by_contra hW
    have hmem := hs hW
    rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_div] at hmem
      linarith [hmem.1]
    · have h1 : (1:ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hpos
      have hb := hmem.2
      rw [div_le_iff₀ hX] at hb
      linarith
  simp only [hterm, mul_zero, tsum_zero]

theorem positiveSlotRow_eq_zero_of_small_left {ι : Type*} [Fintype ι] (η : Character)
    (m A z : O) (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W₁ ⊆ Set.Icc a b)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ) (hX : 0 < X₁)
    (hsmall : b * X₁ < 1) : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ = 0 := by
  unfold positiveSlotRow
  rw [rowTwistedSum_eq_zero_of_small η m A z W₁ a b ha hs t X₁ hX hsmall]
  simp

theorem positiveSlotRow_eq_zero_of_small_right {ι : Type*} [Fintype ι] (η : Character)
    (m A z : O) (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W₂ ⊆ Set.Icc a b)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ) (hX : 0 < X₂)
    (hsmall : b * X₂ < 1) : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ = 0 := by
  unfold positiveSlotRow
  rw [rowTwistedSum_eq_zero_of_small η m A z W₂ a b ha hs t X₂ hX hsmall]
  simp

/-- An energy whose rows all vanish is zero. -/
theorem energy_eq_zero_of_row {ι : Type*} [Fintype ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ)
    (h : ∀ z, positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ = 0) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = 0 := by
  unfold energy
  simp [h]

/-! ### Finite row supports -/

theorem ball_lt_of_ne_zero (x K : ℝ) (hx : 0 ≤ x) (hK : 0 < K)
    (h : (ballProfile (x / K)).re ≠ 0) : x < 2 * K := by
  have hb : ballProfile (x / K) ≠ 0 := fun h0 => h (by rw [h0, Complex.zero_re])
  have := CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper (x / K)
    (div_nonneg hx hK.le) hb
  rw [div_lt_iff₀ hK] at this
  linarith

theorem mem_rowNormBall_of_norm_sq_le (R : ℝ) (y : O) (h : ‖eisEmbedding y‖ ^ 2 ≤ R) :
    y ∈ ShortDraftLatticeCount.rowNormBall ⌈R⌉₊ := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact_mod_cast h.trans (Nat.le_ceil R)

theorem ball_one_of_le (x K : ℝ) (hx : 0 ≤ x) (hK : 0 < K) (h : x ≤ K) :
    (ballProfile (x / K)).re = 1 := by
  rw [ballProfile_one (x / K) (div_nonneg hx hK.le) ((div_le_one hK).mpr h), Complex.one_re]

end
end QRH.SilDensitySplit.CubeFree.Packet.Grouped
