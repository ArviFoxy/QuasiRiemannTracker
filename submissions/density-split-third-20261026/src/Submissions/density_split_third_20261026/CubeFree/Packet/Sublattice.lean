/- Copyright (c) 2026 Sil. Apache-2.0.
Sublattice packing at the level of the OAI row encoding.

A column twist `idealRowHom V` times the row weight at row `z` is the row weight at
row `V*z`; consequently the positive slot row with frozen factor `A := V` at row `z`
is the plain (`A := 1`) positive slot row at row `V*z`.  The OAI induction energy taken
with `A := V` and keep `fun z => keep (V*z)` is the plain energy restricted to the
sublattice `V•O`, and since `‖Vz‖² = N(V)‖z‖²` its radial weight is the plain weight at
scale `N(V)·K`.  By positivity it is bounded by the plain energy at scale `N(V)·K`
(`packed_energy_le`).  The fixed-inducing classification only sees `A*z`
(`packed_keep_iff`). -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

set_option autoImplicit false

namespace QRH.DensitySplitThird.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators SchwartzMap

open OAI OAI.SevenEighths
open OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.CenteredMomentInductionEnergy
open OAI.SevenEighths.CenteredMomentRetainedEnergy
open OAI.SevenEighths.CenteredMomentHeckeHeight
open OAI.SevenEighths.CenteredMomentHeckeSlots
open OAI.SevenEighths.CenteredMomentHeckeExpansion
open OAI.SevenEighths.CenteredMomentPositiveSummability
open OAI.SevenEighths.CenteredExceptionalProfile

local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- Row packing for the row weight: the frozen factor `V` may be moved into the row. -/
theorem rowWeight_frozen_eq (η : Character) (m V z : O) (t : ℝ) :
    rowWeight η m V z t = rowWeight η m 1 (V*z) t := by
  ext I
  simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, one_mul]

/-- A numerator-form column twist `idealRowHom V` is absorbed into the row: row `z` becomes
row `V*z`. -/
theorem rowWeight_mul_twist (η : Character) (m A V z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I * CanonicalRowCompletion.idealRowHom V I =
      rowWeight η m A (V*z) t I := by
  have h := CanonicalRowCompletion.idealRowHom_argument_mul (m^6*(A*z)) V I
  rw [show m^6*(A*z)*V = m^6*(A*(V*z)) by ring] at h
  simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, h]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The positive slot row with frozen factor `V` at row `z` is the plain positive slot row
at row `V*z`. -/
theorem positiveSlotRow_frozen_eq (η : Character) (m V z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η m V z W₁ W₂ S β P t X₁ X₂ =
      positiveSlotRow η m 1 (V*z) W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow, rowTwistedSum, rowSlot, one_mul]

/-- The Eisenstein embedding is norm-multiplicative: `‖Vz‖² = N(V)·‖z‖²`. -/
theorem eisEmbedding_mul_norm_sq (V z : O) :
    ‖ConcreteTraceCRT.eisEmbedding (V*z)‖^2 =
      ((Ideal.span {V}).absNorm : ℝ) * ‖ConcreteTraceCRT.eisEmbedding z‖^2 := by
  rw [map_mul, norm_mul, mul_pow, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]

/-- The radial weight at row `z` and scale `K` is the radial weight at row `V*z` and scale
`N(V)·K`. -/
theorem radial_packed_scale (V : O) (hV : V ≠ 0) (K : ℝ) (z : O) :
    ‖ConcreteTraceCRT.eisEmbedding z‖^2/K =
      ‖ConcreteTraceCRT.eisEmbedding (V*z)‖^2/(((Ideal.span {V}).absNorm : ℝ)*K) := by
  have hN : ((Ideal.span {V}).absNorm : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV)
  rw [eisEmbedding_mul_norm_sq, mul_div_mul_left _ _ hN]

omit [DecidableEq ι] in
/-- **Sublattice packing of the OAI induction energy.**  The energy with frozen factor
`A := V` and keep `fun z => keep (V*z)` is the plain energy restricted to the sublattice
`V•O`; by positivity it is at most the plain energy at scale `N(V)·K`. -/
theorem packed_energy_le (η : Character) (m V : O) (hV : V ≠ 0) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ X₁ X₂ : ℝ) (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x, 0 ≤ (Φ x).re) (K : ℝ) (hK : 0 < K) :
    energy η m V t W₁ W₂ S β P X₁ X₂ (fun z => keep (V*z)) Φ K ≤
      energy η m 1 t W₁ W₂ S β P X₁ X₂ keep Φ (((Ideal.span {V}).absNorm : ℝ)*K) := by
  have hNpos : (0:ℝ) < (Ideal.span {V}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  have hK' : 0 < ((Ideal.span {V}).absNorm : ℝ)*K := mul_pos hNpos hK
  let g : O → ℝ := fun y => if keep y then
    ‖positiveSlotRow η m 1 y W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖ConcreteTraceCRT.eisEmbedding y‖^2/(((Ideal.span {V}).absNorm : ℝ)*K))).re else 0
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  obtain ⟨B, hB⟩ := product_bounded η m 1 t
    (Real.sqrt (X₁*X₂*∏ i, P i) : ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hg_sum : Summable g :=
    bounded_radial_summable (fun y => positiveSlotRow η m 1 y W₁ W₂ S β P t X₁ X₂) B
      (fun y => hB y) keep Φ _ hK'
  have hcomp : (fun z : O => if keep (V*z) then
      ‖positiveSlotRow η m V z W₁ W₂ S β P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) = g ∘ (fun z => V*z) := by
    funext z
    simp only [Function.comp_apply, g]
    rw [positiveSlotRow_frozen_eq, ← radial_packed_scale V hV K z]
  unfold energy
  rw [hcomp]
  have hinj : Function.Injective (fun z : O => V*z) := mul_right_injective₀ hV
  have hcs : Summable (g ∘ fun z : O => V*z) := hg_sum.comp_injective hinj
  exact Summable.tsum_le_tsum_of_inj (fun z : O => V*z) hinj (fun c _ => hg_nonneg c)
    (fun _ => le_rfl) hcs hg_sum

/-- **Keep classification under packing.**  `FixedInducingRow` depends only on `A*z`. -/
theorem packed_keep_iff (η : Character) (Q : Ideal O) (m V z : O) :
    FixedInducingRow η Q m V z ↔ FixedInducingRow η Q m 1 (V*z) := by
  simp only [FixedInducingRow, one_mul]

end

end QRH.DensitySplitThird.CubeFree.Packet
