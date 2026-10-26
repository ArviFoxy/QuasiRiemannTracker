/- Mixed source step, L3 (collisions): adapted from Collet's `Cycle61Moment` dictionary theorems
(`actual_second_natural_mask`, `actual_second_punctured_natural_mask`,
`actual_retained_fixed_dictionary_mask`, `actual_joint_retained_dictionary_mask`,
`actual_joint_extra_mask`) and `Cycle61InitialMass.actual_second_{reflected_}input_dictionary_mask`;
changes: the Euler mask of the parent dictionary is an arbitrary nonzero ideal `M` instead of
`χ₁.modulus`.

The hypothesis `hfirst` says `χ₁` equals the first natural row on the ideals coprime to `M` and is
`0` elsewhere. For a column character `M` is its modulus; for the collision twist `M` is still the
*plain* column modulus, because the fixed natural row at `u₀ = δ³` already vanishes on ideals that
share a prime with `δ`. The conclusions then keep the plain mask `M·P` (the modulus of the twisted
character, whose primes are not controlled, never enters). All proofs are Collet's, with
`χ₁.modulus` replaced by `M`. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondDictionary
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Collision
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion Cycle61Moment Cycle61InitialMass
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum
open CenteredMomentHeckeColumnWindow CenteredMomentSecondChildProfile
open CenteredMomentFirstCanonicalFamily Record12518109Raw ActualEisensteinCubic
local notation "O" => HeckeFamily.O

theorem actual_second_natural_mask_flex (η χ : Character) (M : Ideal O) (hM : M ≠ 0) (w A : O)
    (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I M then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A)) (I : Ideal O) :
    idealCoeff child.character I = idealCoeff (excluded final.character M) I := by
  by_cases hs : Supported I
  · rw [natural_row_supported_ideal _ _ child I hs,
      childCharacter, idealCoeff_product, hmask I,
      natural_row_supported_ideal _ _ F I hs,
      excluded_ideal _ _ hM,
      natural_row_supported_ideal _ _ final I hs,
      childCharacter, idealCoeff_product, idealRowHom_argument_mul]
    by_cases hc : IsCoprime I M <;> simp only [hc, ite_true, ite_false] <;> ring
  · rw [natural_row_ideal_zero_of_not_supported _ _ child I hs,
      excluded_ideal _ _ hM,
      natural_row_ideal_zero_of_not_supported _ _ final I hs]
    split_ifs <;> rfl

theorem actual_second_punctured_natural_mask_flex (η χ : Character) (M : Ideal O) (hM : M ≠ 0)
    (w A : O) (F : NaturalRow η w)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I M then idealCoeff F.character I else 0)
    (ξ : RayCharacter) (child : NaturalRow (childCharacter χ ξ) A)
    (final : NaturalRow (childCharacter η ξ) (w*A))
    (R : Ideal O) (hR : R ≠ 0) (I : Ideal O) :
    idealCoeff (excluded child.character R) I =
      idealCoeff (excluded final.character (M*R)) I := by
  rw [excluded_ideal _ _ hR, actual_second_natural_mask_flex η χ M hM w A F hmask ξ child final I,
    excluded_ideal _ _ hM,
    excluded_ideal _ _ (mul_ne_zero hM hR), IsCoprime.mul_right_iff]
  by_cases hc : IsCoprime I M <;> by_cases hr : IsCoprime I R <;>
    simp only [hc, hr, and_self, true_and, false_and, ite_true, ite_false]

theorem actual_retained_fixed_dictionary_mask_flex (η χ₁ : Character) (M : Ideal O) (hM : M ≠ 0)
    (w : O) (first : NaturalRow η w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I M then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ₁ C D hC hD U τ)
    (ξ : RayCharacter) (z : O) (F : NaturalRow (τ ξ) z)
    (second : NaturalRow (childCharacter χ₁ ξ)
      ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))
    (fixed : NaturalRow (childCharacter η ξ)
      (w * ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z)))
    (P : Ideal O) (hP : P ≠ 0) (hCP : C ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded fixed.character (M * P)) I := by
  rw [actual_retained_reduced_mask χ₁ C D hC hD hCD U τ hf ξ z F second P hP hCP I]
  exact actual_second_punctured_natural_mask_flex η χ₁ M hM w _ first hfirst ξ second fixed P hP I

theorem actual_joint_retained_dictionary_mask_flex (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel → O) (l : NonzeroJointSourceLabel left u₀ unit)
    (η χ₁ : Character) (M : Ideal O) (hM : M ≠ 0)
    (first : NaturalRow η (jointFirstFrequency left u₀ unit l.val))
    (hfirst : ∀ I : Ideal O, idealCoeff χ₁ I =
      if IsCoprime I M then idealCoeff first.character I else 0)
    (hC : Supported l.val.2.1.1) (hD : Supported l.val.2.1.2)
    (hCD : primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2)
    (τ : RayCharacter → Character)
    (hf : Family χ₁ l.val.2.1.1 l.val.2.1.2 hC hD l.val.2.2.val.1 τ)
    (ξ : RayCharacter) (F : NaturalRow (τ ξ) l.val.2.2.val.2)
    (P : Ideal O) (hP : P ≠ 0) (hCP : l.val.2.1.1 ∣ P) (I : Ideal O) :
    idealCoeff (excluded F.character P) I =
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
        (M * P)) I := by
  let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2 *
    nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1) * l.val.2.2.val.2
  have he : jointFirstFrequency left u₀ unit l.val * A = (nonzeroJointSourceRow l).val :=
    (joint_source_row_factorization left u₀ unit l.val).symm
  have hprod : jointFirstFrequency left u₀ unit l.val * A ≠ 0 := by
    rw [he]
    exact l.property
  let second := naturalRow (childCharacter χ₁ ξ) A (mul_ne_zero_iff.mp hprod).2
  let fixed := naturalRow (childCharacter η ξ)
    (jointFirstFrequency left u₀ unit l.val * A) hprod
  have h := actual_retained_fixed_dictionary_mask_flex η χ₁ M hM _ first hfirst
    _ _ hC hD hCD _ τ hf ξ _ F second fixed P hP hCP I
  apply h.trans
  rw [excluded_ideal _ _ (mul_ne_zero hM hP),
    excluded_ideal _ _ (mul_ne_zero hM hP)]
  split_ifs
  · rw [fixed.ideal, NaturalRow.ideal, he]
  · rfl

/-- The structured mask form (Collet's `actual_joint_extra_mask`). -/
theorem actual_joint_extra_mask_flex
    (left second : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit)
    (η χ₁ : Character) (M : Ideal O) (hM : M ≠ 0)
    (first : NaturalRow η (jointFirstFrequency left u₀ unit l.val))
    (hfirst : ∀I : Ideal O,idealCoeff χ₁ I=
      if IsCoprime I M then idealCoeff first.character I else 0)
    (hC₁ : Supported l.val.1.1.1) (hD₁ : Supported l.val.1.1.2)
    (hs₁ : CompletedGauss.primeSupport l.val.1.1.1=CompletedGauss.primeSupport l.val.1.1.2)
    (hC₂ : Supported l.val.2.1.1) (hD₂ : Supported l.val.2.1.2)
    (hs₂ : CompletedGauss.primeSupport l.val.2.1.1=CompletedGauss.primeSupport l.val.2.1.2)
    (τ : RayCharacter→Character)
    (hf : Family χ₁ l.val.2.1.1 l.val.2.1.2 hC₂ hD₂ l.val.2.2.val.1 τ)
    (ξ : RayCharacter) (F : NaturalRow (τ ξ) l.val.2.2.val.2)
    (P R : Ideal O) (hP : P≠0) (hR : R≠0) (hCP : l.val.2.1.1∣P)
    (hmask : M*P=R*(Ideal.span {
      primeSubsetGenerator (fun p : CommonIndex l.val.1.1.1 l.val.1.1.2=>p.val) l.val.1.2.val*
        activeConductor l.val.1.1.1 l.val.1.1.2}*
      ((if left then l.val.1.1.1 else l.val.1.1.2)*
        (if second then l.val.2.1.2 else l.val.2.1.1)))) (I : Ideal O) :
    idealCoeff (excluded F.character P) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
        (R*firstSourceMissing left l.val.1)) I := by
  rw [actual_joint_retained_dictionary_mask_flex left u₀ unit l η χ₁ M hM first hfirst
    hC₂ hD₂ hs₂ τ hf ξ F P hP hCP I,hmask]
  exact actual_joint_common_mask left second u₀ unit l hC₁ hD₁ hs₁ hC₂ hD₂ hs₂
    (childCharacter η ξ) (naturalRow _ _ (nonzeroJointSourceRow l).property) R hR I

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem actual_second_input_dictionary_mask_flex
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character) (M : Ideal O) (hM : M ≠ 0)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I M then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) r.val.2.2.2.val)
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).C)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          (M*((d r.val.1).R*(d r.val.1).C))) I := by
  exact actual_joint_retained_dictionary_mask_flex left u₀ unit
    (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    η (d r.val.1).input.η M hM F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I

theorem actual_second_reflected_input_dictionary_mask_flex
    (d : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)≠0)
    (η : Character) (M : Ideal O) (hM : M ≠ 0)
    (F₁ : NaturalRow η (jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first r)))
    (hfirst : ∀I : Ideal O,idealCoeff (d r.val.1).input.η I=
      if IsCoprime I M then idealCoeff F₁.character I else 0)
    (ξ : RayCharacter) (F₂ : NaturalRow ((d r.val.1).τ ξ) (-r.val.2.2.2.val))
    (hR : (d r.val.1).R≠0) (I : Ideal O) :
    let l := reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf)
    idealCoeff (excluded F₂.character ((d r.val.1).R*(d r.val.1).D)) I=
      idealCoeff (excluded (naturalRow (childCharacter η ξ)
        (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
          (M*((d r.val.1).R*(d r.val.1).D))) I := by
  have he := actual_joint_retained_dictionary_mask_flex left u₀ unit
    (reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun l=>(d l).block) first r left u₀ unit hf))
    η (d r.val.1).input.η M hM F₁ hfirst (d r.val.1).hC (d r.val.1).hD
    (d r.val.1).sameSupport (d r.val.1).τ (d r.val.1).family ξ F₂ _
    (mul_ne_zero hR (d r.val.1).hC.1) (dvd_mul_left _ _) I
  apply (excluded_common_pair_ideal F₂.character (d r.val.1).R (d r.val.1).C
    (d r.val.1).D hR (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I).symm.trans
  apply he.trans
  simpa only [mul_assoc] using excluded_common_pair_ideal _
    (M*(d r.val.1).R) (d r.val.1).C (d r.val.1).D
    (mul_ne_zero hM hR)
    (d r.val.1).hC.1 (d r.val.1).hD.1 (d r.val.1).sameSupport I

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.actual_joint_retained_dictionary_mask_flex
#print axioms QRH.MixedStep.Collision.actual_joint_extra_mask_flex
#print axioms QRH.MixedStep.Collision.actual_second_input_dictionary_mask_flex
#print axioms QRH.MixedStep.Collision.actual_second_reflected_input_dictionary_mask_flex
