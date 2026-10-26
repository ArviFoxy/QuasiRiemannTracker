/- Mixed source step, L3 (collisions): new in this submission; uses the baseline's
`exists_second_family` by import.

Absorbing the collision twist into the Hecke character (step 3). For `A ≠ 0`,
`twistChar τ A` is a character whose row weight on supported ideals is
`rowWeight τ · idealRowHom A`, with conductor at most
`rowConductorBound (childCharacter τ 1) fixedBadMask 1 A`
`= N(τ.modulus ⊓ 12)·N(fixedBadMask)·N(72)·N(A)`. For the collision twist `A = δ³`
the conductor grows by `N(D)³` (times absolute constants). -/
import Submissions.arvi_mixed_step.Collision.CollRow
import Submissions.arvi_mixed_step.Residual.RayShift

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Collision
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentChildRows
local notation "O" => ActualEisensteinCubic.O

/-- The character with the row twist `A` absorbed. -/
def twistChar (τ : Character) (A : O) : Character :=
  if h : A ≠ 0 then Classical.choose (exists_second_family τ 1 A h) else τ

theorem rayCharacter_one_supported (a : O) (ha : Supported (Ideal.span {a})) :
    rayCharacter (1 : RayCharacter) a = 1 := by
  unfold rayCharacter
  exact MulChar.one_apply (CenteredMomentCommonSupport.isUnit_residue_of_coprime 4 a
    (CenteredMomentFixedRay.supported_coprime_four a ha))

theorem rowWeight_twist_eq (τ : Character) (A : O) (t : ℝ) (I : Ideal O) :
    rowWeight τ fixedBadMask 1 A t I = rowWeight τ fixedBadMask 1 1 t I * idealRowHom A I := by
  simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_one, one_mul,
    idealRowHom_argument_mul]
  ring

/-- **Row weights of the twisted character.** -/
theorem twistChar_rowWeight (τ : Character) (A : O) (hA : A ≠ 0) (t : ℝ) (I : Ideal O)
    (hI : Supported I) :
    rowWeight (twistChar τ A) fixedBadMask 1 1 t I = rowWeight τ fixedBadMask 1 A t I := by
  have hspec := (Classical.choose_spec (exists_second_family τ 1 A hA)).2 I hI t
  have hdef : twistChar τ A = Classical.choose (exists_second_family τ 1 A hA) := by
    unfold twistChar
    simp only [hA, ne_eq, not_false_eq_true, ↓reduceDIte]
  rw [hdef, ← heightCoeff_eq_fixed_rowWeight _ t I hI, hspec,
    heightCoeff_eq_fixed_rowWeight _ t I hI,
    rayCharacter_one_supported _ (MixedSelectedCommon_primary I hI), mul_one,
    rowWeight_twist_eq τ A t I]
where
  MixedSelectedCommon_primary (I : Ideal O) (hI : Supported I) :
      Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
    Candidate.FourthPower.MixedSelectedCommon.primary_supported I hI

/-- **Conductor of the twisted character.** -/
theorem twistChar_modulus (τ : Character) (A : O) (hA : A ≠ 0) :
    (twistChar τ A).modulus.absNorm ≤
      HeckeRowClosure.rowConductorBound (childCharacter τ 1) fixedBadMask 1 A := by
  have hdef : twistChar τ A = Classical.choose (exists_second_family τ 1 A hA) := by
    unfold twistChar
    simp only [hA, ne_eq, not_false_eq_true, ↓reduceDIte]
  rw [hdef]
  exact (Classical.choose_spec (exists_second_family τ 1 A hA)).1

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.twistChar_rowWeight
#print axioms QRH.MixedStep.Collision.twistChar_modulus
