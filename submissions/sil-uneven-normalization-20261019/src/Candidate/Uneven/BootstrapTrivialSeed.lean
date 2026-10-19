/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.BootstrapNaturalBases
noncomputable section
open scoped Classical
open HeckeFamily HeckeFiniteDeletion HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- Inserting the fixed natural row at 1 repeats an idempotent Euler mask.
This lets an arbitrary fixed dictionary base enter the fixed-natural API. -/
theorem trivial_seed_element (η : Character) (u : O) (hu : u≠0) (n : O) :
    elementCoeff (naturalRow (naturalRow η 1 one_ne_zero).character u hu).character n =
      rowTwist (elementHom η) fixedBadMask 1 u n := by
  rw [(naturalRow _ u hu).element]
  by_cases hs : Supported (Ideal.span {n})
  · change elementCoeff (naturalRow η 1 one_ne_zero).character n *
      idealRowHom (fixedBadMask^6*1^4*u) (Ideal.span {n}) = _
    rw [(naturalRow η 1 one_ne_zero).element]
    change (elementCoeff η n * idealRowHom (fixedBadMask^6*1^4*1) (Ideal.span {n})) *
      idealRowHom (fixedBadMask^6*1^4*u) (Ideal.span {n}) =
        elementCoeff η n * idealRowHom (fixedBadMask^6*1^4*u) (Ideal.span {n})
    simp only [one_pow, mul_one, idealRowHom_argument_mul]
    rw [idealRowHom_sixth_mask fixedBadMask _ hs]
    split_ifs <;> simp
  · have hmLam : ConcretePrimeRowBridge.goodLambda ∣ fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O) ∣ fixedBadMask := dvd_mul_left _ _
    rw [rowTwist_zero_of_not_supported _ fixedBadMask 1 u n hmLam hm2 hs,
        rowTwist_zero_of_not_supported _ fixedBadMask 1 u n hmLam hm2 hs]

theorem trivial_seed_coefficients (η : Character) (u : O) (hu : u≠0) (I : Ideal O) :
    idealCoeff (naturalRow (naturalRow η 1 one_ne_zero).character u hu).character I =
      idealCoeff (naturalRow η u hu).character I := by
  rw [idealCoeff_eq_row η _ fixedBadMask 1 u (trivial_seed_element η u hu) I,
      (naturalRow η u hu).ideal]
  simp only [one_pow, mul_one]

theorem trivial_seed_excluded_one_coefficients (η : Character) (u : O) (hu : u≠0)
    (I : Ideal O) :
    idealCoeff (naturalRow (excluded (naturalRow η 1 one_ne_zero).character 1) u hu).character I =
      idealCoeff (naturalRow η u hu).character I := by
  have he := trivial_seed_coefficients η u hu I
  rw [(naturalRow _ u hu).ideal, excluded_ideal _ _ one_ne_zero, if_pos (isCoprime_one_right)]
  rw [(naturalRow _ u hu).ideal] at he
  exact he

theorem trivial_seed_masked_coefficients (η : Character) (u : O) (hu : u≠0)
    (R I : Ideal O) :
    idealCoeff (excluded
      (naturalRow (excluded (naturalRow η 1 one_ne_zero).character 1) u hu).character R) I =
      idealCoeff (excluded (naturalRow η u hu).character R) I := by
  have he := trivial_seed_excluded_one_coefficients η u hu I
  simp only [excluded, idealCoeff_excludePrimes] at he ⊢
  rw [he]

end
end OAI.SevenEighths.BootstrapNaturalBases
#print axioms OAI.SevenEighths.BootstrapNaturalBases.trivial_seed_coefficients
#print axioms OAI.SevenEighths.BootstrapNaturalBases.trivial_seed_excluded_one_coefficients
#print axioms OAI.SevenEighths.BootstrapNaturalBases.trivial_seed_masked_coefficients
