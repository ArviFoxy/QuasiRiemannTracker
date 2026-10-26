/- Mixed source step, L3 (collisions): new in this submission; uses the baseline's natural rows
and Collet's `natural_row_supported_ideal` by import.

The collision twist in dictionary form. `twistChar τ A` (`CollTwist`) is characterized by its row
weights on supported ideals only. For the LOW supply the twisted parent must also satisfy the
dictionary identity of a column character at *all* ideals. `twistDict τ A` is the natural row of
`τ` at `A`, cut to the ideals coprime to `τ.modulus`; its coefficients are explicit:

* `twistDict_ideal_supported`: `idealCoeff (twistDict τ A) I = idealCoeff τ I · idealRowHom A I` on
  supported `I`, and `0` elsewhere (`twistDict_ideal_unsupported`);
* `twistDict_rowWeight`: the row weights of `twistChar` (so the energies agree,
  `child_energy_twistDict`);
* `twistDict_dict`: if `τ` equals a natural row `F` of `B` on the ideals coprime to `M`, then
  `twistDict τ A` equals any natural row of `B` at `A·w` there, with the same `M`. -/
import Submissions.arvi_mixed_step.Collision.CollTwist
import Submissions.hailey_collet_1252270103.Cycle61.Moment.PrimaryMaskTransport

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Collision
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentNaturalRowSource Cycle61Moment
local notation "O" => ActualEisensteinCubic.O

/-- The twist in dictionary form: the natural row of `τ` at `A`, cut to the support of `τ`. -/
def twistDict (τ : Character) (A : O) : Character :=
  if h : A ≠ 0 then excluded (naturalRow τ A h).character τ.modulus else τ

theorem twistDict_ideal_supported (τ : Character) (A : O) (hA : A ≠ 0) (I : Ideal O)
    (hI : Supported I) :
    idealCoeff (twistDict τ A) I = idealCoeff τ I * idealRowHom A I := by
  unfold twistDict
  simp only [ne_eq, hA, not_false_eq_true, ↓reduceDIte]
  rw [excluded_ideal _ _ τ.modulus_ne_bot,
    natural_row_supported_ideal τ A (naturalRow τ A hA) I hI]
  by_cases hc : IsCoprime I τ.modulus
  · simp only [hc, ite_true]
  · have h0 : idealCoeff τ I = 0 := by
      simpa only [hc, ite_false] using idealCoeff_source_mask τ I
    simp only [hc, ite_false, h0, zero_mul]

theorem twistDict_ideal_unsupported (τ : Character) (A : O) (hA : A ≠ 0) (I : Ideal O)
    (hI : ¬Supported I) : idealCoeff (twistDict τ A) I = 0 := by
  unfold twistDict
  simp only [ne_eq, hA, not_false_eq_true, ↓reduceDIte]
  rw [excluded_ideal _ _ τ.modulus_ne_bot,
    natural_row_ideal_zero_of_not_supported τ A (naturalRow τ A hA) I hI]
  exact ite_self _

/-- **Row weights of the dictionary twist** (the same as those of `twistChar`). -/
theorem twistDict_rowWeight (τ : Character) (A : O) (hA : A ≠ 0) (t : ℝ) (I : Ideal O)
    (hI : Supported I) :
    rowWeight (twistDict τ A) fixedBadMask 1 1 t I = rowWeight τ fixedBadMask 1 A t I := by
  rw [← heightCoeff_eq_fixed_rowWeight _ t I hI, rowWeight_twist_eq τ A t I,
    ← heightCoeff_eq_fixed_rowWeight _ t I hI]
  unfold heightCoeff
  rw [twistDict_ideal_supported τ A hA I hI]
  ring

theorem twistDict_rowWeight_eq (τ : Character) (A : O) (hA : A ≠ 0) (t : ℝ) (I : Ideal O)
    (hI : Supported I) :
    rowWeight (twistDict τ A) fixedBadMask 1 1 t I =
      rowWeight (twistChar τ A) fixedBadMask 1 1 t I := by
  rw [twistDict_rowWeight τ A hA t I hI, twistChar_rowWeight τ A hA t I hI]

/-- **The dictionary of the twist.** If `τ` is a natural row `F` of `B` on the ideals coprime to
`M` (and `0` elsewhere), then `twistDict τ A` is any natural row of `B` at `A·w` there. -/
theorem twistDict_dict {B : Character} {w : O} (τ : Character) (M : Ideal O)
    (F : NaturalRow B w)
    (hτ : ∀ I : Ideal O, idealCoeff τ I = if IsCoprime I M then idealCoeff F.character I else 0)
    (A : O) (hA : A ≠ 0) (F' : NaturalRow B (A * w)) (I : Ideal O) :
    idealCoeff (twistDict τ A) I = if IsCoprime I M then idealCoeff F'.character I else 0 := by
  by_cases hI : Supported I
  · rw [twistDict_ideal_supported τ A hA I hI, hτ I,
      natural_row_supported_ideal B (A * w) F' I hI]
    by_cases hc : IsCoprime I M
    · simp only [hc, ite_true]
      rw [natural_row_supported_ideal B w F I hI, idealRowHom_argument_mul]
      ring
    · simp only [hc, ite_false, zero_mul]
  · rw [twistDict_ideal_unsupported τ A hA I hI,
      natural_row_ideal_zero_of_not_supported B (A * w) F' I hI]
    simp only [ite_self]

/-- The modulus of the dictionary twist. -/
theorem twistDict_modulus (τ : Character) (A : O) (hA : A ≠ 0) :
    (twistDict τ A).modulus =
      (naturalRow τ A hA).character.modulus *
        ∏ P ∈ CompletedGauss.primeSupport τ.modulus, P := by
  unfold twistDict
  simp only [ne_eq, hA, not_false_eq_true, ↓reduceDIte]
  rfl

/-- **The two twists give the same child energy.** The corrected child energy reads the character
only through its row weights on supported ideals. -/
theorem child_energy_twistDict {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O → ℂ) (P : Finset (Ideal O))
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (τ : Character) (A : O) (hA : A ≠ 0) (ξ : RayCharacter) (t T H : ℝ) :
    QRH.Record1252270103Source.High.GlobalPhysical.correctedChildGaussEnergy s A₁ A₂ D K C R L F P B
        (childCharacter (twistChar τ A) ξ) t T H =
      QRH.Record1252270103Source.High.GlobalPhysical.correctedChildGaussEnergy s A₁ A₂ D K C R L F P B
        (childCharacter (twistDict τ A) ξ) t T H := by
  apply QRH.MixedStep.Residual.corrected_energy_congr
  intro I hI
  rw [QRH.MixedStep.Residual.rowWeight_child _ ξ t I hI,
    QRH.MixedStep.Residual.rowWeight_child _ ξ t I hI,
    twistChar_rowWeight τ A hA t I hI, twistDict_rowWeight τ A hA t I hI]

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.twistDict_rowWeight
#print axioms QRH.MixedStep.Collision.twistDict_dict
#print axioms QRH.MixedStep.Collision.twistDict_modulus
#print axioms QRH.MixedStep.Collision.child_energy_twistDict
