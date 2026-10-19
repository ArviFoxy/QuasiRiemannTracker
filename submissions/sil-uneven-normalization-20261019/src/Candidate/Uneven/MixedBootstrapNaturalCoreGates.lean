/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedBootstrapNaturalBatch
import Candidate.Cycle63.Marked.DeletionFiniteExceptions
import Candidate.Cycle63.Marked.NaturalSlotPhase

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.MixedBootstrapNaturalBases
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open Cycle63Moment Cycle63MarkedPlain CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The exceptional free cores are one fixed finite set, chosen before
the scale, every root ideal, and every moving amplitude or zero label. -/
theorem whole_core_exception_set (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (bad : WholeSourceIndex M H→Ideal O)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E ↔ ∀j,initialKeep (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val :=
  Deletion26.fixed_initial_exception_union (base M H hH ηcoarse η₀ u₀ hu₀ R₀)
    (fun j=>internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) hbad0 hbadTop hbad72

/-- A fixed positive padding absorbs all natural conductor constants.
The original row norm alone supplies the embedding and clean modulus caps. -/
theorem eventually_whole_core_norm_caps (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (pad : ℝ) (hpad : 0< pad) :
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀(Y : ℝ)(u : FreeRow),rowNorm u≤ Y →
      ((Ideal.span {u.val}).absNorm:ℝ)≤ Y*U^pad ∧
      ‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤ Y*U^pad ∧
      ∀j,(naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u.val u.property.1).character.modulus.absNorm≤ Y*U^pad := by
  let D := FixedUnmarkedDictionary.ofBases (base M H hH ηcoarse η₀ u₀ hu₀ R₀)
  obtain ⟨K,hK,hmod⟩ := D.natural_conductor_bound
  have hlarge : ∀ᶠU : ℝ in atTop,K≤ U^pad :=
    (tendsto_rpow_atTop hpad).eventually (eventually_ge_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hKU hU
  refine ⟨hU,?_⟩
  intro Y u hu
  have hY : 0≤ Y := (zero_le_one.trans (rowNorm_ge_one u)).trans hu
  have hnorm : rowNorm u≤ Y*U^pad :=
    hu.trans (le_mul_of_one_le_right hY (hK.trans hKU))
  refine ⟨hnorm,?_,?_⟩
  · simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,rowNorm] using hnorm
  · intro j
    apply (hmod u j).trans
    calc
      K*rowNorm u ≤ K*Y := mul_le_mul_of_nonneg_left hu (zero_le_one.trans hK)
      _ ≤ _ := by nlinarith

/-- A positive lower physical width eventually puts every slot beyond
all fixed deleted detector conductors, uniformly over the whole dictionary. -/
theorem eventually_whole_core_inverse_large (ηcoarse η₀ : Character) (u₀ : O) (hu₀ : u₀≠0) (R₀ : Ideal O) (wmin : ℝ) (hwmin : 0< wmin) :
    ∀ᶠU : ℝ in atTop,1< U ∧ ∀w : ℝ,wmin≤ w → ∀j : WholeSourceIndex M H,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase
        (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)< U^w := by
  let K : ℝ := ∑j : WholeSourceIndex M H,
    ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)
  have hlarge : ∀ᶠU : ℝ in atTop,K< U^wmin :=
    (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro w hw j
  have hj : ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)≤ K :=
    by
      dsimp only [K]
      exact Finset.single_le_sum (f := fun j : WholeSourceIndex M H=>
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ))
        (fun _ _=>by positivity) (Finset.mem_univ j)
  exact (hj.trans_lt hlarge).trans_le (Real.rpow_le_rpow_of_exponent_le hU.le hw)


end
end OAI.SevenEighths.MixedBootstrapNaturalBases
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.whole_core_exception_set
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.eventually_whole_core_norm_caps
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.eventually_whole_core_inverse_large
