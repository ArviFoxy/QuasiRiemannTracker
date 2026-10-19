/- Independent coarse source and relative anchor. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedBootstrapNaturalBases
import Candidate.Cycle63.Marked.DeletionAnnular
import Candidate.Cycle63.Marked.WholeFamilyZeros

set_option autoImplicit false
namespace OAI.SevenEighths.MixedBootstrapNaturalBases
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState Cycle63Moment Cycle63MarkedPlain
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def wholeNaturalBatch {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀)
    (hu₀ : u₀≠0) (R₀ : Ideal O) (hR₀ : R₀≠0) (bad : WholeSourceIndex M H→Ideal O)
    (W : ℝ→ℂ) (lo hi U : ℝ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (rows : Finset FreeRow) (slots : Finset Slot) (w σ v : Slot→ℝ)
    (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (hw : ∀s∈slots,0<w s) (hσlo : ∀s∈slots,lo≤σ s) (hσhi : ∀s∈slots,σ s≤hi)
    (hrow : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U)
    (hnorm : ∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤U)
    (hkeep : ∀u∈rows,∀j,initialKeep (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val)
    (hlarge : ∀s∈slots,∀j,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (momentData (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j))).modulus.absNorm:ℝ)<U^(w s)) :
    Cycle63ActualWeighted.NaturalBatch (Slot:=Slot) M H hH (base M H hH ηcoarse η₀ u₀ hu₀ R₀)
      (wholeSourceAnchor M H hH η₀) bad W lo hi U where
  rows:=rows
  family:=fun u j=>(naturalRow (base M H hH ηcoarse η₀ u₀ hu₀ R₀ j) u.val u.property.1).character
  slots:=slots
  widths:=w
  sigma:=σ
  relativeHeight:=v
  commonHeight:=t
  Q:=fun u s=>naturalSlot
    (naturalRow (excluded (excluded F₀.character R₀) (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
      (primePool M H 2 (U^(w s)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))
  rays:=fun _=>θ
  inversePools:=fun s=>annularPool (primePool M H 2 (U^(w s))) (U^(w s))
  inverseBase:=excluded (excluded F₀.character R₀) (wholeAnchorMask M H hH η₀)
  inverseCoefficients:=fun s=>relativeCharacter M H hH η₀ (θ s)
  widthsPositive:=hw
  sigmaLower:=hσlo
  sigmaUpper:=hσhi
  rowNorm:=hrow
  embeddingNorm:=hnorm
  idealCoefficients:=by
    intro u hu j I
    exact natural_raw_coefficients _ (momentElement u) I
  elementCoefficients:=by
    intro u hu j n
    exact natural_initial_element _ u.val u.property.1 n
  retained:=hkeep
  inversePrime:=by
    intro s hs I hI
    exact (Finset.mem_filter.mp (annularPool_subset _ _ hI)).2.1
  inverseRatios:=fun s hs I hI=>annularPool_ratio _ _ _ hI
  inverseLarge:=hlarge
  inverseIdentity:=by
    intro u hu s hs
    exact (naturalSlot_annular_filter _ _ _ W hWs _ _ _).symm
  plainIdentity:=by
    intro u hu j s hs
    have he := whole_family_common_slot M H hH (excluded F₀.character R₀) η₀
      u.val u.property.1 j (θ s) (primePool M H 2 (U^(w s)))
      (fun I=>HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))
    have heq := Deletion26.naturalSlot_congr_ideal _ _
      (fun I=>natural_coefficients M H hH ηcoarse η₀ u₀ F₀ hu₀ R₀ hR₀ j u.val u.property.1 I)
      (primePool M H 2 (U^(w s)))
      (fun I=>idealCoeff (relativeCharacter M H hH (wholeSourceAnchor M H hH η₀ j) (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))
    exact he.symm.trans heq

end
end OAI.SevenEighths.MixedBootstrapNaturalBases
#print axioms OAI.SevenEighths.MixedBootstrapNaturalBases.wholeNaturalBatch
