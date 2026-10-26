/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.RetainedLowCofactorDictionary;
changes: type split (the first layer `s : Input ι` is typed apart from the second-layer datum type
`α`; proof verbatim). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowCofactorDictionary
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentNaturalRowSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion CenteredMomentCommonRadialData
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass Record12518109Raw
open FirstFamily
local notation "O"=>HeckeFamily.O
local notation "source"=>QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

variable {ι α Label : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype Label]
variable (reflected second : Bool) (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (source s modifier R seed K Z ξ hK bin))
    (datum : Label→SecondInputDatum α) (first : Label→FirstSourceLabel)
    (row : secondLiveRows (fun l=>(datum l).block))
    (hfirst : first row.val.1=firstLabel s modifier R seed K Z ξ hK bin column)
local notation "key"=>rawKey reflected s modifier R seed K Z ξ hK bin column datum first row hfirst second
local notation "dd"=>datum row.val.1

lemma actual_key_support_mx :
    (Supported (key).val.1.1.1 ∧ (key).val.1.1.2≠0 ∧ Supported (key).val.2.1.1 ∧ (key).val.2.1.2≠0) ∧
    (CompletedGauss.primeSupport (key).val.1.1.1=CompletedGauss.primeSupport (key).val.1.1.2 ∧
      CompletedGauss.primeSupport (key).val.2.1.1=CompletedGauss.primeSupport (key).val.2.1.2) := by
  have hk : (key).val.1=firstLabel s modifier R seed K Z ξ hK bin column := by
    cases second <;> exact hfirst
  have hs:=FirstFamily.label_supported s modifier R seed K Z ξ hK bin column
  have hp : (key).val.2.1=((dd).C,(dd).D) := by cases second <;> rfl
  rw [hk,hp]
  exact ⟨⟨hs.1,hs.2.1.1,(dd).hC,(dd).hD.1⟩,hs.2.2,(dd).sameSupport⟩

end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.actual_key_support_mx
