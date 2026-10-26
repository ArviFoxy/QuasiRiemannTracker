/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F1, two-parent twin): fork of
Record1252270103Source.Admission.SelectedHighCoordinatesScalar (Hailey Collet).

`eventual_modified_high_coefficient` uses its first column only through the support facts of its
label (`FirstFamily.label_supported`). With two parents the label comes from the first layer `s₀`
and the first allocation from the second-layer parent `s`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCoordinatesScalar
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCoordinates
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentFirstAmplificationChoice Cycle61Moment Cycle61InitialMass
open Record1252270103Second OAI.SevenEighths.Record1252270103Source
local notation "O"=>HeckeFamily.O
local instance selectedHighCoordinatesDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem eventual_modified_high_coefficient_mx (N:ℕ) (lo errv:ℝ) (hlo:0<lo) (he:0<errv) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι₀ ι:Type} [Fintype ι₀] [Fintype ι] (s₀:Input ι₀) (s:Input ι),
    Fintype.card ι≤N→lo≤s.lower→∀(modifier₀:Tuple ι₀→ℂ) (R seed:Ideal O) (K ξ:ℝ) (hK:0<K)
      (bin:ℤ×(Fin 5→ℤ))
      (j:FirstColumnIndex (High.CoupledFirst.geometryFirstSource s₀ modifier₀ R seed K Z ξ hK bin))
      (reflected left second:Bool),
    let l:=FirstFamily.firstLabel s₀ modifier₀ R seed K Z ξ hK bin j
    ∀(B₁:actualAllocations s.pools (if reflected then l.1.2 else l.1.1)) (τ₁:Character) (t₁:ℝ),
    frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0→
    ∀M a reserve ε:ℝ,SecondAllocationBound s reflected left second l R B₁ τ₁ t₁ Z M a ξ reserve ε errv := by
  filter_upwards [eventual_selected_high_coefficient N lo errv hlo he] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι₀ ι _ _ s₀ s hN hloS modifier₀ R seed K ξ hK bin j reflected left second l B₁ τ₁ t₁ hB₁ M a reserve ε
  have hl:=FirstFamily.label_supported s₀ modifier₀ R seed K Z ξ hK bin j
  exact hz.2 s hN hloS reflected left second l hl.1 hl.2.1 hl.2.2 R B₁ τ₁ t₁ hB₁ M a ξ reserve ε

end
end QRH.Record1252270103Source.Admission.SelectedHighCoordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCoordinates.eventual_modified_high_coefficient_mx
