/- Mixed step (L4/L5, F1): fork of Record1252270103Source.High.GlobalPhysicalSelectedMass
(Hailey Collet, Apache-2.0; inherited notices retained).

`actual_selected_paid_weight` with two parents: the balanced first mass (scalar at the original
volume `A₀ = logb Z (volume s₀)`, first common ideal) is read from the first layer `s₀`, the
selection, its frozen coefficient, the volume and the MAIN radius from the second-layer parent `s`.
The proof is Collet's: `selected_two_allocation_weight` is generic in the scalar. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSelectedMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstSourceReduction Cycle61InitialMass Cycle61Moment Record1252270103Second
open OAI.SevenEighths.Record1252270103Source
open Admission.SelectedHighCofactorFamily Admission.SelectedHighCofactorCoordinates
local notation "O"=>HeckeFamily.O
local instance selectedMassDecidable_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Two parents: first layer `s₀`, second-layer parent `s`. -/
theorem actual_selected_paid_weight_mx {α₀ α:Type}[Fintype α₀][Fintype α]
    (s₀:Input α₀)(modifier₀:Tuple α₀→ℂ)(s:Input α)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (D Z ξ amp reserve ε:ℝ)(hZ:0<Z)(hK:0<Z^D)(hε:0≤ε)
    (bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (Admission.FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ)(he:0≤extra)(hl:0<lower)
    (hω:ω≤
      (‖CoupledFirst.balancedColumnScalar reflected s₀ modifier₀ R seed (Z^D) Z ξ D
        (Real.logb Z (volume s₀)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s₀ modifier₀ R seed W (Z^D) Z ξ q)) j‖^2*
      extra*‖frozenCoefficient sel.B₁.val
        (if reflected then (Admission.FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j).1.2
          else (Admission.FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j).1.1)
        R s.ν s.W s.P‖^2/volume s)*
      (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
        (Admission.FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j)/lower)*
      normalizer C₂ D₂ U):
    selectedPaidWeight sel ω≤
      (extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
        Z^amp/lower*forcedProfileCost s)*
      CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ ε hK bin j*
      sel.raw U Z D amp ξ reserve := by
  let l:=Admission.FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j
  let scalar:=CoupledFirst.balancedColumnScalar reflected s₀ modifier₀ R seed (Z^D) Z ξ D
    (Real.logb Z (volume s₀)) hK bin
    (fun q=>normPhase (CoupledFirst.coordinateBlock s₀ modifier₀ R seed W (Z^D) Z ξ q)) j
  have hmain:0≤firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve l:=
    (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*amp) reserve hZ l).le
  have hh:=selected_two_allocation_weight s (if reflected then l.1.2 else l.1.1) R sel.B₁
    sel.τ₁ sel.t₁ C₂ D₂ hC₂ U second sel.B₂ sel.τ₂ sel.t₂ scalar extra
    ((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve l)
    lower Z amp ε ω he hmain hl hZ hε hω
  have hideal:CoupledFirst.geometryColumnIdeal reflected s₀ modifier₀ R seed (Z^D) Z ξ hK bin j=
      if reflected then l.1.2 else l.1.1:=by cases reflected <;> rfl
  unfold CoupledFirst.balancedFirstHighMass
  rw [hideal]
  dsimp only [selectedPaidWeight,Selection.raw,secondAllocationCoefficient,Selection.firstInput]
  simpa only [scalar,l,Selection.firstInput,CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume,mul_assoc] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_selected_paid_weight_mx
