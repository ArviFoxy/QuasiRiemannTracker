/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F1, two-parent twin): fork of
Record1252270103Source.Admission.SelectedHighCofactorCoordinates (Hailey Collet, Apache-2.0;
inherited notices retained).

`eventual_modified_normalized_cofactor` with the first label from the first layer `s₀` and the
first allocation, the raw coefficient and the coordinates (at `logb Z (volume s)`, the virtual
volume) from the second-layer parent `s`. -/
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedHighCoordinatesScalar
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open Cycle61Moment Cycle61InitialMass Record12518109Natural.MarkedPlain
open OAI.SevenEighths.Record1252270103Source Record1252270103Second
open SelectedHighSlots SelectedHighCoordinates HighScalar
local notation "O" => HeckeFamily.O
noncomputable local instance selectedHighCofactorCoordinatesDecEq_mx {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem eventual_modified_normalized_cofactor_mx (N : ℕ) (lo errv : ℝ) (hlo : 0<lo) (he : 0<errv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι₀ ι : Type} [Fintype ι₀] [Fintype ι] (s₀ : Input ι₀) (s : Input ι),
    Fintype.card ι≤N→lo≤s.lower→∀(modifier₀ : CenteredMomentAddedZeroUniform.Tuple ι₀→ℂ)
      (R seed : Ideal O) (K ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
      (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s₀ modifier₀ R seed K Z ξ hK bin))
      (reflected second : Bool),
    let l:=FirstFamily.firstLabel s₀ modifier₀ R seed K Z ξ hK bin j
    ∀(B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1)) (τ₁ : Character) (t₁ : ℝ),
    frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0→
    ∀M amp reserve err : ℝ,
    NormalizedSecondAllocationBound s reflected second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv := by
  filter_upwards [eventual_modified_high_coefficient_mx N lo errv hlo he] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι₀ ι _ _ s₀ s hN hloS modifier₀ R seed K ξ hK bin j reflected second l B₁ τ₁ t₁ hB₁ M amp reserve err
  exact normalize_second_allocation s reflected second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv hz.1
    (hz.2 s₀ s hN hloS modifier₀ R seed K ξ hK bin j reflected (!reflected) second B₁ τ₁ t₁ hB₁
      M amp reserve err)

end QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.eventual_modified_normalized_cofactor_mx
