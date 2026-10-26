/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained MAIN width, reusing the generic Cycle61 row conductor budget. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.RetainedGeometryWidth
(Hailey Collet, Apache-2.0); changes: two parents. `main_scale_upper` with the first label read from
the first layer `s₀` and a free positive volume `V` (the second-layer volume `volume s` downstream).
The proof is Collet's: `main_fourier_scale_upper` takes the volume as a free positive real. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedGeometryWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization Cycle61InitialMass Record1252270103Second
open Record1252270103Source.Collision QRH.Record1252270103Low
open High.GlobalPhysical CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondCanonical Cycle61FinalNatural
open CenteredMomentCanonicalFirst RayFourExpansion CenteredMomentSecondRadicalBudget
local notation "O"=>ActualEisensteinCubic.O
local notation "source"=>High.CoupledFirst.geometryFirstSource

/-- Collet's `main_scale_upper` with the label of the first layer `s₀` and a free volume `V`. -/
theorem main_scale_upper_mx {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    (reflected : Bool) (s₀ : Input ι₀) (modifier₀ : Tuple ι₀→ℂ)
    (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (source s₀ modifier₀ R seed K Z ξ hK key))
    (V a reserve b : ℝ) (N : ℕ) (hV : 0<V)
    (hZ : 1<Z) (hb : 0<b) (ha : 0≤a) (hξ : 0≤ξ) (hr : 0≤reserve) :
    firstMainFourierScale reflected K V Z ξ (3*a) reserve b N
      (FirstFamily.firstLabel s₀ modifier₀ R seed K Z ξ hK key j)≤b^(2*N)*K := by
  let src:=source s₀ modifier₀ R seed K Z ξ hK key j.1
  exact main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K V Z (3*a) (frequencyLoss Z 32 ξ) reserve b N
    hK hV hZ hb (by positivity) (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hr

end
end QRH.Record1252270103Source.Admission.RetainedGeometry
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.main_scale_upper_mx
