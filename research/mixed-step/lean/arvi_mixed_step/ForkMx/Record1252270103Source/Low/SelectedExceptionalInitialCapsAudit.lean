/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Low.SelectedExceptionalInitialCapsAudit
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: actual canonical initial and
modified first-label exceptional caps.

`modified_main_frequency_cap` with the label of the first layer `s₀` and a free second-layer volume
`V` (the cap uses only the label support and the radius formula; Collet's proof is unchanged). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedExceptionalInitialCapsAudit

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open ActualEisensteinCubic
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open Cycle61InitialMass Record1252270103Second OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost Pool Admission.FirstFamily
open High.GlobalPhysical SecondSectorDatum
local notation "O"=>HeckeFamily.O
local instance capsAuditDecidableEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance capsAuditSumDecidableEq_mx {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
local notation "source"=>High.CoupledFirst.geometryFirstSource

/-- The first-layer modified label obeys the main Fourier cap at any second-layer volume. -/
theorem modified_main_frequency_cap_mx {ι₀:Type*}[Fintype ι₀]
    (reflected:Bool)(s₀:Input ι₀)(modifier:Tuple ι₀→ℂ)(R seed:Ideal O)
    (K Z ξ sigma reserve V:ℝ)(N:ℕ)(hK:0<K)(hZ:1<Z)(hV:0<V)
    (hξ:0≤ξ)(hξ1:ξ≤1)(hsigma:0≤sigma)(hreserve:0≤reserve)
    (hKZ:K≤Z)(hN:(2:ℝ)^(2*N)≤Z)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (source s₀ modifier R seed K Z ξ hK bin)):
    frequencyRadius (firstMainFourierScale reflected K V Z ξ sigma reserve 2 N
      (firstLabel s₀ modifier R seed K Z ξ hK bin j)) Z ξ≤Z^(3:ℝ) := by
  let src:=source s₀ modifier R seed K Z ξ hK bin j.1
  have hh:=main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p:CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K V Z sigma (frequencyLoss Z 32 ξ) reserve 2 N
    hK hV hZ (by norm_num) hsigma
    (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  change firstMainFourierScale reflected K V Z ξ sigma reserve 2 N
    (firstLabel s₀ modifier R seed K Z ξ hK bin j)≤(2:ℝ)^(2*N)*K at hh
  unfold frequencyRadius
  calc
    _≤((2:ℝ)^(2*N)*K)*Z^(ξ/2):=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _≤(Z*Z)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      (mul_le_mul hN hKZ hK.le (zero_lt_one.trans hZ).le) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(2+ξ/2):=by
      rw [show Z*Z=Z^(2:ℝ) by norm_num;ring,←Real.rpow_add (zero_lt_one.trans hZ)]
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

end
end QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
#print axioms QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps.modified_main_frequency_cap_mx
