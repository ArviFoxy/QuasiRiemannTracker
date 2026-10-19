/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.CoarseEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRemainder
import Candidate.Uneven.MainAssemblyUnevenMainRemainder
import Candidate.Uneven.MainRetained
import Candidate.Uneven.MainZeroScalar
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.MainAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryContraction
import Candidate.Uneven.MainAffineExceptionalGates

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open MainReconstruction
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentLogDyadic CenteredMomentSectorLocalization CenteredMomentSourceMass
open CenteredMomentAmplifiedRetainedRadius EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {plane : Sil.Uneven.MainSource.Plane}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance affineRemainderSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The main source before retained contraction, with the original allocation
weights and the actual slot cardinality in its Fourier scale. -/
def unevenAffineMainSourceTotal (s : Input ι) (Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ) (hZ : 1<Z) (reflected : Bool) (key : ℤ×(Fin 5→ℤ)) : ℝ :=
  let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let phase := fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)
  ∑q : GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key,
    unevenAllocationWeight reflected s 1 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2 *
    actualMainSource (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key t q)
      (geometryBranch reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key q.1.val) Z (3*amp) 1 ξ reserve

/-- The small losses in the width-one zero term leave a fixed strict saving. -/
theorem geometry_affine_zero_loss (Z μ A beta : ℝ)
    (hμ : 0<μ) (hcap : μ≤1/128) (hA : A≤3)
    (hb : Sil.Uneven.MainSource.widthLo≤beta ∧ beta≤Sil.Uneven.MainSource.widthHi)
    (hω : frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128) :
    MainReconstruction.zeroPaymentExponent Z 1 A (Sil.Uneven.MainSource.amp plane beta) (μ/64) (μ/8)
      (μ/128) (μ/128) (μ/128) 3+3*(μ/128)≤-(1/20:ℝ) := by
  have hpaid := geometry_zero_exponent_saving (plane:=plane) Z 1 A (Sil.Uneven.MainSource.amp plane beta)
    (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3 (μ/128) beta
    (by norm_num) hb (by simp)
  have hmul := mul_le_mul_of_nonneg_left hA (show 0≤μ/128 by positivity)
  have hsq : μ*(μ/128)≤μ := by
    have hh : μ/128≤1 := by linarith
    exact (mul_le_mul_of_nonneg_left hh hμ.le).trans_eq (mul_one μ)
  have hbudget : frequencyLoss Z 32 (μ/64)+μ/8+
      μ/128*(A+μ/128)+3*(μ/128)+3*(μ/128)≤1/380 := by nlinarith
  simpa only [MainReconstruction.zeroPaymentExponent, Cycle63InitialMass.zeroPaymentExponent, neg_div] using hpaid hbudget

/-- Genuine source and cone receipts pay the complete zero and tail terms.
Only the exact retained sum remains on the right, before its low/high split. -/
theorem eventual_actual_affine_main_remainder
    (Cs μ : ℝ) (hCs : 1≤Cs) (hμ : 0<μ) (hcap : μ≤1/128) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
    ∀(s : Input ι)(p : Profiles (1/4) (9/4)),
      GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
    ∀beta : ℝ,Sil.Uneven.MainSource.widthLo≤beta ∧ beta≤Sil.Uneven.MainSource.widthHi →
      Real.logb Z (volume s)≤Sil.Uneven.MainSource.total plane beta →
    ∀(Ψ : 𝓢(ℝ,ℂ))(t : ℝ)(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      unevenAffineMainSourceTotal s Ψ Z (Sil.Uneven.MainSource.amp plane beta) (μ/64) (μ/8)
        t hZ reflected key ≤
      C*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1/20:ℝ))+
      ‖unevenMainRetainedSum reflected s 1 1 Z 1 (Sil.Uneven.MainSource.amp plane beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
  obtain ⟨F,Cz,Ct,hCz,hCt,hraw⟩ := eventual_actual_geometry_main_remainder (plane:=plane) (ι:=ι)
    (Fintype.card ι) Cs (9/4) (1/4) (9/4) 1 3 3 (μ/64) (μ/128) (μ/128) (μ/128) 1
    hCs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity)
  let zconst := Cz*‖paperRadialFourier ballProfile 0‖
  let tconst := Ct*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile
  refine ⟨1+zconst+tconst,by dsimp [zconst,tconst];positivity,?_⟩
  have hpad := (tendsto_rpow_atTop (show 0<μ/128 by positivity)).eventually
    (eventually_ge_atTop ((9/4:ℝ)^(Fintype.card ι)))
  filter_upwards [hraw,eventual_geometry_small_frequency μ hμ,hpad] with Z hr hfreq hpad
  intro hZ s p caps beta hb hcone Ψ t reflected key
  have ha := (Sil.Uneven.MainSource.amplifier_pos plane hb).le
  have haB : Sil.Uneven.MainSource.amp plane beta≤3 := (Sil.Uneven.MainSource.scheduling_guards plane hb).2.2.2.1.le.trans (by norm_num)
  have hh := hr.2 s 1 1 Ψ le_rfl caps.controls caps.endpoints.1
    (by rw [caps.lower]) p caps.profile₁ caps.profile₂ beta 1
    (Sil.Uneven.MainSource.amp plane beta) (μ/8) (μ/128) t hZ hb (by norm_num) (by norm_num)
    ha haB (by positivity) (hfreq.2.2.trans (by linarith)) (by simpa using hcone)
    (by simp) hpad squarefree_one one_ne_zero caps.sourcePositive caps.sourceCap
    caps.volumeLog caps.poolCap reflected key
  have hz := geometry_affine_zero_loss (plane:=plane) Z μ (Real.logb Z (volume s)) beta hμ hcap
    (abs_le.mp caps.volumeLog).2 hb hfreq.2.2
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hz
  have htail := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -(1:ℝ)≤-(1/20:ℝ))
  have hside := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hzconst : 0≤zconst := by dsimp [zconst];positivity
  have htconst : 0≤tconst := by dsimp [tconst];positivity
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hzconst (sq_nonneg (p.control {(0,0)}))) hside)
  have h₂ := mul_le_mul_of_nonneg_left htail
    (mul_nonneg (mul_nonneg htconst (sq_nonneg (p.control {(0,0)}))) hside)
  have hrest : 0≤(p.control {(0,0)})^2*
      geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
      Z^(-(1/20:ℝ)) := by positivity
  simp only [map_one,Nat.cast_one,div_one] at hh
  have hnorm : unevenAffineMainSourceTotal s Ψ Z (Sil.Uneven.MainSource.amp plane beta) (μ/64) (μ/8)
      t hZ reflected key≤
      zconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(MainReconstruction.zeroPaymentExponent Z 1 (Real.logb Z (volume s)) (Sil.Uneven.MainSource.amp plane beta)
          (μ/64) (μ/8) (μ/128) (μ/128) (μ/128) 3+3*(μ/128))+
      tconst*(p.control {(0,0)})^2*
        geometryHighFactor reflected (geometrySupportConstant (Fintype.card ι) 1 (1/4) (1/4)) key*
        Z^(-(1:ℝ))+
      ‖unevenMainRetainedSum reflected s 1 1 Z 1 (Sil.Uneven.MainSource.amp plane beta)
        (μ/64) (μ/8) (9/4) t hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (μ/64) q))‖ := by
    convert hh using 1 <;>
      simp only [unevenAffineMainSourceTotal,unevenMainRetainedSum,
        unevenLowFirstWeight,geometryLowFirstChild,Fintype.sum_sigma,zconst,tconst,
        original,OriginalData.columns,OriginalData.beta,OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,one_mul]; ring
  nlinarith

end
end OAI.SevenEighths.MainAssembly
#print axioms OAI.SevenEighths.MainAssembly.geometry_affine_zero_loss
#print axioms OAI.SevenEighths.MainAssembly.eventual_actual_affine_main_remainder
