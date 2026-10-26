/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Original modified joint-row support for the actual selected regular family. -/
/- Mixed step (L4/L5, F5): fork of Record1252270103Source.Low.SelectedRegularFibersGeometry
(Hailey Collet); changes: the family is `Family_mx` over `Anchor_mx` (two parents). The
first labels, their units, supports and caps read the first layer (`F.s₀`, `F.modifier₀`, `F.zero₁₀`,
`F.zero₂₀`, `sourceRadius F.s₀`); the joint blocks and rows read the second-layer family as in Collet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedRegularFibersGeometry
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularNormalized
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedRegularFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT CanonicalRowCompletion CenteredMomentFirstScale
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondLiveBlock
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open Admission Admission.SelectedRegularSourceData Admission.ModifiedFibers Admission.SelectedSecondFibers
open High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance selectedRegularFibersGeometryDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedRegularFibersGeometrySumDecEq_mx {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)

abbrev OriginalIndex_mx:=JointIndex F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ

def originalDatum_mx (q:OriginalIndex_mx F):SecondInputDatum α:=
  jointDatum F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos q

def originalBlocks_mx (q:OriginalIndex_mx F):SecondBlockSource:=
  jointBlock F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos q

def originalFirst_mx (q:OriginalIndex_mx F):FirstSourceLabel:=a.label (F.column q.1)

def originalUnit_mx (l:FirstSourceLabel):O:=(Record12518109Raw.fixedParentUnit (!F.reflected) F.s₀.η l:O)

theorem original_first_frequency_nonzero_mx (r:secondLiveRows (originalBlocks_mx F)):
    jointFirstFrequency (!F.reflected) 1 (originalUnit_mx F)
      (secondEncodedRow (originalBlocks_mx F) (originalFirst_mx F) r)≠0:=by
  exact FirstFamily.first_frequency_ne_zero F.reflected F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK
    F.bin (F.column r.val.1.1) (originalDatum_mx F) (originalFirst_mx F) r rfl

/-- Actual signed numerator and original inactive subset give a coarse
first-frequency cap. No positive lower bound on either raw plain scale enters. -/
theorem first_frequency_cap_mx (Bfirst:ℝ)(hsource:sourceRadius F.s₀≤Z^Bfirst)
    (r:secondLiveRows (originalBlocks_mx F)):
    normValue (jointFirstFrequency (!F.reflected) 1 (originalUnit_mx F)
      (secondEncodedRow (originalBlocks_mx F) (originalFirst_mx F) r))≤Z^(6*Bfirst):=by
  let l:FirstSourceLabel:=originalFirst_mx F r.val.1
  have hs:=FirstFamily.label_supported F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (F.column r.val.1.1)
  have hc:Supported l.1.1:=hs.1
  have hd:Supported l.1.2:=hs.2.1
  have hb:=FirstFamily.label_common_bounds F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    F.seed_sf F.zero₁₀ F.zero₂₀ (F.column r.val.1.1)
  have hNC:(l.1.1.absNorm:ℝ)≤Z^Bfirst:=hb.2.2.1.trans hsource
  have hsubset:normValue (primeSubsetGenerator (fun p:CommonIndex l.1.1 l.1.2=>p.val) l.2.val)≤Z^Bfirst:=
    (divisor_norm_le _ l.1.1 hc.1 ((subsetGenerator_span_dvd l.1.1 l.1.2 l.2.val).trans
      (CenteredMomentCompleteCommon.commonPart_dvd l.1.1 l.1.2 hc.1))).trans hNC
  have hlog:=Real.logb_le_logb_of_le F.hZ (norm_pos l.1.1 hc.1) hNC
  rw [Real.logb_rpow (zero_lt_one.trans F.hZ) F.hZ.ne'] at hlog
  have hnumlog:Real.logb Z (normValue (firstSourceNumerator (!F.reflected) l))≤5*Bfirst:=
    (first_numerator_log_le (!F.reflected) l hc hd Z F.hZ).trans (by linarith)
  have hn:0<normValue (firstSourceNumerator (!F.reflected) l):=
    normValue_pos _ (first_source_numerator_ne_zero (!F.reflected) l hc)
  have hnum:normValue (firstSourceNumerator (!F.reflected) l)≤Z^(5*Bfirst):=by
    have hh:=Real.rpow_le_rpow_of_exponent_le F.hZ.le hnumlog
    rwa [Real.rpow_logb (zero_lt_one.trans F.hZ) F.hZ.ne' hn] at hh
  change normValue ((1*originalUnit_mx F l)*primeSubsetGenerator
    (fun p:CommonIndex l.1.1 l.1.2=>p.val) l.2.val*firstSourceNumerator (!F.reflected) l)≤_
  rw [normValue_mul,normValue_mul,Cycle61HighFrequency.fixed_unit_norm 1 (originalUnit_mx F l) (Units.isUnit _)]
  rw [show normValue (1:O)=1 by simp [normValue],one_mul]
  have hh:=mul_le_mul hsubset hnum hn.le (Real.rpow_nonneg (zero_lt_one.trans F.hZ).le _)
  convert hh using 1
  rw [←Real.rpow_add (zero_lt_one.trans F.hZ)]
  congr 1
  ring

/-- The entire original row carrier has polynomial support. The nonzero
retained Fourier weight supplies the full second frequency, before keep. -/
theorem original_joint_row_cap_mx (Bfirst L Cr:ℝ)
    (hsource:sourceRadius F.s₀≤Z^Bfirst)
    (hradius:∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Cr*Z^L)(hCr:4*Cr≤Z)
    (r:secondLiveRows (originalBlocks_mx F)):
    ((Ideal.span {jointSourceRow (!F.reflected) 1 (originalUnit_mx F)
      (secondEncodedRow (originalBlocks_mx F) (originalFirst_mx F) r)}).absNorm:ℝ)≤Z^(6*Bfirst+L+1):=by
  have hret:=actual_second_live_retained_weight (originalBlocks_mx F) r.val r.property
  have hfreq:0<normValue ((originalBlocks_mx F r.val.1).frequency*r.val.2.2.2.val) ∧
      normValue ((originalBlocks_mx F r.val.1).frequency*r.val.2.2.2.val)≤4*frequencyRadius (F.Tsec r.val.1.1) Z F.ξ:=
    retainedWeight_enclosure _ _ hret
  have hc:=first_frequency_cap_mx F Bfirst hsource r
  have hs:normValue ((originalBlocks_mx F r.val.1).frequency*r.val.2.2.2.val)≤4*Cr*Z^L:=by
    exact hfreq.2.trans (by have hh:=mul_le_mul_of_nonneg_left (hradius r.val.1.1) (by norm_num : (0:ℝ)≤4);nlinarith only [hh])
  change normValue (jointSourceRow (!F.reflected) 1 (originalUnit_mx F)
    (secondEncodedRow (originalBlocks_mx F) (originalFirst_mx F) r))≤_
  rw [joint_source_row_factorization,normValue_mul]
  change normValue (jointFirstFrequency (!F.reflected) 1 (originalUnit_mx F)
      (secondEncodedRow (originalBlocks_mx F) (originalFirst_mx F) r))*
    normValue ((originalBlocks_mx F r.val.1).frequency*r.val.2.2.2.val)≤_
  calc
    _≤Z^(6*Bfirst)*(4*Cr*Z^L):=mul_le_mul hc hs hfreq.1.le (Real.rpow_nonneg (zero_lt_one.trans F.hZ).le _)
    _≤Z^(6*Bfirst)*(Z*Z^L):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hCr (Real.rpow_nonneg (zero_lt_one.trans F.hZ).le _))
      (Real.rpow_nonneg (zero_lt_one.trans F.hZ).le _)
    _=_:=by
      rw [show Z*Z^L=Z^(1+L) by rw [Real.rpow_add (zero_lt_one.trans F.hZ),Real.rpow_one],
        ←Real.rpow_add (zero_lt_one.trans F.hZ)]
      congr 1
      ring

/-- The selected original column key is exactly the first-label/projector
key used in the fiber theorem, with no dyad or ray silently discarded. -/
theorem original_first_key_injective_mx
    (hcolumn:Function.Injective (fun l=>FirstAllocationSelection.columnKey F.s₀ F.modifier₀ F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column l))):
    Function.Injective (fun l=>(a.label (F.column l),F.childSeed l)):=hcolumn
end
end QRH.Record1252270103Source.Low.SelectedRegularFibers
#print axioms QRH.Record1252270103Source.Low.SelectedRegularFibers.original_first_frequency_nonzero_mx
#print axioms QRH.Record1252270103Source.Low.SelectedRegularFibers.first_frequency_cap_mx
#print axioms QRH.Record1252270103Source.Low.SelectedRegularFibers.original_joint_row_cap_mx
#print axioms QRH.Record1252270103Source.Low.SelectedRegularFibers.original_first_key_injective_mx
