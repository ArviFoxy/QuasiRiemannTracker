/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.High.ActualAllocation
import Candidate.Target830.High.Frequency
import Candidate.Uneven.AuxiliaryPayment

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open Target830
local notation "O" => HeckeFamily.O

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_auxiliary_retained_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta live : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi)
    (hd : Sil.Uneven.AuxiliarySource.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ Sil.Uneven.AuxiliarySource.total b) (ha : a ≤ Sil.Uneven.AuxiliarySource.amp b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ Sil.Uneven.AuxiliarySource.frequencyAllowance)
    (herr : 0 ≤ err) (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    c+b2 ≤ Sil.Uneven.AuxiliarySource.supplied b → Sil.Uneven.AuxiliarySource.supplied b ≤ c+b2+live →
    retainedHighExponent delta (fun freq=>Sil.Uneven.Saturated.physicalGain delta live freq) x
      ≤ side+target-Sil.Uneven.AuxiliarySource.highReserve := by
  intro l side x c b2 target hsmall hsupply
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := by norm_num [Sil.Uneven.AuxiliarySource.q] at hd;linarith
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
  have hf:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (Sil.Uneven.AuxiliarySource.amp b) Sil.Uneven.AuxiliarySource.frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [mul_one,one_mul] at hf
  change 0 ≤ c ∧ 0 ≤ b2 ∧ xc 3=A-(c+b2) ∧ Sil.Uneven.AuxiliarySource.frequency b-2*(c+b2) ≤ xc 2 at hf
  have hg:=Sil.Uneven.AuxiliarySource.gamma_bounds hd hu
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_right ha hg.2.2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.AuxiliarySource.highBase b delta-Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 := by
    change highExponentValue delta xc ≤ target-
      (1*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 at hcone
    change a*(5-6*unmarkedDensity delta) ≤ Sil.Uneven.AuxiliarySource.amp b*(5-6*unmarkedDensity delta) at haa
    change highExponentValue delta xc ≤ target-
      (1-unmarkedDensity delta-delta*Sil.Uneven.AuxiliarySource.total b-Sil.Uneven.AuxiliarySource.amp b*(5-6*unmarkedDensity delta))-
        Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2
    linarith only [hcone,hAA,haa]
  have hguards:=Sil.Uneven.AuxiliarySource.source_guards hb
  have hF : 2*Sil.Uneven.AuxiliarySource.supplied b ≤ Sil.Uneven.AuxiliarySource.frequency b := hguards.2.2.2.2.2.2.2.1.le
  have hx2 : 0 ≤ xc 2 := by linarith only [hf.2.2.2,hF,hsmall]
  have hfrequency : Sil.Uneven.AuxiliarySource.frequency b ≤ 2*(c+b2)+xc 2 := by linarith only [hf.2.2.2]
  have hp:=Sil.Uneven.AuxiliarySource.retained_payment hb hd hu hf.1 hf.2.1 hlive hx2 hsupply hfrequency hsource
  have hid:=compensated_high_exponent delta side x
  have hx : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  unfold retainedHighExponent
  rw [hx] at hp
  change highExponentValue delta (compensatedHighCoordinates x side)=_ at hid
  linarith only [hp,hid]

theorem actual_geometry_auxiliary_unmarked_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi) (hd : Sil.Uneven.AuxiliarySource.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ Sil.Uneven.AuxiliarySource.total b) (ha : a ≤ Sil.Uneven.AuxiliarySource.amp b) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    (Sil.Uneven.AuxiliarySource.supplied b ≤ c+b2) →
    highExponentValue delta x ≤ side+target-Sil.Uneven.AuxiliarySource.highReserve := by
  intro l side x c b2 target hbranch
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := by norm_num [Sil.Uneven.AuxiliarySource.q] at hd;linarith
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
  have hC := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have hc : 0 ≤ c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hb2 : 0 ≤ b2 := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d2.C d2.hC.1
    · exact norm_ge_one d2.D d2.hD.1
  have hg:=Sil.Uneven.AuxiliarySource.gamma_bounds hd hu
  have hr:=Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith) hu
  have hcoeff : 0 ≤ 5-6*unmarkedDensity delta := by
    change 0 ≤ 5-6*rho delta
    linarith [hr.2]
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_left ha hcoeff
  have hbb:=mul_le_mul_of_nonneg_right hg.2.1 hb2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.AuxiliarySource.highBase b delta-Sil.Uneven.AuxiliarySource.gamma delta*(c+b2) := by
    change highExponentValue delta xc ≤ target-
      (1*(1-rho delta)-delta*A-a*(5-6*rho delta))-Sil.Uneven.AuxiliarySource.gamma delta*c-delta*b2 at hcone
    change highExponentValue delta xc ≤ target-
      (1-rho delta-delta*Sil.Uneven.AuxiliarySource.total b-Sil.Uneven.AuxiliarySource.amp b*(5-6*rho delta))-Sil.Uneven.AuxiliarySource.gamma delta*(c+b2)
    have haa2 : a*(5-6*rho delta) ≤ Sil.Uneven.AuxiliarySource.amp b*(5-6*rho delta) := by
      simpa only [←Target830.Source.Valuation.rho_eq_local,mul_comm] using haa
    linarith only [hcone,hAA,haa2,hbb]
  have hreserve : Sil.Uneven.AuxiliarySource.highReserve ≤ Sil.Uneven.AuxiliarySource.highBase b delta+Sil.Uneven.AuxiliarySource.gamma delta*(c+b2) := by
    have hh:=(Sil.Uneven.AuxiliarySource.channel_reserves hb hd hu).1
    have hm:=mul_le_mul_of_nonneg_left hbranch hg.1
    linarith only [hh,hm]
  have hid:=compensated_high_exponent delta side x
  change highExponentValue delta xc=highExponentValue delta x-side at hid
  linarith only [hsource,hreserve,hid]

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_auxiliary_retained_payment

#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_auxiliary_unmarked_payment
