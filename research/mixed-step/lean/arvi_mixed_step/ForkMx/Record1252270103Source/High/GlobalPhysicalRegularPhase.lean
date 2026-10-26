/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F1): fork of Record1252270103Source.High.GlobalPhysicalRegularPhase
(Hailey Collet).

The regular family supplies `PhaseBound_mx` (two parents) with the residual normalization: the
phases are `amplitude_mx / volume s` with `s` the second-layer parent, and the MAIN radius is the
family's `Hmain` at `(volume s, 3·amp)`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularPhase
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularAbsoluteData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedHighPaidComparison
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical CenteredMomentSecondInputCapacitySource
open CenteredMomentSectorLocalization Cycle61InitialMass Cycle61Moment Record1252270103Second
open Admission.SelectedRegularSourceData Admission.SelectedSecondPhase Admission.SelectedHighPaid
local notation "O"=>HeckeFamily.O
local instance regularPhaseDecidable_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)

def regularFamilyKeep_mx:Admission.SelectedRegularAbsolute.Keep_mx F:=
  Admission.SelectedSecondNatural.regularKeep F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ F.χ₀ F.Q F.m

def regularFamilyWeight_mx (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)
    (H0 radius:Label→ℝ)(ell:ℝ):F.Complete→ℂ:=
  Admission.SelectedRegularAbsolute.effectivePhase_mx F W P poolAmp H0 radius ell (regularFamilyKeep_mx F)

theorem regular_family_datum_mx (q:F.Complete):
    Admission.SelectedRegularAbsolute.datum_mx F (regularFamilyKeep_mx F) q=F.datum q:=rfl

/-- Two parents: the second-layer caps (`hN`, `hlower`, `hW₁`, `hW₂`) are on `s`; the
amplitude's pool width `poolAmp` enters only `mainExtra`. -/
theorem actual_regular_phase_mx (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (hN:Fintype.card α≤N)(hlower:lo≤F.s.lower)
    (hW₁:∀x,F.s.W₁ x≠0→ap≤x)(hW₂:∀x,F.s.W₂ x≠0→ap≤x)
    (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)(H0 radius:Label→ℝ)(ell:ℝ)
    (hell:0<ell)(hrad:∀l,0≤radius l+6*poolAmp l)
    {Row:Type}(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)(r:rows):
    PhaseBound_mx F.s₀ F.modifier₀ F.s F.R F.seed W F.D Z F.ξ (F.amp (G.row r).val.1.1)
      F.reserve F.hK F.bin F.reflected second (G.column r)
      (G.datum r).C (G.datum r).D (G.datum r).inactive (G.sel r)
      (mainExtra F.s₀ (F.stage (G.row r).val.1.1).common (P (G.row r).val.1.1)
        (H0 (G.row r).val.1.1) (radius (G.row r).val.1.1) (poolAmp (G.row r).val.1.1) ell)
      (lowerFactor N lo ap)
      (residualWeight F.datum (regularFamilyWeight_mx F W P poolAmp H0 radius ell) (G.row r).val):=by
  let amplitude:=Admission.SelectedRegularAbsolute.amplitude_mx F W P poolAmp H0 radius ell
  let phase:=Admission.SelectedRegularAbsolute.phase_mx F W P poolAmp H0 radius ell (regularFamilyKeep_mx F)
  have ha(l:Label):0≤amplitude l:=
    Admission.SelectedRegularAbsolute.amplitude_nonneg_mx F W P poolAmp H0 radius ell hell hrad l
  have hw(q:F.Complete):‖phase q‖≤amplitude q.1/volume F.s:=
    actual_family_weight_parent F.slots F.input F.childModifier F.mask F.childSeed ballProfile
      F.Hmain F.Tsec (fun _=>Z) (fun _=>F.ξ) (fun _=>volume F.s) amplitude
      (fun _=>volume_pos F.s) ha (regularFamilyKeep_mx F) q
  have hh:=actual_effective_weight_parent_bound N lo ap hlo hap F.datum
    (fun q=>F.childModifier q.1) phase ballProfile hN
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂)
    (fun q=>amplitude q.1) (fun _=>volume F.s) (fun _=>volume_pos F.s) hw (G.row r).val
  change _≤(amplitude (G.row r).val.1.1/volume F.s)*(F.Hmain (G.row r).val.1.1/lowerFactor N lo ap)*
    normalizer (G.datum r).C (G.datum r).D (G.datum r).inactive at hh
  simpa only [PhaseBound_mx,G.first_allocation r,amplitude,Admission.SelectedRegularAbsolute.amplitude_mx,
    FirstStage.height,FirstStage.common,Family_mx.first,Anchor_mx.label,Selected_mx.column,Selected_mx.datum,
    Family_mx.Hmain,regularFamilyWeight_mx,Admission.SelectedRegularAbsolute.effectivePhase_mx,
    Admission.SelectedRegularAbsolute.datum_mx,regular_family_datum_mx,phase,residualWeight,
    CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_regular_phase_mx
