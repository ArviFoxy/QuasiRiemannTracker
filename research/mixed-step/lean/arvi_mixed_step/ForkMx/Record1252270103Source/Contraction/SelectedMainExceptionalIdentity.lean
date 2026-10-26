/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact constructor alignment of the actual MAIN frozen-one family and the
regular complete family. No correction estimate or analytic norm is assumed. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F5): fork of Record1252270103Source.Contraction.SelectedMainExceptionalIdentity
(Hailey Collet, Apache-2.0); changes: two parents. `regularMainFamily_mx` is Collet's family over the
second-layer parent `F.s` of a `Family_mx` with the two-parent amplitude `amplitude_mx` (scalar at the
first layer, `mainExtra` at the first layer with the actual pool width `poolAmp l`, frozen coefficient of
the second layer). The two `rfl` bridges are Collet's, with `phase_mx`/`regularFamilyKeep_mx`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedMainExceptionalIdentity
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularPhase
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction.SelectedMainExceptional
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open QRH.Record1252270103Source
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic RayFourExpansion
open Admission High.GlobalPhysical Admission.SelectedRegularSourceData Admission.SelectedSecondPhase
open Low.SelectedExceptionalNormalized Low.SelectedExceptionalInitialCaps
open InitialRegularToTruncated SecondSectorDatum
open OAI.SevenEighths.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
local instance mainIdentityDecidable_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

section
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
variable (F:Family_mx a Label)

/-- Collet's `regularMainFamily` with two parents and two amplitudes: the common parent, allocations,
characters, MAIN radius and Fourier scale are the second layer's; the amplitude is `amplitude_mx`. -/
def regularMainFamily_mx (P:Finset (Ideal O)) (W₁ W₂ Wfirst:𝓢(ℝ,ℂ))(H0 radius:Label→ℝ)(ell:ℝ)
    (poolAmp:Label→ℝ):CorrectedFamilyData F.slots ballProfile Z :=
  mainAllocatedFamily F.s ballProfile W₁ W₂ Z F.R
    (fun l=>(F.stage l).common) F.childSeed (fun l=>(F.stage l).B)
    (fun l=>(F.stage l).τ) (fun l=>(F.stage l).t) P F.childSeed_sf F.zero₁ F.zero₂
    F.Hmain F.Tsec (fun _=>volume F.s)
    (Admission.SelectedRegularAbsolute.amplitude_mx F Wfirst (fun _=>P) poolAmp H0 radius ell)
    F.ξ F.Hmain_pos F.χ₀ F.m

private def regularNorm_mx (modifier:∀l,Tuple (F.slots l)→ℂ) (amplitude:Label→ℝ):ℝ :=
  let keep:=SelectedSecondNatural.regularKeep F.slots F.input modifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ F.χ₀ F.Q F.m
  let datum:=SelectedSecondNatural.regularDatum F.slots F.input modifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂)
    F.Hmain_pos F.χ₀ F.Q F.m
  let phase:=familyWeight F.slots F.input modifier F.mask F.childSeed ballProfile F.Hmain F.Tsec
    (fun _=>Z) (fun _=>F.ξ) (fun _=>volume F.s) amplitude keep
  ‖∑q:CompleteFamily F.slots F.input modifier F.mask F.childSeed ballProfile F.Hmain F.Tsec
    (fun _=>Z) (fun _=>F.ξ), phase q*(modifiedDatumBlock (datum q) (modifier q.1)).value ballProfile‖

theorem regularMainFamily_joint_norm_of_modifier_mx (P:Finset (Ideal O))
    (hm:(fun l=>markedSourceModifier ((F.stage l).B.val (Sum.inr 0))
      ((F.stage l).B.val (Sum.inr 1)) 1 (markedProduct (F.stage l).B.val)
      (poolCorrection P))=F.childModifier)
    (W₁ W₂ Wfirst:𝓢(ℝ,ℂ))(H0 radius:Label→ℝ)(ell:ℝ)(poolAmp:Label→ℝ):
    regularJointNorm (regularMainFamily_mx F P W₁ W₂ Wfirst H0 radius ell poolAmp) F.Q=
      ‖∑q:F.Complete,
        Admission.SelectedRegularAbsolute.phase_mx F Wfirst (fun _=>P) poolAmp H0 radius ell
          (regularFamilyKeep_mx F) q*
          (modifiedDatumBlock (F.datum q) (F.childModifier q.1)).value ballProfile‖ := by
  exact congrArg (fun modifier=>regularNorm_mx F modifier
    (Admission.SelectedRegularAbsolute.amplitude_mx F Wfirst (fun _=>P) poolAmp H0 radius ell)) hm

end

section
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}(a:Anchor_mx α₀ α Z)
variable (column:Label→a.Column)
variable (hLive:∀l,column l∈firstLiveColumns
  (High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
  (fun _=>logAnnulus))
variable (alloc:∀l,actualAllocations a.s.pools
  (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l)))
variable (P:Finset (Ideal O))(amp ht:ℝ)(N:ℕ)(χ₀:Label→RayCharacter)
local notation "F"=>allocatedRegularFamily_mx a column hLive alloc P amp ht N χ₀

theorem regularMainFamily_joint_norm_mx (W₁ W₂ Wfirst:𝓢(ℝ,ℂ))(H0 radius:Label→ℝ)(ell:ℝ)
    (poolAmp:Label→ℝ):
    regularJointNorm (regularMainFamily_mx F P W₁ W₂ Wfirst H0 radius ell poolAmp) a.Q=
      ‖∑q:(F).Complete,
        Admission.SelectedRegularAbsolute.phase_mx F Wfirst (fun _=>P) poolAmp H0 radius ell
          (regularFamilyKeep_mx F) q*
          (modifiedDatumBlock ((F).datum q) ((F).childModifier q.1)).value ballProfile‖ := by
  apply regularMainFamily_joint_norm_of_modifier_mx
  funext l
  exact (corrected_modifier_constant_one P _ _ 1 _).symm

end
end
end QRH.Record1252270103Source.Contraction.SelectedMainExceptional
#print axioms QRH.Record1252270103Source.Contraction.SelectedMainExceptional.regularMainFamily_joint_norm_mx
