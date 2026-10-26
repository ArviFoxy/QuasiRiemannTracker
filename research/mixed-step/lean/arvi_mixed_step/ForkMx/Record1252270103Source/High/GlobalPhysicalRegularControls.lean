/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine parent sources choose one shared parameter record and one LOW/HIGH
control package before every moving physical family. -/
/- Mixed step (L4/L5, F5): fork of Fork.Record1252270103Source.High.GlobalPhysicalRegularControls
(PR 76 fork of Hailey Collet's module, Apache-2.0); changes: two parents, two amplitudes, node price
as a hypothesis. The LOW package is `regular_low_controls_mx` at the node price
`MixedNodePrice n low bcell φ` with the pool cell width `ellPool = poolAmp/2`; the HIGH package is
the F4 `regular_some_source_rm_mx`/`SourceAt_rm_mx` at the same `poolAmp` (PR 76's section variable
`amp` only enters as `ell = amp/2`, so it is the pool width `poolAmp` here). -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularControls
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularHighPointSome
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularHighParameters
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularLowAt
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Admission
open CenteredMomentNaturalFixedRaySource
open Filter QRH.Record1252270103Graph QRH.Record1252270103Low Record1252270103StepScalar
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {α₀ α:Type}[Fintype α₀][Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (reserve θ mesh poolAmp:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hm:0≤mesh)(hmesh:100*mesh≤θ)(hpoolAmp:0<poolAmp)
variable (R₀:Ideal O)(hR₀:R₀≠0)
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)

variable (bcell φ:ℝ)(hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)
variable (hlow:ParentGood low)(ha:0<(n.allowance:ℝ))
variable (hqhalf:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
variable (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
variable (hLowMesh:mesh≤regularLowMesh_mx n low bcell φ θ hprice hlow ha hqhalf hq1 hG hf.positive)
variable (hN:Fintype.card α≤N)(Q:Ideal O)(hQM:Q≤M)
variable (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
include hprice hlow ha hqhalf hq1 hG hLowMesh hN hQ hQt hQ72

theorem regular_some_controls_rm_mx (high:Source) (hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ):
    ∃bound:ℕ→ℝ,∃hb:∀k,0≤bound k,∃J:ℕ,
    let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hb
    ∃SH:Finset (ℕ×ℕ),∃CH Cslot Cpref:ℝ,∃JL:ℕ,∃SL:Finset (ℕ×ℕ),∃CL:ℝ,
      0<CH ∧ 1≤Cslot ∧ 0<Cpref ∧ 0<CL ∧ ∀ᶠZ:ℝ in atTop,2≤Z ∧
      RegularLowAt_mx (α:=α) M H hH n low bcell φ (poolAmp/2) θ mesh εslot P.τ N
        (fun _=>initialSlotBound W hW hWs) W ηanchor η₀ Q hQM Cslot Cpref JL SL CL Z ∧
      SelectedRegularHighPointSome.SourceAt_rm_mx (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low setup W hWs hW
        bRad hbRad hrad reserve θ mesh poolAmp N wmin rmin εslot hf hc hm hmesh hpoolAmp R₀ hR₀ hβ hβhi
        high hB0 hB1 hlam hcap0 hcap1 hparent J P.τ P SH CH Z:=by
  let hs:=regular_some_source_rm_mx (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad
    reserve θ mesh poolAmp N wmin rmin εslot hf hc hm hmesh hpoolAmp R₀ hR₀ hβ hβhi high hB0 hB1 hlam hcap0 hcap1 hparent
  let bound:=Classical.choose hs
  have hb:= (Classical.choose_spec hs).1
  let hj:= (Classical.choose_spec hs).2
  let J:=Classical.choose hj
  have hJ:=Classical.choose_spec hj
  let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  have ht:=regular_parameters_height W θ εslot J bound hWs hW hf.positive hc.slot_pos (fun k=>(hb k).le)
  have hh:=hJ P.τ P.hτ ht.1 ht.2.1 ht.2.2.1 P rfl rfl rfl le_rfl le_rfl
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters]) rfl rfl
    ht.2.2.2.2.1 ht.2.2.2.1
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])
    (by norm_num [P,regularParameters,actualPhysicalParameters,highParameters])
  obtain ⟨SH,CH,hCH,eH⟩:=hh
  have hΦs:Function.support (ballProfile:ℝ→ℂ)⊆Iic (2:ℝ):=by
    intro x hx
    by_cases hx0:0≤x
    · exact (ballProfile_support_upper x hx0 hx).le
    · exact le_trans (le_of_not_ge hx0) (by norm_num)
  obtain ⟨Cslot,Cpref,JL,SL,CL,hslot,hpref,hCL,eL⟩:=regular_low_controls_mx n low bcell φ (poolAmp/2) θ
    hprice hlow (div_pos hpoolAmp (by norm_num)) ha hqhalf hq1 hG hf.positive (α:=α) M H hH W hWs hW
    (fun _=>initialSlotBound W hW hWs) (fun _=>zero_le_one.trans (initialSlotBound_ge_one W hW hWs))
    mesh hLowMesh N wmin rmin εslot P.τ hc hN P.hτ ht.2.2.2.2.2.2
    ηanchor η₀ Q hQM hQ hQt hQ72 ballProfile hΦs ballProfile_nonneg
    (fun x hx=>by rw [ballProfile_one x hx.1 hx.2];norm_num)
  refine ⟨bound,(fun k=>(hb k).le),J,SH,CH,Cslot,Cpref,JL,SL,CL,hCH,hslot,hpref,hCL,?_⟩
  filter_upwards [eL,eH] with Z hl hh
  exact ⟨hl.1,hl.2,hh.2⟩

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_some_controls_rm_mx
