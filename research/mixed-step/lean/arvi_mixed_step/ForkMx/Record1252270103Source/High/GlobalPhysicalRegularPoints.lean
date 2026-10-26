/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
/- Mixed step (L4/L5, F5): fork of Fork.Record1252270103Source.High.GlobalPhysicalRegularPoints
(PR 76 fork of Hailey Collet's module); changes: two parents, two amplitudes, node price
as a hypothesis.
`RegularPointAt_mx … n low bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ N degree controls C Z`:
- the anchor is `Initial.anchor_mx i₀ i` (first layer `i₀`, second layer `i` with `i₀.p = i.p`);
- the second layer satisfies `InitialGeometry i n bcell width mesh r` at the (virtual) node `n`;
- the first layer satisfies only the face hypotheses of `eventually_initial_caps` on `globalFace B₀ lam₀ cap₀`;
- the actual pool sits at the width `poolAmp`, and `F.amp = sourceAReal n low bcell`;
- `∀ κ, hshift → (frozen margins) →`, and the bound is `C * … * Z^(κ - reserve/2)`.

`regular_some_point_source_rm_mx` supplies it from the node price `MixedNodePrice n low bcell φ`, `Scalar_mx`,
the LOW mesh `mesh ≤ regularLowMesh_mx …` and PR 76's HIGH gate data at the node. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularPoints
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularControls
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record1252270103Finite PhysicalScalar HighScalar Record1252270103Source.Collision
open Cycle61HighGeometry Record1252270103CommonGeometry
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open SelectedHighPaid Pool
local instance regularPointsDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint

/-- The two-parent point estimate at a (virtual) node: the full centered family of the second-layer
selections, with the first layer read on `i₀` and the actual pool at `poolAmp`. -/
def RegularPointAt_mx {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀:ℝ)(N degree:ℕ)
    (controls:Finset (ℕ×ℕ))(C Z:ℝ):Prop:=
    let amp:=sourceAReal n low bcell
    ∀hZ:1<Z,
      ∀(i₀:Initial (α:=α₀) M H Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
        i₀.p=i.p→(∀j,0≤ i₀.w j)→
        (globalFace B₀ lam₀ cap₀).Admissible (length Z i₀.X₁) (length Z i₀.X₂) (∑j,i₀.w j) 1→
        1≤ i₀.Y₂→i₀.Y₂≤ i₀.X₁→i₀.Y₂≤ i₀.X₂→
      ∀(seed:Ideal O)(hs:Squarefree seed)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),
      let a:=Initial.anchor_mx i₀ i hH W hW hWs hZ ηanchor η₀ R₀ seed hR₀ hs 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
      ∀{Label:Type}[Fintype Label](F:Family_mx a Label),(∀l,F.amp l=amp)→
      ∀{Row:Type}(rows:Finset Row)(G:Selected_mx F Row rows second),Function.Injective G.key→
        (G.L.absNorm:ℝ)≤Z^(4:ℝ)→
        (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
          (3*amp) θ 2 N (F.first (G.row u).val.1))→
      ∀(pool S A:Finset (Ideal O))(BD Bsource:ℝ)(depth:ℕ),
        FixedCellPoolData pool Z poolAmp (poolAmp/2) mesh θ BD Bsource depth→
        S⊆pool→A⊆S→S.card≤depth→(depth:ℝ)*poolAmp<5→
      ∀T:Finset α,(∀u,T⊆(G.sel u).full)→
      ∀(t height:ℝ),0≤height→(∀j∈T,|i.freq j|≤height)→
        |t|≤Z^τsource→(∀j,|t+i.freq j|≤Z^τsource)→
      ∀(Wa:𝓢(ℝ,ℂ))(H0 mainRadius:Label→ℝ),(∀l,0<H0 l)→
        (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤32)→
      ∀κ:ℝ,amp-poolAmp≤Real.logb Z (volume F.s₀)-Real.logb Z (volume F.s)+κ→
        (∀u:rows,φ≤(∑j,i.w j)-∑j∈liveIndices (G.sel u).B₁.val,i.w j)→
      (∑u:rows,‖regularSelectedCentered_mx G S A T t u‖^2*
        selectedPaidWeight (G.sel u) (residualWeight F.datum
          (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 mainRadius (poolAmp/2)) (G.row u).val))≤
      C*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
        (i.p.control controls)^2*(1+|t|+height)^degree*Z^(κ-(reserve/2))

variable {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (bcell φ reserve θ mesh ξ width poolAmp:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (sc:Scalar_mx n low bcell θ mesh ξ width)(hpoolAmp:0<poolAmp)
variable (hmesh:100*mesh≤θ)(hwidth:width≤θ)(hbcell:bcell≤1)
variable (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))(hq:1/2≤(n.q:ℝ))
variable (R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)(hQM:Q≤M)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)
variable (hq1:(n.q:ℝ)≤1)(hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
variable (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)
variable (hLowMesh:mesh≤regularLowMesh_mx n low bcell φ θ hprice sc.low_parent sc.allowance_pos hq hq1 hG hf.positive)
variable (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)
variable (B₀ lam₀ cap₀:ℝ)(hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)
include setup hbRad hrad hc hmesh hβ hβhi hQM hLowMesh hQ hQt hwidth hbcell hr hfee hq hQ72 hpoolAmp
  hB₀ hlam₀ hcap₀ in
/-- The two estimates are obtained from the earlier genuine sources, with
all source constants preceding the original physical data. -/
theorem regular_some_point_source_rm_mx (hN₀:Fintype.card α₀≤N)(hN:Fintype.card α≤N)
    (high:Source)(hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
    ∃C τsource:ℝ,0<C ∧ 0<τsource ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      RegularPointAt_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
        bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ N degree controls C Z:=by
  obtain ⟨bound,hb,J,SH,CH,Cslot,Cpref,JL,SL,CL,hCH,hslot,hpref,hCL,econtrols⟩:=
    regular_some_controls_rm_mx (α₀:=α₀) (α:=α) (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n)
    (low:=low) (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (reserve:=reserve) (θ:=θ) (mesh:=mesh) (poolAmp:=poolAmp) (N:=N) (wmin:=wmin) (rmin:=rmin)
    (εslot:=εslot) (hf:=hf) (hc:=hc) (hm:=sc.mesh_nonneg) (hmesh:=hmesh) (hpoolAmp:=hpoolAmp)
    (R₀:=R₀) (hR₀:=hR₀) (hβ:=hβ) (hβhi:=hβhi) (bcell:=bcell) (φ:=φ) (hprice:=hprice)
    (hlow:=sc.low_parent) (ha:=sc.allowance_pos) (hqhalf:=hq) (hq1:=hq1) (hG:=hG)
    (hLowMesh:=hLowMesh) (hN:=hN) (Q:=Q) (hQM:=hQM) (hQ:=hQ) (hQt:=hQt) (hQ72:=hQ72)
    (high:=high) (hB0:=hB0) (hB1:=hB1) (hlam:=hlam) (hcap0:=hcap0) (hcap1:=hcap1) (hparent:=hparent)
  let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hb
  obtain ⟨Cpoint,hCpoint,epoint⟩:=SelectedRegularCombinedPointSome.eventually_actual_point_rm_mx
    (α₀:=α₀) (α:=α) (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n)
    (low:=low) (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (bcell:=bcell) (φ:=φ) (reserve:=reserve) (θ:=θ) (mesh:=mesh) (ξ:=ξ)
    (width:=width) (poolAmp:=poolAmp) (N:=N) (wmin:=wmin) (rmin:=rmin) (εslot:=εslot) (hf:=hf)
    (hc:=hc) (sc:=sc) (hpoolAmp:=hpoolAmp) (hmesh:=hmesh) (hwidth:=hwidth) (hbcell:=hbcell) (hr:=hr)
    (hfee:=hfee) (hq:=hq) (R₀:=R₀) (hR₀:=hR₀) (Q:=Q) (hQM:=hQM)
    (hQ72:=hQ72) (hβ:=hβ) (hβhi:=hβhi) (bound:=bound) (hbound:=hb) (J:=J) (JL:=JL) (SL:=SL) (SH:=SH)
    (CL:=CL) (Cpref:=Cpref) (Cslot:=Cslot) (CH:=CH) (hCL:=hCL.le) (hCpref:=hpref.le)
    (hCslot:=zero_le_one.trans hslot) (hCH:=hCH.le) (B₀:=B₀) (lam₀:=lam₀) (cap₀:=cap₀)
    (hB₀:=hB₀) (hlam₀:=hlam₀) (hcap₀:=hcap₀) (hN₀:=hN₀) (hN:=hN) (high:=high) (hB0:=hB0) (hB1:=hB1)
    (hlam:=hlam) (hcap0:=hcap0) (hcap1:=hcap1) (hparent:=hparent) (hgaps:=hgaps)
  refine ⟨JL,regularProfileControl SL SH,Finset.mem_insert_self _ _,Cpoint,P.τ,hCpoint,P.hτ,?_⟩
  filter_upwards [econtrols,epoint] with Z hcZ hpZ
  refine ⟨hpZ.1,?_⟩
  intro hZ
  exact hpZ.2 hZ hcZ.2.1 hcZ.2.2

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.RegularPointAt_mx
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_some_point_source_rm_mx
