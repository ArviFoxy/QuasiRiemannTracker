/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual LOW corners and HIGH bins use the same retained states and selector.
The one point constant precedes every moving canonical input and row family. -/
/- Mixed step (L4/L5, F5): fork of Fork.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
(PR 76 fork of Hailey Collet's module, Apache-2.0); changes: two parents, two amplitudes, node price
as a hypothesis.
`eventually_actual_point_rm_mx`: the anchor is `Initial.anchor_mx i₀ i` (first layer `i₀`, second
layer `i` with `i₀.p = i.p`); the second layer satisfies `InitialGeometry i n bcell width mesh r` at the
(virtual) node `n` (`Scalar_mx`); the first layer only needs the hypotheses of Collet's
`eventually_initial_caps` on the face `globalFace B₀ lam₀ cap₀` (fixed before `Z`), which give its
source cap `sourceRadius F.s₀ ≤ Z^2`; the actual pool sits at `poolAmp`; `∀ κ, hshift → (frozen
margins) →`. The LOW corners (`eventually_initial_low_point_mx`) and the HIGH bins (F4
`actual_point_rm_mx`) both cost the factor `Z^κ`, which multiplies Collet's paid budget: the bound is
`Cpoint * … * Z^(κ - reserve/2)`. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularLowPoint
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularHighPointSome
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularCofactor
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
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
local instance combinedPointSomeDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
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
variable (bound:ℕ→ℝ)(hbound:∀k,0≤bound k)(J JL:ℕ)(SL SH:Finset (ℕ×ℕ))
variable (CL Cpref Cslot CH:ℝ)(hCL:0≤CL)(hCpref:0≤Cpref)(hCslot:0≤Cslot)(hCH:0≤CH)
variable (B₀ lam₀ cap₀:ℝ)(hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)
local notation "P"=>regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hbound
local notation "amp"=>sourceAReal n low bcell

include hwidth hbcell hr hfee hq hQ72 hCL hCpref hCslot hCH hB₀ hlam₀ hcap₀ in
/-- A single fixed constant bounds the complete original row family, after
applying the genuine earlier sources to the same actual retained states. -/
theorem eventually_actual_point_rm_mx (hN₀:Fintype.card α₀≤N)(hN:Fintype.card α≤N)
    (high:Source)(hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    ∃Cpoint:ℝ,0<Cpoint ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
      RegularLowAt_mx (α:=α) M H hH n low bcell φ (poolAmp/2) θ mesh εslot (P).τ N
        (fun _=>initialSlotBound W hW hWs) W ηanchor η₀ Q hQM Cslot Cpref JL SL CL Z→
      SelectedRegularHighPointSome.SourceAt_rm_mx (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low setup W hWs hW
        bRad hbRad hrad reserve θ mesh poolAmp N wmin rmin εslot hf hc sc.mesh_nonneg hmesh hpoolAmp
        R₀ hR₀ hβ hβhi high hB0 hB1 hlam hcap0 hcap1 hparent J (P).τ P SH CH Z→
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
        |t|≤Z^(P).τ→(∀j,|t+i.freq j|≤Z^(P).τ)→
      ∀(Wa:𝓢(ℝ,ℂ))(H0 mainRadius:Label→ℝ),(∀l,0<H0 l)→
        (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤32)→
      ∀κ:ℝ,amp-poolAmp≤Real.logb Z (volume F.s₀)-Real.logb Z (volume F.s)+κ→
        (∀u:rows,φ≤(∑j,i.w j)-∑j∈liveIndices (G.sel u).B₁.val,i.w j)→
      (∑u:rows,‖regularSelectedCentered_mx G S A T t u‖^2*
        selectedPaidWeight (G.sel u) (residualWeight F.datum
          (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 mainRadius (poolAmp/2)) (G.row u).val))≤
      Cpoint*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
        (i.p.control (regularProfileControl SL SH))^2*(1+|t|+height)^JL*Z^(κ-(reserve/2)):=by
  let pcCap:=((initialSlotBound W hW hWs)^N)^2*(2:ℝ)^N
  obtain ⟨Cpoint,hCpoint,hpay⟩:=regular_point_budgets_paid n reserve θ εslot wmin rmin N J JL
    hf hc hr hfee hq W bound hWs hW hbound CL Cpref Cslot CH pcCap SL SH
    hCL hCpref hCslot hCH (by dsimp [pcCap];positivity)
  refine ⟨Cpoint,hCpoint,?_⟩
  filter_upwards [eventual_scale_guards N θ ξ hf.positive sc.xi_pos.le sc.xi_loss,
    eventually_initial_low_point_mx n low bcell φ θ mesh ξ width εslot (P).τ poolAmp sc hpoolAmp N hN₀ hN
      M H hH W hW hWs ηanchor η₀ Q hQM R₀ hR₀ Cslot Cpref JL SL CL,
    InitialTruncated.eventually_initial_caps N B₀ lam₀ cap₀ hB₀ hlam₀ hcap₀]
    with Z hguard hLow hcaps₀
  refine ⟨hguard.1,?_⟩
  intro hZ hAtLow hAtHigh i₀ i r hi hp₀ hw₀ hface₀ hy₀ hl₁₀ hl₂₀ seed hs bin reflected second a Label instLabel
    F hamps Row rows G hinj hLcap hTsec pool S A BD Bsource depth hpool hS hA hdepth hdepthamp T hT
    t height hheight hfreq ht hslot Wa H0 mainRadius hH0 hradius κ hshift hφ
  have hgeometry:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hZκ:0≤Z^κ:=Real.rpow_nonneg (zero_lt_one.trans hZ).le κ
  have hsrc₀:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s₀≤Z^(2:ℝ):=
    (hcaps₀.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i₀.θ i₀.w i₀.freq i₀.t₀ i₀.p
      i₀.X₁ i₀.X₂ i₀.Y₁ i₀.Y₂ i₀.hX₁ i₀.hX₂ i₀.hY₁ i₀.hY₂ i₀.same hN₀ hw₀ hface₀ hy₀ hl₁₀ hl₂₀).2.1
  by_cases hrows:Nonempty rows
  · letI:Nonempty rows:=hrows
    let c₀:=initialCanonical i₀ hH W hW hWs hZ ηanchor η₀ R₀
    let c:=initialCanonical i hH W hW hWs hZ ηanchor η₀ R₀
    have hnB:(n.B:ℝ)≤1:=by exact_mod_cast sc.geometry.B_le_one
    have hnL:1≤(n.L:ℝ):=by exact_mod_cast sc.geometry.L_gt_one.le
    have ha1:amp≤1:=by linarith [sc.geometry.a_small]
    have hallow:θ≤(n.allowance:ℝ):=by linarith [sc.loss_small,sc.allowance_pos]
    have hallow1:(n.allowance:ℝ)≤1:=by linarith [sc.geometry.a_allowance,sc.geometry.a_small]
    have hwidthlo:bcell-θ≤∑j,i.w j:=by linarith [hi.cell_lower]
    have homega:frequencyLoss Z 32 ξ+θ≤(n.allowance:ℝ):=by linarith [hguard.2.2.2.2.2,sc.loss_small,sc.allowance_pos]
    have hm0:F.m≠0:=mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero R₀ hR₀)
    have hml:goodLambda∣F.m:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
    have hm2:(2:O)∣F.m:=dvd_mul_of_dvd_left (by simp [fixedBadMask]) _
    have hQMF:F.Q≤M:=inf_le_left.trans hQM
    have hQη:F.Q≤η₀.modulus:=inf_le_right
    have hTsec':∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve 2 N (F.first (G.row u).val.1):=by
      intro u
      change F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
        (3*F.amp (G.row u).val.1.1) θ 2 N (F.first (G.row u).val.1)
      rw [hamps]
      exact hTsec u
    obtain ⟨st,hfixed,keep,select,hdata,hHigh⟩:=SelectedRegularHighPointSome.actual_point_rm_mx
      (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh poolAmp N wmin rmin εslot
      hf hc sc.mesh_nonneg hmesh hpoolAmp R₀ hR₀ hβ hβhi bound hbound J SH CH Z
      high hB0 hB1 hlam hcap0 hcap1 hparent hAtHigh rows a F second G c₀ c rfl rfl rfl rfl sc.xi_pos.le sc.xi_loss
      bcell r t amp sc.geometry.a_pos rfl ha1 hamps hN₀ hN hnB hnL hq hallow hallow1 hi.widths_nonneg hi.widths_mesh
      hi.face hi.r_nonneg hi.long_left hi.long_right hi.reference hwidthlo hi.cell_upper hbcell homega hgaps hsrc₀ hinj
      hTsec' hLcap hm0 hQ72 hml hm2 hQMF hQη pool S A depth θ BD Bsource hpool le_rfl
      hdepthamp hS hA hdepth T hT ht hslot Wa H0 mainRadius hH0 (fun l=>(hradius l).1)
      (fun l=>(hradius l).2) hguard.2.1 hguard.2.2.1 hguard.2.2.2.1 κ hshift
    simp only [show F.reflected=reflected from rfl,show F.bin=bin from rfl,
      show F.ξ=ξ from rfl,show c.p=i.p from rfl] at hHigh
    let shared:Shared_mx G M H hH η₀ Q hQM S A (highBuffer 1 1 εslot (θ/16)) (P).τ:={
      states:=st, fixed:=hfixed, keep:=keep, select:=select,
      gates:=fun u=>by
        rcases hdata u with ⟨hc',hp,hw,hbin,_,_,hprof,hkey,_⟩
        exact ⟨hc',hp,hw,hprof,hbin,hkey⟩ }
    have hpair:=High.CorrectedCentered.newton_divisor_pair_good pool S A hS hA hpool.prime
      (fun p hp=>by exact_mod_cast hpool.norm_ge_sixteen p hp)
    have havoid:=regular_original_newton_avoidance F.s pool S A Z poolAmp (poolAmp/2) mesh θ BD Bsource depth
      hpool M H i.w (fun _=>rfl) hi.widths_mesh hS hA
    have hL:=hLow.2 hZ hAtLow i₀ i r hi hp₀ seed 1 1 1 1 (fun _=>1) hs bin reflected second
      F hamps hsrc₀ rows G hinj hLcap hTsec pool S A mesh BD Bsource depth hpool hS hA hdepth hdepthamp hpair
      T hT (fun j _ I hI=>havoid j I hI) shared t height hheight hfreq (fun j _=>hslot j)
      Wa H0 mainRadius hH0 hradius κ hshift hφ
    dsimp only [shared] at hL
    have hfuse:=regular_selected_source_fusion_mx G S A T t (highBuffer 1 1 εslot (θ/16)) (n.q:ℝ) select
      (fun u=>residualWeight F.datum (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 mainRadius (poolAmp/2)) (G.row u).val)
      (fun _=>residualWeight_nonneg _ _ _) (by change (9/4:ℝ)≤9/4;rfl) (by change (9/4:ℝ)≤9/4;rfl)
      hpair (Z^κ*regularLowBudget N JL CL Cpref Cslot (forcedProfileCost F.s)
        (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
        ((i.p.control SL)^2) (1+|t|+height) Z (lowExponent n θ εslot N)) _
      (fun side=>by
        refine (hL side).trans (le_of_eq ?_)
        rw [regularLowBudget,Real.rpow_add (zero_lt_one.trans hZ)]
        ring) hHigh
    have hpc:=InitialPhysical.initial_cost_bounds M H hH W hW hWs Z (zero_lt_one.trans hZ)
      ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same N hN
    have hpaid:=hpay F.s Z ξ (1+|t|+height) i.p reflected bin hZ (by linarith only [abs_nonneg t,hheight])
      hpc.2 hguard.2.2.2.2.1 hguard.2.2.2.2.2
    have hpaid':4*regularLowBudget N JL CL Cpref Cslot (forcedProfileCost F.s)
          (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
          ((i.p.control SL)^2) (1+|t|+height) Z (lowExponent n θ εslot N)+
        pointBudget n N J θ reserve εslot wmin CH Z P SH F.s reflected bin ξ i.p≤
      Cpoint*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control (regularProfileControl SL SH))^2*(1+|t|+height)^JL*Z^(-(reserve/2)):=by
      rw [low_loss_eq];exact hpaid
    have hsplit:Z^(κ-(reserve/2))=Z^κ*Z^(-(reserve/2)):=by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)];ring_nf
    calc _ ≤ _ := hfuse
      _ = Z^κ*(4*regularLowBudget N JL CL Cpref Cslot (forcedProfileCost F.s)
            (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
            ((i.p.control SL)^2) (1+|t|+height) Z (lowExponent n θ εslot N)+
          pointBudget n N J θ reserve εslot wmin CH Z P SH F.s reflected bin ξ i.p) := by ring
      _ ≤ Z^κ*(Cpoint*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
          (i.p.control (regularProfileControl SL SH))^2*(1+|t|+height)^JL*Z^(-(reserve/2))) :=
        mul_le_mul_of_nonneg_left hpaid' hZκ
      _ = _ := by rw [hsplit];ring
  · letI:IsEmpty rows:=not_nonempty_iff.mp hrows
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    positivity

end
end QRH.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCombinedPointSome.eventually_actual_point_rm_mx
