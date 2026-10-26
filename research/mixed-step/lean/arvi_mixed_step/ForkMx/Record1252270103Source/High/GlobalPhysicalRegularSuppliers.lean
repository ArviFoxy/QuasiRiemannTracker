/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F5): fork of Fork.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
(PR 76 fork of Hailey Collet's module); changes: two parents, two amplitudes, node price
as a hypothesis.
`regular_point_supplier_rm_mx`: PR 76's `regular_supplier_some_rm` up to the point supplier. For
every first-layer type `α₀` and second-layer type `α` with `card α ≤ card α₀`, and every ambient
datum, the constants of `RegularPointAt_mx` at the (virtual) node `n` exist, with `N = card α₀`.
The cardinality budget, the radial support and the counting setup are chosen inside, as in PR 76.
The node facts are `Scalar_mx`, the node price and the LOW mesh; the first layer is the face
`globalFace B₀ lam₀ cap₀`; the pool is at `poolAmp`. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularPoints
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
local instance regularSuppliersDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open Record1252270103StepScalar QRH.Record1252270103Graph CenteredMomentLogDyadic
open SelectedRegularCanonicalAbsolute
local instance regularSuppliersFinite_mx (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- **The two-parent point supplier at a node** (PR 76's `regular_supplier_some_rm`, before
`regular_supplier_of_points`). -/
theorem regular_point_supplier_rm_mx (n low high:Source)(bcell φ reserve θ mesh ξ width poolAmp:ℝ)
    (B₀ lam₀ cap₀:ℝ)(hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)
    (hf:FixedBudget reserve 100 100 1 θ)(sc:Scalar_mx n low bcell θ mesh ξ width)(hpoolAmp:0<poolAmp)
    (hmesh:100*mesh≤θ)(hwidth:width≤θ)(hbcell:bcell≤1)
    (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))
    (hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
    (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)
    (hLowMesh:mesh≤regularLowMesh_mx n low bcell φ θ hprice sc.low_parent sc.allowance_pos hq hq1 hG hf.positive)
    (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)
    (hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    ∀(α₀ α:Type)[Fintype α₀][DecidableEq α₀][Fintype α],Fintype.card α≤Fintype.card α₀→
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
      (ηanchor η₀:Character)(Q:Ideal O),Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→∀(R₀:Ideal O)(hR₀:R₀≠0),
    ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
    ∃C τsource:ℝ,0<C ∧ 0<τsource ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      RegularPointAt_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
        bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ (Fintype.card α₀) degree controls C Z:=by
  intro α₀ α _ _ _ hcard M _ H hH W hW hWs ηanchor η₀ Q hQM hQ hQt hQ72 R₀ hR₀
  obtain ⟨wmin,rmin,εslot,hc⟩:=cardinality_loss_exists θ 100 100 1 1 hf.positive
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Fintype.card α₀)
  obtain ⟨bRad₀,hbRad₀,hsRad⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bRad:=max 2 bRad₀
  have hbRad:2≤bRad:=le_max_left _ _
  have hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad:=
    by
      intro x hx
      change x≤bRad
      exact (show x≤bRad₀ from hsRad hx).trans (le_max_right 2 bRad₀)
  let setup:=OAI.SevenEighths.LocalMoment.canonicalDensityCountingSetup
  exact regular_some_point_source_rm_mx (α₀:=α₀) (α:=α)
    (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n) (low:=low)
    (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (bcell:=bcell) (φ:=φ) (reserve:=reserve) (θ:=θ) (mesh:=mesh) (ξ:=ξ)
    (width:=width) (poolAmp:=poolAmp) (N:=Fintype.card α₀) (wmin:=wmin) (rmin:=rmin) (εslot:=εslot)
    (hf:=hf) (hc:=hc) (sc:=sc) (hpoolAmp:=hpoolAmp) (hmesh:=hmesh) (hwidth:=hwidth) (hbcell:=hbcell)
    (hr:=hr) (hfee:=hfee) (hq:=hq) (R₀:=R₀) (hR₀:=hR₀) (Q:=Q) (hQM:=hQM)
    (hQ72:=hQ72) (hβ:=hβ) (hβhi:=hβhi) (hq1:=hq1) (hG:=hG) (hprice:=hprice) (hLowMesh:=hLowMesh)
    (hQ:=hQ) (hQt:=hQt) (B₀:=B₀) (lam₀:=lam₀) (cap₀:=cap₀) (hB₀:=hB₀) (hlam₀:=hlam₀) (hcap₀:=hcap₀)
    (hN₀:=le_refl _) (hN:=hcard) high hB0 hB1 hlam hcap0 hcap1 hparent hgaps

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_point_supplier_rm_mx
