/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F3): fork of Record1252270103Source.Admission.SelectedRegularLowPointData;
changes: two parents (`Initial.anchor_mx` from a first-layer initial datum `i₀` and a second-layer
initial datum `i`), node facts `NodeGeometry_mx` in place of `RealGeometry`/`ParentGood n`
(`Scalar_mx`), `Shared_mx`/`radial_mx` over `Selected_mx`. `Initial`, `InitialGeometry`,
`step_le_quarter`, `modifier_radial` and `missing_norm_from_key_caps` are reused verbatim. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularLowPointData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.PhysicalLowGuard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open CenteredMomentSourceMass
open CenteredMomentEnergyBands
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle61HighGeometry Record12518109Natural
open Cycle61Moment Cycle61InitialMass LocalMoment CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentPrimeSlot CenteredMomentEnergyState
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open Record12518109Raw Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open SelectedSecondKeyCaps SelectedSecondNatural
open SelectedRegularSourceData SelectedHighCofactorFamily High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance selectedLowPointDataDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance selectedLowPointDataFinite_mx (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)


namespace Initial
variable {α₀ α:Type}[Fintype α₀][Fintype α]{rayM:Ideal O}[NeZero rayM]{H:Subgroup (O⧸rayM)ˣ}{Z:ℝ}

/-- The two-parent anchor of a first-layer initial datum `i₀` and a second-layer initial datum `i`
(for the transfer residual, the restriction of `i₀` to the slots off the transferred block). -/
def anchor_mx (i₀:Initial (α:=α₀) rayM H Z)(i:Initial (α:=α) rayM H Z)
    (hH:RayOrthogonality.globalUnits rayM≤H)(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)
    (hsW:Function.support W⊆Set.Icc (1:ℝ) 2)(hZ:1<Z)(η η₀:Character)(R₀ seed:Ideal O)
    (hR₀:R₀≠0)(hs:Squarefree seed)(A₁ A₂ D K:Ideal O)(Fm:Ideal O→ℂ)
    (ξ θloss:ℝ)(bin:ℤ×(Fin 5→ℤ))(reflected:Bool)(Q:Ideal O):Anchor_mx α₀ α Z where
  s₀:=i₀.input hH W hW hsW hZ η η₀ R₀
  modifier₀:=Collision.markedSourceModifier A₁ A₂ D K Fm
  s:=i.input hH W hW hsW hZ η η₀ R₀
  R:=R₀
  seed:=seed
  R_ne:=hR₀
  seed_sf:=hs
  zero₁₀:=initial_plain_zero i₀.p (by norm_num) 0
  zero₂₀:=initial_plain_zero i₀.p (by norm_num) 1
  zero₁:=initial_plain_zero i.p (by norm_num) 0
  zero₂:=initial_plain_zero i.p (by norm_num) 1
  D:=1
  ξ:=ξ
  reserve:=θloss
  hZ:=hZ
  hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1
  bin:=bin
  reflected:=reflected
  Q:=internalQ Q η₀
  m:=fixedBadMask*idealGenerator R₀
end Initial

open QRH.MixedStep.Downstream in
/-- Collet's `eventually_low_scalar` at an abstract node: `NodeGeometry_mx` replaces
`RealGeometry`/`ParentGood n` (only `parent_budget_room` and `1 < n.L` are used). -/
theorem eventually_low_scalar_mx (n low:Source)(b θloss ξ:ℝ)
    (hg:NodeGeometry_mx n low b)(hlow:ParentGood low)
    (ha:0<(n.allowance:ℝ))(hθ:0<θloss)(hθsmall:θloss≤(n.allowance:ℝ)/16)
    (hθstep:θloss≤PhysicalLowGuard.step n)(hξ:0<ξ)(hξstep:ξ≤PhysicalLowGuard.step n)(N:ℕ):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      (0≤frequencyLoss Z 32 ξ ∧ frequencyLoss Z 32 ξ≤(n.allowance:ℝ)/4) ∧
      let annular:=3*(N:ℝ)*Real.logb Z 2+2*Real.logb Z (max 1 (9/4:ℝ))+2*θloss
      0≤annular ∧ annular≤(n.allowance:ℝ)/4 ∧
      ∀width:ℝ,width≤PhysicalLowGuard.step n→
        annular+(low.B:ℝ)*frequencyLoss Z 32 ξ+2*(n.allowance:ℝ)≤
          (low.B:ℝ)*sourceFReal n low b-PhysicalLowReserve.plainBudget n b width-b:=by
  have hL:0≤(n.L:ℝ):=by exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<1) hg.L_gt_one).le
  have hB0:0≤(low.B:ℝ):=by exact_mod_cast hlow.1.le
  have hB1:(low.B:ℝ)≤1:=by exact_mod_cast hlow.2.1
  filter_upwards [PhysicalLowGuard.eventually_geometry_guard_mx n low N 2 (9/4) ξ ha hL hB0 hB1
    (by norm_num) hξ hξstep,PhysicalLowGuard.eventually_fixed_losses n N 2 (9/4) ξ ha (by norm_num) hξ hξstep,
    PhysicalLowGuard.eventually_logarithmic_loss N 2 (9/4) ((n.allowance:ℝ)/8) (by norm_num) (by positivity)]
      with Z hgZ hf hl
  refine ⟨hgZ.1,⟨hf.2.2.1,hf.2.2.2.trans (step_le_quarter n ha.le hL)⟩,?_,?_,?_⟩
  · linarith [hl.2.1]
  · linarith [hl.2.2]
  · intro width hw
    exact hgZ.2 b hg (PhysicalLowReserve.plainBudget n b width) (sourceFReal n low b) b
      width θloss (frequencyLoss Z 32 ξ) θloss hθ.le hf.2.2.1 hw hθstep hf.2.2.2 hθstep
      le_rfl (by linarith [hf.2.2.1]) le_rfl

open QRH.MixedStep.Downstream in
/-- Collet's `Scalar` at an abstract node: `NodeGeometry_mx n low b` replaces
`RealGeometry Kgraph n low b` and `ParentGood n`. -/
structure Scalar_mx (n low:Source)(b θloss mesh ξ width:ℝ):Prop where
  geometry : NodeGeometry_mx n low b
  low_parent : ParentGood low
  allowance_pos : 0<(n.allowance:ℝ)
  loss_pos : 0<θloss
  loss_small : θloss≤(n.allowance:ℝ)/16
  loss_step : θloss≤PhysicalLowGuard.step n
  xi_pos : 0<ξ
  xi_loss : ξ≤θloss
  mesh_nonneg : 0≤mesh
  mesh_small : mesh≤(n.allowance:ℝ)/4
  width_nonneg : 0≤width
  width_step : width≤PhysicalLowGuard.step n

structure Shared_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
    {F:Family_mx a Label}{rows:Finset Row}{second:Bool}(G:Selected_mx F Row rows second)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (η₀:Character)(Q:Ideal O)(hQM:Q≤M)(S A:Finset (Ideal O))(e τsource:ℝ) where
  states : rows→NaturalState Z 20 2
  fixed : ∀u,(states u).fixedModulus=internalQ Q η₀
  keep : ∀u,(states u).radial.keep (G.z u)
  select : rows→BufferIndex e
  gates : ∀u,(states u).character=G.τ u ∧
    (states u).puncture=Selection.puncture (G.sel u)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2) ∧
    (states u).width≤40 ∧
    (states u).radial.profile (‖eisEmbedding (G.z u)‖^2/(states u).radial.scale)≠0 ∧
    RetainedZeroBin M H hH (states u) η₀ ((fixed u).trans_le (inf_le_left.trans hQM))
      ((fixed u).trans_le inf_le_right) (G.z u) (keep u) e (Z^τsource) (select u) ∧
    KeyCaps (G.key u) Z 6
      (Real.logb Z ((firstSourceMissing (!F.reflected) (G.key u).val.1).absNorm:ℝ))

def radial_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
    {F:Family_mx a Label}{rows:Finset Row}{second:Bool}(G:Selected_mx F Row rows second)
    (n low:Source)(b:ℝ)(u:rows):ℝ:=
  sourceFReal n low b-max (labelD F.reflected (F.first (G.row u).val.1) Z-
    labelC F.reflected (F.first (G.row u).val.1) Z) 0-frequencyLoss Z 32 F.ξ

/-- The literal radial bound of the key, with two parents: the label is the first layer's, the
MAIN Fourier scale and the coordinates are read at the second-layer volume `volume F.s`. -/
theorem eventually_selected_frequency_mx (θloss:ℝ)(N:ℕ)(hθ:0<θloss):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
      (n low:Source)(b:ℝ)(A₁ A₂ D K:Ideal O)(Fm:Ideal O→ℂ),
      F.D=1→F.reserve=θloss→F.modifier₀=Collision.markedSourceModifier A₁ A₂ D K Fm→F.ξ≤θloss→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*sourceAReal n low b) F.reserve 2 N (F.first (G.row u).val.1))→
      ∀u,max (labelD F.reflected (F.first (G.row u).val.1) Z-
        labelC F.reflected (F.first (G.row u).val.1) Z) 0≤labelC F.reflected (F.first (G.row u).val.1) Z ∧
      radial_mx G n low b u=childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
        (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
        Z 1 (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ θloss θloss) θloss 2 ∧
      rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(radial_mx G n low b u):=by
  filter_upwards [FirstFamily.eventual_literal_high_frequency_mx 2 θloss N (by norm_num) hθ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α₀ α Label Row instα₀ instα instLabel a F rows second G n low b A₁ A₂ D K Fm hD hreserve hmodifier hξ hT u
  have hrad:(G.datum u).radius=frequencyRadius
      (firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ (3*sourceAReal n low b)
        F.reserve 2 N (FirstFamily.firstLabel F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (G.column u))) Z F.ξ:=by
    change frequencyRadius (F.Tsec (G.row u).val.1.1) Z F.ξ=_
    rw [hT u]
    rfl
  have hf:=hZ.2 F.reflected second F.s₀ F.modifier₀ F.R F.seed F.D F.ξ F.hK F.bin
    (G.column u) F.datum F.first (G.row u) rfl (volume F.s) (sourceAReal n low b) F.reserve θloss
    (CenteredMomentAmplificationChildInput.volume_pos F.s) hξ hrad
  have hg:=modifier_radial n low b F.s₀ F.modifier₀ A₁ A₂ D K F.R F.seed Fm
    (Z^F.D) Z F.ξ F.hK F.hZ F.bin hmodifier (G.column u) F.reflected second (G.datum u).C (G.datum u).D
    (G.datum u).inactive (Real.logb Z (volume F.s)) F.reserve θloss θloss
  have hg':max (labelD F.reflected (F.first (G.row u).val.1) Z-labelC F.reflected (F.first (G.row u).val.1) Z) 0≤
      labelC F.reflected (F.first (G.row u).val.1) Z ∧
      childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
        (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
        Z 1 (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ θloss θloss) θloss 2=radial_mx G n low b u:=by
    simpa only [Family_mx.first,Selected_mx.column,Anchor_mx.label,hreserve,
      add_sub_cancel_right,radial_mx] using hg
  refine ⟨hg'.1,hg'.2.symm,?_⟩
  change rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(
    childHighCoordinates (actualHighCoordinates F.reflected (!F.reflected) second
      (F.first (G.row u).val.1) (G.datum u).C (G.datum u).D (G.datum u).inactive
      Z F.D (Real.logb Z (volume F.s)) (sourceAReal n low b) F.ξ F.reserve θloss) θloss 2) at hf
  rw [hD,hreserve,hg'.2] at hf
  exact hf

/-- Two parents: the first common ideal is capped through the first layer (`hsource₀`), the second
through the second-layer child (`hsource`, slot caps of `F.s`). -/
theorem selected_common_norm_caps_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
    (F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
    (hsource₀:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s₀≤Z^(2:ℝ))
    (hsource:CenteredMomentOriginalCommonHarmonic.sourceRadius F.s≤Z^(2:ℝ))
    (hhi:∀i,1≤F.s.hi i)(hP:∀i,1≤F.s.P i)(hb₁:0≤F.s.b₁)(hb₂:0≤F.s.b₂)
    : ∀u,
      ((if F.reflected then (F.first (G.row u).val.1).1.2 else (F.first (G.row u).val.1).1.1).absNorm:ℝ)≤Z^(2:ℝ) ∧
      ((if second then (G.datum u).D else (G.datum u).C).absNorm:ℝ)≤Z^(2:ℝ):=by
  have hchild(l:Label):CenteredMomentOriginalCommonHarmonic.sourceRadius (F.input l)≤Z^(2:ℝ):=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t hhi hP hb₁ hb₂).trans hsource
  intro u
  constructor
  · have hc:=High.CoupledFirst.actual_geometry_norm_caps F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ 2
      F.seed_sf F.zero₁₀ F.zero₂₀ hsource₀ (G.column u).1.val
    cases hr:F.reflected
    · exact (hc 0).2
    · exact (hc 1).2
  · have hc:=SelectedSecondKeyCaps.regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed
      F.Hmain F.Tsec Z F.ξ CenteredMomentFirstAmplificationChoice.ballProfile F.childSeed_sf
      (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (G.row u).val.1
    cases second
    · exact hc.1.trans (hchild (G.row u).val.1.1)
    · exact hc.2.trans (hchild (G.row u).val.1.1)

end
end QRH.Record1252270103Source.Admission.SelectedRegularLowPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.eventually_low_scalar_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.eventually_selected_frequency_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowPoint.selected_common_norm_caps_mx
