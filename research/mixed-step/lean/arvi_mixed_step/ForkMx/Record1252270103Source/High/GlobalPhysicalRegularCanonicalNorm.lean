/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
/- Mixed step (L4/L5, F5): fork of Record1252270103Source.High.GlobalPhysicalRegularCanonicalNorm
(Hailey Collet); changes: two parents, two amplitudes, the δ-shift. `regular_canonical_joint_mx`
integrates the family `allocatedRegularFamily_mx` of the anchor `Initial.anchor_mx i₀ i`: the small-height
premise is `regular_canonical_small_mx` (with the shift `κ`), the absolute budget is
`eventually_canonical_absolute_mx`, the constants and the integration degree precede the family
(`regular_joint_of_bounded_normalized_mx`). The shift enters through the control: for `0 ≤ κ` the control
`(i.p.control controls)^2 * Z^κ` serves both the small premise and the (weaker) absolute budget, so the
conclusion is Collet's with `Z^(κ - reserve/8)`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularCanonicalNorm
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularCanonicalSmall
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularNorm
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularCanonicalAbsoluteData
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
local instance regularCanonicalNormDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
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
local instance regularCanonicalNormFinite_mx (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)


set_option maxHeartbeats 1000000 in
theorem regular_canonical_joint_mx {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ Cpoint:ℝ)(N depth degree:ℕ)
    (controls:Finset (ℕ×ℕ))(h00:(0,0)∈controls)(hf:FixedBudget reserve 100 100 1 θ)
    (hg:QRH.MixedStep.Downstream.NodeGeometry_mx n low bcell)
    (hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)
    (hpoolAmp:0<poolAmp)(hpoolAmp1:poolAmp≤1)
    (ampv:ℝ)(hampv:ampv=sourceAReal n low bcell)
    (hξ:0<ξ)(hξ1:ξ ≤ 1)(hθ:0 ≤ θ)(hθ1:θ ≤ 1)
    (hpoint:0<Cpoint)(hτ:0<τsource):
    ∃Cs:ℝ,0<Cs ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀hp:RegularPointAt_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
      bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ N degree controls Cpoint Z,
    ∀(hZ:1<Z)(i₀:Initial (α:=α₀) M H Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
      i₀.p=i.p→(∀j,0≤ i₀.w j)→
      (globalFace B₀ lam₀ cap₀).Admissible (length Z i₀.X₁) (length Z i₀.X₂) (∑j,i₀.w j) 1→
      1≤ i₀.Y₂→i₀.Y₂≤ i₀.X₁→i₀.Y₂≤ i₀.X₂→
    Fintype.card α₀ ≤ N→Fintype.card α ≤ N→
    ∀(bin:ℤ×(Fin 5→ℤ))(reflected:Bool),
    let a:=Initial.anchor_mx i₀ i hH W hW hWs hZ ηanchor η₀ R₀ 1 hR₀ (by simp) 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
    ∀{Label:Type}[Fintype Label](column:Label→a.Column)
      (hLive:∀l,column l∈firstLiveColumns
        (CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
        (fun _=>logAnnulus))
      (alloc:∀l,actualAllocations a.s.pools (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed
        (Z^a.D) Z a.ξ a.hK a.bin (column l)))
      (P:Finset (Ideal O))(ht:ℝ)(χ₀:Label→RayCharacter),
    Function.Injective (fun l=>(a.label (column l),(column l).2.1.val))→
    (∀l,frozenCoefficient (alloc l).val
      (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l))
      a.R a.s.ν a.s.W a.s.P≠0)→
    FixedCellPoolData P Z poolAmp (poolAmp/2) mesh θ 10 4 depth→
    2/(poolAmp/2) ≤ depth→(depth:ℝ)*poolAmp < 5→
    let F:=allocatedRegularFamily_mx a column hLive alloc P ampv ht N χ₀
    let H0:=fun l=>(CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l).1).H0
    let radius:=fun l=>ExceptionalPrice.literalFirstRadius reflected Z (volume a.s₀) Z ξ θ (a.label (column l))
    ∀(Wa:𝓢(ℝ,ℂ))(height:ℝ),0 ≤ height→(∀j,|i.freq j| ≤ height)→
    1+|ht|+height ≤ Z^(τsource/4)→
    ∀κ:ℝ,0 ≤ κ→ampv-poolAmp ≤ Real.logb Z (volume a.s₀)-Real.logb Z (volume a.s)+κ→
      (∀l,φ ≤ (∑j,i.w j)-∑j∈liveIndices (F.stage l).B.val,i.w j)→
    ‖∑q:F.Complete,SelectedRegularAbsolute.phase_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius
      (poolAmp/2) (regularFamilyKeep_mx F) q*
      (modifiedDatumBlock (F.datum q) (F.childModifier q.1)).value ballProfile‖ ≤
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*Z^(κ-(reserve/8)):=by
  subst hampv
  have hnB:(n.B:ℝ) ≤ 1:=by exact_mod_cast hg.B_le_one
  have hnL:1 ≤ (n.L:ℝ):=by exact_mod_cast hg.L_gt_one.le
  have hncap:(n.cap:ℝ) ≤ 1:=by exact_mod_cast hg.cap_lt_one.le
  have hamp:0<sourceAReal n low bcell:=hg.a_pos
  have hamp1:sourceAReal n low bcell≤1:=hg.a_small.le.trans (by norm_num)
  let amp:=sourceAReal n low bcell
  obtain ⟨Cs,hCs,es⟩:=regular_canonical_small_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q
    n low bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ Cpoint N depth degree controls hf hg
    hB₀ hlam₀ hcap₀ hpoolAmp hpoolAmp1 (sourceAReal n low bcell) rfl hξ hξ1 hθ hθ1 hpoint hτ
  obtain ⟨Ca,hCa,ea⟩:=eventually_canonical_absolute_mx N B₀ lam₀ cap₀ (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) ξ amp poolAmp θ
    hB₀ hlam₀ hcap₀ hnB hnL hncap hξ hξ1 hamp.le hamp1 hpoolAmp hpoolAmp1 hθ hθ1 W hW hWs
  obtain ⟨C,hC,en⟩:=regular_joint_of_bounded_normalized_mx (τsource/4) 75 reserve Cs Ca N degree
    (by positivity) (by linarith [hf.tiny,hf.positive]) hCs.le hCa.le
  refine ⟨C,hC,?_⟩
  filter_upwards [es,ea,en,InitialTruncated.eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hnB hnL hncap,
    InitialTruncated.eventually_initial_caps N B₀ lam₀ cap₀ hB₀ hlam₀ hcap₀,
    ExceptionalPrice.eventually_initial_first_geometry N B₀ lam₀ cap₀ ξ poolAmp θ
      hB₀ hlam₀ hcap₀ hξ hξ1 hpoolAmp.le hpoolAmp1 hθ hθ1,
    CenteredMomentFirstAmplificationChoice.eventually_frequency_loss 32 ξ (by norm_num) hξ,
    allocated_frequency_mx N] with Z hs ha hnZ hc hc₀ hgZ hfl hfZ
  refine ⟨hs.1,?_⟩
  have hpow:∀(x y:ℝ),0<Z→Z^(x+y)=Z^x*Z^y:=fun x y hz=>Real.rpow_add hz x y
  intro hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ hN₀ hN bin reflected a Label _ column hLive alloc P ht χ₀
    hinj hfreeze hcell hdepth hdepth5 F H0 radius Wa height hh hv hext κ hκ hshift hmargin
  have hz:=zero_lt_one.trans hZ
  have hy:1 ≤ i.Y₂:=hi.reference.symm ▸ Real.one_le_rpow hZ.le hi.r_nonneg
  have hyl:i.Y₂ ≤ i.X₁:=hi.reference.symm ▸ hi.long_left
  have hyr:i.Y₂ ≤ i.X₂:=hi.reference.symm ▸ hi.long_right
  have caps₀:=hc₀.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i₀.θ i₀.w i₀.freq i₀.t₀ i₀.p
    i₀.X₁ i₀.X₂ i₀.Y₁ i₀.Y₂ i₀.hX₁ i₀.hX₂ i₀.hY₁ i₀.hY₂ i₀.same hN₀ hw₀ hadm₀ hy₀ hyl₀ hyr₀
  have caps:=hc.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p
    i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same hN hi.widths_nonneg hi.face hy hyl hyr
  have geom:=hgZ.2 hZ M H hH W hW hWs ηanchor η₀ R₀ i₀.θ i₀.w i₀.freq i₀.t₀ i₀.p
    i₀.X₁ i₀.X₂ i₀.Y₁ i₀.Y₂ i₀.hX₁ i₀.hX₂ i₀.hY₁ i₀.hY₂ i₀.same hN₀ hw₀ hadm₀ hy₀ hyl₀ hyr₀
  have hfreq1:frequencyLoss Z 32 ξ ≤ 1:=hfl.2.2.le.trans hξ1
  have hgeom (l:Label):0<H0 l ∧ 0 ≤ radius l+6*poolAmp ∧ radius l+6*poolAmp ≤ 32 ∧
      Z^(-(32:ℝ)) ≤ F.Hmain l ∧ F.Hmain l ≤ Z^(32:ℝ):=by
    have gg:=fun j=>by
      have g:=geom a.modifier₀ reflected bin j
      have m:=mixed_main_radius_bounds_mx a.s₀ a.modifier₀ a.R a.seed Z ξ amp θ (volume a.s) hZ
        a.seed_sf (initial_plain_zero i₀.p (by norm_num) 0) (initial_plain_zero i₀.p (by norm_num) 1)
        caps₀.2.1 caps₀.2.2.2.1 caps.2.2.1 caps.2.2.2.1 hamp.le hamp1 hθ hθ1 hfreq1 reflected bin j
      exact And.intro g.1 (And.intro g.2.1 (And.intro g.2.2.1
        (And.intro g.2.2.2.2.2.1 (And.intro m.1 m.2))))
    let prop:=(fun (K:ℝ)(hK:0<K)=>∀j:FirstColumnIndex
        (CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin),
      0<(CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j.1).H0 ∧
      let rad:=ExceptionalPrice.literalFirstRadius reflected Z (volume a.s₀) Z ξ θ
        (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j)
      0 ≤ rad+6*poolAmp ∧ rad+6*poolAmp ≤ 32 ∧ (j.2.1.val.absNorm:ℝ) ≤ Z^(4:ℝ) ∧
        Z^(-(32:ℝ)) ≤ firstMainRadius reflected K (volume a.s) Z ξ (3*amp) θ
          (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j) ∧
        firstMainRadius reflected K (volume a.s) Z ξ (3*amp) θ
          (FirstFamily.firstLabel a.s₀ a.modifier₀ a.R a.seed K Z ξ hK bin j) ≤ Z^(32:ℝ))
    have base:prop Z hz:=gg
    have transport (K:ℝ)(hK:0<K)(he:K=Z):prop K hK:=by subst K;exact base
    have hl:=transport (Z^a.D) a.hK (by change Z^(1:ℝ)=Z;exact Real.rpow_one Z) (column l)
    exact ⟨hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.2.1,hl.2.2.2.2.2⟩
  have hHlo(l:Label):Z^(-(32:ℝ)) ≤ F.Hmain l:=(hgeom l).2.2.2.1
  have hHhi(l:Label):F.Hmain l ≤ Z^(32:ℝ):=(hgeom l).2.2.2.2
  have hchild(l:Label):sourceRadius (F.input l) ≤ Z^(2:ℝ):=
    (InitialPhysical.child_source_radius_le F.s (F.stage l).common F.R (F.stage l).B
      (F.stage l).τ (F.stage l).t
      (fun _=>by change (1:ℝ) ≤ 2;norm_num)
      (fun j=>by change 1 ≤ Z^(i.w j);exact Real.one_le_rpow hZ.le (hi.widths_nonneg j))
      (by change (0:ℝ) ≤ 9/4;norm_num) (by change (0:ℝ) ≤ 9/4;norm_num)).trans caps.2.1
  have hZκ:1 ≤ Z^κ:=Real.one_le_rpow hZ.le hκ
  have hsmall(second:Bool)(t u:ℝ)(hpair:(1+‖t‖)*(1+‖u‖) ≤ Z^(τsource/4)):
      modifiedSecondNormalizedSum second F.datum (fun q=>F.childModifier q.1)
        (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) t u ≤
        Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
          ((i.p.control controls)^2*Z^κ)*(1+|ht|+height)^degree*((1+‖t‖)*(1+‖u‖))^degree*Z^(-(reserve/4)):=by
    have h:=hs.2 hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ hN₀ hN bin reflected column hLive alloc P ht χ₀ hinj
      hfreeze hcell hdepth hdepth5 Wa height hh hv hext κ hshift hmargin second t u hpair
    refine h.trans (le_of_eq ?_)
    have e:Z^(κ-(reserve/4))=Z^κ*Z^(-(reserve/4)):=by
      rw [sub_eq_add_neg (κ) (reserve/4),hpow κ (-(reserve/4)) hz]
    have hm:mellinPairHeight t u=(1+‖t‖)*(1+‖u‖):=rfl
    rw [e,hm]
    ring
  have hab:=ha.2 hZ M H hH i₀ i ηanchor η₀ R₀ hR₀ bin reflected Q hN₀ hN hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀
    hi.widths_nonneg hi.face hy hyl hyr column hLive alloc P ht χ₀ hinj hcell.nonempty mesh θ 10 depth hcell Wa
  have hcontrol:(i.p.control {(0,0)})^2 ≤ (i.p.control controls)^2:=
    pow_le_pow_left₀ (i.p.control_nonneg _) (CenteredMomentEnergyBandMonotonicity.profile_control_mono i.p
      (Finset.singleton_subset_iff.mpr h00)) 2
  have hab':secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) ≤
        Ca*((i.p.control controls)^2*Z^κ)*Z^(75:ℝ):=by
    apply hab.trans
    have h75:0 ≤ Z^(75:ℝ):=Real.rpow_nonneg hz.le _
    have hc2:0 ≤ (i.p.control controls)^2:=sq_nonneg _
    calc
      _≤Ca*(i.p.control controls)^2*Z^(75:ℝ):=by gcongr
      _≤Ca*((i.p.control controls)^2*Z^κ)*Z^(75:ℝ):=by
        have : (i.p.control controls)^2 ≤ (i.p.control controls)^2*Z^κ := le_mul_of_one_le_right hc2 hZκ
        gcongr
  have e:Z^(κ-(reserve/8))=Z^κ*Z^(-(reserve/8)):=by
    rw [sub_eq_add_neg (κ) (reserve/8),hpow κ (-(reserve/8)) hz]
  rw [e]
  calc
    _≤C*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        ((i.p.control controls)^2*Z^κ)*(1+|ht|+height)^degree*Z^(-(reserve/8)):=
      hnZ.2 a F caps₀.2.1 hHlo hHhi
        (hfZ.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hθ hamp.le) hchild
        Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2) ((i.p.control controls)^2*Z^κ) (1+|ht|+height)
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hz.le _)) (by linarith [abs_nonneg ht]) hsmall hab'
    _=_:=by ring
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_canonical_joint_mx
