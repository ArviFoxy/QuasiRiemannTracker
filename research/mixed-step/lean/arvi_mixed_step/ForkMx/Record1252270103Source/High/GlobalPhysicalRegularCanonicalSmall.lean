/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F5): fork of Record1252270103Source.High.GlobalPhysicalRegularCanonicalSmall
(Hailey Collet, Apache-2.0); changes: two parents, two amplitudes, the δ-shift. `regular_canonical_small_mx`
applies `regular_small_normalized_mx` to the family `allocatedRegularFamily_mx` of the anchor
`Initial.anchor_mx i₀ i`. The first layer `i₀` carries the face hypotheses of `eventually_initial_caps` on
`globalFace B₀ lam₀ cap₀`, the second layer `i` the `InitialGeometry` at the node `n`. The first geometry
(`H0`, `radius`, read at `volume a.s₀`) is Collet's `eventually_initial_first_geometry` on `i₀`; the MAIN radius
`Hmain` (read at `volume a.s`) is bounded by `mixed_main_radius_bounds_mx`. The pool depth is a parameter and
the node geometry enters through `0 < sourceAReal n low bcell ≤ 1`, `0 < poolAmp ≤ 1`. The conclusion carries
`Z^(κ - reserve/4)` for every `κ` with `sourceAReal - poolAmp ≤ logb Z (volume a.s₀) - logb Z (volume a.s) + κ`
and every per-label frozen margin `φ`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularCanonicalSmall
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularSmall
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularPoints
import Submissions.arvi_mixed_step.Downstream.Node
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
local instance regularCanonicalDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
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
local instance regularCanonicalFinite_mx (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem regular_canonical_small_mx {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ Cpoint:ℝ)(N depth degree:ℕ)
    (controls:Finset (ℕ×ℕ))(hf:FixedBudget reserve 100 100 1 θ)
    (hg:QRH.MixedStep.Downstream.NodeGeometry_mx n low bcell)
    (hB₀:B₀≤1)(hlam₀:1≤lam₀)(hcap₀:cap₀≤1)
    (hpoolAmp:0<poolAmp)(hpoolAmp1:poolAmp≤1)
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
    let F:=allocatedRegularFamily_mx a column hLive alloc P (sourceAReal n low bcell) ht N χ₀
    let H0:=fun l=>(CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l).1).H0
    let radius:=fun l=>ExceptionalPrice.literalFirstRadius reflected Z (volume a.s₀) Z ξ θ (a.label (column l))
    ∀(Wa:𝓢(ℝ,ℂ))(height:ℝ),0 ≤ height→(∀j,|i.freq j| ≤ height)→
    1+|ht|+height ≤ Z^(τsource/4)→
    ∀κ:ℝ,sourceAReal n low bcell-poolAmp ≤ Real.logb Z (volume a.s₀)-Real.logb Z (volume a.s)+κ→
      (∀l,φ ≤ (∑j,i.w j)-∑j∈liveIndices (F.stage l).B.val,i.w j)→
    ∀(second:Bool)(t u:ℝ),mellinPairHeight t u ≤ Z^(τsource/4)→
    modifiedSecondNormalizedSum second F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) t u ≤
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*(mellinPairHeight t u)^degree*Z^(κ-(reserve/4)):=by
  have hnB:(n.B:ℝ) ≤ 1:=by exact_mod_cast hg.B_le_one
  have hnL:1 ≤ (n.L:ℝ):=by exact_mod_cast hg.L_gt_one.le
  have hncap:(n.cap:ℝ) ≤ 1:=by exact_mod_cast hg.cap_lt_one.le
  have hamp:0<sourceAReal n low bcell:=hg.a_pos
  have hamp1:sourceAReal n low bcell≤1:=hg.a_small.le.trans (by norm_num)
  let amp:=sourceAReal n low bcell
  obtain ⟨Cs,hCs,es⟩:=regular_small_normalized_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
    bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ (initialSlotBound W hW hWs) Cpoint N depth
    degree controls hf (initialSlotBound_ge_one W hW hWs) hpoint hτ hpoolAmp
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [es,InitialTruncated.eventually_initial_caps N (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) hnB hnL hncap,
    InitialTruncated.eventually_initial_caps N B₀ lam₀ cap₀ hB₀ hlam₀ hcap₀,
    ExceptionalPrice.eventually_initial_first_geometry N B₀ lam₀ cap₀ ξ poolAmp θ
      hB₀ hlam₀ hcap₀ hξ hξ1 hpoolAmp.le hpoolAmp1 hθ hθ1,
    CenteredMomentFirstAmplificationChoice.eventually_frequency_loss 32 ξ (by norm_num) hξ,
    allocated_frequency_mx N,
    eventually_ge_atTop ((9/4:ℝ)^2)] with Z hs hc hc₀ hgZ hfl hfZ hlarge
  refine ⟨hs.1,?_⟩
  intro hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ hN₀ hN bin reflected a Label _ column hLive alloc P ht χ₀
    hinj hfreeze hcell hdepth hdepth5 F H0 radius Wa height hh hv hext κ hshift hmargin second t u hpair
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
  have hplain:(9/4:ℝ)^2*(F.s.X₁*F.s.X₂) ≤ Z^(2:ℝ):=by
    have hcorners:=SelectedRegularCanonicalGeometry.initial_long_corners M H hH W hW hWs Z hZ
      ηanchor η₀ R₀ i.θ i.w i.freq i.t₀ i.p i.X₁ i.X₂ i.Y₁ i.Y₂ i.hX₁ i.hX₂ i.hY₁ i.hY₂ i.same
      (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) r hnB hnL hi.widths_nonneg hi.face hi.r_nonneg hi.long_left hi.long_right hi.reference
    calc
      _ ≤ Z*Z:=mul_le_mul hlarge hcorners.2.2.2.2 (mul_pos i.hX₁ i.hX₂).le hz.le
      _=Z^(2:ℝ):=by rw [Real.rpow_two,pow_two]
  have hcoeff(j:α)(I:Ideal O)(hI:I∈F.s.slots j):‖restoredSlotCoeff F.s j I‖ ≤ initialSlotBound W hW hWs:=
    F.s.coefficient_bound j I hI
  have hnorm(j:α)(I:Ideal O)(hI:I∈F.s.slots j):(I.absNorm:ℝ) ≤ 2*F.s.P j:=by
    exact (Collision.primePool_norm_le M H (Z^(i.w j))
      (Real.rpow_nonneg hz.le _) I hI).2
  exact hs.2 hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ 1 (by simp) bin reflected F hN hinj hfreeze
    caps₀.2.1 caps.2.1 hHlo hHhi
    (hfZ.2 a column hLive alloc P amp ht χ₀ rfl hξ.le hξ1 hθ hamp.le)
    (SelectedRegularAbsolute.column_cap_irrel _ _ _ _ caps.2.2.2.2)
    (fun _=>by change (1:ℝ) ≤ 2;norm_num)
    (fun j=>by change 1 ≤ Z^(i.w j);exact Real.one_le_rpow hZ.le (hi.widths_nonneg j))
    (by change (0:ℝ) ≤ 9/4;norm_num) (by change (0:ℝ) ≤ 9/4;norm_num) P hcell
    (fun p hp j I hI=>hcell.avoids_canonical_slot M H (i.w j) (hi.widths_mesh j) p hp I hI)
    hdepth hdepth5 hplain hcoeff hnorm (i.p.profile 0) (i.p.profile 1) Wa rfl rfl le_rfl le_rfl H0 radius
    (fun l=>(hgeom l).1) (fun l=>⟨(hgeom l).2.1,(hgeom l).2.2.1⟩)
    (fun _=>rfl) (fun _=>rfl) ht height hh hv (fun _=>rfl) hext κ hshift hmargin second t u hpair
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_canonical_small_mx
