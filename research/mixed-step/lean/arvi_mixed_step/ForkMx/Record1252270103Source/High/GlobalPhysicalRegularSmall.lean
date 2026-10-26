/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F5): fork of Record1252270103Source.High.GlobalPhysicalRegularSmall
(Hailey Collet, Apache-2.0); changes: two parents, two amplitudes, the δ-shift. The point source is the
lead's `RegularPointAt_mx` (first layer `i₀` with the face hypotheses on `globalFace B₀ lam₀ cap₀`, second
layer `i` with `InitialGeometry` at the node); the pool, its depth and the ball factor sit at `poolAmp`,
`F.amp = sourceAReal n low bcell`. `∀ κ, hshift → (frozen margins per label) →` precede the Mellin
heights, and the bound carries `Z^(κ - reserve/4)`: the point factor `Z^κ` rides in the geometry factor
of `regular_finite_normalized_mx`. The parent cap splits into `sourceRadius F.s₀ ≤ Z^2` (first layer) and
`sourceRadius F.s ≤ Z^2` (second layer). -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSmall
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularPoints
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularFinite
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularCofactorBridge
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
local instance regularSmallDecEq_mx {ι : Type*} : DecidableEq ι := Classical.decEq _
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
theorem regular_small_normalized_mx {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ Bslot Cpoint:ℝ)(N depth degree:ℕ)
    (controls:Finset (ℕ×ℕ))(hf:FixedBudget reserve 100 100 1 θ)
    (hslot:1≤Bslot)(hpoint:0<Cpoint)(hτ:0<τsource)(hpoolAmp:0<poolAmp):
    ∃Cs:ℝ,0<Cs ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀hp:RegularPointAt_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
      bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ N degree controls Cpoint Z,
    ∀(hZ:1<Z)(i₀:Initial (α:=α₀) M H Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
      i₀.p=i.p→(∀j,0≤ i₀.w j)→
      (globalFace B₀ lam₀ cap₀).Admissible (length Z i₀.X₁) (length Z i₀.X₂) (∑j,i₀.w j) 1→
      1≤ i₀.Y₂→i₀.Y₂≤ i₀.X₁→i₀.Y₂≤ i₀.X₂→
    ∀(seed:Ideal O)(hs:Squarefree seed)(bin:ℤ×(Fin 5→ℤ))(reflected:Bool),
    let a:=Initial.anchor_mx i₀ i hH W hW hWs hZ ηanchor η₀ R₀ seed hR₀ hs 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
    ∀{Label:Type}[Fintype Label](F:Family_mx a Label),
    Fintype.card α≤N→
    Function.Injective (fun l=>(a.label (F.column l),F.childSeed l))→
    (∀l,frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P≠0)→
    sourceRadius F.s₀≤Z^(2:ℝ)→sourceRadius F.s≤Z^(2:ℝ)→
    (∀l,Z^(-(32:ℝ))≤F.Hmain l)→(∀l,F.Hmain l≤Z^(32:ℝ))→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^(4:ℝ))→
    (∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))→
    (∀j,1≤F.s.hi j)→(∀j,1≤F.s.P j)→0≤F.s.b₁→0≤F.s.b₂→
    ∀(P:Finset (Ideal O)),
    FixedCellPoolData P Z poolAmp (poolAmp/2) mesh θ 10 4 depth→
    (∀p∈P,∀j I,I∈F.s.slots j→¬p∣I)→
    2/(poolAmp/2)≤depth→(depth:ℝ)*poolAmp<5→
    (9/4:ℝ)^2*(F.s.X₁*F.s.X₂)≤Z^(2:ℝ)→
    (∀j,∀p∈F.s.slots j,‖restoredSlotCoeff F.s j p‖≤Bslot)→
    (∀j,∀p∈F.s.slots j,(p.absNorm:ℝ)≤2*F.s.P j)→
    ∀(W₁ W₂ Wa:𝓢(ℝ,ℂ)),F.s.W₁=(W₁:ℝ→ℂ)→F.s.W₂=(W₂:ℝ→ℂ)→
    F.s.b₁≤9/4→F.s.b₂≤9/4→
    ∀(H0 radius:Label→ℝ),(∀l,0<H0 l)→
    (∀l,0≤radius l+6*poolAmp ∧ radius l+6*poolAmp≤32)→
    (∀l,F.amp l=sourceAReal n low bcell)→
    (∀l,F.Tsec l=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
      (3*sourceAReal n low bcell) θ 2 N (a.label (F.column l)))→
    ∀(ht height:ℝ),0≤height→(∀j,|i.freq j|≤height)→(∀l,(F.stage l).t=ht)→
    1+|ht|+height≤Z^(τsource/4)→
    ∀κ:ℝ,sourceAReal n low bcell-poolAmp≤Real.logb Z (volume F.s₀)-Real.logb Z (volume F.s)+κ→
      (∀l,φ≤(∑j,i.w j)-∑j∈liveIndices (F.stage l).B.val,i.w j)→
    ∀(second:Bool)(t u:ℝ),mellinPairHeight t u≤Z^(τsource/4)→
    modifiedSecondNormalizedSum second F.datum (regularModifier_mx F P)
      (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) t u≤
      Cs*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (i.p.control controls)^2*(1+|ht|+height)^degree*(mellinPairHeight t u)^degree*Z^(κ-(reserve/4)):=by
  obtain ⟨Cf,hCf,ef⟩:=regular_finite_normalized_mx reserve θ Bslot Cpoint N depth degree hf hslot hpoint
  refine ⟨Cf*mellinShiftConstant^degree,by unfold mellinShiftConstant;positivity,?_⟩
  filter_upwards [ef,eventually_nested_source_height τsource hτ] with Z hfin hheight
  refine ⟨hfin.1,?_⟩
  intro hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ seed hs bin reflected a Label _ F hN hinj hfreeze hsource₀ hsource
    hHlo hHhi hfreq hpool hhi hP hb1 hb2 P hcell havoid hdepth hdepth5 hplain hcoeff hnorm W1 W2 Wa hW1 hW2 hb1' hb2'
    H0 radius hH0 hrad hamp hfourier ht height hh hfreqs hstage hext κ hshift hmargin second t u hpair
  have hz:0<Z:=zero_lt_one.trans hZ
  let shifted:=mellinShift ht second t u
  have hbound:1+|shifted|+height≤Z^τsource:=by
    have h:=hheight.2 ht height 0 0 t u false second hh
    simp only [mellinPairHeight,norm_zero,add_zero,mul_one,one_mul,mellinShift] at h
    simpa [shifted,mellinShift] using h hext hpair
  have hg:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin:=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hgκ:0≤geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*Z^κ:=
    mul_nonneg hg (Real.rpow_nonneg hz.le _)
  have hcof:RegularCofactorBound_mx F second P depth
      (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) t u (9/4) 4
      (Cpoint*(geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*Z^κ)*
        (i.p.control controls)^2*(1+|shifted|+height)^degree*Z^(-(reserve/2))):=by
    apply regular_cofactor_of_centered_mx F second P depth
      (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2)) ht t u
      _ (by positivity) hstage
    intro Row _ rows _ G hkey hL hLcap hψ S hS A hA T hT
    have hS':S⊆P:=Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hA':A⊆S:=Finset.mem_powerset.mp hA
    have hpt:=hp hZ i₀ i r hi hp0 hw₀ hadm₀ hy₀ hyl₀ hyr₀ seed hs bin reflected second F hamp rows G hkey hLcap
      (fun r=>hfourier (G.row r).val.1.1) P S A 10 4 depth hcell hS' hA'
      (Finset.mem_filter.mp hS).2 hdepth5 T hT shifted height hh
      (fun j _=>hfreqs j) (by linarith [abs_nonneg shifted])
      (fun j=>(abs_add_le shifted (i.freq j)).trans (by linarith [hfreqs j]))
      Wa H0 radius hH0 hrad κ hshift (fun u=>by rw [G.first_allocation u];exact hmargin _)
    calc
      _≤_:=hpt
      _=_:=by rw [show κ-(reserve/2)=κ+(-(reserve/2)) by ring,Real.rpow_add hz];ring
  have hn:=hfin.2 a F hN hinj hfreeze hsource₀ hsource hHlo hHhi hfreq hpool hhi hP hb1 hb2
    P poolAmp mesh hpoolAmp hcell havoid hdepth hplain hcoeff hnorm
    W1 W2 hW1 hW2 hb1' hb2'
    (regularFamilyWeight_mx F Wa (fun _=>P) (fun _=>poolAmp) H0 radius (poolAmp/2))
    second t u (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*Z^κ)
    ((i.p.control controls)^2) (1+|shifted|+height) hgκ (sq_nonneg _) (by linarith [abs_nonneg shifted]) hcof
  have he:=pow_le_pow_left₀ (show 0≤1+|shifted|+height by positivity)
    (literal_mellin_shift_height ht height t u second hh) degree
  calc
    _≤Cf*(geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*Z^κ)*
        (i.p.control controls)^2*(1+|shifted|+height)^degree*Z^(-(reserve/4)):=hn
    _≤Cf*(geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*Z^κ)*
        (i.p.control controls)^2*(mellinShiftConstant*mellinPairHeight t u*(1+|ht|+height))^degree*
        Z^(-(reserve/4)):=by gcongr
    _=_:=by
      rw [show κ-(reserve/4)=κ+(-(reserve/4)) by ring,Real.rpow_add hz]
      simp only [mul_pow];ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_small_normalized_mx
