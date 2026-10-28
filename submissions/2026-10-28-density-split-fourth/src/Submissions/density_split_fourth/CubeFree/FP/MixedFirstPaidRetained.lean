/- Copyright (c) 2026 Sil. Apache-2.0.
Actual paid selected first retained energy. The source support and common
labels are fixed before the selected product. Only numerical geometry and
the original canonical profile data are premises; all energy estimates
are supplied by uniform_paid_physical. Parent checks Lean.
Modified by Sil (2026-10-26): cube-free: retained aggregate threaded through the balanced paid physical bound (alphaloss (2/3-alpha)*lref, pair gate); BandGeometry children at the uncompleted childScale on blocks with dyadicScale (n 1) at least 1/2 (others vanish); cube label hypotheses proved from source_fifth_free (label_cubes); Gates gains c0_le_one and alpha_loss/alpha_margin; supplier_dvd_puncture from MixedFirstAvoidance..
-/
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstPaidPhysical
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstRetainedFixed
import Submissions.density_split_fourth.CubeFree.FP.MixedOriginalCoprimality
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstAveragedWindow
import Submissions.density_split_fourth.CubeFree.FP.KernelIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.MixedFirstPaidRetained
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectorTransform
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentFirstTailAggregate
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedHeightEnvelope
open MixedFirstActualNonexceptional MixedFirstFullBudget MixedFirstLiveSource
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstPhysicalBudget
open MixedFirstIntegratedWindows MixedFirstPaidCosts MixedFirstPaidPhysical
open MixedFirstCommonSum MixedFirstRetainedFixed MixedFirstGeometricCaps
open MixedOriginalCoprimality MixedFirstAvoidance ReferencePrimeEnclosure MixedCompletedRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- One provenance condition, before all common labels. Actual suppliers
have u=f*seed and puncture R*f, so need not have u dividing R alone. -/
theorem avoidance_on_labels (s : Source ι a b) (ha : 0<a) (seed u : Id)
    (hseed : Squarefree seed) (hu : u∣s.R*seed)
    (p : Labels (avoidSource s u) ha seed) :
    seed∣p.val.1 ∧ seed∣p.val.2 ∧ u∣s.R*p.val.1 ∧ u∣s.R*p.val.2 := by
  have hs := active_common_seed (sourceColumns (avoidSource s u))
    (sourceCoefficient (avoidSource s u) ha seed) seed hseed
    (fun I hI=>source_coefficient_seed (avoidSource s u) ha seed I hI) p
  exact ⟨hs.1,hs.2,hu.trans (mul_dvd_mul_left s.R hs.1),
    hu.trans (mul_dvd_mul_left s.R hs.2)⟩

open QRH.Record1252270103KernelMass in
/-- Cube-free (CF (6.4) bookkeeping): a cube-free ideal with the prime support of `D`
divides `D²`, hence `N C ≤ N D² ≤ N D³`. -/
theorem cube_free_common_norm (C D : Id) (hC : C≠0) (hD : D≠0)
    (hf : SexticSieve.PowerFree 3 C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (C.absNorm:ℝ)≤(D.absNorm:ℝ)^3 := by
  have hdvd : C∣D^2 := by
    apply (dvd_iff_valuation_le hC (pow_ne_zero 2 hD)).mpr
    intro P
    rw [valuation_pow]
    have hl := (KernelIdeal.powerFree_iff_valuations hC).mp hf P
    by_cases hp : P∈QRH.Record1252270103KernelMass.primeSupport C
    · have hp' : P∈QRH.Record1252270103KernelMass.primeSupport D := by
        have h' : P∈CompletedGauss.primeSupport C := hp
        rw [hCD] at h'
        exact h'
      have hv : valuation D P≠0 := by
        have hs : P∈(factorization D).support := by rw [support_factorization];exact hp'
        exact Finsupp.mem_support_iff.mp hs
      omega
    · rw [valuation_eq_zero_of_not_mem hp]
      exact Nat.zero_le _
  have hpos : 0<Ideal.absNorm (D^2) :=
    Nat.pos_iff_ne_zero.mpr (fun hz=>pow_ne_zero 2 hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (C.absNorm:ℝ)≤((D^2).absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hdvd)
  rw [map_pow,Nat.cast_pow] at hn
  exact hn.trans (pow_le_pow_right₀ (ideal_norm_one_le hD) (by norm_num))

/-- Both common labels of an actual source are cube-free (`source_fifth_free`). -/
theorem label_cube_free (s : Source ι a b) (ha : 0<a) (seed : Id) (p : Labels s ha seed) :
    SexticSieve.PowerFree 3 p.val.1 ∧ SexticSieve.PowerFree 3 p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hI := Finset.mem_filter.mp (Finset.mem_product.mp hq).1
  have hJ := Finset.mem_filter.mp (Finset.mem_product.mp hq).2
  have hfI := MixedFirstAveragedWindow.source_fifth_free s ha seed q.1 (Finset.mem_filter.mp hI.1).2
  have hfJ := MixedFirstAveragedWindow.source_fifth_free s ha seed q.2 (Finset.mem_filter.mp hJ.1).2
  rw [←he]
  exact ⟨fun P hP hd=>hfI P hP (hd.trans (CenteredMomentCompleteCommon.commonPart_dvd _ _ hI.2.1)),
    fun P hP hd=>hfJ P hP (hd.trans (CenteredMomentCompleteCommon.commonPart_dvd _ _ hJ.2.1))⟩

/-- The two cube label hypotheses of the balanced exceptional supplier. -/
theorem label_cubes (s : Source ι a b) (ha : 0<a) (seed : Id) (p : Labels s ha seed) :
    (p.val.2.absNorm:ℝ)≤(p.val.1.absNorm:ℝ)^3 ∧ (p.val.1.absNorm:ℝ)≤(p.val.2.absNorm:ℝ)^3 := by
  have hs := commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p
  have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
  have hf := label_cube_free s ha seed p
  exact ⟨cube_free_common_norm _ _ hs.2.1 hs.1.1 hf.2 hCD.symm,
    cube_free_common_norm _ _ hs.1.1 hs.2.1 hf.1 hCD⟩

/-- A block whose dyad is below `1/2` has no nonzero annular row. -/
theorem fixedRows_eq_empty (r : ℝ) (n : Fin 4→ℤ) (h : dyadicScale (n 1)<1/2) :
    fixedRows r n=∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  have hh := (MixedFirstExceptionalWindow.mem_annularRows (n 1) z).mp (fixedRows_annular r n hz)
  have h1 : (1:ℝ)≤normValue z := QRH.Record1252270103KernelMass.ideal_norm_one_le (fun h0=>hh.1 (Ideal.span_singleton_eq_bot.mp h0))
  linarith [hh.2]

theorem supplier_global_avoidance (R f seed u : Id) (hu : u=f*seed) :
    u∣(R*f)*seed := supplier_dvd_puncture R f seed u seed hu dvd_rfl

/-- Literal finite-band geometry. These are scalar/cutoff/support caps,
not bounds for any source, moment, block, or energy. The checked
uniform_actual_cutoffs supplies the child fields using annular inclusion. -/
structure BandGeometry (s : Source ι a b) (ha : 0<a) (seed : Id)
    (K Z ξ κ W Tsecond H Btail Bfrequency : ℝ) : Prop where
  radius : ∀p : Labels s ha seed,∀E : Finset (CommonIndex p.val.1 p.val.2),
    firstRadius s p.val.1 p.val.2 E K Z ξ≤Z^Bfrequency
  artificial : ∀p : Labels s ha seed,
    ∀Dart∈artificialDivisors s p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2.1,
      (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0→(Dart.absNorm:ℝ)≤Z^Btail
  children : ∀p : Labels s ha seed,∀E∈inactiveSubsets p.val.1 p.val.2,
    ∀n : Blocks (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    1/2≤dyadicScale (n 1)→
    let Kc:=MixedFirstExceptionalWindow.childScale Z κ (n 1)
    Kc≤Z^Btail ∧ sharpSupport s^2/(16*Kc*W^4)≤Tsecond ∧
    ∀z∈fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>(n i:ℤ)),
      (Ideal.absNorm (Ideal.span {z}):ℝ)≤Kc

def retainedFactor (U : Controls) (c : Constants) (s : Source ι a b)
    (η : Character) (Q : Id) (c0 t V K mass Cpush Ckernel ε : ℝ) : ℝ :=
  (4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*Ckernel*
    (mass*Cpush*(16:ℝ)^ε)*profileEnvelope U c s Q c0 t V*rayMass

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Complete retained aggregate, using the actual paid block theorem.
The only common-label hypotheses are literal numerical BandGeometry.
The full seed norm is saved after the genuine/artificial/dyadic sums. -/
theorem uniform_paid_retained
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi α ξsecond saving Bfrequency εsum : ℝ)
    (ha : 0<a) (hb : 1≤b) (hL : 0≤L) (hBG : 0≤BG) (hBH : 0≤BH)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hε : 0<ε) (hδ : 0<δ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hgap : α+2*δ<1) (hξsecond : 0<ξsecond)
    (hfrequency : 0≤Bfrequency) (hεsum : 0<εsum)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (expo : (ι→ℝ)→Id→Id→Character→ℝ→ℝ)
    (hsupply : AllocatedSupply (ι:=ι) M Hray hHray Holes Wslot a b L Lslot Lcap Cap BR BG BH Bsource
      (Bη+BG+ε) δ lo hi Mgeom 1 ha hb Q expo) :
    ∃U : Controls,∃Cpush Ckernel Csum : ℝ,0<Cpush ∧ 0≤Ckernel ∧ 0<Csum ∧
    ∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      s.d=(1,1)→(s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀(K ξfirst κpad W Tsecond H : ℝ),0<K→0<W→0≤ξfirst→
      0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→Tsecond≤Z^Btail→
      1≤sharpSupport s→sharpSupport s≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→
      0<H→sourceNormCap s.P b s.T s.d≤H→H≤Z^BG→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀seed : Id,Squarefree seed→seed≠0→∀u : Id,u∣s.R*seed→
    let sActual:=avoidSource s u
    BandGeometry sActual ha seed K Z ξfirst κpad W Tsecond H Btail Bfrequency→
    ∀Ds : Finset Id,(∀F∈Ds,Supported F)→∀(weight : Id→ℝ)(mass : ℝ),0≤mass→
      (∀F∈Ds,0≤weight F∧weight F≤mass)→(∀F∈Ds,(F.absNorm:ℝ)≤2*W)→
    ∀Rexp Praw Sraw dsel lref c0 omega sigma loss BX enon : ℝ,MixedFirstFullBudget.PairGate Z enon (fun G Gopp τ=>expo w G Gopp τ W)→
    let p0 : Parameters :=
      { Z:=Z,Kfirst:=K,Tfirst:=0,Cfirst:=1,ξfirst:=ξfirst,κpad:=κpad,W:=W,
        ε:=ε,δ:=δ,Bnorm:=normExponent L Pexp ε,BG:=BG,BX:=BX,R:=Rexp,P:=Praw,S:=Sraw,
        d:=dsel,l:=lref,c0:=c0,omega:=omega,sigma:=sigma,loss:=loss,saving:=saving,
        enon:=enon,αloss:=(2/3-α)*lref }
    Gates p0→SourceGeometry p0 s η w→
    ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t
      (sourceColumns sActual) (selectedCoefficient sActual ha seed F) Φ K (sourceVolume s) Z ξfirst‖/
        sourceVolume s≤
      Csum*retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε*
        Z^(loss+5*Btail*ε+εsum)/(seed.absNorm:ℝ) := by
  obtain ⟨U,Cpush,Ckernel,hCpush,hCkernel,hpaid⟩ := uniform_paid_physical
    (ι:=ι) M Hray hHray Φ 0 N Holes hcard Wslot a b L Lslot Lcap Cap
    BR BG BH Bsource Bη Pexp Mgeom Btail ε δ lo hi α ξsecond saving
    ha hb hL hBH hPexp
    hMgeom hBtail hBGtail hε hδ hα0 hα23 hgap hξsecond Q hQt hQ72 expo hsupply
  obtain ⟨Csum,hCsum,hcommon⟩ := uniform_common_artificial_band_mass
    BG Bfrequency Btail 1 εsum hBG hfrequency hBtail (by norm_num) hεsum
  refine ⟨U,Cpush,Ckernel,Csum,hCpush,hCkernel,hCsum,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hpaid⟩ := hpaid η₀ hη₀
  refine ⟨c,?_⟩
  filter_upwards [hpaid,hcommon] with Z hz hm
  obtain ⟨hZ,hpaid⟩ := hz
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hR hHholes hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η hη K ξfirst κpad W Tsecond H hK hWblock hξ
    hT hTcap hTupper hX hXupper hWupper hWinv hH hsourceH hHcap
    χ₀ msecond hmsecond hml hm2 seed hseed hseed0 u hu sActual hgeometry
    Ds hDs weight mass hmass hweight hDN Rexp Praw Sraw dsel lref c0 omega sigma loss BX enon hexpo p0 hp0 hg0
  let A:=retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε
  have hA : 0≤A := by
    have hprofiles := profileEnvelope_nonneg U c s ha hunit Q c0 t V hp0.hc0 hV
    have hpresentation := fixedPresentationCost_pos.le
    have hrays := rayMass_nonneg
    dsimp only [A,retainedFactor]
    positivity
  let radius:=fun (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))=>
    firstRadius sActual p.val.1 p.val.2 E K Z ξfirst
  let divisors:=fun (p : Labels sActual ha seed) (_E : Finset (CommonIndex p.val.1 p.val.2))=>
    artificialDivisors sActual p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1
  have hmasssum := hm.2 ι a b sActual ha seed hseed hseed0 K H hK hH hsourceH hHcap
    radius (fun p E=>by simpa only [one_mul] using hgeometry.radius p E) divisors
    (fun p E D hD hμ=>hgeometry.artificial p D hD hμ)
  let term:=fun (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm))=>
    physicalAverage sActual ha seed η t p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).1
      (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2
      E (fixedRows (radius p E) (fun i=>(n i:ℤ))) Ds weight W Φ K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
  have hpoint (p : Labels sActual ha seed) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E∈inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm)) :
      ‖term p E n‖/sourceVolume s≤
        (A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
          artificialMass sActual p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1 := by
    have hs := commonLabels_supported
      (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p
    have hCD := (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
    have hnorm := commonLabel_norm_bounds (sourceColumns sActual) (sourceCoefficient sActual ha seed) H
      (fun I _ hI=>(original_coefficient_cap sActual ha seed I hI).2.trans hsourceH)
      p.val.1 p.val.2 p.property
    have havoid := avoidance_on_labels s ha seed u hseed hu p
    let Tfirst:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (sourceVolume s)
    have hfirst : Tfirst≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex p.val.1 p.val.2=>P.val) E})
        K (sourceVolume s) := by
      simp only [Tfirst,one_mul,primeSubsetGenerator,span_idealGenerator,le_refl]
    have hret : Retained (frequencyRadius Tfirst Z ξfirst) (n 1) :=
      block_retained _ _ _ _ n
    have hnonneg : 0≤(A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2 hs.2.1 :=
      mul_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by linarith [hZ]) _))
        (common_weight_nonneg _ _ _)) (artificialMass_nonneg _ _ _ _)
    by_cases hdy : 1/2≤dyadicScale (n 1)
    swap
    · have hempty := fixedRows_eq_empty (radius p E) (fun i=>(n i:ℤ)) (not_le.mp hdy)
      have h0 : term p E n=0 := by
        dsimp only [term]
        rw [hempty]
        simp [physicalAverage,CenteredMomentFirstPhysicalSource.block]
      rw [h0,norm_zero,zero_div]
      exact hnonneg
    obtain ⟨hKc,hTc,hrows⟩ := hgeometry.children p E hE n hdy
    have hcubes := label_cubes sActual ha seed p
    have hp1 : Gates {p0 with Tfirst := Tfirst} :=
      ⟨hp0.hZ,hp0.hK,hp0.hW,hp0.hc0,hp0.c0_le_one,hp0.hCfirst,hp0.hξ,hp0.hε,hp0.hδ,
        hp0.hS,hp0.hd,hp0.mixed,hp0.native,hp0.reference,hp0.Wlower,hp0.Wupper,
        hp0.frequency,hp0.zero_loss,hp0.alpha_loss,hp0.alpha_margin,hp0.exceptional_loss,hp0.tail_loss⟩
    have hg1 : SourceGeometry {p0 with Tfirst := Tfirst} s η w :=
      ⟨hg0.volume,hg0.width,hg0.length,hg0.support,hg0.slots⟩
    have hbnd := hpaid θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit
      hR hHholes hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η
      p.val.1 p.val.2 hs.1 hs.2 hCD hη (hnorm.1.trans hHcap) (hnorm.2.trans hHcap)
      E hE K Tfirst 1 ξfirst κpad W hK hWblock (by norm_num) hξ hfirst
      χ₀ msecond hmsecond hml hm2 Tsecond hT hTcap hX le_rfl hXupper hWupper hWinv hTupper
      (n 1) hret hcubes.1 hcubes.2 hKc hKc hTc hTc seed havoid.1 havoid.2.1 u havoid.2.2.1 havoid.2.2.2
      Ds (fixedRows (radius p E) (fun i=>(n i:ℤ))) hDs
      (fixedRows_nonzero _ _) weight mass hmass hweight hDN
      (fun z hz=>hrows z hz) (fun z hz=>hrows z hz)
      (hgeometry.artificial p)
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))
      (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
      Rexp Praw Sraw dsel lref c0 omega sigma loss BX enon hexpo hp1 hg1
    have hheight : ‖commonHeight sActual η t p.val.1 p.val.2‖≤1 := by
      rw [commonHeight,norm_mul,norm_star]
      exact (mul_le_mul (rowWeight_norm_le_one η (fixedBadMask*idealGenerator sActual.R)
        1 1 t p.val.1 hs.1.1) (rowWeight_norm_le_one η (fixedBadMask*idealGenerator sActual.R)
        1 1 t p.val.2 hs.2.1) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    apply (show ‖term p E n‖/sourceVolume s≤‖commonHeight sActual η t p.val.1 p.val.2‖*
      ((A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2 hs.2.1) from by
      convert hbnd using 1 <;> simp only [pow_zero,one_mul,term,A,retainedFactor] <;> ring).trans
    exact mul_le_of_le_one_left hnonneg hheight
  change ‖∑F∈Ds,((weight F/W:ℝ):ℂ)*retainedEnergy η
    (fixedBadMask*idealGenerator sActual.R) 1 t (sourceColumns sActual)
    (selectedCoefficient sActual ha seed F) Φ K (sourceVolume sActual) Z ξfirst‖/
    sourceVolume s≤_
  rw [selected_retained_average sActual ha seed η t Φ K Z ξfirst H hK hsourceH Ds weight W]
  change ‖∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
    ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
      (H/p.val.1.absNorm) (H/p.val.2.absNorm),term p E n‖/sourceVolume s≤_
  have htri : ‖∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),term p E n‖≤
      ∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (H/p.val.1.absNorm) (H/p.val.2.absNorm),‖term p E n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun E hE=>norm_sum_le _ _)
  apply (div_le_div_of_nonneg_right htri (sourceVolume_pos s).le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      (A*Z^(loss+5*Btail*ε))*commonWeight p.val.1 p.val.2 E*
        artificialMass sActual p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns sActual) (sourceCoefficient sActual ha seed)) p).2.1 :=
      Finset.sum_le_sum (fun p _=>Finset.sum_le_sum (fun E hE=>Finset.sum_le_sum (fun n _=>hpoint p E hE n)))
    _=(A*Z^(loss+5*Btail*ε))*(∑p : Labels sActual ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),∑Dart∈divisors p E,
      commonWeight p.val.1 p.val.2 E*(‖(UniqueFactorizationMonoid.moebius Dart:ℂ)‖/(Dart.absNorm:ℝ))) := by
      simp only [artificialMass,divisors,Finset.mul_sum,mul_assoc]
    _≤(A*Z^(loss+5*Btail*ε))*(Csum*Z^εsum/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hmasssum (mul_nonneg hA (Real.rpow_nonneg (by linarith [hZ]) _))
    _=_ := by
      have he : Z^(loss+5*Btail*ε+εsum)=Z^(loss+5*Btail*ε)*Z^εsum := by
        rw [Real.rpow_add (zero_lt_one.trans hZ)]
      rw [he]
      dsimp only [A]
      ring

end
end QRH.DensitySplitThird.CubeFree.FP.MixedFirstPaidRetained
