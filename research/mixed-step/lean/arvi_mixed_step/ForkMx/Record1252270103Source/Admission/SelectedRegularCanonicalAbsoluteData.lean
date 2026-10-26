/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0. -/
/- Mixed step (L4/L5, F5): fork of Record1252270103Source.Admission.SelectedRegularCanonicalAbsoluteData
(Hailey Collet); changes: two parents and two amplitudes, as in this fork's
`selected_family_absolute_mx` (first-layer hypotheses on `F.s₀`, second-layer ones on `F.s`, the weight at
`poolAmp`). `allocated_frequency_mx` reads the first label on `a.s₀` and the MAIN Fourier scale at the
second-layer volume `volume a.s` (`main_scale_upper_mx`). `budget_true` is reused verbatim. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCanonicalAbsoluteData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularAbsolute
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularPhase
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.RetainedGeometryWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open RayFourExpansion CenteredMomentCommonAllocationSum
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass CenteredMomentLogDyadic
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open CenteredMomentFiniteProfileExceptional CenteredMomentOriginalCommonHarmonic
open High.GlobalPhysical SecondSectorDatum SelectedRegularSourceData SelectedRegularLowPoint
local notation "O"=>HeckeFamily.O
local instance canonicalAbsoluteDataDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem full_budget_of_true_mx {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
    (F:Family_mx a Label)(Wa:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)(H0 radius:Label→ℝ)(ell B:ℝ)
    (h:@secondAbsoluteBudget α {q:F.Complete//True} inferInstance inferInstance
      (@Subtype.fintype F.Complete (fun _=>True) (fun _=>Classical.propDecidable True) inferInstance)
      (fun q=>SelectedRegularAbsolute.datum_mx F (regularFamilyKeep_mx F) q.val)
      (fun q=>F.childModifier q.val.1)
      (fun q=>SelectedRegularAbsolute.effectivePhase_mx F Wa P poolAmp H0 radius ell (regularFamilyKeep_mx F) q.val)≤B):
    secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
      (regularFamilyWeight_mx F Wa P poolAmp H0 radius ell)≤B:=by
  have hh:=(budget_true (SelectedRegularAbsolute.datum_mx F (regularFamilyKeep_mx F))
    (fun q=>F.childModifier q.1)
    (SelectedRegularAbsolute.effectivePhase_mx F Wa P poolAmp H0 radius ell (regularFamilyKeep_mx F))).symm.le.trans h
  convert hh using 1 <;> rfl

theorem full_family_absolute_mx (N:ℕ)(Cs hi ap bp ell radiusMax B L BH Dlo Brows Bpool:ℝ)
    (hCs:1≤Cs)(hhi:1≤hi)(hap:0<ap)(hbp:0≤bp)(hell:0<ell)(hmax:0≤radiusMax)
    (hB:0≤B)(hL:0≤L)(hBH:0≤BH)(hDlo:0≤Dlo)(hBrows:0≤Brows):
    ∃C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧
    ∀{α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label](a:Anchor_mx α₀ α Z)(F:Family_mx a Label)
      (p:Profiles ap bp)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)(H0 radius:Label→ℝ),
      Fintype.card α₀≤N→Fintype.card α≤N→(∀i,F.s.M i≤Cs)→(∀i,1≤F.s.hi i)→(∀i,F.s.hi i≤hi)→
      (∀i,1≤F.s.P i)→0≤F.s.b₁→0≤F.s.b₂→1≤F.s₀.lower→1≤F.s.lower→
      F.s₀.W₁=p.profile 0→F.s₀.W₂=p.profile 1→F.s.W₁=p.profile 0→F.s.W₂=p.profile 1→
      sourceRadius F.s₀≤Z^B→sourceRadius F.s≤Z^B→1≤volume F.s→volume F.s≤Z^B→|Real.logb Z (volume F.s₀)|≤B→
      F.seed≠0→
      Function.Injective (fun l=>(FirstFamily.firstLabel F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (F.column l),
        F.childSeed l))→
      (∀l,F.column l∈firstLiveColumns (High.CoupledFirst.geometryFirstSource F.s₀ F.modifier₀ F.R F.seed
        (Z^F.D) Z F.ξ F.hK F.bin) (fun _=>logAnnulus))→
      (∀l,((F.childSeed l).absNorm:ℝ)≤Z^L)→
      (∀l,Z^(-Dlo)≤F.Hmain l)→(∀l,F.Hmain l≤Z^BH)→
      (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^Brows)→
      (∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^Bpool)→
      (∀l,(P l).Nonempty)→(∀l,0<H0 l)→(∀l,0≤radius l+6*poolAmp l)→
      (∀l,radius l+6*poolAmp l≤radiusMax)→
      ∀(A1 A2 D K:Label→Ideal O)(cellA mesh loss BD:Label→ℝ)(depth:Label→ℕ),
      (∀l,Pool.FixedCellPoolData (P l) Z (cellA l) ell (mesh l) (loss l) (BD l) Bpool (depth l))→
      (∀l,F.childModifier l=SecondRemainder.correctedModifier (P l) (A1 l) (A2 l) (D l) (K l) (fun _=>1))→
      secondAbsoluteBudget F.datum (fun q=>F.childModifier q.1)
        (regularFamilyWeight_mx F W P poolAmp H0 radius ell)≤
        C*(p.control {(0,0)})^2*Z^(SelectedRegularAbsolute.exponent B L BH Brows Bpool) := by
  obtain ⟨C,hC,h⟩:=SelectedRegularAbsolute.selected_family_absolute_mx N Cs hi ap bp ell radiusMax B L BH Dlo Brows Bpool
    hCs hhi hap hbp hell hmax hB hL hBH hDlo hBrows
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with Z hz
  refine ⟨hz.1,?_⟩
  intro α₀ α Label _ _ _ a F p W P poolAmp H0 radius hN₀ hN hM hlo hhi' hP hb1 hb2 hl₀ hl he1₀ he2₀ he1 he2 hs₀ hs hv0 hv1 hlog hseed
    hinj hlive hseedcap hH0 hH1 hfreq hpool hPne hpos hrad hradcap A1 A2 D K cellA mesh loss BD depth
    hcell hmodifier
  exact full_budget_of_true_mx F W P poolAmp H0 radius ell _
    (hz.2 a F p W P poolAmp H0 radius hN₀ hN hM hlo hhi' hP hb1 hb2 hl₀ hl he1₀ he2₀ he1 he2 hs₀ hs hv0 hv1 hlog hseed
      hinj hlive hseedcap hH0 hH1 hfreq hpool hPne hpos hrad hradcap A1 A2 D K cellA mesh loss BD depth
      hcell hmodifier (regularFamilyKeep_mx F) (fun _=>True)).1

theorem allocated_frequency_mx (N:ℕ):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀{α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(column:Label→a.Column)
      (hLive:∀l,column l∈firstLiveColumns
        (High.CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
        (fun _=>logAnnulus))
      (alloc:∀l,actualAllocations a.s.pools (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed
        (Z^a.D) Z a.ξ a.hK a.bin (column l)))
      (P:Finset (Ideal O))(amp ht:ℝ)(χ₀:Label→RayCharacter),
      a.D=1→0≤a.ξ→a.ξ≤1→0≤a.reserve→0≤amp→
      ∀l,frequencyRadius ((allocatedRegularFamily_mx a column hLive alloc P amp ht N χ₀).Tsec l) Z a.ξ≤Z^(4:ℝ) := by
  filter_upwards [eventually_ge_atTop ((2:ℝ)^(2*N)),eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro α₀ α Label _ _ _ a column hLive alloc P amp ht χ₀ hD hξ hξ1 hr ha l
  have hh:=RetainedGeometry.main_scale_upper_mx a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK
    a.bin (column l) (volume a.s) amp a.reserve 2 N (volume_pos a.s) hZ (by norm_num) ha hξ hr
  have hK:Z^a.D=Z:=by rw [hD,Real.rpow_one]
  have hc:(allocatedRegularFamily_mx a column hLive alloc P amp ht N χ₀).Tsec l≤Z^(2:ℝ):=by
    apply hh.trans
    rw [hK,Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_right hconst (zero_lt_one.trans hZ).le]
  unfold frequencyRadius
  calc
    _≤Z^(2:ℝ)*Z^(2:ℝ):=mul_le_mul hc
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(4:ℝ):=by rw [←Real.rpow_add (zero_lt_one.trans hZ)];norm_num
end
end QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.allocated_frequency_mx

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.full_budget_of_true_mx

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalAbsolute.full_family_absolute_mx
