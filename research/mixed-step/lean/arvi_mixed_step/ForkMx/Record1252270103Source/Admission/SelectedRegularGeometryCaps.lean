/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
Actual modified retained geometry discharges the three remaining coarse caps. -/
/- Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.SelectedRegularGeometryCaps
(Hailey Collet); changes: two parents. Over `Anchor_mx`/`Family_mx`/`Selected_mx`:
the first label, its column and the marked modifier are read from the first layer `F.s₀`,
`F.modifier₀`; the MAIN Fourier scale (at `volume F.s`, via `main_scale_upper_mx`), the children,
the data and the coordinates (at `logb Z (volume F.s)`) from the second-layer parent.
`modified_cofactor_coordinate_cap` takes a free volume and is reused from Collet. The proofs
are Collet's. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularGeometryCaps
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.RetainedGeometryWidth
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open Cycle61Moment Cycle61InitialMass Cycle61HighGeometry LocalMoment
open Record12518109Natural Record12518109Natural.MarkedPlain Record1252270103Finite
open OAI.SevenEighths.Record1252270103Source OAI.SevenEighths.Record1252270103Source.Collision
open SelectedRegularSourceData SelectedSecondKeyCaps SelectedHighCofactorFamily
open SelectedHighCofactorCoordinates HighScalar RegularLowRetainedRadial
local notation "O"=>HeckeFamily.O
local instance selectedRegularGeometryCapsDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- One fixed threshold absorbs the original support factor, before every
modified source, first allocation, complete second block and retained row. -/
theorem eventual_selected_radius_mx (N:ℕ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second),
      F.D=1→0≤F.ξ→F.ξ≤1→0≤F.reserve→
      (∀u,0≤F.amp (G.row u).val.1.1)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve 2 N (F.first (G.row u).val.1))→
      ∀u,(G.datum u).radius≤Z^(4:ℝ) := by
  filter_upwards [eventually_ge_atTop ((2:ℝ)^(2*N)),eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro α₀ α Label Row _ _ _ a F rows second G hD hξ hξ₁ hreserve hamp hT u
  have hh:=RetainedGeometry.main_scale_upper_mx F.reflected F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK
    F.bin (G.column u) (volume F.s) (F.amp (G.row u).val.1.1) F.reserve 2 N (volume_pos F.s) hZ (by norm_num) (hamp u) hξ hreserve
  have hK:(Z^F.D)=Z:=by rw [hD,Real.rpow_one]
  have hTcap:F.Tsec (G.row u).val.1.1≤Z^(2:ℝ):=by
    rw [hT u]
    apply hh.trans
    rw [hK,Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_right hconst (zero_lt_one.trans hZ).le]
  have hxi:Z^(F.ξ/2)≤Z^(2:ℝ):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  change frequencyRadius (F.Tsec (G.row u).val.1.1) Z F.ξ≤_
  unfold frequencyRadius
  calc
    _≤Z^(2:ℝ)*Z^(2:ℝ):=mul_le_mul hTcap hxi
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(4:ℝ):=by rw [←Real.rpow_add (zero_lt_one.trans hZ)];norm_num

/-- The original full second-column source cap bounds its actual inactive
prime product. Kept or ratio-restricted rows add no norm assumption. -/
theorem selected_inactive_norm_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
    (hsource:∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^(2:ℝ)):
    ∀u,((∏p∈(G.datum u).inactive,p.val).absNorm:ℝ)≤Z^(2:ℝ) := by
  intro u
  have hcommon:=regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
    ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (G.row u).val.1
  have hc:((G.datum u).C.absNorm:ℝ)≤Z^(2:ℝ):=hcommon.1.trans (hsource u)
  have hh:=common_subset_log_box (G.datum u).C (G.datum u).D (G.datum u).hC (G.datum u).hD
    (G.datum u).inactive Z 2 F.hZ hc
  have hp:(0:ℝ)<(∏p∈(G.datum u).inactive,p.val).absNorm:=by
    exact_mod_cast firstCommonSubsetNorm_pos (G.datum u).C (G.datum u).D (G.datum u).hC (G.datum u).inactive
  exact (Real.logb_le_iff_le_rpow F.hZ hp).mp hh.2

/-- The previous exact formula specializes to the same selected family and
coordinate consumed by the retained-state constructor. -/
theorem selected_radial_cap_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
    (n low:Source)(b:ℝ)(A₁ A₂ D K:Ideal O)(Fmark:Ideal O→ℂ)
    (hmodifier:F.modifier₀=markedSourceModifier A₁ A₂ D K Fmark)
    (err errv annular:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α)
    (hD:F.D=1)(hamp:∀u,F.amp (G.row u).val.1.1=sourceAReal n low b)
    (hF:sourceFReal n low b≤1)(hrho:0≤frequencyLoss Z 32 F.ξ+F.reserve-err):
    ∀u,G.x err errv annular w wmin T u 2≤1 := by
  intro u
  change cofactorCoordinates F.reflected second (F.first (G.row u).val.1)
    (G.datum u).C (G.datum u).D (G.datum u).inactive Z F.D (Real.logb Z (volume F.s))
    (F.amp (G.row u).val.1.1) F.ξ F.reserve err errv ((G.sel u).forced Z)
    ((G.sel u).live w wmin) (∑i∈largeSlots T w wmin,w i) annular 2≤1
  rw [hD,hamp u]
  exact modified_cofactor_coordinate_cap n low b F.s₀ F.modifier₀ A₁ A₂ D K F.R F.seed Fmark hmodifier
    (Z^F.D) Z F.ξ F.hK F.hZ F.bin (G.column u) F.reflected second (G.datum u).C (G.datum u).D
    (G.datum u).inactive (Real.logb Z (volume F.s)) F.reserve err errv ((G.sel u).forced Z)
    ((G.sel u).live w wmin) (∑i∈largeSlots T w wmin,w i) annular hF hrho

/-- Concrete substitution Bradius=4, Binactive=2 and Brow=2 for the
retained data constructor. The source cap and actual MAIN scale remain literal. -/
theorem eventual_selected_geometry_caps_mx (N:ℕ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
      (n low:Source)(b:ℝ)(A₁ A₂ D K:Ideal O)(Fmark:Ideal O→ℂ)
      (err errv annular:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α),
      F.modifier₀=markedSourceModifier A₁ A₂ D K Fmark→F.D=1→0≤F.ξ→F.ξ≤1→0≤F.reserve→
      (∀u,F.amp (G.row u).val.1.1=sourceAReal n low b)→
      0≤sourceAReal n low b→sourceFReal n low b≤1→0≤frequencyLoss Z 32 F.ξ+F.reserve-err→
      (∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^(2:ℝ))→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve 2 N (F.first (G.row u).val.1))→
      ∀u,(G.datum u).radius≤Z^(4:ℝ) ∧
        ((∏p∈(G.datum u).inactive,p.val).absNorm:ℝ)≤Z^(2:ℝ) ∧ G.x err errv annular w wmin T u 2≤2 := by
  filter_upwards [eventual_selected_radius_mx N] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α₀ α Label Row _ _ _ a F rows second G n low b A₁ A₂ D K Fmark err errv annular w wmin T
    hmodifier hD hξ hξ₁ hreserve hamp hA hF hrho hsource hT u
  have hr:=hZ.2 a F rows second G hD hξ hξ₁ hreserve (fun u=>by rw [hamp u];exact hA) hT u
  have hi:=selected_inactive_norm_mx F rows second G hsource u
  have hx:=selected_radial_cap_mx F rows second G n low b A₁ A₂ D K Fmark hmodifier
    err errv annular w wmin T hD hamp hF hrho u
  exact ⟨hr,hi,hx.trans (by norm_num)⟩

end
end QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps.eventual_selected_radius_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps.selected_inactive_norm_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps.selected_radial_cap_mx
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularGeometryCaps.eventual_selected_geometry_caps_mx
