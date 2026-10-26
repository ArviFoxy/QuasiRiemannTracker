/- Mixed source step, ledger N5: the LOW price at a virtual node, with the frozen width kept.

Collet's three erasure branches (`raw_low_three_branches`, Low/RawCaps.lean) drop the frozen-width
terms `-q(1-1/λ)f` (affine cap) and `-qf` (upper cap) and use the weak cap `(BF-t)/λ ≤ hF` for the
upper branch. Here both terms are kept and the weak cap is not assumed:
  `-a - B12 - D + q·erased ≤ -min a (g + q·min ((1-1/λ)f) (f - ((BF-t)/λ - hF))) + …`
(`raw_low_three_branches_f`, `actual_low_coordinate_payment_f`). This is the coordinate form of
`raw_erasure_identity` (Virtual.lean), which keeps `-(q - q/λ)f`.

`MixedNodePrice n low b φ` is Collet's `ModifiedNodePrice` (Coefficient/RegularLowPhysicalPrice.lean)
with two parents (the first label `j` over `s₀ : Input ι₀`, the second datum over `ι`) and the extra
hypothesis `φ ≤ f` on the frozen width. It is proved at every virtual node:
* the top node `δ = d` (fee `r`) with `φ = 0` (`mixed_node_price_top`): Collet's argument;
* every node `δ ∈ [0, d]` with `φ = (b - δ) - ε`, `0 ≤ ε ≤ 6e` (`mixed_node_price_frozen`): the live
  width left at the node is at most `ε`, so both cap branches cost at most `qε`; neither the weak cap
  nor the fee identity is used.
The design's fee margin `φ_k = (qX₀ + r - r(1-6qβ) - δ·den3)₊/(q(1-1/Λ₀))` (`phiK`) pays the affine
branch, but with it the upper branch needs the weak cap at the node scale `1 - 6r - 6δ`, which fails at
`δ = 0` on the chain (LEAN_NOTES); `mixed_node_price_phi` records that version with the weak cap as an
explicit hypothesis. -/
import Submissions.arvi_mixed_step.Ledger.Nodes
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowPhysicalPrice
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.MixedStep.Ledger
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle61HighGeometry Cycle61InitialMass Cycle61Moment Record12518109Natural Record12518109Raw
open Record1252270103CommonGeometry Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph QRH.Record1252270103Source.High QRH.Record1252270103Source
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission OAI.SevenEighths.Record1252270103Source.Collision
open QRH.Record1252270103Source.HighScalar
open QRH.Record1252270103Source.PhysicalLowReserve QRH.MixedStep.Finite
local notation "O" => HeckeFamily.O

/-! ## The three branches with the frozen width kept -/

/-- Collet's `raw_low_three_branches` without the weak cap, keeping the frozen terms. -/
theorem raw_low_three_branches_f (a g q B lam h F t b c delta f B12 D : ℝ)
    (hq : 0 ≤ q) (hB : B ≤ 1) (hlam : 1 < lam)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdc : delta ≤ c)
    (hB12 : 0 ≤ B12) (hdB : delta ≤ B12) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hh : 0 ≤ h) (hqh : q*h ≤ 1)
    (hgap : g = a-q*(b+(t-B*F)/lam)) :
    -a-B12-D + q*max 0 (max
      (b-f-(B*(F-delta)-(t-c+f))/lam)
      (b-f-h*(F-delta))) ≤
      -min a (g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F))) := by
  have hlam0 : 0 < lam := by linarith
  have hcB : 0 ≤ c-B*delta := by nlinarith
  have hqdiv : 0 ≤ q/lam := div_nonneg hq hlam0.le
  set G := g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F)) with hG
  have hG1 : G ≤ g+q*((1-1/lam)*f) := by
    have := mul_le_mul_of_nonneg_left (min_le_left ((1-1/lam)*f) (f-((B*F-t)/lam-h*F))) hq
    linarith
  have hG2 : G ≤ g+q*(f-((B*F-t)/lam-h*F)) := by
    have := mul_le_mul_of_nonneg_left (min_le_right ((1-1/lam)*f) (f-((B*F-t)/lam-h*F))) hq
    linarith
  have hmA := min_le_left a G
  have hmG := min_le_right a G
  have hzero : -a-B12-D ≤ -min a G := by linarith
  have heq : -a-B12-D+q*(b-f-(B*(F-delta)-(t-c+f))/lam) =
      -g-B12-D-(q/lam)*(c-B*delta)-q*((1-1/lam)*f) := by
    rw [hgap]
    field_simp
    ring
  have haff : -a-B12-D+q*(b-f-(B*(F-delta)-(t-c+f))/lam) ≤ -min a G := by
    rw [heq]
    have hx := mul_nonneg hqdiv hcB
    linarith
  have heqh : -a-B12-D+q*(b-f-h*(F-delta)) =
      -(g+q*(f-((B*F-t)/lam-h*F)))+q*h*delta-B12-D := by
    rw [hgap]
    field_simp
    ring
  have hup : -a-B12-D+q*(b-f-h*(F-delta)) ≤ -min a G := by
    rw [heqh]
    have hy : q*h*delta ≤ B12 :=
      (mul_le_mul_of_nonneg_right hqh hdelta).trans (by simpa using hdB)
    linarith
  rcases le_total 0 (max (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta))) with hmax | hmax
  · rw [max_eq_right hmax]
    rcases le_total (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta)) with h' | h'
    · simpa only [max_eq_right h'] using hup
    · simpa only [max_eq_left h'] using haff
  · simpa only [max_eq_left hmax, mul_zero, add_zero] using hzero

/-- With the clipping loss, radial rounding and whole-slot mesh (Collet's
`raw_low_three_branches_with_loss`, frozen terms kept). -/
theorem actual_erasure_three_branch_payment_f
    (a g q B lam h F t b c delta f B12 D loss rho mesh erased : ℝ)
    (hq : 0 ≤ q) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hlam : 1 < lam)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdc : delta ≤ c)
    (hB12 : 0 ≤ B12) (hdB : delta ≤ B12) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hh : 0 ≤ h) (hqh : q*h ≤ 1)
    (hgap : g = a-q*(b+(t-B*F)/lam)) (hloss : 0 ≤ loss) (hrho : 0 ≤ rho)
    (herased : erased ≤ max 0 (max
      (b-f-(B*(F-delta-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-delta-rho)))+mesh) :
    -a-B12-D+q*erased ≤
      -min a (g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F)))+
        q*(max ((B*rho+loss)/lam) (h*rho)+mesh) := by
  have hlam0 : 0 < lam := by linarith only [hlam]
  have ha := raw_low_three_branches_f a g q B lam h F t b c delta f B12 D
    hq hB hlam hc hdelta hdc hB12 hdB hD hf hh hqh hgap
  have hp := three_branch_perturb
    (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta))
    ((B*rho+loss)/lam) (h*rho)
    (div_nonneg (add_nonneg (mul_nonneg hB0 hrho) hloss) hlam0.le) (mul_nonneg hh hrho)
  have e₁ : b-f-(B*(F-delta-rho)-(t-c+f+loss))/lam =
      (b-f-(B*(F-delta)-(t-c+f))/lam)+(B*rho+loss)/lam := by ring
  have e₂ : b-f-h*(F-delta-rho) = (b-f-h*(F-delta))+h*rho := by ring
  rw [e₁, e₂] at herased
  have hm := mul_le_mul_of_nonneg_left (herased.trans (add_le_add_right hp mesh)) hq
  nlinarith only [ha, hm]

/-- Collet's `actual_low_coordinate_payment` (High/GlobalPhysicalLowPayment.lean) without the weak
cap, with the frozen-width terms kept. -/
theorem actual_low_coordinate_payment_f (reflected second:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (C D:Ideal O)(hC₂:Supported C)(hD₂:Supported D)(heq₂:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D))
    (Z M A a ξ reserve err errv q B lam h F t b c f loss rho mesh erased g radial radialRound:ℝ)
    (hZ:1<Z)(hq:0≤q)(hB0:0≤B)(hB:B≤1)(hlam:1<lam)
    (hc:labelC reflected l Z≤c)(hf:0≤f)(hh:0≤h)(hqh:q*h≤1)
    (hgap:g=a-q*(b+(t-B*F)/lam))
    (hloss:0≤loss)(hrho:0≤rho)
    (herased:erased≤max 0 (max
      (b-f-(B*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh)
    (hrad:radial≤(childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U
      Z M A a ξ reserve err) errv) 2+radialRound):
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U Z M A a ξ reserve err) errv
    x 0+x 1+radial-labelSide reflected l Z A-labelSurplus reflected l Z+q*erased≤
      -min a (g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F)))+
        q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound := by
  intro x
  obtain ⟨hd0,hdc,hdpen,hpen⟩:=low_first_deficit_gates reflected l hC hD heq hbC hbD Z hZ
  have hcc:0≤c:=hd0.trans (hdc.trans hc)
  have hsecond:0≤lowSecondPenalty second C D U Z:=actual_raw_second_nonneg second C D hC₂ hD₂ heq₂ U Z hZ
  have he:0≤labelE l Z := by
    apply Real.logb_nonneg hZ
    exact_mod_cast firstCommonSubsetNorm_pos l.1.1 l.1.2 hC l.2.val
  have hrest:0≤stratumWidth Z l.1.1 l.1.2 2 2+labelE l Z+lowSecondPenalty second C D U Z :=
    add_nonneg (add_nonneg (stratumWidth_nonneg Z hZ _ _ _ _) he) hsecond
  have hp:=actual_erasure_three_branch_payment_f a g q B lam h F t b c
    (max (labelD reflected l Z-labelC reflected l Z) 0) f
    (lowTypePenalty reflected l Z)
    (stratumWidth Z l.1.1 l.1.2 2 2+labelE l Z+lowSecondPenalty second C D U Z)
    loss rho mesh erased hq hB0 hB hlam hcc hd0 (hdc.trans hc) hpen hdpen hrest hf hh hqh hgap
    hloss hrho herased
  have hi:=actual_low_coordinate_identity reflected second l hC hD heq hbC hbD C D U Z M A a ξ reserve err errv hZ
  change x 0+x 1+x 2-_-_=_ at hi
  change radial≤x 2+radialRound at hrad
  linarith only [hp,hi,hrad]

/-- Two parents: the first label over `s₀ : Input ι₀`, any supported second pair `(C, D)`. -/
theorem modified_low_coordinate_payment_f {ι₀:Type}[Fintype ι₀][DecidableEq ι₀]
    (s₀:Input ι₀)(A₁ A₂ Dmark Kmark R seed:Ideal O)
    (Fmark:Ideal O→ℂ)(H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ))
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀
      (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin))
    (reflected second:Bool)(C D:Ideal O)(hC₂:Supported C)(hD₂:Supported D)
    (heq₂:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (M A a reserve err errv q B lam h F t b c f loss rho mesh erased g radial radialRound:ℝ)
    (hZ:1<Z)(hq:0≤q)(hB0:0≤B)(hB:B≤1)(hlam:1<lam):
    let l:=FirstFamily.firstLabel s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U
      Z M A a ξ reserve err) errv
    labelC reflected l Z≤c→0≤f→0≤h→q*h≤1→
    g=a-q*(b+(t-B*F)/lam)→0≤loss→0≤rho→
    erased≤max 0 (max
      (b-f-(B*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh→
    radial≤x 2+radialRound→
    x 0+x 1+radial-
      balancedGeometrySide reflected A (CoupledFirst.geometryExponents s₀
        (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ j.1.val)+q*erased≤
      -min a (g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F)))+
        q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound := by
  intro l x hc hf hh hqh hgap hloss hrho herased hrad
  have hl:=FirstFamily.label_supported s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j
  obtain ⟨hbC,hbD⟩:=modified_first_label_valuations s₀ A₁ A₂ Dmark Kmark R seed Fmark H Z ξ hH bin j
  have hp:=actual_low_coordinate_payment_f reflected second l hl.1 hl.2.1 hl.2.2 hbC hbD
    C D hC₂ hD₂ heq₂ U Z M A a ξ reserve err errv q B lam h F t b c f loss rho mesh erased g radial
    radialRound hZ hq hB0 hB hlam hc hf hh hqh hgap hloss hrho herased hrad
  have hside:=modified_balanced_side s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin j
    reflected A
  change balancedGeometrySide reflected A _=labelSide reflected l Z A+labelSurplus reflected l Z at hside
  rw [hside]
  convert hp using 1 <;> ring

/-! ## The mixed node price -/

/-- Collet's `ModifiedNodePrice` with two parents and the frozen hypothesis `φ ≤ f`. -/
def MixedNodePrice (n low : Source) (b φ : ℝ) : Prop :=
  ∀(ι₀:Type)[Fintype ι₀][DecidableEq ι₀](ι:Type)[Fintype ι][DecidableEq ι],
  ∀(s₀:Input ι₀)(A₁ A₂ Dmark Kmark R seed:Ideal O)(Fmark:Ideal O→ℂ)
    (H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ)),
  ∀j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀
    (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin),
  ∀(reflected second:Bool)(d₂:SecondInputDatum ι)(U:Finset (CommonIndex d₂.C d₂.D)),
  ∀(M A reserve width err errv c f loss rho mesh erased radial radialRound outer:ℝ),
    1<Z → 0≤width → width≤PhysicalLowGuard.step n → 0≤loss → 0≤rho →
    rho≤(n.allowance:ℝ)/4 → loss≤(n.allowance:ℝ)/4 → mesh≤(n.allowance:ℝ)/4 →
    err≤(n.allowance:ℝ)/4 → errv≤(n.allowance:ℝ)/4 → radialRound≤(n.allowance:ℝ)/4 →
    outer≤4*(n.allowance:ℝ) →
  let l:=FirstFamily.firstLabel s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
    R seed H Z ξ hH bin j;
  let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d₂.C d₂.D U
    Z M A (sourceAReal n low b) ξ reserve err) errv;
    labelC reflected l Z≤c → 0≤f → φ≤f →
    erased≤max 0 (max
      (b-f-((low.B:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-
        (plainBudget n b width-c+f+loss))/(low.L:ℝ))
      (b-f-(low.cap:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh →
    radial≤x 2+radialRound →
    x 0+x 1+radial-balancedGeometrySide reflected A
      (CoupledFirst.geometryExponents s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
        R seed H Z ξ j.1.val)+(n.q:ℝ)*erased+outer≤-8*(n.allowance:ℝ)

/-- The node gain with the frozen width kept, at plain budget `plainBudget n b width`. -/
def frozenGain (n low : Source) (b width f : ℝ) : ℝ :=
  (sourceAReal n low b-(n.q:ℝ)*(b+(plainBudget n b width-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ)))+
    (n.q:ℝ)*min ((1-1/(low.L:ℝ))*f)
      (f-(((low.B:ℝ)*sourceFReal n low b-plainBudget n b width)/(low.L:ℝ)-(low.cap:ℝ)*sourceFReal n low b))

/-- The price follows from a lower bound `13.5e` on the frozen gain. -/
theorem mixed_price_of_gain (n low : Source) (b φ : ℝ) (hlow : ParentGood low)
    (he : 0≤(n.allowance:ℝ)) (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1)
    (hqcap : (n.q:ℝ)*(low.cap:ℝ)≤1)
    (hgain : ∀ width f : ℝ, 0≤width → width≤PhysicalLowGuard.step n → 0≤f → φ≤f →
      (27/2:ℝ)*(n.allowance:ℝ)≤min (sourceAReal n low b) (frozenGain n low b width f)) :
    MixedNodePrice n low b φ := by
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hB1 : (low.B:ℝ)≤1 := by exact_mod_cast hlow.2.1
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hh0 : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  have hh1 : (low.cap:ℝ)≤1 := by exact_mod_cast hlow.2.2.2.2.le
  intro ι₀ _ _ ι _ _ s₀ A₁ A₂ Dmark Kmark R seed Fmark H Z ξ hH bin j reflected second d₂ U
    M A reserve width err errv c f loss rho mesh erased radial radialRound outer
    hZ hw0 hw hloss0 hrho0 hrho hloss hmesh herr herrv hround houter l x hc hf hφ herased hrad
  have hp := modified_low_coordinate_payment_f s₀ A₁ A₂ Dmark Kmark R seed Fmark H Z ξ hH bin j
    reflected second d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U M A (sourceAReal n low b) reserve err errv
    (n.q:ℝ) (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ) (sourceFReal n low b) (plainBudget n b width) b c f
    loss rho mesh erased
    (sourceAReal n low b-(n.q:ℝ)*(b+(plainBudget n b width-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ)))
    radial radialRound hZ hq0 hB0 hB1 hlam hc hf hh0 hqcap rfl hloss0 hrho0 herased hrad
  have herrs := error_budget (n.allowance:ℝ) (n.q:ℝ) (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)
    rho loss mesh err errv radialRound he hq0 hq1 hB0 hB1 hlam.le hh0 hh1 hrho hloss hmesh herr herrv
    hround
  have hg := hgain width f hw0 hw hf hφ
  change x 0+x 1+radial-balancedGeometrySide reflected A _+(n.q:ℝ)*erased≤
    -min (sourceAReal n low b) (frozenGain n low b width f)+
      (n.q:ℝ)*(max (((low.B:ℝ)*rho+loss)/(low.L:ℝ)) ((low.cap:ℝ)*rho)+mesh)+err+errv+radialRound at hp
  linarith only [hp, herrs, hg, houter]

/-- The width step costs at most a sixteenth of an allowance (Collet's `width_charge`). -/
theorem width_charge' (n low : Source) (width : ℝ) (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1) (hlam : 1≤(low.L:ℝ))
    (hw : width≤PhysicalLowGuard.step n) (hw0 : 0≤width) :
    (n.L:ℝ)*width≤(n.allowance:ℝ)/16 ∧ (n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ)≤(n.allowance:ℝ)/16 := by
  refine ⟨?_, width_charge n low width he hL hq0 hq1 hlam hw⟩
  apply (mul_le_mul_of_nonneg_left hw hL).trans
  rw [PhysicalLowGuard.step, ←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<16*((n.L:ℝ)+1))).mpr
  nlinarith only [he, mul_nonneg hL he]

/-- **Frozen price.** At a node with the low geometry, a frozen width `f ≥ b - ε` (`0 ≤ ε ≤ 6e`)
leaves at most `ε` of live width, and both cap branches cost at most `qε`. -/
theorem mixed_node_price_frozen_of (n low : Source) (b ε : ℝ) (hg : RealGeometryLow n low b)
    (hlow : ParentGood low) (hL : 0≤(n.L:ℝ)) (he : 0≤(n.allowance:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1) (hε0 : 0≤ε) (hε : ε≤6*(n.allowance:ℝ)) :
    MixedNodePrice n low b (b-ε) := by
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hh0 : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  apply mixed_price_of_gain n low b (b-ε) hlow he hq0 hq1 hg.qcap_room.le
  intro width f hw0 hw hf hφ
  have hLw := (width_charge' n low width he hL hq0 hq1 hlam.le hw hw0).1
  have hLpos : 0<(low.L:ℝ) := hg.lowL_pos
  set a := sourceAReal n low b
  set F := sourceFReal n low b
  set P := plainBudget n b width
  have hP : P = sourceTReal n b+(n.L:ℝ)*width := rfl
  have hF : F = 1-6*a := rfl
  have hF0 : 0≤F := by rw [hF]; linarith [hg.a_small]
  -- the plain budget stays below the parent budget at the node
  have hroom : b+P-(low.B:ℝ)*F≤0 := by
    have := hg.parent_budget_room; rw [hP]; linarith
  have hqε : (n.q:ℝ)*ε≤6*(n.allowance:ℝ) := by nlinarith
  -- affine branch
  have h1 : a-6*(n.allowance:ℝ)≤
      (a-(n.q:ℝ)*(b+(P-(low.B:ℝ)*F)/(low.L:ℝ)))+(n.q:ℝ)*((1-1/(low.L:ℝ))*f) := by
    have hlf : (1-1/(low.L:ℝ))*(b-ε)≤(1-1/(low.L:ℝ))*f :=
      mul_le_mul_of_nonneg_left hφ (by
        have : 1/(low.L:ℝ)≤1 := (div_le_one hLpos).mpr hlam.le
        linarith)
    have hid : (a-(n.q:ℝ)*(b+(P-(low.B:ℝ)*F)/(low.L:ℝ)))+(n.q:ℝ)*((1-1/(low.L:ℝ))*(b-ε)) =
        a-(n.q:ℝ)*((b+P-(low.B:ℝ)*F)/(low.L:ℝ))-(n.q:ℝ)*((1-1/(low.L:ℝ))*ε) := by
      field_simp; ring
    have hneg : (n.q:ℝ)*((b+P-(low.B:ℝ)*F)/(low.L:ℝ))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos hq0 (div_nonpos_of_nonpos_of_nonneg hroom hLpos.le)
    have hε1 : (n.q:ℝ)*((1-1/(low.L:ℝ))*ε)≤(n.q:ℝ)*ε := by
      apply mul_le_mul_of_nonneg_left _ hq0
      have : 0≤1/(low.L:ℝ) := by positivity
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hlf hq0]
  -- upper branch
  have h2 : a-6*(n.allowance:ℝ)≤
      (a-(n.q:ℝ)*(b+(P-(low.B:ℝ)*F)/(low.L:ℝ)))+
        (n.q:ℝ)*(f-(((low.B:ℝ)*F-P)/(low.L:ℝ)-(low.cap:ℝ)*F)) := by
    have hid : (a-(n.q:ℝ)*(b+(P-(low.B:ℝ)*F)/(low.L:ℝ)))+
        (n.q:ℝ)*(f-(((low.B:ℝ)*F-P)/(low.L:ℝ)-(low.cap:ℝ)*F)) =
        a-(n.q:ℝ)*b+(n.q:ℝ)*f+(n.q:ℝ)*((low.cap:ℝ)*F) := by
      field_simp; ring
    rw [hid]
    have hcf : 0≤(n.q:ℝ)*((low.cap:ℝ)*F) := mul_nonneg hq0 (mul_nonneg hh0 hF0)
    nlinarith [mul_le_mul_of_nonneg_left hφ hq0]
  have hmin : a-6*(n.allowance:ℝ)≤frozenGain n low b width f := by
    simp only [frozenGain]
    rw [mul_min_of_nonneg _ _ hq0, ← add_min]
    exact le_min h1 h2
  have ha := hg.a_allowance
  apply le_min <;> linarith

/-- **Top price.** At a node whose fee clears Collet's fee room and whose weak cap holds (the top
virtual node), any frozen width `f ≥ 0` pays: Collet's argument with the frozen terms dropped. -/
theorem mixed_node_price_top_of (n low : Source) (b : ℝ) (hg : RealGeometryLow n low b)
    (hlow : ParentGood low) (hL : 0≤(n.L:ℝ)) (he : 0≤(n.allowance:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1)
    (hfee : ((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ)+4)*(n.allowance:ℝ)+
      10*(n.allowance:ℝ)<(n.lowFee:ℝ))
    (hweak : ((low.B:ℝ)*sourceFReal n low b-sourceTReal n b)/(low.L:ℝ)≤
      (low.cap:ℝ)*sourceFReal n low b) :
    MixedNodePrice n low b 0 := by
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hh0 : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  apply mixed_price_of_gain n low b 0 hlow he hq0 hq1 hg.qcap_room.le
  intro width f hw0 hw hf _
  have hLpos : 0<(low.L:ℝ) := hg.lowL_pos
  have hc := width_charge n low width he hL hq0 hq1 hlam.le hw
  -- Collet's conservative gain: the node gain is the fee minus the width charge
  have hgain : sourceAReal n low b-(n.q:ℝ)*
      (b+(plainBudget n b width-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=
      (n.lowFee:ℝ)-(n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ) := by
    have hfi := hg.fee_identity
    simp only [plainBudget]
    rw [← hfi]; ring
  -- the frozen terms are nonnegative
  have hexcess : ((low.B:ℝ)*sourceFReal n low b-plainBudget n b width)/(low.L:ℝ)-
      (low.cap:ℝ)*sourceFReal n low b≤0 := by
    have hh := mul_nonneg hL hw0
    have : ((low.B:ℝ)*sourceFReal n low b-plainBudget n b width)/(low.L:ℝ)≤
        ((low.B:ℝ)*sourceFReal n low b-sourceTReal n b)/(low.L:ℝ) := by
      apply div_le_div_of_nonneg_right _ hLpos.le
      simp only [plainBudget]; linarith
    linarith
  have hfz : 0≤min ((1-1/(low.L:ℝ))*f)
      (f-(((low.B:ℝ)*sourceFReal n low b-plainBudget n b width)/(low.L:ℝ)-
        (low.cap:ℝ)*sourceFReal n low b)) := by
    apply le_min
    · apply mul_nonneg _ hf
      have : 1/(low.L:ℝ)≤1 := (div_le_one hLpos).mpr hlam.le
      linarith
    · linarith
  have hp : 0≤((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ))*(n.allowance:ℝ) :=
    mul_nonneg (add_nonneg (div_nonneg (mul_nonneg hq0 hB0) hLpos.le) (mul_nonneg hq0 hh0)) he
  have hfg : (27/2:ℝ)*(n.allowance:ℝ)≤frozenGain n low b width f := by
    simp only [frozenGain]
    rw [hgain]
    nlinarith [mul_nonneg hq0 hfz]
  have ha := hg.a_allowance
  apply le_min <;> linarith

/-! ## The design's fee margin `φ_k` and the pool-only gate (§1d) -/

/-- The design's frozen margin at node `δ`: `(qX₀ + r - r(1-6qβ) - δ·den3)₊/(q(1-1/Λ₀))`. -/
def phiK (n low : Source) (b δ : ℚ) : ℝ :=
  max 0 ((n.q:ℝ)*(sourceX0 n low b:ℝ)+(n.lowFee:ℝ)-(n.lowFee:ℝ)*(1-6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ)))-
    (δ:ℝ)*(sourceDen3 n low:ℝ))/((n.q:ℝ)*(1-1/(low.L:ℝ)))

/-- The margin is the fee deficit of the node: `phiK = (r - vfee)₊/(q(1-1/Λ₀))`. -/
theorem phiK_eq (n low : Source) (b δ : ℚ) :
    phiK n low b δ = max 0 ((n.lowFee:ℝ)-(vfee n low b δ:ℝ))/((n.q:ℝ)*(1-1/(low.L:ℝ))) := by
  simp only [phiK, vfee]; push_cast; ring_nf

/-- With `f ≥ phiK`, the frozen gain restores the fee: `vfee + q(1-1/Λ₀)f ≥ r`. -/
theorem phiK_spec (n low : Source) (b δ : ℚ) (hq : 0<(n.q:ℝ)) (hlam : 1<(low.L:ℝ))
    {f : ℝ} (hf : phiK n low b δ≤f) :
    (n.lowFee:ℝ)≤(vfee n low b δ:ℝ)+(n.q:ℝ)*(1-1/(low.L:ℝ))*f := by
  have hk : 0<(n.q:ℝ)*(1-1/(low.L:ℝ)) := by
    apply mul_pos hq
    have : 1/(low.L:ℝ)<1 := (div_lt_one (by linarith)).mpr hlam
    linarith
  rw [phiK_eq, div_le_iff₀ hk] at hf
  have := le_max_right 0 ((n.lowFee:ℝ)-(vfee n low b δ:ℝ))
  nlinarith

/-- **Pool-only gate (§1d).** For a frozen width `f ≥ b - s` with `s(Λ₀ - 1) ≤ 4e`:
`r(1-6qβ) + q(1-1/Λ₀)f ≥ qX₀ + r`. It follows from scalar gate 5 (`T + 4e < B₀F'`) and `d ≥ 0`. -/
theorem pool_only_gate (n low h : Source) (hv : SourceValidC3 n low h) (hlow : ParentGood low)
    (he : 0≤(n.allowance:ℝ)) {b : ℚ} (hb : (b:ℝ)∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    {s f : ℝ} (hs : s*((low.L:ℝ)-1)≤4*(n.allowance:ℝ)) (hf : (b:ℝ)-s≤f) :
    (n.q:ℝ)*(sourceX0 n low b:ℝ)+(n.lowFee:ℝ)≤
      (n.lowFee:ℝ)*(1-6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ)))+(n.q:ℝ)*(1-1/(low.L:ℝ))*f := by
  have S := shape3_of n low h hv
  have hq0 : 0≤(n.q:ℝ) := by linarith [S.q_half]
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hL0 : 0<(low.L:ℝ) := by linarith
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hd := sourceDReal_nonneg n low h hv hlow he hb
  have g5 := (scalar3_full_width n low h hv hb).1 5
  simp only [scalarGate3Real, sourceF3Real] at g5
  norm_num at g5
  -- B₀(1 - 6r) - T ≥ 4e ≥ s(Λ₀ - 1)
  have hroom : sourceTReal n (b:ℝ)+(b:ℝ)+s*((low.L:ℝ)-1)≤(low.B:ℝ)*(1-6*(n.lowFee:ℝ)) := by
    nlinarith [mul_nonneg hB0 hd]
  have hX : (sourceX0 n low b:ℝ) = (b:ℝ)+(sourceTReal n (b:ℝ)-low.B)/low.L := by
    rw [sourceTReal_rat]; simp [sourceX0]
  have hkey : (sourceX0 n low b:ℝ)+6*((low.B:ℝ)/(low.L:ℝ))*(n.lowFee:ℝ)≤
      (1-1/(low.L:ℝ))*((b:ℝ)-s) := by
    rw [hX]
    have hid : (1-1/(low.L:ℝ))*((b:ℝ)-s)-((b:ℝ)+(sourceTReal n (b:ℝ)-low.B)/low.L+
        6*((low.B:ℝ)/(low.L:ℝ))*(n.lowFee:ℝ)) =
        ((low.B:ℝ)*(1-6*(n.lowFee:ℝ))-(sourceTReal n (b:ℝ)+(b:ℝ)+s*((low.L:ℝ)-1)))/low.L := by
      field_simp; ring
    have : 0≤((low.B:ℝ)*(1-6*(n.lowFee:ℝ))-(sourceTReal n (b:ℝ)+(b:ℝ)+s*((low.L:ℝ)-1)))/low.L :=
      div_nonneg (by linarith) hL0.le
    linarith
  have hk : 0≤1-1/(low.L:ℝ) := by
    have : 1/(low.L:ℝ)≤1 := (div_le_one hL0).mpr hlam.le
    linarith
  have hmono := mul_le_mul_of_nonneg_left hf hk
  have := mul_le_mul_of_nonneg_left (hkey.trans hmono) hq0
  nlinarith

/-- The design's price with the margin `phiK`: valid when the weak cap holds at the node, which
`SourceValid3` gives only at the top node (it is false at `δ = 0` on the chain, LEAN_NOTES). -/
theorem mixed_node_price_phi (n low h : Source) (hv : SourceValidC3 n low h) (hlow : ParentGood low)
    (hden : sourceDen n low ≠ 0) (he : 0≤(n.allowance:ℝ))
    {b δ : ℚ} (hb : (b:ℝ)∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) (hδ0 : 0≤δ) (hδ : δ≤sourceD n low b)
    (hweak : ((low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-
        sourceTReal (vnode n low b δ) ((b-δ:ℚ):ℝ))/(low.L:ℝ)≤
      (low.cap:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)) :
    MixedNodePrice (vnode n low b δ) low ((b-δ:ℚ):ℝ) (phiK n low b δ) := by
  have S := shape3_of n low h hv
  have hg := realGeometryLow_vnode n low h hv hlow hden he hb hδ0 hδ
  have hq0 : 0<(n.q:ℝ) := by linarith [S.q_half]
  have hq1 : (n.q:ℝ)≤1 := by linarith [S.q_lt]
  have hlam : 1<(low.L:ℝ) := by exact_mod_cast hlow.2.2.1
  have hL : 0≤(n.L:ℝ) := by linarith [S.L_gt]
  have hB0 : 0≤(low.B:ℝ) := by exact_mod_cast hlow.1.le
  have hh0 : 0≤(low.cap:ℝ) := by exact_mod_cast hlow.2.2.2.1
  have g7 := (scalar3_full_width n low h hv hb).1 7
  simp only [scalarGate3Real] at g7
  norm_num at g7
  apply mixed_price_of_gain _ low _ _ hlow he hq0.le hq1 hg.qcap_room.le
  intro width f hw0 hw hf hφ
  have hLpos : 0<(low.L:ℝ) := hg.lowL_pos
  have hc := width_charge (vnode n low b δ) low width he hL hq0.le hq1 hlam.le hw
  simp only [vnode_q, vnode_L] at hc
  have hgain : sourceAReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-(n.q:ℝ)*
      (((b-δ:ℚ):ℝ)+(plainBudget (vnode n low b δ) ((b-δ:ℚ):ℝ) width-
        (low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ))/(low.L:ℝ))=
      (vfee n low b δ:ℝ)-(n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ) := by
    have hfi := hg.fee_identity
    simp only [vnode_q, vnode_lowFee] at hfi
    simp only [plainBudget, vnode_L]
    rw [← hfi]; ring
  have hexcess : ((low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-
      plainBudget (vnode n low b δ) ((b-δ:ℚ):ℝ) width)/(low.L:ℝ)-
      (low.cap:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)≤0 := by
    have hh := mul_nonneg hL hw0
    have : ((low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-
        plainBudget (vnode n low b δ) ((b-δ:ℚ):ℝ) width)/(low.L:ℝ)≤
        ((low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-
          sourceTReal (vnode n low b δ) ((b-δ:ℚ):ℝ))/(low.L:ℝ) := by
      apply div_le_div_of_nonneg_right _ hLpos.le
      simp only [plainBudget, vnode_L]; linarith
    linarith
  have hk : 0≤1-1/(low.L:ℝ) := by
    have : 1/(low.L:ℝ)≤1 := (div_le_one hLpos).mpr hlam.le
    linarith
  have hspec := phiK_spec n low b δ hq0 hlam hφ
  -- the affine frozen term is the smaller one
  have hmin : (n.q:ℝ)*((1-1/(low.L:ℝ))*f)≤(n.q:ℝ)*min ((1-1/(low.L:ℝ))*f)
      (f-(((low.B:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ)-
        plainBudget (vnode n low b δ) ((b-δ:ℚ):ℝ) width)/(low.L:ℝ)-
        (low.cap:ℝ)*sourceFReal (vnode n low b δ) low ((b-δ:ℚ):ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hq0.le
    apply le_min le_rfl
    have : (1-1/(low.L:ℝ))*f≤f := by
      have : 0≤1/(low.L:ℝ) := by positivity
      nlinarith
    linarith
  have hp : 0≤((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ))*(n.allowance:ℝ) :=
    mul_nonneg (add_nonneg (div_nonneg (mul_nonneg hq0.le hB0) hLpos.le) (mul_nonneg hq0.le hh0)) he
  have hfg : (27/2:ℝ)*(n.allowance:ℝ)≤frozenGain (vnode n low b δ) low ((b-δ:ℚ):ℝ) width f := by
    simp only [frozenGain, vnode_q]
    rw [hgain]
    have g7' : ((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ)+4)*(n.allowance:ℝ)+
        10*(n.allowance:ℝ)<(n.lowFee:ℝ) := by
      have := g7; push_cast at this ⊢; linarith
    nlinarith
  have ha := hg.a_allowance
  simp only [vnode_allowance] at ha hfg ⊢
  apply le_min <;> linarith

end
end QRH.MixedStep.Ledger
#print axioms QRH.MixedStep.Ledger.raw_low_three_branches_f
#print axioms QRH.MixedStep.Ledger.actual_low_coordinate_payment_f
#print axioms QRH.MixedStep.Ledger.modified_low_coordinate_payment_f
#print axioms QRH.MixedStep.Ledger.mixed_node_price_frozen_of
#print axioms QRH.MixedStep.Ledger.mixed_node_price_top_of
#print axioms QRH.MixedStep.Ledger.pool_only_gate
#print axioms QRH.MixedStep.Ledger.mixed_node_price_phi
