/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Core.ExceptionalFirstSum
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: the genuine first common
geometry and centered gate pay the entire selected first-label/projector sum, using the original
modified coefficient.

Two parents, two amplitudes. The first-label/projector sum runs over the columns of the first
layer `s` (= `s₀`: labels, balanced first mass, counting), while the radial factor
`firstRadialFactor_mx` carries the second-layer volume `V`, the MAIN-radius amplitude `amp` and the
pool reciprocal at the actual pool amplitude `a`. The node gate is the mixed centered gate. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstSum
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Core.ExceptionalFirstScalar

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentAmplificationChildInput
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open OAI.SevenEighths.Record1252270103Source.Collision
open High.CoupledFirst Admission MarkedMainRemainder
local notation "O"=>HeckeFamily.O

/-- Collet's `firstRadialFactor` with the radius amplitude `amp` and the pool amplitude
`poolAmp` separated. -/
def firstRadialFactor_mx (reflected : Bool) (l : FirstSourceLabel)
    (Z V r amp poolAmp ξ reserve loss : ℝ) : ℝ :=
  let C : Ideal O:=if reflected then l.1.2 else l.1.1
  (V/(C.absNorm:ℝ))^(1/3:ℝ)*
    (firstMainRadius reflected Z V Z ξ (3*amp) reserve l)^(5/6:ℝ)*
    (max 1 (Z^r/(C.absNorm:ℝ)))^(-(2*(499/1000:ℝ)))*Z^(-poolAmp+loss)

lemma firstRadialFactor_mx_nonneg (reflected : Bool) (l : FirstSourceLabel)
    (Z V r amp poolAmp ξ reserve loss : ℝ) (hZ : 0<Z) (hV : 0<V) :
    0≤firstRadialFactor_mx reflected l Z V r amp poolAmp ξ reserve loss := by
  have hH:=first_main_radius_pos reflected Z V Z ξ (3*amp) reserve hZ l
  unfold firstRadialFactor_mx
  positivity

/-- Collet's radial factor with the loss shifted by `amp - poolAmp` is the mixed one. -/
theorem firstRadialFactor_shift_mx (reflected : Bool) (l : FirstSourceLabel)
    (Z V r amp poolAmp ξ reserve loss loss' : ℝ) (hloss : loss'=loss+(amp-poolAmp)) :
    firstRadialFactor reflected l Z V r amp ξ reserve loss'=
      firstRadialFactor_mx reflected l Z V r amp poolAmp ξ reserve loss := by
  unfold firstRadialFactor firstRadialFactor_mx
  rw [hloss,show -amp+(loss+(amp-poolAmp))=-poolAmp+loss by ring]

/-- Every selected first arithmetic key of the first layer and its residual projector is summed,
against the second-layer radial factor (two parents, two amplitudes). -/
theorem selected_first_radical_sum_mx (N : ℕ)(lo ap B Bseed ε : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(hB : 0≤B)(hBseed : 0≤Bseed)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι)
      (A₁ A₂ Dmark Kmark R seed : Ideal O)(F : Ideal O→ℂ)(W : 𝓢(ℝ,ℂ))
      (K : ℚ)(n : Source)(b ξ reserve loss plainError V Amix a κ amp : ℝ),
      sourceTReal n b+b+9*Amix+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b)→
      Fintype.card ι≤N→lo≤s.lower→
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      (∀x,s.W₁ x≠0→ap≤x)→(∀x,s.W₂ x≠0→ap≤x)→
      Real.logb Z (volume s)≤sourceTReal n b+b+plainError→
      0<V→amp-a≤Real.logb Z (volume s)-Real.logb Z V+κ→amp≤Amix→
      plainError+5*(frequencyLoss Z 32 ξ+reserve)/6+loss+2*κ≤2*Amix-a→
    let modifier:=markedSourceModifier A₁ A₂ Dmark Kmark F
    ∀(hZ : 1<Z)(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R seed (Z^1) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^Bseed)→
      (∑j,balancedFirstHighMass reflected s modifier R seed W 1 Z ξ 0
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)*
        firstRadialFactor_mx reflected (FirstFamily.firstLabel s modifier R seed (Z^1) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) bin (column j)) Z V
          (49/100-(K:ℝ)*b) amp a ξ reserve loss/
        ((column j).2.1.val.absNorm:ℝ))≤
        C*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
          Z^(-(n.highFee:ℝ)-4*Amix+2*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩:=eventual_selected_modified_payment B Bseed ε hB hBseed hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst dec s A₁ A₂ Dmark Kmark R seed F W K n b ξ reserve loss plainError V Amix a κ amp
    hgate hN hlower hs hs0 hz₁ hz₂ hsource hs₁ hs₂ hA hV hshift hamp herr modifier hZ reflected bin
    J instJ column hinj hlive hcap
  let hK : 0<Z^(1:ℝ):=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1
  let factor:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  have hfactor : 0≤factor := (geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  apply hz.2 s modifier R seed (Z^1) ξ hK bin hs hs0 hz₁ hz₂ hsource J column hinj hlive hcap
    factor (-(n.highFee:ℝ)-4*Amix) _ hfactor
  intro j
  let l:=FirstFamily.firstLabel s modifier R seed (Z^1) Z ξ hK bin (column j)
  have hsupp:=FirstFamily.label_supported s modifier R seed (Z^1) Z ξ hK bin (column j)
  have hv:=HighScalar.modified_first_label_valuations s A₁ A₂ Dmark Kmark R seed F
    (Z^1) Z ξ hK bin (column j)
  have hprice:=actual_first_scalar_cost_mx K n b Amix a κ hgate reflected l hsupp.1 hsupp.2.1
    hsupp.2.2 hv.1 hv.2 Z (volume s) V amp ξ reserve loss plainError hZ hV hA hshift hamp herr
  have hm:=actual_balanced_uniform_high_mass reflected N lo ap hlo hap s modifier R seed W 1 Z ξ B 0
    hZ hK (le_refl 0) hN hlower hs hz₁ hz₂ hsource hs₁ hs₂ bin (column j)
  simp only [mul_zero,Real.rpow_zero,mul_one] at hm
  rw [modified_balanced_scalar_side s modifier R seed (Z^1) Z ξ hK bin (column j)] at hm
  have hfn:=firstRadialFactor_mx_nonneg reflected l Z V (49/100-(K:ℝ)*b)
    amp a ξ reserve loss (zero_lt_one.trans hZ) hV
  have hh:=mul_le_mul_of_nonneg_right hm hfn
  have he : (factor/Z^(QRH.Record12518109Assembly.Scalar.left (Real.logb Z (volume s))
        (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelE l Z)))*
        firstRadialFactor_mx reflected l Z V (49/100-(K:ℝ)*b) amp a ξ reserve loss=
      factor*firstScalarCost_mx reflected l Z (volume s) V (49/100-(K:ℝ)*b)
        amp a ξ reserve loss := by
    unfold firstRadialFactor_mx firstScalarCost_mx
    ring
  change _≤(factor/Z^(QRH.Record12518109Assembly.Scalar.left (Real.logb Z (volume s))
      (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelE l Z)))*
    firstRadialFactor_mx reflected l Z V (49/100-(K:ℝ)*b) amp a ξ reserve loss at hh
  rw [he] at hh
  have hb:=hh.trans (mul_le_mul_of_nonneg_left hprice hfactor)
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.firstRadialFactor_mx_nonneg
#print axioms QRH.Record1252270103Source.ExceptionalPrice.firstRadialFactor_shift_mx
#print axioms QRH.Record1252270103Source.ExceptionalPrice.selected_first_radical_sum_mx
