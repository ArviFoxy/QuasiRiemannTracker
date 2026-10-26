/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Shared actual selected HIGH geometry; no analytic estimate is assumed. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.SelectedRegularHighSource
(Hailey Collet, Apache-2.0); changes: two parents. `selected_common_caps` over
`Anchor_mx`/`Family_mx`/`Selected_mx`: the first common ideal is capped through the first layer
(`sourceRadius F.s₀`, `F.zero₁₀`, `F.zero₂₀`), the second through the children of the second-layer
parent. `eventualPredicate` and `key_caps_mono` are reused from Collet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighSource
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceDataState
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularGeometryCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighSource
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice
open Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open SelectedRegularSourceData SelectedSecondKeyCaps
local notation "O"=>HeckeFamily.O
local instance selectedRegularHighSourceDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem selected_common_caps_mx {α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(g:Selected_mx F Row rows second)
    (Af Bfirst Bsecond:ℝ)(hAf:Af≤Bfirst)(hsecond:2≤Bsecond)
    (hs:sourceRadius F.s₀≤Z^Af)(hc:∀u,sourceRadius (F.input (g.row u).val.1.1)≤Z^(2:ℝ)):
    ∀u,((if F.reflected then (F.first (g.row u).val.1).1.2 else
        (F.first (g.row u).val.1).1.1).absNorm:ℝ)≤Z^Bfirst ∧
      ((if second then (g.datum u).D else (g.datum u).C).absNorm:ℝ)≤Z^Bsecond := by
  intro u
  have hf:=FirstFamily.label_common_bounds F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    F.seed_sf F.zero₁₀ F.zero₂₀ (g.column u)
  have hh:=regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ
    ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m (g.row u).val.1
  constructor
  · have hbound:=hs.trans (Real.rpow_le_rpow_of_exponent_le F.hZ.le hAf)
    split_ifs
    · exact hf.2.2.2.trans hbound
    · exact hf.2.2.1.trans hbound
  · have hbound:=(hc u).trans (Real.rpow_le_rpow_of_exponent_le F.hZ.le hsecond)
    split_ifs
    · exact hh.2.trans hbound
    · exact hh.1.trans hbound
end
end QRH.Record1252270103Source.Admission.SelectedRegularHighSource
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighSource.selected_common_caps_mx
