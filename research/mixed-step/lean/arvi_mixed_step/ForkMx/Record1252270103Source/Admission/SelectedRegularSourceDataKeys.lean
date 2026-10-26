/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The same concrete selected rows receive the actual signed-key and frequency caps. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.SelectedRegularSourceDataKeys
(Hailey Collet, Apache-2.0); changes: two parents. Over `Anchor_mx`/`Family_mx`/`Selected_mx` the
first caps come from the first layer (`sourceRadius F.s₀`, `F.zero₁₀`, `F.zero₂₀`), the second caps
from the children of the second-layer parent, and the MAIN Fourier scale, the frequency radius and
the coordinates are read at the second-layer volume `volume F.s`. The proof is Collet's, with
`eventual_regular_key_caps_mx` and `eventual_literal_high_frequency_mx` at `V = volume F.s`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularSourceDataKeys
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceData
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedSecondKeyCaps
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularSourceData
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open Cycle61Moment Cycle61InitialMass LocalMoment
open SelectedSecondNatural SelectedSecondKeyCaps SelectedHighCofactorFamily SelectedHighCofactorCoordinates HighScalar
local notation "O"=>HeckeFamily.O
local instance selectedRegularSourceDataKeysDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Collet's `eventual_selected_keys` with two parents. -/
theorem eventual_selected_keys_mx (b err:ℝ)(N:ℕ)(hb:0<b)(herr:0<err):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
      (errv annular Afirst Asecond Brow:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α),
      F.ξ≤err→sourceRadius F.s₀≤Z^Afirst→
      (∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^Asecond)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve b N (F.first (G.row u).val.1))→
      (∀u,G.x err errv annular w wmin T u 2≤Brow)→∀u,
      KeyCaps (G.key u) Z (coarseExponent Afirst Asecond Brow) (G.x err errv annular w wmin T u 1) ∧
      rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(G.x err errv annular w wmin T u 2) := by
  filter_upwards [eventual_regular_key_caps_mx b err N hb herr,
    FirstFamily.eventual_literal_high_frequency_mx b err N hb herr] with Z hk hf
  refine ⟨hk.1,?_⟩
  intro α₀ α Label Row _ _ _ a F rows second G errv annular Afirst Asecond Brow w wmin T hξ hs₀ hs₁ hT hq u
  have hcaps:=hk.2 F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec F.ξ ballProfile
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m
    F.s₀ F.modifier₀ F.R F.seed F.D F.hK F.bin F.reflected second F.column F.seed_sf F.zero₁₀ F.zero₂₀
    (volume F.s) (volume_pos F.s)
    (G.row u) (F.amp (G.row u).val.1.1) F.reserve errv ((G.sel u).forced Z) ((G.sel u).live w wmin)
    (∑i∈Record12518109Natural.MarkedPlain.largeSlots T w wmin,w i) annular Afirst Asecond Brow hξ hs₀ (hs₁ u) (hT u) (hq u)
  have hradius:(F.datum (G.row u).val.1).radius=frequencyRadius
    (firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ (3*F.amp (G.row u).val.1.1)
      F.reserve b N (F.first (G.row u).val.1)) Z F.ξ:=by
    change frequencyRadius (F.Tsec (G.row u).val.1.1) Z F.ξ=_
    rw [hT u]
  have hfreq:=hf.2 F.reflected second F.s₀ F.modifier₀ F.R F.seed F.D F.ξ F.hK F.bin (G.column u)
    F.datum F.first (G.row u) rfl (volume F.s) (F.amp (G.row u).val.1.1) F.reserve errv (volume_pos F.s) hξ hradius
  refine ⟨hcaps,?_⟩
  simpa [Selected_mx.key,FirstFamily.rawKey,Selected_mx.x,Selection.coordinate,cofactorCoordinates,
    lostWidthCoordinates,Selected_mx.datum,Family_mx.first,Selected_mx.column] using hfreq

end
end QRH.Record1252270103Source.Admission.SelectedRegularSourceData
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.eventual_selected_keys_mx
