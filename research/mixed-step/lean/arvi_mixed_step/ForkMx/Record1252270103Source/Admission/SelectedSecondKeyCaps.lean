/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained signed-key support caps. The original modified columns,
complete-block filter and single-reference-ray kept rows are retained. -/
/- Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.SelectedSecondKeyCaps
(Hailey Collet, Apache-2.0); changes: two parents. In `eventual_regular_key_caps` the original
(first-layer) input `original : Input α₀` gives the columns, labels and the first caps; the second
blocks (`slots`, `s`) live on the second-layer slot type `α`; the volume of the MAIN Fourier scale
and of the coordinates is a free positive real `V` (the second-layer volume downstream). The proof
is Collet's, with `eventual_literal_high_frequency_mx`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondKeyCaps
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.FirstFamilyGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildInput CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open Cycle61Moment Cycle61InitialMass LocalMoment
open CenteredMomentOriginalCommonHarmonic
open High.GlobalPhysical SecondSectorDatum SelectedSecondNatural SelectedHighCofactorCoordinates HighScalar
local notation "O" => HeckeFamily.O
local instance selectedSecondKeyCapsDecEq_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Collet's `eventual_regular_key_caps` with two parents and a free volume `V`. -/
theorem eventual_regular_key_caps_mx (b err:ℝ)(N:ℕ)(hb:0<b)(herr:0<err):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label],
    ∀(slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
      (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(ξ:ℝ)(W:𝓢(ℝ,ℂ))
      (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
      (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)
      (original:Input α₀)(originalModifier:Tuple α₀→ℂ)(R₀ seed₀:Ideal O)
      (D:ℝ)(hK₀:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
      (column:Label→FirstColumnIndex (High.CoupledFirst.geometryFirstSource original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin))
      (hs₀:Squarefree seed₀)(hz₀₁:original.W₁ 0=0)(hz₀₂:original.W₂ 0=0)(V:ℝ)(hV:0<V),
    let datum:=regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m
    let first : CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)→FirstSourceLabel :=fun q=>FirstFamily.firstLabel original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin (column q.1)
    ∀(r:secondLiveRows (fun q=>(datum q).block))
      (amp reserve errv forced live small annular Afirst Asecond Brow:ℝ),
      ξ≤err→sourceRadius original≤Z^Afirst→sourceRadius (s r.val.1.1)≤Z^Asecond→
      Tsec r.val.1.1=firstMainFourierScale reflected (Z^D) V Z ξ (3*amp) reserve b N (first r.val.1)→
    let key:=FirstFamily.rawKey reflected original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin
      (column r.val.1.1) datum first r rfl second
    let x:=cofactorCoordinates reflected second (first r.val.1) (datum r.val.1).C (datum r.val.1).D
      (datum r.val.1).inactive Z D (Real.logb Z V) amp ξ reserve err errv forced live small annular
    x 2≤Brow→KeyCaps key Z (coarseExponent Afirst Asecond Brow) (x 1) := by
  filter_upwards [FirstFamily.eventual_literal_high_frequency_mx b err N hb herr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α₀ α Label _ _ _ slots s modifier R seed K Tsec ξ W hseed hz₁ hz₂ hK χ₀ Q m
    original originalModifier R₀ seed₀ D hK₀ bin reflected second column hs₀ hz₀₁ hz₀₂ V hV
    datum first r amp reserve errv forced live small annular Afirst Asecond Brow hξ hsource₀ hsource₁ hT key x hq
  have hradius:(datum r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) V Z ξ (3*amp) reserve b N (first r.val.1)) Z ξ:=by
    change frequencyRadius (Tsec r.val.1.1) Z ξ=_
    rw [hT]
  have hf:=hZ.2 reflected second original originalModifier R₀ seed₀ D ξ hK₀ bin (column r.val.1.1)
    datum first r rfl V amp reserve errv hV hξ hradius
  have hraw:rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2):=by
    simpa [key,FirstFamily.rawKey,x,cofactorCoordinates,lostWidthCoordinates,first] using hf
  have hrow:=hraw.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hq)
  have hfirst:=FirstFamily.label_common_bounds original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin hs₀ hz₀₁ hz₀₂ (column r.val.1.1)
  have hsecond:=regular_common_caps slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1
  have hsupp:=FirstFamily.label_supported original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin (column r.val.1.1)
  have hkeyfirst:key.val.1=first r.val.1:=by cases second <;> rfl
  have hkeysecond:key.val.2.1=((datum r.val.1).C,(datum r.val.1).D):=by cases second <;> rfl
  have hc:Supported key.val.1.1.1:=by rw [hkeyfirst];exact hsupp.1
  have hd:Supported key.val.1.1.2:=by rw [hkeyfirst];exact hsupp.2.1
  have hc₁:(key.val.1.1.1.absNorm:ℝ)≤Z^Afirst:=by
    rw [hkeyfirst];exact hfirst.2.2.1.trans hsource₀
  have hd₁:(key.val.1.1.2.absNorm:ℝ)≤Z^Afirst:=by
    rw [hkeyfirst];exact hfirst.2.2.2.trans hsource₀
  have hc₂:(key.val.2.1.1.absNorm:ℝ)≤Z^Asecond:=by
    rw [hkeysecond];exact hsecond.1.trans hsource₁
  have hd₂:(key.val.2.1.2.absNorm:ℝ)≤Z^Asecond:=by
    rw [hkeysecond];exact hsecond.2.trans hsource₁
  have hx:x 1=Real.logb Z ((firstSourceMissing (!reflected) key.val.1).absNorm:ℝ):=by
    rw [hkeyfirst]
    simp [x,cofactorCoordinates,lostWidthCoordinates,childHighCoordinates,actualHighCoordinates]
  rw [hx]
  exact key_caps_of_frequency key Z Afirst Asecond Brow hZ.1 hc hd hc₁ hd₁ hc₂ hd₂ hrow

end
end QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps.eventual_regular_key_caps_mx
