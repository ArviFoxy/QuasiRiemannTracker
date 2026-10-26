/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
First-label geometry is read from the actual modified common-label fiber. -/
/- Mixed step (L4/L5, F4): fork of Record1252270103Source.Admission.FirstFamilyGeometry
(Hailey Collet); changes: two parents. In `eventual_literal_high_frequency` the first
label, its column and the fixed parent unit are read from the first layer `s₀ : Input α₀`, the
second datum lives on the second-layer slot type `α`, and the volume of the MAIN Fourier scale and
of the coordinates is a free positive real `V` (the second-layer volume `volume s` downstream).
The proof is Collet's: `eventual_actual_child_high_frequency` already takes the volume as a free
positive real. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.FirstFamily
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentFirstSourceConductorCaps CenteredMomentEnergyState
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentCommonRadialData
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic Cycle61InitialMass
open Record12518109Raw Filter CenteredMomentSectorLocalization LocalMoment ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- Collet's `eventual_literal_high_frequency` with two parents: the first label from `s₀`, the
datum over `α`, and a free positive volume `V`. -/
theorem eventual_literal_high_frequency_mx
    (b εfreq : ℝ)(N : ℕ)(hb : 0<b)(hε : 0<εfreq) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀{α₀ α DataLabel : Type}[Fintype α₀][DecidableEq α₀][Fintype α][DecidableEq α][Fintype DataLabel],
    ∀(reflected second : Bool)(s₀ : Input α₀)(modifier₀ : CenteredMomentAddedZeroUniform.Tuple α₀→ℂ)
      (R seed : Ideal O)(D ξ : ℝ)(hK : 0<Z^D)
      (bin : ℤ×(Fin 5→ℤ))
      (column : FirstColumnIndex (source s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : secondLiveRows (fun l=>(datum l).block))
      (hfirst : first row.val.1=firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin column)
      (V ampExponent reserveShift εvolume : ℝ),
    0<V → ξ≤εfreq →
    (datum row.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) V Z ξ (3*ampExponent) reserveShift b N
        (firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin column)) Z ξ →
    let left:=!reflected
    let unit:=fun l=>(fixedParentUnit left s₀.η l:O)
    let hf:=first_frequency_ne_zero reflected s₀ modifier₀ R seed (Z^D) Z ξ hK
      bin column datum first row hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left 1 unit hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let d₂:=datum row.val.1
    let x:=childHighCoordinates (actualHighCoordinates reflected left second
      (firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin column) d₂.C d₂.D d₂.inactive
      Z D (Real.logb Z V) ampExponent ξ reserveShift εfreq) εvolume
    rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2) := by
  filter_upwards [eventual_actual_child_high_frequency 1 b εfreq N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro α₀ α DataLabel _ _ _ _ _ reflected second s₀ modifier₀ R seed D ξ hK bin column datum first row hfirst
    V ampExponent reserveShift εvolume hV hξ hradius left unit hf key₀ key d₂ x
  have hC : Supported (first row.val.1).1.1 := hfirst.symm ▸
    (source s₀ modifier₀ R seed (Z^D) Z ξ hK bin column.1).hC
  have hD : Supported (first row.val.1).1.2 := hfirst.symm ▸
    (source s₀ modifier₀ R seed (Z^D) Z ξ hK bin column.1).hD
  have heq : primeSupport (first row.val.1).1.1=primeSupport (first row.val.1).1.2 := hfirst.symm ▸
    (source s₀ modifier₀ R seed (Z^D) Z ξ hK bin column.1).sameSupport
  have hret:=actual_second_live_retained_weight (fun l=>(datum l).block) row.val row.property
  change retainedWeight d₂.radius (normValue
    ((commonFrequencyGenerator d₂.C d₂.D*nonunitFrequencyGenerator d₂.C d₂.D d₂.inactive)*
      row.val.2.2.2.val))≠0 at hret
  rw [hradius] at hret
  have hh:=hz.2 reflected left second (fixedParentUnit left s₀.η) key₀ hC hD heq
    V D ampExponent reserveShift ξ εvolume hV hξ (by
      simpa only [key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
        originalSecondBlock,hfirst] using hret)
  have hfreq : rawFrequencyNorm (nonzeroJointSourceRow key₀)≤Z^(x 2) := by
    simpa only [x,key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
      originalSecondBlock,hfirst,rawFrequencyNorm,nonzeroJointSourceRow,normValue] using hh.2
  cases second
  · exact hfreq
  · exact (reflected_joint_norm key₀).trans_le hfreq

end
end QRH.Record1252270103Source.Admission.FirstFamily
#print axioms QRH.Record1252270103Source.Admission.FirstFamily.eventual_literal_high_frequency_mx
