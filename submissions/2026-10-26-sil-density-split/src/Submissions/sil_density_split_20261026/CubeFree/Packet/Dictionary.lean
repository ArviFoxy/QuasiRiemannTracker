/- Copyright (c) 2026 Sil. Apache-2.0.
The packing dictionary of the cube-free step (CPL §3(i),(v); second audit §4).

The finite dictionary index is `DictIdx := RayCharacter` (the characters of `(O/4)ˣ`, a finite
type); the anchors are `anchors η j := rayAnchor η j`, with column coefficients
`rowWeight η fixedBadMask 1 1 t I · j(primaryGenerator I)`.  They depend only on the fixed
base character `η` and on `j`, never on the common factors or the scale.

Composing OAI's second-step exceptional family identity (`Family.height_eq`, base character
the first-step fixed-pair character `F.left`) with the first-side packing gives
(`second_packed`) on residual columns
  `heightCoeff (τ χ) t I = heightCoeff (anchors η j) t I · idealRowHom (V_C·A₂) I`,
`j = ξ₁·firstPhase·χ`, `A₂ = commonFrequencyGenerator·nonunitFrequencyGenerator`.
The second-step canonical keep (`canonicalRadial`) at row `z` is the source keep
`initialKeep (anchors η j) Q` at the packed row `(V_C·A₂)·z` (`packed_keep`): the extra
mask primes (exponent-zero punctures and the genuine second common factor) are removed by
`fixedInducingRow_mul_mask_iff`.  The natural characters agree on the masked columns
(`packed_naturalCharacter`). -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.FirstSidePacking
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalChosenBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRowMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

set_option autoImplicit false

namespace QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators

open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ActualEisensteinCubic RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentDetectorEnergyInitialState CenteredExceptionalProfile

local notation "O" => ActualEisensteinCubic.O

/-- The finite dictionary index. -/
abbrev DictIdx : Type := RayCharacter

instance : Fintype DictIdx := rayCharacterFintype

/-- The fixed finite anchor family over the base character `η`. -/
def anchors (η : Character) : DictIdx → Character := fun j => rayAnchor η j

theorem anchors_height (η : Character) (j : DictIdx) (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff (anchors η j) t I =
      rowWeight η fixedBadMask 1 1 t I * rayCharacter j (primaryGenerator I) :=
  rayAnchor_height η j I hI t

/-! ### Generic keep and natural-character transfer -/

theorem heightCoeff_zero (τ : Character) (I : Ideal O) : heightCoeff τ 0 I = idealCoeff τ I := by
  simp only [heightCoeff, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one]

/-- If `τ`'s ideal coefficients are `σ`'s times `idealRowHom V` on supported columns coprime
to a mask `w`, then the fixed-inducing classification of `τ` at row `z` is that of `σ` at
row `V*z`. -/
theorem fixedInducingRow_transfer (τ σ : Character) (Q : Ideal O) (m V w z : O)
    (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hw : w ≠ 0) (hV : V ≠ 0) (hz : z ≠ 0)
    (hcoef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {w}) →
      idealCoeff τ I = idealCoeff σ I * idealRowHom V I) :
    FixedInducingRow τ Q m 1 z ↔ FixedInducingRow σ Q m 1 (V*z) := by
  rw [← CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q m w 1 z hm hw one_ne_zero hz
      hmLam hm2,
    ← CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff σ Q m w 1 (V*z) hm hw one_ne_zero
      (mul_ne_zero hV hz) hmLam hm2]
  have hmLam' : ConcretePrimeRowBridge.goodLambda ∣ m*w := dvd_mul_of_dvd_left hmLam w
  have hm2' : (2:O) ∣ m*w := dvd_mul_of_dvd_left hm2 w
  have heq : ∀ n : O, rowTwist (HeckeRowClosure.elementHom τ) (m*w) 1 (1*z) n =
      rowTwist (HeckeRowClosure.elementHom σ) (m*w) 1 (1*(V*z)) n := by
    intro n
    by_cases hs : Supported (Ideal.span {n})
    · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs, rowTwist_extract_sixth_mask _ _ _ _ _ hs]
      by_cases hc : IsCoprime (m*w) n
      · have hn0 : n ≠ 0 := CenteredMomentSupportedCorrelation.supported_element_ne_zero n hs
        have hcw : IsCoprime (Ideal.span {n}) (Ideal.span {w}) :=
          (Ideal.isCoprime_span_singleton_iff n w).mpr hc.of_mul_left_right.symm
        have hτn : HeckeRowClosure.elementHom τ n =
            HeckeRowClosure.elementHom σ n * idealRowHom V (Ideal.span {n}) := by
          change elementCoeff τ n = elementCoeff σ n * idealRowHom V (Ideal.span {n})
          rw [← idealCoeff_span τ hn0, ← idealCoeff_span σ hn0]
          exact hcoef _ hs hcw
        rw [hτn]
        simp only [one_pow, one_mul, idealRowHom_argument_mul]
        ring
      · have h0 : coprimalityMask (m*w) n = 0 := by
          change (if IsCoprime (m*w) n then (1:ℂ) else 0) = 0
          rw [ite_eq_right hc]
        rw [h0, mul_zero, zero_mul, mul_zero, zero_mul]
    · rw [rowTwist_zero_of_not_supported _ _ _ _ _ hmLam' hm2' hs,
        rowTwist_zero_of_not_supported _ _ _ _ _ hmLam' hm2' hs]
  have hfun : rowTwist (HeckeRowClosure.elementHom τ) (m*w) 1 (1*z) =
      rowTwist (HeckeRowClosure.elementHom σ) (m*w) 1 (1*(V*z)) := MonoidHom.ext heq
  unfold FixedInducingRow
  rw [hfun]

/-- The second-step canonical keep at row `z` is the source keep at the packed row `V*z`. -/
theorem keep_transfer (τ σ : Character) (Q : Ideal O) (n : Fin 4 → ℤ) (V w z : O)
    (hw : w ≠ 0) (hV : V ≠ 0)
    (hcoef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {w}) →
      idealCoeff τ I = idealCoeff σ I * idealRowHom V I) :
    (canonicalRadial τ Q n).keep z ↔ initialKeep σ Q (V*z) := by
  change (z ≠ 0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z) ↔
    (V*z ≠ 0 ∧ ¬FixedInducingRow σ Q (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (V*z))
  by_cases hz : z = 0
  · simp [hz]
  · have hVz : V*z ≠ 0 := mul_ne_zero hV hz
    rw [CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff σ Q fixedBadMask
        (ConcretePrimeRowBridge.idealGenerator 1) 1 (V*z) fixedBadMask_ne_zero
        (ConcretePrimeRowBridge.idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hVz
        (dvd_mul_right _ _) (dvd_mul_left _ _),
      fixedInducingRow_transfer τ σ Q fixedBadMask V w z fixedBadMask_ne_zero (dvd_mul_right _ _)
        (dvd_mul_left _ _) hw hV hz hcoef]
    simp [hz, hVz]

/-- Natural characters agree on the masked columns after packing. -/
theorem naturalCharacter_transfer (τ σ : Character) (V w z : O) (hV : V ≠ 0) (hz : z ≠ 0)
    (hcoef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {w}) →
      idealCoeff τ I = idealCoeff σ I * idealRowHom V I)
    (I : Ideal O) (hI : Supported I) (hIw : IsCoprime I (Ideal.span {w})) :
    idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter τ z) I =
      idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter σ (V*z)) I := by
  rw [CenteredMomentAllocatedNaturalRadial.naturalCharacter_eq τ z hz,
    CenteredMomentAllocatedNaturalRadial.naturalCharacter_eq σ (V*z) (mul_ne_zero hV hz),
    CenteredMomentNaturalRowSource.NaturalRow.ideal, CenteredMomentNaturalRowSource.NaturalRow.ideal,
    hcoef I hI hIw]
  simp only [idealRowHom_argument_mul]
  ring

/-! ### The packed second-step dictionary -/

theorem firstPacked_ne_zero (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D)) :
    firstPacked C D hC E ≠ 0 := by
  unfold firstPacked
  refine mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ E) (activeUnit C D hC).ne_zero)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ ?_))
  exact supported_primaryGenerator_ne_zero _ (activePrime_supported C D hC i)

theorem firstPackedRight_ne_zero (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) : firstPackedRight C D hC E ≠ 0 := by
  unfold firstPackedRight
  refine mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ E) (activeUnit C D hC).ne_zero)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ ?_))
  exact supported_primaryGenerator_ne_zero _ (activePrime_supported C D hC i)

/-- The second-step frequency twist `A₂`. -/
def secondTwist (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂)) : O :=
  commonFrequencyGenerator C₂ D₂ * nonunitFrequencyGenerator C₂ D₂ U

theorem secondTwist_ne_zero (C₂ D₂ : Ideal O) (hC₂ : Supported C₂)
    (U : Finset (CommonIndex C₂ D₂)) : secondTwist C₂ D₂ U ≠ 0 :=
  mul_ne_zero (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C₂ D₂ hC₂)
    (nonunitFrequencyGenerator_ne_zero C₂ D₂ hC₂ U)

/-- Mask element of the packed dictionary: exponent-zero primes times the genuine second common
factor. -/
def packMask (Z C₂ : Ideal O) : O := ConcretePrimeRowBridge.idealGenerator (Z * C₂)

theorem firstZeroPrimes_ne_zero (C D : Ideal O) : firstZeroPrimes C D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => commonIndex_ne_zero C D i.val)

theorem firstZeroPrimesRight_ne_zero (C D : Ideal O) : firstZeroPrimesRight C D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => commonIndex_ne_zero C D i.val)

theorem packMask_ne_zero (Z C₂ : Ideal O) (hZ : Z ≠ 0) (hC₂ : Supported C₂) : packMask Z C₂ ≠ 0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero _ (mul_ne_zero hZ hC₂.1)

theorem packMask_coprime (Z C₂ I : Ideal O) (h : IsCoprime I (Ideal.span {packMask Z C₂})) :
    IsCoprime I Z ∧ IsCoprime C₂ I := by
  rw [packMask, ConcretePrimeRowBridge.span_idealGenerator, IsCoprime.mul_right_iff] at h
  exact ⟨h.1, h.2.symm⟩

/-- Dictionary index of the second-step character `τ χ` built on the first-step side with
ray twist `ξ` (`ξ = ξ₁` on the left, `ξ = ξ₂` on the right). -/
def dictIdx (C D : Ideal O) (hC : Supported C) (ξ χ : RayCharacter) : DictIdx :=
  ξ * firstPhase C D hC * χ

/-- The packed row multiplier `V_C·A₂` of the left side. -/
def leftRow (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂)) : O :=
  firstPacked C D hC E * secondTwist C₂ D₂ U

/-- The packed row multiplier `V_D·A₂` of the right side. -/
def rightRow (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂)) : O :=
  firstPackedRight C D hC E * secondTwist C₂ D₂ U

section Left
variable {η : Character} {C D : Ideal O} {hC : Supported C} {E : Finset (CommonIndex C D)}
  {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
  {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂} {U : Finset (CommonIndex C₂ D₂)}
  {τ : RayCharacter → Character}

/-- **Second-step packing (left).** -/
theorem second_packed (h : Family F.left C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I (firstZeroPrimes C D))
    (hi : IsCoprime C₂ I ∨ IsCoprime D₂ I) (t : ℝ) :
    heightCoeff (τ χ) t I =
      heightCoeff (anchors η (dictIdx C D hC ξ₁ χ)) t I *
        idealRowHom (leftRow C D hC E C₂ D₂ U) I := by
  rw [h.height_eq χ I hI hi t, left_packed F I hI hZ t, anchors, dictIdx,
    rayAnchor_mul_height η _ χ I hI t, leftRow, secondTwist]
  simp only [idealRowHom_argument_mul]
  ring

theorem second_packed_idealCoeff (h : Family F.left C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I)
    (hw : IsCoprime I (Ideal.span {packMask (firstZeroPrimes C D) C₂})) :
    idealCoeff (τ χ) I =
      idealCoeff (anchors η (dictIdx C D hC ξ₁ χ)) I *
        idealRowHom (leftRow C D hC E C₂ D₂ U) I := by
  obtain ⟨hZ, hc⟩ := packMask_coprime _ _ I hw
  have hh := second_packed F h χ I hI hZ (Or.inl hc) 0
  rwa [heightCoeff_zero, heightCoeff_zero] at hh

/-- **Packed keep (left).**  The canonical second-step keep at row `z` is the source keep of
the anchor `anchors η (dictIdx C D hC ξ₁ χ)` at the packed row `(V_C·A₂)·z`. -/
theorem packed_keep (h : Family F.left C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter) (Q : Ideal O)
    (n : Fin 4 → ℤ) (z : O) :
    (canonicalRadial (τ χ) Q n).keep z ↔
      initialKeep (anchors η (dictIdx C D hC ξ₁ χ)) Q
        (leftRow C D hC E C₂ D₂ U * z) :=
  keep_transfer _ _ Q n _ _ z (packMask_ne_zero _ _ (firstZeroPrimes_ne_zero C D) hC₂)
    (mul_ne_zero (firstPacked_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U))
    (fun I hI hw => second_packed_idealCoeff F h χ I hI hw)

/-- **Packed natural character (left).** -/
theorem packed_naturalCharacter (h : Family F.left C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (z : O) (hz : z ≠ 0) (I : Ideal O) (hI : Supported I)
    (hw : IsCoprime I (Ideal.span {packMask (firstZeroPrimes C D) C₂})) :
    idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter (τ χ) z) I =
      idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter
        (anchors η (dictIdx C D hC ξ₁ χ))
        (leftRow C D hC E C₂ D₂ U * z)) I :=
  naturalCharacter_transfer _ _ _ _ z
    (mul_ne_zero (firstPacked_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U)) hz
    (fun I hI hw => second_packed_idealCoeff F h χ I hI hw) I hI hw

end Left

section Right
variable {η : Character} {C D : Ideal O} {hC : Supported C} {E : Finset (CommonIndex C D)}
  {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
  {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂} {U : Finset (CommonIndex C₂ D₂)}
  {τ : RayCharacter → Character}

/-- **Second-step packing (right).** -/
theorem second_packed_right (h : Family F.right C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I (firstZeroPrimesRight C D))
    (hi : IsCoprime C₂ I ∨ IsCoprime D₂ I) (t : ℝ) :
    heightCoeff (τ χ) t I =
      heightCoeff (anchors η (dictIdx C D hC ξ₂ χ)) t I *
        idealRowHom (rightRow C D hC E C₂ D₂ U) I := by
  rw [h.height_eq χ I hI hi t, right_packed F I hI hZ t, anchors, dictIdx,
    rayAnchor_mul_height η _ χ I hI t, rightRow, secondTwist]
  simp only [idealRowHom_argument_mul]
  ring

theorem second_packed_right_idealCoeff (h : Family F.right C₂ D₂ hC₂ hD₂ U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I)
    (hw : IsCoprime I (Ideal.span {packMask (firstZeroPrimesRight C D) C₂})) :
    idealCoeff (τ χ) I =
      idealCoeff (anchors η (dictIdx C D hC ξ₂ χ)) I *
        idealRowHom (rightRow C D hC E C₂ D₂ U) I := by
  obtain ⟨hZ, hc⟩ := packMask_coprime _ _ I hw
  have hh := second_packed_right F h χ I hI hZ (Or.inl hc) 0
  rwa [heightCoeff_zero, heightCoeff_zero] at hh

/-- **Packed keep (right).** -/
theorem packed_keep_right (h : Family F.right C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (Q : Ideal O) (n : Fin 4 → ℤ) (z : O) :
    (canonicalRadial (τ χ) Q n).keep z ↔
      initialKeep (anchors η (dictIdx C D hC ξ₂ χ)) Q
        (rightRow C D hC E C₂ D₂ U * z) :=
  keep_transfer _ _ Q n _ _ z (packMask_ne_zero _ _ (firstZeroPrimesRight_ne_zero C D) hC₂)
    (mul_ne_zero (firstPackedRight_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U))
    (fun I hI hw => second_packed_right_idealCoeff F h χ I hI hw)

/-- **Packed natural character (right).** -/
theorem packed_naturalCharacter_right (h : Family F.right C₂ D₂ hC₂ hD₂ U τ)
    (χ : RayCharacter) (z : O) (hz : z ≠ 0) (I : Ideal O) (hI : Supported I)
    (hw : IsCoprime I (Ideal.span {packMask (firstZeroPrimesRight C D) C₂})) :
    idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter (τ χ) z) I =
      idealCoeff (CenteredMomentAllocatedNaturalRadial.naturalCharacter
        (anchors η (dictIdx C D hC ξ₂ χ))
        (rightRow C D hC E C₂ D₂ U * z)) I :=
  naturalCharacter_transfer _ _ _ _ z
    (mul_ne_zero (firstPackedRight_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U)) hz
    (fun I hI hw => second_packed_right_idealCoeff F h χ I hI hw) I hI hw

end Right

end

end QRH.SilDensitySplit.CubeFree.Packet
