/- `row_rays_fourth` is adapted from Sil's `fixed_product_rays`
(FourthPower/MixedSupplierKernel.lean, PR 74, vendored in PR 76). Changes: no fixed
supplier `f`; stated for ideals through `primaryGaussRow` (unsupported columns
included) and followed by Sil's `normalized_fourth_power` column by column. The rest
is new in this submission.

Mixed source step, L2 transfer: the per-column fourth-power identity and the
column/tuple dictionary for Collet's source polynomials.

`row_rays_fourth` is the exact CRT + ray + fourth-power identity for one
column `D·n`, with the coprimality mask on the left; it is Sil's
`masked_product_rays` followed by `normalized_fourth_power`, stated for
ideals through `primaryGaussRow` (so unsupported columns are covered). -/
import Submissions.arvi_mixed_step.Transfer.Factor
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierKernel
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierReconstruction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondChildProfile

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentHeckeExpansion
open CenteredMomentFirstColumns CenteredMomentChildRows CenteredMomentSupportedCorrelation
open RayFourExpansion CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

theorem gaussRow_congr (a b : O) (h : a = b) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (k : O) : gaussRow a ha k = gaussRow b hb k := by
  subst h
  rfl

theorem primaryGaussRow_of_supported (I : Ideal O) (hI : Supported I) (k : O) :
    primaryGaussRow I k = gaussRow (primaryGenerator I) (MixedSelectedCommon.primary_supported I hI) k := by
  simp only [primaryGaussRow, hI, ↓reduceDIte]

theorem primaryGaussRow_of_not_supported (I : Ideal O) (hI : ¬Supported I) (k : O) :
    primaryGaussRow I k = 0 := by
  simp only [primaryGaussRow, hI, ↓reduceDIte]

/-- Exact CRT/ray/fourth-power identity for a single column `D·n`. The
coprimality mask is on the left; on the right it is produced by the natural
zero of the moving character. Only `n` needs to be fifth-power free. -/
theorem row_rays_fourth (D n : Ideal O) (hfree : Supported n → SexticSieve.PowerFree 5 n)
    (k : O) :
    (if IsCoprime D n then primaryGaussRow (D * n) k else 0) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (rayCharacter χ (primaryGenerator D) * primaryGaussRow D k) *
        (rayCharacter ξ (primaryGenerator n) * primaryGaussRow n ((primaryGenerator D)^4 * k)) := by
  by_cases hD : Supported D
  · by_cases hn : Supported n
    · have hDn : Supported (D * n) := (supported_mul_iff D n).mpr ⟨hD, hn⟩
      have hd := MixedSelectedCommon.primary_supported D hD
      have ha := MixedSelectedCommon.primary_supported n hn
      have hpd := (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
      have hpa := (primaryGenerator_spec n (supported_primaryGenerator_ne_zero n hn)).2
      have hff : GaussTransfer.FifthFree (primaryGenerator n) :=
        KernelWholeColumns.element_fifth_free _ (by rw [primary_span_supported n hn]; exact hfree hn)
      have hcop : IsCoprime (primaryGenerator D) (primaryGenerator n) ↔ IsCoprime D n := by
        rw [← Ideal.isCoprime_span_singleton_iff, primary_span_supported D hD,
          primary_span_supported n hn]
      have hrow : primaryGaussRow (D * n) k =
          gaussRow (primaryGenerator D * primaryGenerator n) (supported_mul_elements _ _ hd ha) k := by
        rw [primaryGaussRow_of_supported _ hDn]
        exact gaussRow_congr _ _ (primaryGenerator_mul D n) _ _ k
      have hL : (if IsCoprime D n then primaryGaussRow (D * n) k else 0) =
          (if IsCoprime (primaryGenerator D) (primaryGenerator n) then
            gaussRow (primaryGenerator D * primaryGenerator n) (supported_mul_elements _ _ hd ha) k
            else 0) := by
        rw [hrow]
        by_cases hc : IsCoprime D n
        · simp only [hc, hcop.mpr hc, ↓reduceIte]
        · have hc' : ¬IsCoprime (primaryGenerator D) (primaryGenerator n) := fun h => hc (hcop.mp h)
          simp only [hc, hc', ↓reduceIte]
      rw [hL, MixedSelectedCommon.masked_product_rays _ _ hd ha hpd hpa k]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      rw [primaryGaussRow_of_supported D hD, primaryGaussRow_of_supported n hn,
        GaussTransfer.normalized_fourth_power _ _ hff]
      ring
    · have h1 : ¬Supported (D * n) := fun h => hn ((supported_mul_iff D n).mp h).2
      simp only [primaryGaussRow_of_not_supported _ h1, primaryGaussRow_of_not_supported _ hn,
        ite_self, mul_zero, Finset.sum_const_zero]
  · have h1 : ¬Supported (D * n) := fun h => hD ((supported_mul_iff D n).mp h).1
    simp only [primaryGaussRow_of_not_supported _ h1, primaryGaussRow_of_not_supported _ hD,
      ite_self, mul_zero, zero_mul, Finset.sum_const_zero]

/-- Collet's source polynomial written as a sum over the tuple box, for an
arbitrary column multiplier `Γ`. -/
theorem gauss_tuple_sum {κ : Type*} [Fintype κ] (box : Finset (Tuple κ)) (β : Tuple κ → ℂ)
    (Γ : Ideal O → ℂ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (finiteColumns box))
        (sourceGenerator_supported (finiteColumns box))
        (fun I : supportedColumns (finiteColumns box) => finiteColumnCoefficient box β I * Γ I) k =
      ∑ v ∈ box, β v * (Γ (finiteTupleProduct v) * primaryGaussRow (finiteTupleProduct v) k) := by
  refine (source_gaussPolynomial (finiteColumns box)
    (fun I => finiteColumnCoefficient box β I * Γ I) k).trans ?_
  rw [MixedSupplierReconstruction.supported_gauss_sum]
  simp only [mul_assoc]
  exact MixedRestrictedDictionary.finite_column_sum box β (fun I => Γ I * primaryGaussRow I k)

/-- The ray label is absorbed into the Hecke character of the row weight. -/
theorem rowWeight_child_gauss (τ : HeckeFamily.Character) (ξ : RayCharacter) (m : O) (t : ℝ)
    (I : Ideal O) (k : O) :
    rowWeight (childCharacter τ ξ) m 1 1 t I * primaryGaussRow I k =
      rowWeight τ m 1 1 t I * rayCharacter ξ (primaryGenerator I) * primaryGaussRow I k := by
  by_cases hI : Supported I
  · have he := CenteredMomentSecondChildProfile.child_ideal_primary τ ξ I hI
    simp only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, he]
    ring
  · simp only [primaryGaussRow_of_not_supported _ hI, mul_zero]

/-- The normalization `T` splits as the selected volume times the residual one. -/
theorem sqrt_split (T W : ℝ) (hW : 0 < W) :
    ((Real.sqrt T : ℂ))⁻¹ = ((Real.sqrt W : ℂ))⁻¹ * ((Real.sqrt (T / W) : ℂ))⁻¹ := by
  have hw : ((Real.sqrt W : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hW).ne'
  rw [Real.sqrt_div' T hW.le, Complex.ofReal_div, inv_div, ← mul_div_assoc,
    inv_mul_cancel₀ hw, one_div]

end
end QRH.MixedStep.Transfer
