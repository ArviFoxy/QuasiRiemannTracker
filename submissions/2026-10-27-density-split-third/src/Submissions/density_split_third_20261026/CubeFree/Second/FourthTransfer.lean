/- Copyright (c) 2026 Sil. Apache-2.0.
D-Cauchy and the D⁴ transfer at f = 1 (CF Section 4, "selected marked factors").

FP's u-freezing supplier lane transfers `k ↦ D⁴k` with a fixed frozen product `f` whose
twist `idealRowHom(f)²` stays in the character (`MixedSupplierKernel.fixed_supplier_row_fourth`).
The cube-free argument never freezes the first artificial divisor, so only the instance
`f = 1` is used (design risk 1). It is `selected_row_fourth_one` below, derived from the
cube-free fork `MixedSelectedCommon.ideal_seeded_selected_row_fourth` at `f = seed = 1`:
for cube-free residual columns `n_v` coprime to the selected product `D`,
  `∑_v A B_v G(D n_v; k) = ∑_{χ,ξ} c(χ,ξ) (A χ(D) G(D; k)) · P_ξ(D⁴ k)`,
with the SAME residual Gauss polynomial `P_ξ` for every `D` (its coefficients
`B_v ξ(n_v)` do not depend on `D`). The transfer changes the Gauss row from `k` to `D⁴ k`,
whose norm is `N(D)⁴ N(k)` (`fourth_scale`): the Gauss radius `K` becomes `K · N(D)⁴`
(CF: `K Z^{4 u_sel}`), with no `f⁴` and no extra twist.

The D-Cauchy (`d_cauchy`) is the plain Cauchy inequality over the selected assignments,
and `grouped_d_cauchy` groups them by their product `D` with the grouped weights of
`Second.SelectedBlock` (the positive weights are removed only after squaring). -/
import Submissions.density_split_third_20261026.CubeFree.FP.MixedSelectedCommon
import Submissions.density_split_third_20261026.CubeFree.Second.SelectedBlock

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second.FourthTransfer
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentFirstColumns CenteredMomentFixedRay
open CenteredMomentSourceRow RayFourExpansion
open QRH.DensitySplitThird.CubeFree.FP.MixedSelectedCommon
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- **The D⁴ transfer at f = 1.** -/
theorem selected_row_fourth_one {ι : Type*} (V : Finset ι)
    (n : ι → Id) (hn : ∀ v, Supported (n v)) (A : ℂ) (B : ι → ℂ)
    (D : Id) (hD : Supported D)
    (hfree : ∀ v ∈ V, B v ≠ 0 → Candidate.FourthPower.SexticSieve.PowerFree 3 (n v)) (k : O) :
    (∑ v ∈ V, A*B v *
      (if IsCoprime D (n v) then
        idealGauss (D*n v) ((supported_mul_iff D (n v)).mpr ⟨hD, hn v⟩) k else 0)) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff firstPhaseTable χ ξ *
          (A * rayCharacter χ (primaryGenerator D) * idealGauss D hD k) *
            gaussPolynomial V (fun v => primaryGenerator (n v))
              (fun v => primary_supported (n v) (hn v))
              (commonCoefficient (fun v => primaryGenerator (n v)) B ξ)
              ((primaryGenerator D)^4*k) := by
  have hB : (fun v => if (1:Id) ∣ n v then B v else 0) = B := by
    funext v
    exact if_pos (one_dvd _)
  have h := ideal_seeded_selected_row_fourth V n hn A B 1 1 D one_ne_zero hD
    isCoprime_one_left (by
      intro v hv hb
      apply hfree v hv
      simpa only [one_dvd, if_true] using hb) k
  rw [hB] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro v _
  simp only [one_mul, one_dvd, if_true]

/-- The transferred row has norm `N(D)⁴ N(k)`: the Gauss radius is multiplied by `N(D)⁴`. -/
theorem fourth_scale (D : Id) (hD : Supported D) (k : O) :
    Ideal.absNorm (Ideal.span {(primaryGenerator D)^4*k}) =
      (Ideal.absNorm D)^4 * Ideal.absNorm (Ideal.span {k}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    primary_span_supported D hD, map_mul, map_pow]

/-- D-Cauchy over a finite family of selected assignments. -/
theorem d_cauchy {Y : Type*} (Ys : Finset Y) (c X : Y → ℂ) :
    ‖∑ y ∈ Ys, c y * X y‖^2 ≤ (∑ y ∈ Ys, ‖c y‖^2) * (∑ y ∈ Ys, ‖X y‖^2) := by
  have h1 : ‖∑ y ∈ Ys, c y * X y‖ ≤ ∑ y ∈ Ys, ‖c y‖ * ‖X y‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Ys (fun y => ‖c y‖) (fun y => ‖X y‖)
  have h0 : 0 ≤ ∑ y ∈ Ys, ‖c y‖ * ‖X y‖ :=
    Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖∑ y ∈ Ys, c y * X y‖^2 ≤ (∑ y ∈ Ys, ‖c y‖ * ‖X y‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

open QRH.DensitySplitThird.CubeFree.Second.SelectedBlock in
/-- D-Cauchy grouped by the selected product: for a row function `R(D)` depending on the
assignment only through `D = selectedProduct y`, the square of the weighted selected sum is
at most the number of supported selected assignments (`≤ 256^{#J} ∏ P_j = Z^{u+o(1)}`, CF's
Z^{u_sel} normalisation) times the grouped weighted sum `∑_D w(D) |R(D)|²`. -/
theorem grouped_d_cauchy {α : Type*} [Fintype α] (q : SelectedBlock α) (R : Id → ℂ) :
    ‖∑ y ∈ supportedSelected q, selectedWeight q y * R (selectedProduct q y)‖^2 ≤
      ((supportedSelected q).card : ℝ) *
        ∑ D ∈ selectedProducts q, groupedWeight q D * ‖R D‖^2 := by
  have h := d_cauchy (supportedSelected q) (fun _ => (1:ℂ))
    (fun y => selectedWeight q y * R (selectedProduct q y))
  simp only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hg := selected_grouping q (fun D => ‖R D‖^2)
  have hsum : (∑ y ∈ supportedSelected q, ‖selectedWeight q y * R (selectedProduct q y)‖^2) =
      ∑ D ∈ selectedProducts q, groupedWeight q D * ‖R D‖^2 := by
    rw [← hg]
    exact Finset.sum_congr rfl fun y _ => by rw [norm_mul, mul_pow]
  rw [hsum] at h
  exact h

end
end QRH.DensitySplitThird.CubeFree.Second.FourthTransfer
