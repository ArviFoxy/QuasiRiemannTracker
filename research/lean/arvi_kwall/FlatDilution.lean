import Mathlib

/-!
# Flat low-rank parts dilute on every thin row set

Research file (QRH, K-wall; Arvi's "replace M by an operator with the RIP we need").

Write the row vector `y = M a` (values `y z = ∑_n a_n χ_z(n)` on the rows `z`) as a combination of
`k` row vectors `θ_j` plus a remainder: `y = ∑_j c_j θ_j + r`. If each `θ_j` is flat,
`|θ_j(z)|² ≤ c / R`, then on ANY row subset `W`

  `‖y|_W‖ ≤ √(k c |W| / R) · ‖c‖ + ‖r‖`   (`norm_restrict_le`).

Take `θ_j` the theta row vectors `conj G(z,1)·profile` (unimodular Gauss sums of the moduli, so
flat) and `r = (I − P_V) M a`. The excess carried by `V` is diluted by `|W|/R` on every thin `W`,
and what is left is the large sieve OFF `V` on the full family: no restriction to `W` is needed
for it. So RIP of `M` on thin row sets follows from the full-family bound for the operator
`(I − P_V) M` (journal, "large sieve off V").

The dilution factor is `k c |W| / R`, so this pays only for low-dimensional `V`. For the sextic family the theta
excess is spread over every twist `conj G·χ_z(m)` with `N(m) ≤ B^{1−6γ}` (Poisson multiplicity), so `k` cannot be
small; see the journal entry "Where the theta excess lives".
-/

namespace QRH.ArviKWall

open Finset
open scoped BigOperators

/-- `ℓ²` norm of a row vector restricted to `W`. -/
noncomputable def l2on {ι : Type*} (W : Finset ι) (y : ι → ℂ) : ℝ :=
  Real.sqrt (∑ z ∈ W, ‖y z‖ ^ 2)

theorem l2on_nonneg {ι : Type*} (W : Finset ι) (y : ι → ℂ) : 0 ≤ l2on W y := Real.sqrt_nonneg _

/-- Triangle inequality for `l2on`. -/
theorem l2on_add_le {ι : Type*} (W : Finset ι) (y₁ y₂ : ι → ℂ) :
    l2on W (y₁ + y₂) ≤ l2on W y₁ + l2on W y₂ := by
  -- Minkowski in ℓ²(W), via the norm of `EuclideanSpace`
  classical
  let e : (ι → ℂ) → EuclideanSpace ℂ W := fun y => WithLp.toLp 2 (fun z : W => y z)
  have hnorm : ∀ y, l2on W y = ‖e y‖ := by
    intro y
    rw [l2on, EuclideanSpace.norm_eq]
    congr 1
    rw [← Finset.sum_coe_sort W]
  have hadd : e (y₁ + y₂) = e y₁ + e y₂ := rfl
  rw [hnorm, hnorm, hnorm, hadd]
  exact norm_add_le _ _

/-- The flat low-rank part is small on a thin set: `‖(∑_j c_j θ_j)|_W‖² ≤ (k c |W| / R) ‖c‖²`. -/
theorem l2on_flat_sq_le {ι : Type*} {k : ℕ} (W : Finset ι) (θ : Fin k → ι → ℂ) (cf : Fin k → ℂ)
    {c R : ℝ} (hflat : ∀ j z, ‖θ j z‖ ^ 2 ≤ c / R) :
    l2on W (fun z => ∑ j, cf j * θ j z) ^ 2 ≤ (k * c * W.card / R) * ∑ j, ‖cf j‖ ^ 2 := by
  rw [l2on, Real.sq_sqrt (Finset.sum_nonneg fun z _ => by positivity)]
  have hpt : ∀ z ∈ W, ‖∑ j, cf j * θ j z‖ ^ 2 ≤ (∑ j, ‖cf j‖ ^ 2) * (k * (c / R)) := by
    intro z _
    have h1 : ‖∑ j, cf j * θ j z‖ ≤ ∑ j, ‖cf j‖ * ‖θ j z‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul]
    have h2 : (∑ j, ‖cf j‖ * ‖θ j z‖) ^ 2 ≤ (∑ j, ‖cf j‖ ^ 2) * (∑ j, ‖θ j z‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ j, ‖θ j z‖ ^ 2 ≤ k * (c / R) := by
      calc ∑ j, ‖θ j z‖ ^ 2 ≤ ∑ _j : Fin k, c / R := Finset.sum_le_sum fun j _ => hflat j z
        _ = k * (c / R) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h0 : 0 ≤ ‖∑ j, cf j * θ j z‖ := norm_nonneg _
    calc ‖∑ j, cf j * θ j z‖ ^ 2 ≤ (∑ j, ‖cf j‖ * ‖θ j z‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ (∑ j, ‖cf j‖ ^ 2) * (∑ j, ‖θ j z‖ ^ 2) := h2
      _ ≤ (∑ j, ‖cf j‖ ^ 2) * (k * (c / R)) :=
          mul_le_mul_of_nonneg_left h3 (Finset.sum_nonneg fun j _ => by positivity)
  calc ∑ z ∈ W, ‖∑ j, cf j * θ j z‖ ^ 2 ≤ ∑ _z ∈ W, (∑ j, ‖cf j‖ ^ 2) * (k * (c / R)) :=
        Finset.sum_le_sum hpt
    _ = (k * c * W.card / R) * ∑ j, ‖cf j‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Dilution by flatness.** If `y = ∑_j c_j θ_j + r` with flat `θ_j` (`|θ_j(z)|² ≤ c/R`), then on
every row subset `W`: `‖y|_W‖ ≤ √(k c |W| / R) ‖c‖ + ‖r‖` (the last norm over all rows). -/
theorem norm_restrict_le {ι : Type*} [Fintype ι] {k : ℕ} (W : Finset ι) (θ : Fin k → ι → ℂ)
    (cf : Fin k → ℂ) (r y : ι → ℂ) {c R : ℝ} (hc : 0 ≤ c) (hR : 0 < R)
    (hflat : ∀ j z, ‖θ j z‖ ^ 2 ≤ c / R) (hy : y = fun z => (∑ j, cf j * θ j z) + r z) :
    l2on W y ≤ Real.sqrt (k * c * W.card / R) * Real.sqrt (∑ j, ‖cf j‖ ^ 2) +
      l2on univ r := by
  have h1 : l2on W y ≤ l2on W (fun z => ∑ j, cf j * θ j z) + l2on W r := by
    rw [hy]
    exact l2on_add_le W (fun z => ∑ j, cf j * θ j z) r
  have h2 : l2on W (fun z => ∑ j, cf j * θ j z) ≤
      Real.sqrt (k * c * W.card / R) * Real.sqrt (∑ j, ‖cf j‖ ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [l2on]
    refine Real.sqrt_le_sqrt ?_
    have := l2on_flat_sq_le W θ cf hflat
    rw [l2on, Real.sq_sqrt (Finset.sum_nonneg fun z _ => by positivity)] at this
    exact this
  have h3 : l2on W r ≤ l2on univ r := by
    refine Real.sqrt_le_sqrt ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ W) (fun z _ _ => by positivity)
  linarith

end QRH.ArviKWall

#print axioms QRH.ArviKWall.norm_restrict_le
