import Mathlib

/-!
# Coupled hybrid norm: the abstract duality step

In the reflected energy (Collet, foundations MF2.29) the active slot primes form a squarefree product
`P` whose coefficient carries the twisted multiplicativity of cubic Gauss sums:
`a₀(P_A P_B) = a₀(P_A) a₀(P_B) ψ(P_A, P_B)` with a cubic residue symbol `ψ`. MF2.29 treats `a(P)` as an
arbitrary bounded coefficient, which costs the `L = q_P` term in `{N + L + (NL)^{2/3}}`. Splitting the
slots into two groups `A, B` and grouping `(P_B, n)` turns the `n`-weighted slot sum into a bilinear form
in `(P_A, P_B n)` with kernel `ψ(P_A, P_B n)`, to which Heath-Brown's cubic large sieve applies with
norm `L_A + L_B N + (L N)^{2/3}`. With a balanced split the `L` term disappears.

This file proves the abstract step (finite sums over ℂ, no arithmetic):

* `bilinear_bound` : if the kernel `K : ι → κ → ℂ` has `Σ_i |Σ_m γ_m K i m|² ≤ Λ ‖γ‖²` for all `γ`, then
  `|Σ_i Σ_m α_i e_m K i m|² ≤ ‖α‖² Λ ‖e‖²`;
* `coupled_bound`  : for rows `k` and the coupled sum `B_k = Σ_i Σ_j α_i β_j c_k K i (j, k)`,
  `Σ_k |B_k|² ≤ ‖α‖² Λ ‖β‖² max_k |c_k|²` (duality: test against `γ_k = conj B_k`).

The arithmetic input (the cubic large sieve for the kernel `ψ_{P_A}(P_B n)`) is Heath-Brown's Theorem 2,
already used by Collet as (36). Status of the application: it improves the row branch of the reflected
energy only; see `MIBranches.lean` for why that does not relax the inverse-moment slot cost.
-/

open scoped BigOperators ComplexConjugate

namespace Lab.CoupledHybrid

variable {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]

/-- Cauchy–Schwarz for finite complex sums, in squared form. -/
theorem cs_sq (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * (∑ i, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i, f i * g i‖ ≤ ∑ i, ‖f i‖ * ‖g i‖ := by
    calc ‖∑ i, f i * g i‖ ≤ ∑ i, ‖f i * g i‖ := norm_sum_le _ _
      _ = ∑ i, ‖f i‖ * ‖g i‖ := by simp
  have h2 : (∑ i, ‖f i‖ * ‖g i‖) ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * (∑ i, ‖g i‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h0 : 0 ≤ ‖∑ i, f i * g i‖ := norm_nonneg _
  nlinarith [h1, h2, h0]

theorem bilinear_bound (K : ι → κ → ℂ) (Λ : ℝ)
    (hK : ∀ γ : κ → ℂ, ∑ i, ‖∑ m, γ m * K i m‖ ^ 2 ≤ Λ * ∑ m, ‖γ m‖ ^ 2)
    (α : ι → ℂ) (e : κ → ℂ) :
    ‖∑ i, ∑ m, α i * e m * K i m‖ ^ 2 ≤ (∑ i, ‖α i‖ ^ 2) * Λ * ∑ m, ‖e m‖ ^ 2 := by
  have hrw : ∑ i, ∑ m, α i * e m * K i m = ∑ i, α i * ∑ m, e m * K i m := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
  rw [hrw]
  calc ‖∑ i, α i * ∑ m, e m * K i m‖ ^ 2
      ≤ (∑ i, ‖α i‖ ^ 2) * (∑ i, ‖∑ m, e m * K i m‖ ^ 2) := cs_sq _ _
    _ ≤ (∑ i, ‖α i‖ ^ 2) * (Λ * ∑ m, ‖e m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hK e) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ = (∑ i, ‖α i‖ ^ 2) * Λ * ∑ m, ‖e m‖ ^ 2 := by ring

/-- The coupled slot sum: rows `k`, slot group `i` (`P_A`), slot group `j` (`P_B`); the kernel sees
`(j, k)` jointly, which is the grouping `m = P_B n`. -/
def coupled (K : ι → κ × ρ → ℂ) (α : ι → ℂ) (β : κ → ℂ) (c : ρ → ℂ) (k : ρ) : ℂ :=
  ∑ i, ∑ j, α i * β j * c k * K i (j, k)

theorem coupled_bound (K : ι → κ × ρ → ℂ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hK : ∀ γ : κ × ρ → ℂ, ∑ i, ‖∑ m, γ m * K i m‖ ^ 2 ≤ Λ * ∑ m, ‖γ m‖ ^ 2)
    (α : ι → ℂ) (β : κ → ℂ) (c : ρ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ k, ‖c k‖ ^ 2 ≤ C) :
    ∑ k, ‖coupled K α β c k‖ ^ 2 ≤ (∑ i, ‖α i‖ ^ 2) * Λ * (∑ j, ‖β j‖ ^ 2) * C := by
  classical
  set B := coupled K α β c with hBdef
  set S := ∑ k, ‖B k‖ ^ 2 with hSdef
  set A := ∑ i, ‖α i‖ ^ 2 with hAdef
  set Bn := ∑ j, ‖β j‖ ^ 2 with hBndef
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ Bn := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- the test vector of the duality step
  set e : κ × ρ → ℂ := fun m => β m.1 * c m.2 * conj (B m.2) with he
  have key : (∑ k, conj (B k) * B k) = ∑ i, ∑ m, α i * e m * K i m := by
    have h1 : ∀ k, conj (B k) * B k = ∑ i, ∑ j, α i * e (j, k) * K i (j, k) := by
      intro k
      simp only [hBdef, coupled, he, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    calc (∑ k, conj (B k) * B k) = ∑ k, ∑ i, ∑ j, α i * e (j, k) * K i (j, k) :=
          Finset.sum_congr rfl fun k _ => h1 k
      _ = ∑ i, ∑ k, ∑ j, α i * e (j, k) * K i (j, k) := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, α i * e (j, k) * K i (j, k) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ m, α i * e m * K i m := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Fintype.sum_prod_type]
  have hnorm : ‖∑ k, conj (B k) * B k‖ = S := by
    have : (∑ k, conj (B k) * B k) = ((S : ℝ) : ℂ) := by
      rw [hSdef, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.conj_mul']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
  have he_sum : ∑ m, ‖e m‖ ^ 2 ≤ Bn * C * S := by
    rw [Fintype.sum_prod_type]
    calc ∑ j, ∑ k, ‖e (j, k)‖ ^ 2
        = ∑ j, ∑ k, ‖β j‖ ^ 2 * (‖c k‖ ^ 2 * ‖B k‖ ^ 2) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          simp only [he, norm_mul, Complex.norm_conj]; ring
      _ ≤ ∑ j, ∑ k, ‖β j‖ ^ 2 * (C * ‖B k‖ ^ 2) := by
          gcongr with j _ k _
          exact hc k
      _ = Bn * C * S := by
          rw [hBndef, hSdef, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  have hmain : S ^ 2 ≤ A * Λ * (Bn * C * S) := by
    have := bilinear_bound K Λ hK α e
    rw [← key, hnorm] at this
    calc S ^ 2 ≤ A * Λ * ∑ m, ‖e m‖ ^ 2 := this
      _ ≤ A * Λ * (Bn * C * S) := mul_le_mul_of_nonneg_left he_sum (mul_nonneg hA hΛ)
  have hR : 0 ≤ A * Λ * Bn * C := by positivity
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]; exact hR
  · have h2 : S * S ≤ (A * Λ * Bn * C) * S := by nlinarith [hmain]
    exact le_of_mul_le_mul_right h2 hpos

end Lab.CoupledHybrid
