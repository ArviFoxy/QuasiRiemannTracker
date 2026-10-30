import Mathlib

/-!
# Coherence certificates for the restricted isometry property, and their square-root barrier

Research file (QRH, RIP program). Columns `u : ι → E` live in a complex inner product space.

* `inner_sum_sum`, `gram_split`: the Gram expansion of `‖∑ x i • u i‖²`.
* `gershgorin_rip`: unit columns of coherence `μ` satisfy the RIP on every support `S`, with
  constant `μ (|S| - 1)`.
* `gram_frame_frobenius`: the Gram and frame matrices of a finite array have equal Frobenius norm.
* `frame_potential_ge`: `(∑ ‖u i‖²)² ≤ n ∑_{i,j} ‖⟪u i, u j⟫‖²` in dimension `n` (Welch's frame potential).
* `welch`: for unit columns, `N² ≤ n (N + N (N - 1) μ²)`.
* `coherence_order_barrier`: once `N ≥ 2n`, a coherence certificate `(k - 1) μ ≤ δ` forces
  `k ≤ 1 + δ √(2n)`. Coherence alone never certifies RIP beyond order `≈ √n`: the square-root barrier.
-/

namespace QRH.ArviRIP

open scoped BigOperators ComplexConjugate InnerProductSpace
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Gram expansion of the self-inner product of a combination of columns. -/
theorem inner_sum_sum (S : Finset ι) (x : ι → ℂ) (u : ι → E) :
    ⟪∑ i ∈ S, x i • u i, ∑ i ∈ S, x i • u i⟫_ℂ =
      ∑ i ∈ S, ∑ j ∈ S, conj (x i) * x j * ⟪u i, u j⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

omit [DecidableEq ι] in
/-- `‖v‖² = Re ⟪v, v⟫` for a complex inner product space. -/
theorem norm_sq_eq_re (v : E) : ‖v‖ ^ 2 = (⟪v, v⟫_ℂ).re := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v, RCLike.re_to_complex]

/-- Diagonal/off-diagonal split for unit columns. -/
theorem gram_split (S : Finset ι) (x : ι → ℂ) (u : ι → E) (hu : ∀ i ∈ S, ‖u i‖ = 1) :
    ⟪∑ i ∈ S, x i • u i, ∑ i ∈ S, x i • u i⟫_ℂ =
      ((∑ i ∈ S, ‖x i‖ ^ 2 : ℝ) : ℂ) +
        ∑ i ∈ S, ∑ j ∈ S.erase i, conj (x i) * x j * ⟪u i, u j⟫_ℂ := by
  rw [inner_sum_sum, Complex.ofReal_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.add_sum_erase S _ hi]
  have h1 : ⟪u i, u i⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu i hi]; simp
  rw [h1, Complex.conj_mul']
  push_cast
  ring

/-- Off-diagonal mass of a vector: `∑_{i ≠ j} |x_i||x_j| = (∑|x_i|)² - ∑|x_i|²`. -/
theorem offdiag_mass (S : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, a i * a j = (∑ i ∈ S, a i) ^ 2 - ∑ i ∈ S, a i ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.add_sum_erase S _ hi]
  ring

/-- **Gershgorin certificate.** Unit columns with coherence at most `μ` satisfy the RIP on
every support `S`, with constant `μ (|S| - 1)`. -/
theorem gershgorin_rip (S : Finset ι) (x : ι → ℂ) (u : ι → E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hμ : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ μ) :
    |‖∑ i ∈ S, x i • u i‖ ^ 2 - ∑ i ∈ S, ‖x i‖ ^ 2| ≤
      μ * ((S.card : ℝ) - 1) * ∑ i ∈ S, ‖x i‖ ^ 2 := by
  set O := ∑ i ∈ S, ∑ j ∈ S.erase i, conj (x i) * x j * ⟪u i, u j⟫_ℂ with hO
  have hre : ‖∑ i ∈ S, x i • u i‖ ^ 2 - ∑ i ∈ S, ‖x i‖ ^ 2 = O.re := by
    have h := congrArg Complex.re (gram_split S x u hu)
    rw [← hO, Complex.add_re, Complex.ofReal_re] at h
    rw [norm_sq_eq_re, h]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm O).trans ?_
  have h1 : ‖O‖ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i, μ * (‖x i‖ * ‖x j‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hb := hμ i hi j hjS (Ne.symm hji)
    have hx := mul_nonneg (norm_nonneg (x i)) (norm_nonneg (x j))
    nlinarith
  have h3 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖x i‖)
  calc ‖O‖ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i, μ * (‖x i‖ * ‖x j‖) := h1
    _ = μ * ∑ i ∈ S, ∑ j ∈ S.erase i, ‖x i‖ * ‖x j‖ := by
        simp only [Finset.mul_sum]
    _ = μ * ((∑ i ∈ S, ‖x i‖) ^ 2 - ∑ i ∈ S, ‖x i‖ ^ 2) := by
        rw [offdiag_mass S (fun i => ‖x i‖)]
    _ ≤ μ * ((S.card : ℝ) - 1) * ∑ i ∈ S, ‖x i‖ ^ 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by nlinarith [h3]) hμ0

section Welch

variable [Fintype ι]

omit [DecidableEq ι] in
/-- Frobenius identity: the Gram matrix `(∑_k c̄_{ik} c_{jk})_{ij}` and the frame matrix
`(∑_i c̄_{ik} c_{il})_{kl}` of an array `c` have the same Frobenius norm. -/
theorem gram_frame_frobenius {κ : Type*} [Fintype κ] (c : ι → κ → ℂ) :
    ∑ i, ∑ j, ‖∑ k, conj (c i k) * c j k‖ ^ 2 =
      ∑ k, ∑ l, ‖∑ i, conj (c i k) * c i l‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq ι] in
/-- **Frame potential (Welch).** In dimension `n`, `(∑ ‖u i‖²)² ≤ n ∑_{i,j} |⟪u i, u j⟫|²`. -/
theorem frame_potential_ge {n : ℕ} (u : ι → E) (b : OrthonormalBasis (Fin n) ℂ E) :
    (∑ i, ‖u i‖ ^ 2) ^ 2 ≤ n * ∑ i, ∑ j, ‖⟪u i, u j⟫_ℂ‖ ^ 2 := by
  set c : ι → Fin n → ℂ := fun i k => ⟪b k, u i⟫_ℂ with hc
  have hG : ∀ i j, ⟪u i, u j⟫_ℂ = ∑ k, conj (c i k) * c j k := by
    intro i j
    rw [← b.sum_inner_mul_inner (u i) (u j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc, inner_conj_symm]
  have hP : ∀ i, ∑ k, ‖c i k‖ ^ 2 = ‖u i‖ ^ 2 := fun i => b.sum_sq_norm_inner_right (u i)
  have hdiag : ∀ k, ‖∑ i, conj (c i k) * c i k‖ = ∑ i, ‖c i k‖ ^ 2 := by
    intro k
    have h : ∑ i, conj (c i k) * c i k = ((∑ i, ‖c i k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' _
    rw [h, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc (∑ i, ‖u i‖ ^ 2) ^ 2 = (∑ k, ∑ i, ‖c i k‖ ^ 2) ^ 2 := by
          rw [Finset.sum_comm]; simp only [hP]
    _ ≤ n * ∑ k, (∑ i, ‖c i k‖ ^ 2) ^ 2 := by
          have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
            (f := fun k => ∑ i, ‖c i k‖ ^ 2)
          simpa using h
    _ = n * ∑ k, ‖∑ i, conj (c i k) * c i k‖ ^ 2 := by simp only [hdiag]
    _ ≤ n * ∑ k, ∑ l, ‖∑ i, conj (c i k) * c i l‖ ^ 2 := by
          gcongr with k
          exact Finset.single_le_sum (f := fun l => ‖∑ i, conj (c i k) * c i l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ k)
    _ = n * ∑ i, ∑ j, ‖⟪u i, u j⟫_ℂ‖ ^ 2 := by
          rw [← gram_frame_frobenius c]; simp only [hG]

/-- **Welch bound.** Unit columns of coherence `μ` in dimension `n` satisfy
`N² ≤ n (N + N (N - 1) μ²)`, `N` the number of columns. -/
theorem welch {n : ℕ} (u : ι → E) (b : OrthonormalBasis (Fin n) ℂ E)
    (hu : ∀ i, ‖u i‖ = 1) {μ : ℝ} (hμ : ∀ i j, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ μ) :
    (Fintype.card ι : ℝ) ^ 2 ≤
      n * (Fintype.card ι + Fintype.card ι * (Fintype.card ι - 1) * μ ^ 2) := by
  have hF := frame_potential_ge u b
  have hsum : ∑ i, ‖u i‖ ^ 2 = (Fintype.card ι : ℝ) := by simp [hu]
  rw [hsum] at hF
  refine hF.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have hrow : ∀ i, ∑ j, ‖⟪u i, u j⟫_ℂ‖ ^ 2 ≤ 1 + ((Fintype.card ι : ℝ) - 1) * μ ^ 2 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hii : ‖⟪u i, u i⟫_ℂ‖ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hu i]; simp
    rw [hii, one_pow]
    have hoff : ∑ j ∈ Finset.univ.erase i, ‖⟪u i, u j⟫_ℂ‖ ^ 2 ≤
        ∑ j ∈ Finset.univ.erase i, μ ^ 2 :=
      Finset.sum_le_sum fun j hj =>
        pow_le_pow_left₀ (norm_nonneg _) (hμ i j (Finset.ne_of_mem_erase hj).symm) 2
    have hcard : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩)]
      simp
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at hoff
    linarith
  calc ∑ i, ∑ j, ‖⟪u i, u j⟫_ℂ‖ ^ 2 ≤ ∑ _i : ι, (1 + ((Fintype.card ι : ℝ) - 1) * μ ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (Fintype.card ι : ℝ) + Fintype.card ι * (Fintype.card ι - 1) * μ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Welch, overcomplete case: with `N ≥ 2n` unit columns in dimension `n ≥ 1`, the coherence
satisfies `μ² ≥ 1/(2n)`. -/
theorem coherence_sq_ge {n : ℕ} (hn : 0 < n) (u : ι → E) (b : OrthonormalBasis (Fin n) ℂ E)
    (hu : ∀ i, ‖u i‖ = 1) (hN : 2 * n ≤ Fintype.card ι) {μ : ℝ}
    (hμ : ∀ i j, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ μ) :
    1 / (2 * (n : ℝ)) ≤ μ ^ 2 := by
  have hW := welch u b hu hμ
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN' : 2 * (n : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : N * (N - n) ≤ N * (n * (N - 1) * μ ^ 2) := by nlinarith [hW]
  have h2 : N - n ≤ n * (N - 1) * μ ^ 2 := le_of_mul_le_mul_left h1 hNpos
  have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have h3 : N / 2 ≤ n * N * μ ^ 2 := by nlinarith
  have h4 : 1 / 2 ≤ n * μ ^ 2 := by
    by_contra hc
    nlinarith [not_le.mp hc]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The square-root barrier for coherence certificates.** With `N ≥ 2n` unit columns in
dimension `n ≥ 1`, any Gershgorin certificate `(k - 1) μ ≤ δ` (`gershgorin_rip`) has
`k ≤ 1 + δ √(2n)`. Beating order `√n` needs cancellation among many inner products at once,
not a bound on each. -/
theorem coherence_order_barrier {n : ℕ} (hn : 0 < n) (u : ι → E)
    (b : OrthonormalBasis (Fin n) ℂ E) (hu : ∀ i, ‖u i‖ = 1) (hN : 2 * n ≤ Fintype.card ι)
    {μ δ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ i j, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ μ)
    {k : ℝ} (hk : 1 ≤ k) (hcert : (k - 1) * μ ≤ δ) :
    k - 1 ≤ δ * Real.sqrt (2 * n) := by
  have hμ2 := coherence_sq_ge hn u b hu hN hμ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * n := by linarith
  have hs : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt (2 * n) ^ 2 = 2 * n := Real.sq_sqrt hpos.le
  -- μ √(2n) ≥ 1
  have hμs : 1 ≤ μ * Real.sqrt (2 * n) := by
    have h : 1 ≤ (μ * Real.sqrt (2 * n)) ^ 2 := by
      rw [mul_pow, hss]
      rw [div_le_iff₀ hpos] at hμ2
      linarith
    nlinarith [mul_nonneg hμ0 hs.le]
  have hk0 : 0 ≤ k - 1 := by linarith
  calc k - 1 ≤ (k - 1) * (μ * Real.sqrt (2 * n)) := le_mul_of_one_le_right hk0 hμs
    _ = ((k - 1) * μ) * Real.sqrt (2 * n) := by ring
    _ ≤ δ * Real.sqrt (2 * n) := mul_le_mul_of_nonneg_right hcert hs.le

end Welch

end QRH.ArviRIP

#print axioms QRH.ArviRIP.gershgorin_rip
#print axioms QRH.ArviRIP.welch
#print axioms QRH.ArviRIP.coherence_order_barrier
