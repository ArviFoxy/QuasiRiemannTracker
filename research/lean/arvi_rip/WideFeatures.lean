import Submissions.arvi_rip.Coherence
import Submissions.arvi_rip.Hoeffding

/-!
# Wide random features: a positive measure of operators with RIP far beyond √

Research file (QRH, RIP program (4): randomized dictionaries of different atoms).

The atoms are not characters. A feature is a product of `ℓ` Rademacher projections,
`feat w x = ∏_{i<ℓ} ⟨w_i, x⟩` with `w_i ∈ {±1}^d`: the polynomial (Maclaurin) pieces of
a wide dot-product kernel such as ReLU's arc-cosine kernel. The kernel of degree `ℓ` is
exactly the `ℓ`-th power of the data Gram (`sum_feat_mul_conj`), so its coherence is `μ^ℓ`.

Main theorem `exists_wide_rip`: for ANY unit data `x_z` (`z ∈ ι`, `N` points) with pairwise
coherence `≤ μ` and `ℓ¹`-norms `≤ C`, if `4 N² C^{4ℓ} < m ε²` then some choice of `m`
features (a positive counting measure of choices, by Chebyshev and a union bound) gives
vectors `u_z ∈ ℂ^m` with
`|‖∑_{z∈S} c_z u_z‖² − ‖c‖²| ≤ (ε + (μ^ℓ + ε)(|S| − 1)) ‖c‖²` on every support `S`.
So the order reaches `≈ μ^{-ℓ}`, while coherence certificates on the raw data stop at
`≈ μ^{-1}` (`coherence_order_barrier`). No measure theory: probability is counting.

`count_le_of_rip` turns RIP into a large-value count, and `mixture_ge_min` records that a
mixture of degrees never counts better than its best single degree.
-/

namespace QRH.ArviRIP

open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace

section Projections

variable {d : ℕ}

/-- Rademacher projection `⟨w, x⟩ = ∑_a sgn(w a) x_a`. -/
def proj (w : Fin d → Bool) (x : Fin d → ℂ) : ℂ := ∑ a, (sgn (w a) : ℂ) * x a

/-- Degree-`ℓ` wide feature: a product of `ℓ` independent Rademacher projections. -/
def feat {ℓ : ℕ} (w : Fin ℓ → Fin d → Bool) (x : Fin d → ℂ) : ℂ := ∏ i, proj (w i) x

theorem sgn_mul_self (b : Bool) : (sgn b : ℂ) * sgn b = 1 := by
  cases b <;> simp [sgn]

/-- Orthogonality of Rademacher coordinates, counting form. -/
theorem sum_sgn_mul_sgn (a b : Fin d) :
    ∑ w : Fin d → Bool, (sgn (w a) : ℂ) * sgn (w b) = if a = b then (2 : ℂ) ^ d else 0 := by
  have hfac : ∀ w : Fin d → Bool, (sgn (w a) : ℂ) * sgn (w b) =
      ∏ c, ((if c = a then (sgn (w c) : ℂ) else 1) * (if c = b then (sgn (w c) : ℂ) else 1)) := by
    intro w
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun c (t : Bool) =>
    (if c = a then (sgn t : ℂ) else 1) * (if c = b then (sgn t : ℂ) else 1))]
  split_ifs with hab
  · subst hab
    have : ∀ c : Fin d, ∑ t : Bool, ((if c = a then (sgn t : ℂ) else 1) *
        (if c = a then (sgn t : ℂ) else 1)) = 2 := by
      intro c
      by_cases hc : c = a
      · simp [hc, sgn_mul_self]
      · simp [hc]
    simp_rw [this]
    simp
  · refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp [hab, sgn]

/-- Degree one: the Rademacher sketch reproduces the inner product exactly on average. -/
theorem sum_proj_mul_conj (x y : Fin d → ℂ) :
    ∑ w : Fin d → Bool, proj w x * conj (proj w y) = (2 : ℂ) ^ d * ∑ a, x a * conj (y a) := by
  have h1 : ∀ w : Fin d → Bool, proj w x * conj (proj w y) =
      ∑ a, ∑ b, x a * conj (y b) * ((sgn (w a) : ℂ) * sgn (w b)) := by
    intro w
    rw [proj, proj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  calc ∑ w : Fin d → Bool, proj w x * conj (proj w y)
      = ∑ w : Fin d → Bool, ∑ a, ∑ b, x a * conj (y b) * ((sgn (w a) : ℂ) * sgn (w b)) :=
        Finset.sum_congr rfl fun w _ => h1 w
    _ = ∑ a, ∑ b, ∑ w : Fin d → Bool, x a * conj (y b) * ((sgn (w a) : ℂ) * sgn (w b)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, x a * conj (y b) * (if a = b then (2 : ℂ) ^ d else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.mul_sum, sum_sgn_mul_sgn]
    _ = (2 : ℂ) ^ d * ∑ a, x a * conj (y a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring

/-- **Kernel of the wide features.** Averaged over all parameter choices, the degree-`ℓ`
features reproduce the `ℓ`-th power of the inner product: coherence `μ` becomes `μ^ℓ`. -/
theorem sum_feat_mul_conj (ℓ : ℕ) (x y : Fin d → ℂ) :
    ∑ w : Fin ℓ → Fin d → Bool, feat w x * conj (feat w y) =
      ((2 : ℂ) ^ d * ∑ a, x a * conj (y a)) ^ ℓ := by
  have h1 : ∀ w : Fin ℓ → Fin d → Bool, feat w x * conj (feat w y) =
      ∏ i, (proj (w i) x * conj (proj (w i) y)) := by
    intro w
    simp only [feat, map_prod, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin ℓ) (v : Fin d → Bool) => proj v x * conj (proj v y))]
  rw [sum_proj_mul_conj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_proj_le (w : Fin d → Bool) (x : Fin d → ℂ) : ‖proj w x‖ ≤ ∑ a, ‖x a‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sgn, one_mul]

theorem norm_feat_le {ℓ : ℕ} (w : Fin ℓ → Fin d → Bool) (x : Fin d → ℂ) :
    ‖feat w x‖ ≤ (∑ a, ‖x a‖) ^ ℓ := by
  rw [feat, norm_prod]
  calc ∏ i, ‖proj (w i) x‖ ≤ ∏ _i : Fin ℓ, ∑ a, ‖x a‖ :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_proj_le _ _)
    _ = (∑ a, ‖x a‖) ^ ℓ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Projections

/-! ### Independent draws and Chebyshev, in counting form -/

section Copies

variable {Ω : Type*} [Fintype Ω]

/-- One coordinate of `m` independent uniform draws: each value is hit `|Ω|^{m-1}` times. -/
theorem sum_pi_single {m : ℕ} (j : Fin m) (h : Ω → ℂ) :
    ∑ W : Fin m → Ω, h (W j) = (Fintype.card Ω : ℂ) ^ (m - 1) * ∑ ω, h ω := by
  classical
  have hfac : ∀ W : Fin m → Ω, h (W j) = ∏ i, (if i = j then h (W i) else 1) := by
    intro W; rw [Fintype.prod_ite_eq']
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun i (ω : Ω) => if i = j then h ω else 1)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)]
  have h2 : ∀ i ∈ (univ : Finset (Fin m)) \ {j},
      ∑ ω : Ω, (if i = j then h ω else 1) = (Fintype.card Ω : ℂ) := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    simp [hij]
  rw [Finset.prod_congr rfl h2, Finset.prod_const]
  have hc : ((univ : Finset (Fin m)) \ {j}).card = m - 1 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  rw [hc]
  simp only [ite_true]
  ring

/-- Two different coordinates of independent draws: the cross sum vanishes when one factor
has mean zero. -/
theorem sum_pi_pair_eq_zero {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (f g : Ω → ℂ)
    (hf : ∑ ω, f ω = 0) : ∑ W : Fin m → Ω, f (W j) * g (W k) = 0 := by
  classical
  have hfac : ∀ W : Fin m → Ω, f (W j) * g (W k) =
      ∏ i, ((if i = j then f (W i) else 1) * (if i = k then g (W i) else 1)) := by
    intro W; rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun i (ω : Ω) =>
    (if i = j then f ω else 1) * (if i = k then g ω else 1))]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  simp [hjk, hf]

/-- Variance of a sum of `m` independent copies of a mean-zero function, counting form. -/
theorem sum_norm_sq_sum_pi {m : ℕ} (g : Ω → ℂ) (hg : ∑ ω, g ω = 0) :
    ∑ W : Fin m → Ω, ‖∑ j, g (W j)‖ ^ 2 =
      (m : ℝ) * (Fintype.card Ω : ℝ) ^ (m - 1) * ∑ ω, ‖g ω‖ ^ 2 := by
  classical
  have hsq : ∀ v : ℂ, ‖v‖ ^ 2 = (conj v * v).re := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hconj : ∑ ω, conj (g ω) = 0 := by rw [← map_sum, hg, map_zero]
  have hjk : ∀ j k : Fin m, ∑ W : Fin m → Ω, conj (g (W j)) * g (W k) =
      if j = k then (Fintype.card Ω : ℂ) ^ (m - 1) * ∑ ω, conj (g ω) * g ω else 0 := by
    intro j k
    split_ifs with h
    · subst h; exact sum_pi_single j (fun ω => conj (g ω) * g ω)
    · exact sum_pi_pair_eq_zero h (fun ω => conj (g ω)) g hconj
  have hS : ∑ ω, conj (g ω) * g ω = ((∑ ω, ‖g ω‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun ω _ => Complex.conj_mul' (g ω)
  calc ∑ W : Fin m → Ω, ‖∑ j, g (W j)‖ ^ 2
      = (∑ W : Fin m → Ω, ∑ j, ∑ k, conj (g (W j)) * g (W k)).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [hsq, map_sum, Finset.sum_mul_sum]
    _ = (∑ j : Fin m, ∑ k : Fin m, ∑ W : Fin m → Ω, conj (g (W j)) * g (W k)).re := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ = (m : ℝ) * (Fintype.card Ω : ℝ) ^ (m - 1) * ∑ ω, ‖g ω‖ ^ 2 := by
        simp_rw [hjk]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
          ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring

/-- Chebyshev/Markov in counting form. -/
theorem card_filter_le_sum_div {α : Type*} [Fintype α] (F : α → ℝ) (hF : ∀ a, 0 ≤ F a)
    {t : ℝ} (ht : 0 < t) :
    ((univ.filter (fun a => t ≤ F a)).card : ℝ) ≤ (∑ a, F a) / t := by
  classical
  rw [le_div_iff₀ ht]
  calc ((univ.filter (fun a => t ≤ F a)).card : ℝ) * t
      = ∑ a ∈ univ.filter (fun a => t ≤ F a), t := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ univ.filter (fun a => t ≤ F a), F a :=
        Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
    _ ≤ ∑ a, F a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hF a)

end Copies

/-! ### RIP from an approximate Gram matrix, and RIP ⇒ large-value count -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Gershgorin with near-unit columns: diagonal within `ε` of `1`, off-diagonal `≤ η`. -/
theorem gershgorin_rip_approx {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℂ)
    (u : ι → E) {ε η : ℝ} (hη : 0 ≤ η)
    (hdiag : ∀ i ∈ S, |‖u i‖ ^ 2 - 1| ≤ ε)
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ‖⟪u i, u j⟫_ℂ‖ ≤ η) :
    |‖∑ i ∈ S, c i • u i‖ ^ 2 - ∑ i ∈ S, ‖c i‖ ^ 2| ≤
      (ε + η * ((S.card : ℝ) - 1)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  set O := ∑ i ∈ S, ∑ j ∈ S.erase i, conj (c i) * c j * ⟪u i, u j⟫_ℂ with hO
  have hsplit : ⟪∑ i ∈ S, c i • u i, ∑ i ∈ S, c i • u i⟫_ℂ =
      ((∑ i ∈ S, ‖c i‖ ^ 2 * ‖u i‖ ^ 2 : ℝ) : ℂ) + O := by
    rw [inner_sum_sum, Complex.ofReal_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase S _ hi]
    have h1 : ⟪u i, u i⟫_ℂ = ((‖u i‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h1, Complex.conj_mul']
    push_cast
    ring
  have hre : ‖∑ i ∈ S, c i • u i‖ ^ 2 - ∑ i ∈ S, ‖c i‖ ^ 2 =
      ∑ i ∈ S, ‖c i‖ ^ 2 * (‖u i‖ ^ 2 - 1) + O.re := by
    have h := congrArg Complex.re hsplit
    rw [Complex.add_re, Complex.ofReal_re] at h
    have hs : ∑ i ∈ S, ‖c i‖ ^ 2 * (‖u i‖ ^ 2 - 1) =
        ∑ i ∈ S, ‖c i‖ ^ 2 * ‖u i‖ ^ 2 - ∑ i ∈ S, ‖c i‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [norm_sq_eq_re, h, hs]
    ring
  have hdiagS : |∑ i ∈ S, ‖c i‖ ^ 2 * (‖u i‖ ^ 2 - 1)| ≤ ε * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [hdiag i hi, sq_nonneg ‖c i‖]
  have hoffS : |O.re| ≤ η * ((S.card : ℝ) - 1) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
    refine (Complex.abs_re_le_norm O).trans ?_
    have h1 : ‖O‖ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i, η * (‖c i‖ * ‖c j‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjS : j ∈ S := Finset.mem_of_mem_erase hj
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hb := hoff i hi j hjS (Ne.symm hji)
      have hx := mul_nonneg (norm_nonneg (c i)) (norm_nonneg (c j))
      nlinarith
    have h3 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖c i‖)
    calc ‖O‖ ≤ ∑ i ∈ S, ∑ j ∈ S.erase i, η * (‖c i‖ * ‖c j‖) := h1
      _ = η * ∑ i ∈ S, ∑ j ∈ S.erase i, ‖c i‖ * ‖c j‖ := by simp only [Finset.mul_sum]
      _ = η * ((∑ i ∈ S, ‖c i‖) ^ 2 - ∑ i ∈ S, ‖c i‖ ^ 2) := by
          rw [offdiag_mass S (fun i => ‖c i‖)]
      _ ≤ η * ((S.card : ℝ) - 1) * ∑ i ∈ S, ‖c i‖ ^ 2 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (by nlinarith [h3]) hη
  rw [hre]
  calc |∑ i ∈ S, ‖c i‖ ^ 2 * (‖u i‖ ^ 2 - 1) + O.re|
      ≤ |∑ i ∈ S, ‖c i‖ ^ 2 * (‖u i‖ ^ 2 - 1)| + |O.re| := abs_add_le _ _
    _ ≤ ε * ∑ i ∈ S, ‖c i‖ ^ 2 + η * ((S.card : ℝ) - 1) * ∑ i ∈ S, ‖c i‖ ^ 2 :=
        add_le_add hdiagS hoffS
    _ = (ε + η * ((S.card : ℝ) - 1)) * ∑ i ∈ S, ‖c i‖ ^ 2 := by ring

/-- **RIP ⇒ large-value count.** If the columns on `S` satisfy the RIP upper bound with
constant `1 + δ`, and every column has `|⟪b, u z⟫| ≥ τ`, then `|S| τ² ≤ (1 + δ) ‖b‖²`. -/
theorem count_le_of_rip {ι : Type*} (S : Finset ι) (u : ι → E) (b : E) {δ τ : ℝ}
    (hδ : 0 ≤ 1 + δ) (hrip : ∀ c : ι → ℂ, ‖∑ z ∈ S, c z • u z‖ ^ 2 ≤ (1 + δ) * ∑ z ∈ S, ‖c z‖ ^ 2)
    (hτ : 0 ≤ τ) (hlarge : ∀ z ∈ S, τ ≤ ‖⟪b, u z⟫_ℂ‖) :
    (S.card : ℝ) * τ ^ 2 ≤ (1 + δ) * ‖b‖ ^ 2 := by
  set T := ∑ z ∈ S, ‖⟪b, u z⟫_ℂ‖ ^ 2 with hT
  set v := ∑ z ∈ S, conj ⟪b, u z⟫_ℂ • u z with hv
  have hinner : ⟪b, v⟫_ℂ = ((T : ℝ) : ℂ) := by
    rw [hv, inner_sum, hT, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [inner_smul_right, Complex.conj_mul']
    push_cast; ring
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun z _ => by positivity
  have hTle : T ≤ ‖b‖ * ‖v‖ := by
    have h1 : T = (⟪b, v⟫_ℂ).re := by rw [hinner, Complex.ofReal_re]
    rw [h1]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm b v)
  have hv2 : ‖v‖ ^ 2 ≤ (1 + δ) * T := by
    have := hrip (fun z => conj ⟪b, u z⟫_ℂ)
    simp only [Complex.norm_conj] at this
    rw [hv, hT]
    exact this
  have hTT : T ≤ (1 + δ) * ‖b‖ ^ 2 := by
    have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
    have h2 : T ^ 2 ≤ ‖b‖ ^ 2 * ((1 + δ) * T) := by
      calc T ^ 2 ≤ (‖b‖ * ‖v‖) ^ 2 := by nlinarith
        _ = ‖b‖ ^ 2 * ‖v‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * ((1 + δ) * T) := mul_le_mul_of_nonneg_left hv2 (by positivity)
    rcases eq_or_lt_of_le hT0 with h0 | hpos
    · rw [← h0]
      exact mul_nonneg hδ (sq_nonneg _)
    · nlinarith
  calc (S.card : ℝ) * τ ^ 2 = ∑ _z ∈ S, τ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ T := Finset.sum_le_sum fun z hz => by
        have := hlarge z hz
        nlinarith
    _ ≤ (1 + δ) * ‖b‖ ^ 2 := hTT

/-- **A mixture of degrees never counts better than its best single degree.** If every degree
`l` certifies `|W| ≤ M l / u l` (from `∑_W g_l ≤ M l` and `g_l ≥ u l` on `W`), and `q` is below
every such ratio, then the mixed certificate `∑ b M / ∑ b u` is still `≥ q`. -/
theorem mixture_ge_min {κ : Type*} (s : Finset κ) (b u M : κ → ℝ) {q : ℝ}
    (hb : ∀ l ∈ s, 0 ≤ b l) (hq : ∀ l ∈ s, q * u l ≤ M l) :
    q * ∑ l ∈ s, b l * u l ≤ ∑ l ∈ s, b l * M l := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l hl => ?_
  have := mul_le_mul_of_nonneg_left (hq l hl) (hb l hl)
  linarith

end Transfer

/-! ### Main theorem: a positive measure of wide-feature operators with RIP -/

section Main

variable {d : ℕ}

/-- Feature vectors `u_z = m^{-1/2} (feat (W j) x_z)_j ∈ ℂ^m`. -/
noncomputable def fvec {m ℓ : ℕ} (W : Fin m → Fin ℓ → Fin d → Bool) (x : Fin d → ℂ) :
    EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (fun j => (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * feat (W j) x)

theorem inner_fvec {m ℓ : ℕ} (W : Fin m → Fin ℓ → Fin d → Bool) (x y : Fin d → ℂ) :
    ⟪fvec W x, fvec W y⟫_ℂ = (∑ j, conj (feat (W j) x) * feat (W j) y) / m := by
  rw [fvec, fvec, PiLp.inner_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hs : Real.sqrt m ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have h1 : (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * (((Real.sqrt m)⁻¹ : ℝ) : ℂ) = 1 / (m : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, ← sq, hs]; push_cast; ring
  linear_combination (conj (feat (W j) x) * feat (W j) y) * h1

/-- **Existence of RIP wide-feature operators by counting measure.** For any unit data
`x_z ∈ ℂ^d` (`z ∈ ι`, `N = |ι|` points) with pairwise coherence `≤ μ` and `ℓ¹`-norms `≤ C`,
if `4 N² C^{4ℓ} < m ε²` then some choice of `m` degree-`ℓ` Rademacher features (the bad
choices are fewer than all choices: Chebyshev plus a union bound over the `N²` pairs) gives
feature vectors with RIP constant `ε + (μ^ℓ + ε)(|S| − 1)` on EVERY support `S`. -/
theorem exists_wide_rip {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Fin d → ℂ)
    (ℓ m : ℕ) (hm : 0 < m) {μ ε C : ℝ} (hμ : 0 ≤ μ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hunit : ∀ z, ∑ a, ‖x z a‖ ^ 2 = 1)
    (hl1 : ∀ z, ∑ a, ‖x z a‖ ≤ C)
    (hcoh : ∀ z z', z ≠ z' → ‖∑ a, conj (x z a) * x z' a‖ ≤ μ)
    (hcount : 4 * (Fintype.card ι : ℝ) ^ 2 * C ^ (4 * ℓ) < m * ε ^ 2) :
    ∃ W : Fin m → Fin ℓ → Fin d → Bool, ∀ (S : Finset ι) (c : ι → ℂ),
      |‖∑ z ∈ S, c z • fvec W (x z)‖ ^ 2 - ∑ z ∈ S, ‖c z‖ ^ 2| ≤
        (ε + (μ ^ ℓ + ε) * ((S.card : ℝ) - 1)) * ∑ z ∈ S, ‖c z‖ ^ 2 := by
  classical
  -- the kernel, the feature products and their centred versions
  set κ : ι → ι → ℂ := fun z z' => (∑ a, conj (x z a) * x z' a) ^ ℓ with hκ
  set f : ι → ι → (Fin ℓ → Fin d → Bool) → ℂ :=
    fun z z' w => conj (feat w (x z)) * feat w (x z') with hf
  set g : ι → ι → (Fin ℓ → Fin d → Bool) → ℂ := fun z z' w => f z z' w - κ z z' with hg
  have hcardΩ : Fintype.card (Fin ℓ → Fin d → Bool) = (2 ^ d) ^ ℓ := by
    simp [Fintype.card_bool, Fintype.card_fin]
  set K : ℝ := (Fintype.card (Fin ℓ → Fin d → Bool) : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
  -- the mean of each centred product vanishes
  have hmean : ∀ z z', ∑ w, g z z' w = 0 := by
    intro z z'
    have h1 := sum_feat_mul_conj ℓ (x z') (x z)
    have h2 : ∑ w, f z z' w = ((2 : ℂ) ^ d) ^ ℓ * κ z z' := by
      simp only [hf, hκ]
      rw [show (∑ w : Fin ℓ → Fin d → Bool, conj (feat w (x z)) * feat w (x z')) =
          ∑ w : Fin ℓ → Fin d → Bool, feat w (x z') * conj (feat w (x z)) from
          Finset.sum_congr rfl fun w _ => mul_comm _ _, h1, mul_pow]
      congr 2
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simp only [hg, Finset.sum_sub_distrib, h2, Finset.sum_const, Finset.card_univ, hcardΩ,
      nsmul_eq_mul]
    push_cast
    ring
  -- pointwise bounds
  have hfeat : ∀ (w : Fin ℓ → Fin d → Bool) z, ‖feat w (x z)‖ ≤ C ^ ℓ := fun w z =>
    (norm_feat_le w (x z)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => norm_nonneg _) (hl1 z) ℓ)
  have hentry : ∀ z a, ‖x z a‖ ≤ C := fun z a =>
    (Finset.single_le_sum (fun b _ => norm_nonneg (x z b)) (Finset.mem_univ a)).trans (hl1 z)
  have hκle : ∀ z z', ‖κ z z'‖ ≤ C ^ (2 * ℓ) := by
    intro z z'
    have hs : ‖∑ a, conj (x z a) * x z' a‖ ≤ C * C := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a, ‖conj (x z a) * x z' a‖ ≤ ∑ a, ‖x z a‖ * C := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul_of_nonneg_left (hentry z' a) (norm_nonneg _)
        _ = C * ∑ a, ‖x z a‖ := by rw [← Finset.sum_mul, mul_comm]
        _ ≤ C * C := mul_le_mul_of_nonneg_left (hl1 z) hC
    simp only [hκ, norm_pow]
    calc ‖∑ a, conj (x z a) * x z' a‖ ^ ℓ ≤ (C * C) ^ ℓ :=
          pow_le_pow_left₀ (norm_nonneg _) hs ℓ
      _ = C ^ (2 * ℓ) := by rw [← sq, ← pow_mul]
  have hgle : ∀ z z' w, ‖g z z' w‖ ^ 2 ≤ 4 * C ^ (4 * ℓ) := by
    intro z z' w
    have hfw : ‖f z z' w‖ ≤ C ^ (2 * ℓ) := by
      simp only [hf, norm_mul, Complex.norm_conj]
      calc ‖feat w (x z)‖ * ‖feat w (x z')‖ ≤ C ^ ℓ * C ^ ℓ :=
            mul_le_mul (hfeat w z) (hfeat w z') (norm_nonneg _) (by positivity)
        _ = C ^ (2 * ℓ) := by ring
    have hgw : ‖g z z' w‖ ≤ 2 * C ^ (2 * ℓ) := by
      simp only [hg]
      calc ‖f z z' w - κ z z'‖ ≤ ‖f z z' w‖ + ‖κ z z'‖ := norm_sub_le _ _
        _ ≤ 2 * C ^ (2 * ℓ) := by linarith [hκle z z']
    have h0 : 0 ≤ ‖g z z' w‖ := norm_nonneg _
    calc ‖g z z' w‖ ^ 2 ≤ (2 * C ^ (2 * ℓ)) ^ 2 := pow_le_pow_left₀ h0 hgw 2
      _ = 4 * C ^ (4 * ℓ) := by ring
  -- Chebyshev for each pair
  set t : ℝ := ((m : ℝ) * ε) ^ 2 with ht
  have htpos : 0 < t := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [ht]; positivity
  set bad : ι × ι → Finset (Fin m → Fin ℓ → Fin d → Bool) := fun p =>
    univ.filter (fun W => t ≤ ‖∑ j, g p.1 p.2 (W j)‖ ^ 2) with hbad
  have hbadle : ∀ p, ((bad p).card : ℝ) ≤ 4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2) := by
    intro p
    have h1 := card_filter_le_sum_div (fun W : Fin m → Fin ℓ → Fin d → Bool =>
      ‖∑ j, g p.1 p.2 (W j)‖ ^ 2) (fun W => by positivity) htpos
    rw [sum_norm_sq_sum_pi (g p.1 p.2) (hmean p.1 p.2)] at h1
    have h2 : ∑ w, ‖g p.1 p.2 w‖ ^ 2 ≤ K * (4 * C ^ (4 * ℓ)) := by
      calc ∑ w, ‖g p.1 p.2 w‖ ^ 2 ≤ ∑ _w : Fin ℓ → Fin d → Bool, 4 * C ^ (4 * ℓ) :=
            Finset.sum_le_sum fun w _ => hgle p.1 p.2 w
        _ = K * (4 * C ^ (4 * ℓ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hKm : K ^ (m - 1) * K = K ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    calc ((bad p).card : ℝ) ≤ ((m : ℝ) * K ^ (m - 1) * ∑ w, ‖g p.1 p.2 w‖ ^ 2) / t := h1
      _ ≤ ((m : ℝ) * K ^ (m - 1) * (K * (4 * C ^ (4 * ℓ)))) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) htpos.le
      _ = 4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2) := by
          rw [ht, ← hKm]
          field_simp
  -- union bound
  set U := (univ : Finset (ι × ι)).biUnion bad with hU
  have hUlt : (U.card : ℝ) < K ^ m := by
    have h1 : (U.card : ℝ) ≤ ∑ p : ι × ι, ((bad p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ p : ι × ι, ((bad p).card : ℝ) ≤
        (Fintype.card ι : ℝ) ^ 2 * (4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2)) := by
      calc ∑ p : ι × ι, ((bad p).card : ℝ) ≤
            ∑ _p : ι × ι, 4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2) :=
            Finset.sum_le_sum fun p _ => hbadle p
        _ = (Fintype.card ι : ℝ) ^ 2 * (4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
            push_cast; ring
    have hmε : (0 : ℝ) < m * ε ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have hKm : 0 < K ^ m := pow_pos hKpos m
    have h3 : (Fintype.card ι : ℝ) ^ 2 * (4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2)) < K ^ m := by
      rw [show (Fintype.card ι : ℝ) ^ 2 * (4 * C ^ (4 * ℓ) * K ^ m / (m * ε ^ 2)) =
          (4 * (Fintype.card ι : ℝ) ^ 2 * C ^ (4 * ℓ)) / (m * ε ^ 2) * K ^ m by ring]
      have h4 : (4 * (Fintype.card ι : ℝ) ^ 2 * C ^ (4 * ℓ)) / (m * ε ^ 2) < 1 := by
        rw [div_lt_one hmε]; exact hcount
      nlinarith
    linarith
  have hlt : U.card < (univ : Finset (Fin m → Fin ℓ → Fin d → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have : ((Fintype.card (Fin ℓ → Fin d → Bool) ^ m : ℕ) : ℝ) = K ^ m := by
      rw [hK]; push_cast; ring
    exact_mod_cast (show (U.card : ℝ) < ((Fintype.card (Fin ℓ → Fin d → Bool) ^ m : ℕ) : ℝ)
      by rw [this]; exact hUlt)
  obtain ⟨W, -, hW⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  -- the chosen features are good on every pair
  have hgood : ∀ z z', ‖⟪fvec W (x z), fvec W (x z')⟫_ℂ - κ z z'‖ < ε := by
    intro z z'
    have hnb : ¬ t ≤ ‖∑ j, g z z' (W j)‖ ^ 2 := by
      intro hb
      exact hW (Finset.mem_biUnion.mpr ⟨(z, z'), Finset.mem_univ _,
        by simp only [hbad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hlt' : ‖∑ j, g z z' (W j)‖ < m * ε := by
      have h0 : 0 ≤ ‖∑ j, g z z' (W j)‖ := norm_nonneg _
      have hme : 0 ≤ (m : ℝ) * ε := by positivity
      rw [ht] at hnb
      nlinarith [not_le.mp hnb]
    have hexp : ⟪fvec W (x z), fvec W (x z')⟫_ℂ - κ z z' = (∑ j, g z z' (W j)) / m := by
      rw [inner_fvec]
      simp only [hg, hf, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    rw [hexp, norm_div, Complex.norm_natCast, div_lt_iff₀ hmpos]
    linarith
  have hdiag : ∀ z ∈ (univ : Finset ι), |‖fvec W (x z)‖ ^ 2 - 1| ≤ ε := by
    intro z _
    have hκ1 : κ z z = 1 := by
      simp only [hκ]
      have : ∑ a, conj (x z a) * x z a = 1 := by
        have h := hunit z
        have : ∑ a, conj (x z a) * x z a = ((∑ a, ‖x z a‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          exact Finset.sum_congr rfl fun a _ => Complex.conj_mul' (x z a)
        rw [this, h]; simp
      rw [this, one_pow]
    have h1 := hgood z z
    rw [hκ1] at h1
    rw [norm_sq_eq_re]
    have h2 : (⟪fvec W (x z), fvec W (x z)⟫_ℂ).re - 1 =
        (⟪fvec W (x z), fvec W (x z)⟫_ℂ - 1).re := by simp
    rw [h2]
    exact (Complex.abs_re_le_norm _).trans h1.le
  have hoff : ∀ z ∈ (univ : Finset ι), ∀ z' ∈ (univ : Finset ι), z ≠ z' →
      ‖⟪fvec W (x z), fvec W (x z')⟫_ℂ‖ ≤ μ ^ ℓ + ε := by
    intro z _ z' _ hzz
    have h1 := hgood z z'
    have h2 : ‖κ z z'‖ ≤ μ ^ ℓ := by
      simp only [hκ, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoh z z' hzz) ℓ
    calc ‖⟪fvec W (x z), fvec W (x z')⟫_ℂ‖
        = ‖(⟪fvec W (x z), fvec W (x z')⟫_ℂ - κ z z') + κ z z'‖ := by ring_nf
      _ ≤ ‖⟪fvec W (x z), fvec W (x z')⟫_ℂ - κ z z'‖ + ‖κ z z'‖ := norm_add_le _ _
      _ ≤ μ ^ ℓ + ε := by linarith
  refine ⟨W, fun S c => ?_⟩
  exact gershgorin_rip_approx S c (fun z => fvec W (x z)) (by positivity)
    (fun z _ => hdiag z (Finset.mem_univ z))
    (fun z _ z' _ hzz => hoff z (Finset.mem_univ z) z' (Finset.mem_univ z') hzz)

end Main

end QRH.ArviRIP

#print axioms QRH.ArviRIP.exists_wide_rip
#print axioms QRH.ArviRIP.count_le_of_rip
#print axioms QRH.ArviRIP.mixture_ge_min
