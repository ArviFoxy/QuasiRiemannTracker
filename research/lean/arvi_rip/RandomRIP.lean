import Submissions.arvi_rip.FlatRIP
import Submissions.arvi_rip.Hoeffding

/-!
# Random sign dictionaries have RIP far beyond the square-root barrier

Research file (QRH, RIP program, randomized dictionaries).

The columns are `u ε j = (sgn ε(r, j) / √n)_r ∈ ℂⁿ`, `j < N`, for a sign matrix `ε`. We prove
that some sign matrix has flat RIP constant `δ` on every pair of disjoint column sets of size
`≤ k` once `|pairs| · 2 · exp (-δ² n / 4) < 1`, i.e. once `n ≳ 8 k log (N + 1) / δ²`. Our
`flat_rip_on` then gives RIP of order `k`: `k ≈ δ² n / (8 log N)`, linear in the dimension,
far beyond the coherence barrier `k ≲ √n` of `coherence_order_barrier`.

Proof: conditional Hoeffding (`card_cond_le`) for each pair, with the norm of the second column
sum as the frozen variance; a minimal-counterexample induction shows that a pattern avoiding all
"bad pair with admissible variance" events has flat RIP everywhere (the variance of a smaller
pair is controlled by flat RIP on that pair, through `flat_rip_on`); then a union bound.
-/

namespace QRH.ArviRIP

open Finset
open scoped ComplexConjugate InnerProductSpace

variable {n N : ℕ}

/-- Row sum of the sign matrix over a column set. -/
def rowSum (ε : Fin n × Fin N → Bool) (J : Finset (Fin N)) (r : Fin n) : ℝ :=
  ∑ j ∈ J, sgn (ε (r, j))

/-- The flat sum `⟨∑_{J₁} u, ∑_{J₂} u⟩ = (1/n) ∑_r R_r(J₁) R_r(J₂)`. -/
noncomputable def flat (ε : Fin n × Fin N → Bool) (J₁ J₂ : Finset (Fin N)) : ℝ :=
  (∑ r, rowSum ε J₁ r * rowSum ε J₂ r) / n

/-- The column vectors of the normalized sign matrix. -/
noncomputable def col (ε : Fin n × Fin N → Bool) (j : Fin N) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun r => ((sgn (ε (r, j)) / Real.sqrt n : ℝ) : ℂ))

theorem sum_col (ε : Fin n × Fin N → Bool) (J : Finset (Fin N)) :
    ∑ j ∈ J, col ε j = WithLp.toLp 2 (fun r => ((rowSum ε J r / Real.sqrt n : ℝ) : ℂ)) := by
  simp only [col]
  rw [← WithLp.toLp_sum]
  congr 1
  funext r
  simp only [Finset.sum_apply, rowSum, Finset.sum_div]
  push_cast
  rfl

theorem inner_sum_col (ε : Fin n × Fin N → Bool) (hn : 0 < n) (J₁ J₂ : Finset (Fin N)) :
    ⟪∑ j ∈ J₁, col ε j, ∑ j ∈ J₂, col ε j⟫_ℂ = ((flat ε J₁ J₂ : ℝ) : ℂ) := by
  rw [sum_col, sum_col, PiLp.inner_apply]
  have hs : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 : Real.sqrt n ≠ 0 := by positivity
  simp only [RCLike.inner_apply, Complex.conj_ofReal, flat]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hn' : (n : ℂ) = ((Real.sqrt n : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hs]; push_cast; rfl
  rw [hn']
  have hs0' : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  field_simp

theorem norm_sq_sum_col (ε : Fin n × Fin N → Bool) (hn : 0 < n) (J : Finset (Fin N)) :
    ‖∑ j ∈ J, col ε j‖ ^ 2 = flat ε J J := by
  rw [norm_sq_eq_re, inner_sum_col ε hn, Complex.ofReal_re]

theorem flat_single (ε : Fin n × Fin N → Bool) (hn : 0 < n) (j : Fin N) :
    flat ε {j} {j} = 1 := by
  simp only [flat, rowSum, Finset.sum_singleton]
  have h : ∀ r : Fin n, sgn (ε (r, j)) * sgn (ε (r, j)) = 1 := fun r => by
    rw [← sq, sgn_sq]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem norm_col (ε : Fin n × Fin N → Bool) (hn : 0 < n) (j : Fin N) : ‖col ε j‖ = 1 := by
  have h := norm_sq_sum_col ε hn {j}
  rw [Finset.sum_singleton, flat_single ε hn] at h
  have h0 : 0 ≤ ‖col ε j‖ := norm_nonneg _
  nlinarith [h, h0]

theorem flat_empty_left (ε : Fin n × Fin N → Bool) (J : Finset (Fin N)) :
    flat ε ∅ J = 0 := by simp [flat, rowSum]

theorem flat_empty_right (ε : Fin n × Fin N → Bool) (J : Finset (Fin N)) :
    flat ε J ∅ = 0 := by simp [flat, rowSum]

/-! ### One pair: conditional Hoeffding -/

/-- Coefficients of the flat sum as a Rademacher sum in the entries of the `J₁` columns. -/
noncomputable def coef (J₁ J₂ : Finset (Fin N)) (ε : Fin n × Fin N → Bool)
    (k : Fin n × Fin N) : ℝ :=
  if k.2 ∈ J₁ then rowSum ε J₂ k.1 / n else 0

theorem coef_sum (J₁ J₂ : Finset (Fin N)) (ε : Fin n × Fin N → Bool) :
    ∑ k, coef J₁ J₂ ε k * sgn (ε k) = flat ε J₁ J₂ := by
  rw [Fintype.sum_prod_type, flat, Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [coef, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  have h1 : ∑ i ∈ J₁, sgn (ε (r, i)) = rowSum ε J₁ r := rfl
  rw [h1]
  ring

theorem coef_sq (J₁ J₂ : Finset (Fin N)) (ε : Fin n × Fin N → Bool) :
    ∑ k, coef J₁ J₂ ε k ^ 2 = J₁.card * flat ε J₂ J₂ / n := by
  rw [Fintype.sum_prod_type, flat]
  have h : ∀ r : Fin n, ∑ j : Fin N, coef J₁ J₂ ε (r, j) ^ 2 =
      J₁.card * (rowSum ε J₂ r / n) ^ 2 := by
    intro r
    simp only [coef]
    have : ∀ j : Fin N, (if j ∈ J₁ then rowSum ε J₂ r / n else 0) ^ 2 =
        if j ∈ J₁ then (rowSum ε J₂ r / n) ^ 2 else 0 := fun j => by
      split_ifs <;> ring
    simp only [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  simp only [h]
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    field_simp

theorem coef_zero (J₁ J₂ : Finset (Fin N)) (ε : Fin n × Fin N → Bool)
    (k : Fin n × Fin N) (hk : ¬ k.2 ∈ J₁) : coef J₁ J₂ ε k = 0 := by
  simp [coef, hk]

theorem coef_dep {J₁ J₂ : Finset (Fin N)} (hd : Disjoint J₁ J₂) (ε ε' : Fin n × Fin N → Bool)
    (h : ∀ k : Fin n × Fin N, ¬ k.2 ∈ J₁ → ε k = ε' k) : coef J₁ J₂ ε = coef J₁ J₂ ε' := by
  funext k
  have hr : rowSum ε J₂ k.1 = rowSum ε' J₂ k.1 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [h (k.1, j) (Finset.disjoint_right.mp hd hj)]
  simp only [coef, hr]

/-- The bad event for a pair: a large flat sum while the second column sum has admissible
norm `‖∑_{J₂} u‖² ≤ 2 |J₂|`. -/
def Bad (δ : ℝ) (J₁ J₂ : Finset (Fin N)) (ε : Fin n × Fin N → Bool) : Prop :=
  δ * Real.sqrt ((J₁.card : ℝ) * J₂.card) < |flat ε J₁ J₂| ∧ flat ε J₂ J₂ ≤ 2 * J₂.card

noncomputable instance (δ : ℝ) (J₁ J₂ : Finset (Fin N)) : DecidablePred (Bad (n := n) δ J₁ J₂) :=
  fun _ => Classical.dec _

/-- **One pair.** At most `2 · 2^{nN} · exp (-δ² n / 4)` sign matrices are bad for a disjoint
pair. -/
theorem card_bad_le (hn : 0 < n) {δ : ℝ} (hδ : 0 ≤ δ) {J₁ J₂ : Finset (Fin N)}
    (hd : Disjoint J₁ J₂) :
    ((univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ J₁ J₂ ε)).card : ℝ) ≤
      2 * 2 ^ (n * N) * Real.exp (-(δ ^ 2 * n / 4)) := by
  have hR : 0 ≤ 2 * 2 ^ (n * N) * Real.exp (-(δ ^ 2 * n / 4)) := by positivity
  rcases J₁.eq_empty_or_nonempty with h1 | h1
  · have : univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ J₁ J₂ ε) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun ε _ hb => ?_)
      have := hb.1
      rw [h1, flat_empty_left] at this; simp at this
    rw [this, Finset.card_empty, Nat.cast_zero]; exact hR
  rcases J₂.eq_empty_or_nonempty with h2 | h2
  · have : univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ J₁ J₂ ε) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun ε _ hb => ?_)
      have := hb.1
      rw [h2, flat_empty_right] at this; simp at this
    rw [this, Finset.card_empty, Nat.cast_zero]; exact hR
  have hc1 : (0 : ℝ) < J₁.card := by exact_mod_cast h1.card_pos
  have hc2 : (0 : ℝ) < J₂.card := by exact_mod_cast h2.card_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (2 * J₁.card * J₂.card / n) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσ2 : σ ^ 2 = 2 * J₁.card * J₂.card / n := by
    rw [hσ, Real.sq_sqrt (by positivity)]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ * Real.sqrt ((J₁.card : ℝ) * J₂.card) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht2 : t ^ 2 = δ ^ 2 * (J₁.card * J₂.card) := by
    rw [ht, mul_pow, Real.sq_sqrt (by positivity)]
  have hsub : univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ J₁ J₂ ε) ⊆
      univ.filter (fun ε : Fin n × Fin N → Bool =>
        t ≤ |∑ k, coef J₁ J₂ ε k * sgn (ε k)| ∧ ∑ k, coef J₁ J₂ ε k ^ 2 ≤ σ ^ 2) := by
    intro ε hε
    simp only [mem_filter, mem_univ, true_and] at hε ⊢
    refine ⟨?_, ?_⟩
    · rw [coef_sum, ht]; exact hε.1.le
    · rw [coef_sq, hσ2]
      have : (J₁.card : ℝ) * flat ε J₂ J₂ ≤ J₁.card * (2 * J₂.card) :=
        mul_le_mul_of_nonneg_left hε.2 hc1.le
      calc (J₁.card : ℝ) * flat ε J₂ J₂ / n ≤ J₁.card * (2 * J₂.card) / n :=
            div_le_div_of_nonneg_right this hnr.le
        _ = 2 * J₁.card * J₂.card / n := by ring
  have hmain := card_cond_le (fun k : Fin n × Fin N => k.2 ∈ J₁) (coef J₁ J₂)
    (fun ε k hk => coef_zero J₁ J₂ ε k hk) (fun ε ε' h => coef_dep hd ε ε' h) ht0 hσ0
  have hexp : -(t ^ 2) / (2 * σ ^ 2) = -(δ ^ 2 * n / 4) := by
    rw [ht2, hσ2]; field_simp; ring
  rw [hexp] at hmain
  have hcard : Fintype.card (Fin n × Fin N) = n * N := by simp
  rw [hcard] at hmain
  calc ((univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ J₁ J₂ ε)).card : ℝ)
      ≤ (univ.filter (fun ε : Fin n × Fin N → Bool =>
          t ≤ |∑ k, coef J₁ J₂ ε k * sgn (ε k)| ∧ ∑ k, coef J₁ J₂ ε k ^ 2 ≤ σ ^ 2)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 * 2 ^ (n * N) * Real.exp (-(δ ^ 2 * n / 4)) := hmain

/-! ### Minimal counterexample: avoiding all bad events gives flat RIP everywhere -/

/-- Column sets of size at most `k`. -/
def Small (N k : ℕ) : Finset (Finset (Fin N)) := univ.filter (fun J => J.card ≤ k)

/-- Disjoint pairs of column sets of size at most `k`. -/
def Pairs (N k : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Small N k ×ˢ Small N k).filter (fun x => Disjoint x.1 x.2)

theorem dyc_le_of_card {T k : ℕ} {W : Finset (Fin N)} (hW : W.card ≤ k) :
    dyc T W ≤ ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt k) ^ 2 := by
  unfold dyc
  have hs : Real.sqrt W.card ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hW)
  have h0 : 0 ≤ (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt W.card := by positivity
  have h1 : (T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt W.card ≤ T + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt k := by
    have h2 : (0 : ℝ) ≤ ((2 : ℝ) ^ T)⁻¹ := inv_nonneg.mpr (pow_nonneg (by norm_num) T)
    have := mul_le_mul_of_nonneg_left hs h2
    linarith only [this]
  exact pow_le_pow_left₀ h0 h1 2

/-- If a sign matrix avoids every bad event of `Pairs N k`, its columns have flat RIP
constant `δ` on all disjoint pairs of size `≤ k`. Strong induction on `|J₁| + |J₂|`: the
second column sum of a pair has admissible norm by flat RIP on smaller pairs. -/
theorem flat_of_not_bad (hn : 0 < n) {δ : ℝ} (hδ : 0 ≤ δ) {k T : ℕ}
    (hT : 32 * (δ * ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt k) ^ 2) ≤ 1)
    (ε : Fin n × Fin N → Bool) (hgood : ∀ x ∈ Pairs N k, ¬ Bad δ x.1 x.2 ε) :
    ∀ m : ℕ, ∀ J₁ J₂ : Finset (Fin N), J₁.card + J₂.card = m → Disjoint J₁ J₂ →
      J₁.card ≤ k → J₂.card ≤ k → |flat ε J₁ J₂| ≤ δ * Real.sqrt ((J₁.card : ℝ) * J₂.card) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro J₁ J₂ hm hd h1 h2
    rcases J₁.eq_empty_or_nonempty with he | hne
    · rw [he, flat_empty_left, abs_zero]; exact mul_nonneg hδ (Real.sqrt_nonneg _)
    have hflat : FlatOn (col ε) J₂ δ := by
      intro A hA B hB hAB
      have hcardAB : A.card + B.card ≤ J₂.card := by
        rw [← Finset.card_union_of_disjoint hAB]
        exact Finset.card_le_card (Finset.union_subset hA hB)
      have hlt : A.card + B.card < m := by
        have := hne.card_pos; omega
      have := ih (A.card + B.card) hlt A B rfl hAB ((Finset.card_le_card hA).trans h2)
        ((Finset.card_le_card hB).trans h2)
      rw [inner_sum_col ε hn, Complex.norm_real, Real.norm_eq_abs]
      exact this
    have hrip := flat_rip_on (col ε) J₂ (fun z _ => norm_col ε hn z) hδ hflat T (fun _ => 1)
    simp only [one_smul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hrip
    rw [norm_sq_sum_col ε hn] at hrip
    have hdyc : 32 * (δ * dyc T J₂) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dyc_le_of_card h2) hδ)
        (by norm_num)) hT
    have hnorm : flat ε J₂ J₂ ≤ 2 * J₂.card := by
      have hc : (0 : ℝ) ≤ J₂.card := Nat.cast_nonneg _
      have h3 := (abs_le.mp hrip).2
      nlinarith [mul_le_mul_of_nonneg_right hdyc hc]
    have hpair : (J₁, J₂) ∈ Pairs N k := by
      simp only [Pairs, Small, mem_filter, mem_product, mem_univ, true_and]
      exact ⟨⟨h1, h2⟩, hd⟩
    have hnb := hgood _ hpair
    by_contra hcon
    exact hnb ⟨lt_of_not_ge hcon, hnorm⟩

/-! ### Union bound and the theorem -/

theorem card_signs : (univ : Finset (Fin n × Fin N → Bool)).card = 2 ^ (n * N) := by
  simp [Finset.card_univ]

/-- **Random sign dictionaries have RIP of order `k`.** If the number of disjoint pairs of
column sets of size `≤ k` times `2 exp (-δ² n / 4)` is below `1`, some `n × N` sign matrix has
unit columns that are near-isometric on every support of size `≤ k`, with the constant of
`flat_rip_on`. -/
theorem exists_rip_sign (hn : 0 < n) {δ : ℝ} (hδ : 0 ≤ δ) (k T : ℕ)
    (hT : 32 * (δ * ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt k) ^ 2) ≤ 1)
    (hcount : ((Pairs N k).card : ℝ) * (2 * Real.exp (-(δ ^ 2 * n / 4))) < 1) :
    ∃ ε : Fin n × Fin N → Bool, (∀ j, ‖col ε j‖ = 1) ∧
      ∀ W : Finset (Fin N), W.card ≤ k → ∀ a : Fin N → ℂ,
        |‖∑ z ∈ W, a z • col ε z‖ ^ 2 - ∑ z ∈ W, ‖a z‖ ^ 2| ≤
          32 * (δ * dyc T W) * ∑ z ∈ W, ‖a z‖ ^ 2 := by
  classical
  set U := (Pairs N k).biUnion
    (fun x => univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ x.1 x.2 ε)) with hU
  have hUcard : (U.card : ℝ) < 2 ^ (n * N) := by
    have h1 : (U.card : ℝ) ≤ ∑ x ∈ Pairs N k,
        ((univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ x.1 x.2 ε)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ x ∈ Pairs N k,
        ((univ.filter (fun ε : Fin n × Fin N → Bool => Bad δ x.1 x.2 ε)).card : ℝ) ≤
        ∑ _x ∈ Pairs N k, 2 * 2 ^ (n * N) * Real.exp (-(δ ^ 2 * n / 4)) := by
      refine Finset.sum_le_sum (fun x hx => card_bad_le hn hδ ?_)
      simp only [Pairs, mem_filter] at hx; exact hx.2
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hpos : (0 : ℝ) < 2 ^ (n * N) := by positivity
    calc (U.card : ℝ) ≤ (Pairs N k).card * (2 * 2 ^ (n * N) * Real.exp (-(δ ^ 2 * n / 4))) :=
          h1.trans h2
      _ = ((Pairs N k).card * (2 * Real.exp (-(δ ^ 2 * n / 4)))) * 2 ^ (n * N) := by ring
      _ < 1 * 2 ^ (n * N) := mul_lt_mul_of_pos_right hcount hpos
      _ = 2 ^ (n * N) := one_mul _
  have hlt : U.card < (univ : Finset (Fin n × Fin N → Bool)).card := by
    rw [card_signs]; exact_mod_cast hUcard
  obtain ⟨ε, -, hε⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hgood : ∀ x ∈ Pairs N k, ¬ Bad δ x.1 x.2 ε := by
    intro x hx hb
    exact hε (Finset.mem_biUnion.mpr ⟨x, hx, by simp only [mem_filter, mem_univ, true_and]; exact hb⟩)
  refine ⟨ε, norm_col ε hn, fun W hW a => ?_⟩
  have hflat : FlatOn (col ε) W δ := by
    intro J₁ h1 J₂ h2 hd
    rw [inner_sum_col ε hn, Complex.norm_real, Real.norm_eq_abs]
    exact flat_of_not_bad hn hδ hT ε hgood _ J₁ J₂ rfl hd
      ((Finset.card_le_card h1).trans hW) ((Finset.card_le_card h2).trans hW)
  exact flat_rip_on (col ε) W (fun z _ => norm_col ε hn z) hδ hflat T a

/-! ### Counting pairs: `|Pairs N k| ≤ (N + 1)^{2k}` -/

theorem card_small_le (N k : ℕ) : (Small N k).card ≤ (N + 1) ^ k := by
  classical
  have hsub : Small N k ⊆ (range (k + 1)).biUnion (fun s => powersetCard s (univ : Finset (Fin N))) := by
    intro J hJ
    simp only [Small, mem_filter, mem_univ, true_and] at hJ
    exact Finset.mem_biUnion.mpr ⟨J.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hJ),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ J, rfl⟩⟩
  calc (Small N k).card
      ≤ ((range (k + 1)).biUnion (fun s => powersetCard s (univ : Finset (Fin N)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s ∈ range (k + 1), (powersetCard s (univ : Finset (Fin N))).card :=
        Finset.card_biUnion_le
    _ = ∑ s ∈ range (k + 1), N.choose s := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ s ∈ range (k + 1), N ^ s * 1 ^ (k - s) * k.choose s := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        have hsk : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
        rw [one_pow, mul_one]
        exact (Nat.choose_le_pow N s).trans (Nat.le_mul_of_pos_right _ (Nat.choose_pos hsk))
    _ = (N + 1) ^ k := (add_pow (N : ℕ) 1 k).symm

theorem card_pairs_le (N k : ℕ) : (Pairs N k).card ≤ (N + 1) ^ (2 * k) := by
  calc (Pairs N k).card ≤ (Small N k ×ˢ Small N k).card := Finset.card_filter_le _ _
    _ = (Small N k).card * (Small N k).card := Finset.card_product _ _
    _ ≤ (N + 1) ^ k * (N + 1) ^ k := Nat.mul_le_mul (card_small_le N k) (card_small_le N k)
    _ = (N + 1) ^ (2 * k) := by ring

/-- **Random sign dictionaries break the square-root barrier** (explicit form). If
`2 (N + 1)^{2k} exp (-δ² n / 4) < 1`, i.e. `n > 4 (2k log (N + 1) + log 2) / δ²`, some `n × N`
sign matrix has unit columns with RIP of order `k` and constant `32 δ dyc T W`. The order is
linear in `n` (up to `log N`), against `k ≲ √n` for every coherence certificate
(`coherence_order_barrier`). -/
theorem exists_rip_sign_explicit (hn : 0 < n) {δ : ℝ} (hδ : 0 ≤ δ) (k T : ℕ)
    (hT : 32 * (δ * ((T : ℝ) + ((2 : ℝ) ^ T)⁻¹ * Real.sqrt k) ^ 2) ≤ 1)
    (hnk : ((N : ℝ) + 1) ^ (2 * k) * (2 * Real.exp (-(δ ^ 2 * n / 4))) < 1) :
    ∃ ε : Fin n × Fin N → Bool, (∀ j, ‖col ε j‖ = 1) ∧
      ∀ W : Finset (Fin N), W.card ≤ k → ∀ a : Fin N → ℂ,
        |‖∑ z ∈ W, a z • col ε z‖ ^ 2 - ∑ z ∈ W, ‖a z‖ ^ 2| ≤
          32 * (δ * dyc T W) * ∑ z ∈ W, ‖a z‖ ^ 2 := by
  refine exists_rip_sign hn hδ k T hT (lt_of_le_of_lt ?_ hnk)
  have hc : ((Pairs N k).card : ℝ) ≤ ((N : ℝ) + 1) ^ (2 * k) := by
    exact_mod_cast card_pairs_le N k
  exact mul_le_mul_of_nonneg_right hc (by positivity)

end QRH.ArviRIP

#print axioms QRH.ArviRIP.card_cond_le
#print axioms QRH.ArviRIP.exists_rip_sign
#print axioms QRH.ArviRIP.exists_rip_sign_explicit
