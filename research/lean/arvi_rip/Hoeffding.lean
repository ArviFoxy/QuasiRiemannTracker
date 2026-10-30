import Mathlib

/-!
# Hoeffding's inequality for sign patterns (finite counting form)

Research file (QRH, RIP program, randomized dictionaries). Probability over uniform sign patterns
`ε : κ → Bool` is counting: `#{ε | t ≤ |∑ a k · sgn (ε k)|} ≤ 2 · 2^{|κ|} · exp (-t² / (2σ²))`
whenever `∑ a k² ≤ σ²`. No measure theory.
-/

namespace QRH.ArviRIP

open Finset

/-- The sign of a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Exponential moment of a Rademacher sum over all sign patterns. -/
theorem sum_exp_signs (a : κ → ℝ) (l : ℝ) :
    ∑ ε : κ → Bool, Real.exp (l * ∑ k, a k * sgn (ε k)) =
      ∏ k, (2 * Real.cosh (l * a k)) := by
  have h1 : ∀ ε : κ → Bool, Real.exp (l * ∑ k, a k * sgn (ε k)) =
      ∏ k, Real.exp (l * a k * sgn (ε k)) := by
    intro ε
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl (fun k _ => by ring_nf)
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun k (b : Bool) => Real.exp (l * a k * sgn b))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Fintype.sum_bool, Real.cosh_eq]
  simp only [sgn_true, sgn_false, mul_one, mul_neg_one]
  ring

omit [DecidableEq κ] in
/-- `2 cosh x ≤ 2 exp (x²/2)`, multiplied over the pattern. -/
theorem prod_cosh_le (a : κ → ℝ) (l : ℝ) :
    ∏ k, (2 * Real.cosh (l * a k)) ≤
      2 ^ Fintype.card κ * Real.exp (l ^ 2 * (∑ k, a k ^ 2) / 2) := by
  have h : ∏ k, (2 * Real.cosh (l * a k)) ≤ ∏ k, (2 * Real.exp ((l * a k) ^ 2 / 2)) := by
    refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
  have hs : ∑ k, (l * a k) ^ 2 / 2 = l ^ 2 * (∑ k, a k ^ 2) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  refine h.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, hs]

/-- One-sided Hoeffding bound, counting form (`0 ≤ t`, `∑ a² ≤ σ²`). -/
theorem card_ge_le (a : κ → ℝ) {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    (hS : ∑ k, a k ^ 2 ≤ σ ^ 2) :
    ((univ.filter (fun ε : κ → Bool => t ≤ ∑ k, a k * sgn (ε k))).card : ℝ) ≤
      2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = t / σ ^ 2 := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := hl ▸ div_nonneg ht hσ2.le
  set F := univ.filter (fun ε : κ → Bool => t ≤ ∑ k, a k * sgn (ε k)) with hF
  have hmk : (F.card : ℝ) * Real.exp (l * t) ≤
      ∑ ε : κ → Bool, Real.exp (l * ∑ k, a k * sgn (ε k)) := by
    calc (F.card : ℝ) * Real.exp (l * t) = ∑ ε ∈ F, Real.exp (l * t) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ε ∈ F, Real.exp (l * ∑ k, a k * sgn (ε k)) := by
          refine Finset.sum_le_sum (fun ε hε => ?_)
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hε).2 hl0)
      _ ≤ ∑ ε : κ → Bool, Real.exp (l * ∑ k, a k * sgn (ε k)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hup : ∑ ε : κ → Bool, Real.exp (l * ∑ k, a k * sgn (ε k)) ≤
      2 ^ Fintype.card κ * Real.exp (l ^ 2 * σ ^ 2 / 2) := by
    rw [sum_exp_signs]
    refine (prod_cosh_le a l).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (sq_nonneg l)) (by norm_num)
  have hexp : Real.exp (l ^ 2 * σ ^ 2 / 2) = Real.exp (-(t ^ 2) / (2 * σ ^ 2)) * Real.exp (l * t) := by
    rw [← Real.exp_add, hl]
    congr 1
    field_simp
    ring
  have h2 : (F.card : ℝ) * Real.exp (l * t) ≤
      (2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2))) * Real.exp (l * t) := by
    calc (F.card : ℝ) * Real.exp (l * t) ≤ 2 ^ Fintype.card κ * Real.exp (l ^ 2 * σ ^ 2 / 2) :=
          hmk.trans hup
      _ = _ := by rw [hexp]; ring
  exact le_of_mul_le_mul_right h2 (Real.exp_pos _)

/-- Two-sided Hoeffding bound, counting form. -/
theorem card_abs_ge_le (a : κ → ℝ) {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    (hS : ∑ k, a k ^ 2 ≤ σ ^ 2) :
    ((univ.filter (fun ε : κ → Bool => t ≤ |∑ k, a k * sgn (ε k)|)).card : ℝ) ≤
      2 * 2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
  have hsub : univ.filter (fun ε : κ → Bool => t ≤ |∑ k, a k * sgn (ε k)|) ⊆
      univ.filter (fun ε : κ → Bool => t ≤ ∑ k, a k * sgn (ε k)) ∪
      univ.filter (fun ε : κ → Bool => t ≤ ∑ k, (-a k) * sgn (ε k)) := by
    intro ε hε
    simp only [mem_filter, mem_univ, true_and, mem_union] at hε ⊢
    rcases le_abs'.mp hε with h | h
    · right
      have : ∑ k, (-a k) * sgn (ε k) = -∑ k, a k * sgn (ε k) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this]; linarith
    · left; exact h
  have hS' : ∑ k, (-a k) ^ 2 ≤ σ ^ 2 := by simpa only [neg_sq] using hS
  calc ((univ.filter (fun ε : κ → Bool => t ≤ |∑ k, a k * sgn (ε k)|)).card : ℝ)
      ≤ ((univ.filter (fun ε : κ → Bool => t ≤ ∑ k, a k * sgn (ε k)) ∪
          univ.filter (fun ε : κ → Bool => t ≤ ∑ k, (-a k) * sgn (ε k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (univ.filter (fun ε : κ → Bool => t ≤ ∑ k, a k * sgn (ε k))).card +
          ((univ.filter (fun ε : κ → Bool => t ≤ ∑ k, (-a k) * sgn (ε k))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) +
          2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) :=
        add_le_add (card_ge_le a ht hσ hS) (card_ge_le (fun k => -a k) ht hσ hS')
    _ = 2 * 2 ^ Fintype.card κ * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by ring


/-! ### Conditional form: Hoeffding on the entries in `p`, the others frozen -/

section Cond

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Conditional Hoeffding, counting form.** The coefficients `c ε` may depend on the pattern,
but only through its entries outside `p`, and vanish outside `p`. Then the patterns with a large
sum and an admissible coefficient mass are at most `2 · 2^{|α|} · exp (-t²/(2σ²))`. -/
theorem card_cond_le (p : α → Prop) [DecidablePred p] (c : (α → Bool) → α → ℝ)
    (hc0 : ∀ ε k, ¬ p k → c ε k = 0)
    (hcd : ∀ ε ε' : α → Bool, (∀ k, ¬ p k → ε k = ε' k) → c ε = c ε')
    {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ) :
    ((univ.filter (fun ε : α → Bool =>
        t ≤ |∑ k, c ε k * sgn (ε k)| ∧ ∑ k, c ε k ^ 2 ≤ σ ^ 2)).card : ℝ) ≤
      2 * 2 ^ Fintype.card α * Real.exp (-(t ^ 2) / (2 * σ ^ 2)) := by
  classical
  set e := Equiv.piEquivPiSubtypeProd p (fun _ : α => Bool) with he
  set P : (α → Bool) → Prop := fun ε =>
    t ≤ |∑ k, c ε k * sgn (ε k)| ∧ ∑ k, c ε k ^ 2 ≤ σ ^ 2 with hP
  set B := Real.exp (-(t ^ 2) / (2 * σ ^ 2)) with hB
  -- frozen coefficients for each assignment `η` of the entries outside `p`
  set a : (∀ k : {k // ¬ p k}, Bool) → {k // p k} → ℝ :=
    fun η k => c (e.symm (fun _ => true, η)) k with ha
  have hce : ∀ ξ η, c (e.symm (ξ, η)) = c (e.symm (fun _ => true, η)) := by
    intro ξ η
    apply hcd
    intro k hk
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hk]
  have hsum : ∀ ξ η, ∑ k, c (e.symm (ξ, η)) k * sgn (e.symm (ξ, η) k) =
      ∑ k : {k // p k}, a η k * sgn (ξ k) := by
    intro ξ η
    rw [← Fintype.sum_subtype_add_sum_subtype p]
    have h0 : ∑ k : {k // ¬ p k}, c (e.symm (ξ, η)) k * sgn (e.symm (ξ, η) k) = 0 :=
      Finset.sum_eq_zero (fun k _ => by rw [hc0 _ _ k.2, zero_mul])
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hce ξ η]
    simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, k.2, ha]
  have hsq : ∀ ξ η, ∑ k, c (e.symm (ξ, η)) k ^ 2 = ∑ k : {k // p k}, a η k ^ 2 := by
    intro ξ η
    rw [← Fintype.sum_subtype_add_sum_subtype p]
    have h0 : ∑ k : {k // ¬ p k}, c (e.symm (ξ, η)) k ^ 2 = 0 :=
      Finset.sum_eq_zero (fun k _ => by rw [hc0 _ _ k.2]; ring)
    rw [h0, add_zero, hce ξ η]
  -- inner count for a fixed frozen part
  have hinner : ∀ η, ((univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η)))).card
      : ℝ) ≤ 2 * 2 ^ Fintype.card {k // p k} * B := by
    intro η
    by_cases hη : ∑ k : {k // p k}, a η k ^ 2 ≤ σ ^ 2
    · have hsub : univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η))) ⊆
          univ.filter (fun ξ : {k // p k} → Bool => t ≤ |∑ k, a η k * sgn (ξ k)|) := by
        intro ξ hξ
        simp only [mem_filter, mem_univ, true_and, hP] at hξ ⊢
        rw [← hsum ξ η]; exact hξ.1
      calc ((univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η)))).card : ℝ)
          ≤ (univ.filter (fun ξ : {k // p k} → Bool => t ≤ |∑ k, a η k * sgn (ξ k)|)).card := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 * 2 ^ Fintype.card {k // p k} * B := card_abs_ge_le (a η) ht hσ hη
    · have hemp : univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η))) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr (fun ξ _ hξ => hη ?_)
        rw [← hsq ξ η]; exact hξ.2
      rw [hemp, Finset.card_empty, Nat.cast_zero]
      positivity
  -- assemble: count = ∑_η inner count
  have hcount : ((univ.filter P).card : ℝ) =
      ∑ η : (∀ k : {k // ¬ p k}, Bool),
        ((univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η)))).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    rw [Finset.card_filter, Nat.cast_sum]
  have hcardα : (2 : ℝ) ^ Fintype.card α =
      2 ^ Fintype.card {k // p k} * 2 ^ Fintype.card {k // ¬ p k} := by
    rw [← pow_add, Fintype.card_subtype_compl, Nat.add_sub_cancel' (Fintype.card_subtype_le p)]
  show ((univ.filter P).card : ℝ) ≤ 2 * 2 ^ Fintype.card α * B
  rw [hcount]
  calc ∑ η : (∀ k : {k // ¬ p k}, Bool),
        ((univ.filter (fun ξ : (∀ k : {k // p k}, Bool) => P (e.symm (ξ, η)))).card : ℝ)
      ≤ ∑ _η : (∀ k : {k // ¬ p k}, Bool), 2 * 2 ^ Fintype.card {k // p k} * B :=
        Finset.sum_le_sum (fun η _ => hinner η)
    _ = 2 * 2 ^ Fintype.card α * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardα]
        simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ]
        push_cast
        ring

end Cond

end QRH.ArviRIP
