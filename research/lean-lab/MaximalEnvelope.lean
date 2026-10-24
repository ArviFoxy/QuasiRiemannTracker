import Mathlib

/-!
# The continuum face map: comparison principle (see `../variational-ceiling/README.md`)

In the continuum limit of the source graph the envelope `E(s)` (the largest proven plain length at
slot width `s`) must descend at least as fast as the minimal admissible face slope:
`E'(s) ≤ -Λ(s, E(s))`. Here `Λ(s, e)` is the flattest slope for which some LOW/HIGH threshold
passes every source-step gate at height `e`. A higher envelope makes the HIGH gate harder, so `Λ`
is nondecreasing in `e`.

`envelope_le_of_monotone_slope`: every admissible envelope stays below the solution `Ê` of the
equation `Ê' = -Λ(s, Ê)` with the same (or a larger) starting value. So within the continuum
class the equality solution is the ceiling.

The core is `nonpos_of_deriv_nonpos_where_pos`: a function that starts `≤ 0` and is nonincreasing
wherever it is positive stays `≤ 0`.
-/

namespace Lab.MaximalEnvelope

open Set

theorem nonpos_of_deriv_nonpos_where_pos {h : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn h (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ h x)
    (hpos : ∀ x ∈ Ioo a b, 0 < h x → deriv h x ≤ 0)
    (ha : h a ≤ 0) : ∀ x ∈ Icc a b, h x ≤ 0 := by
  intro t₁ ht₁
  by_contra hcon
  push Not at hcon
  set S : Set ℝ := Icc a t₁ ∩ h ⁻¹' Iic 0 with hSdef
  have haS : a ∈ S := ⟨⟨le_refl a, ht₁.1⟩, ha⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hclosed : IsClosed S :=
    (hc.mono (Icc_subset_Icc_right ht₁.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set t₀ := sSup S with ht₀def
  have ht₀S : t₀ ∈ S := hclosed.csSup_mem ⟨a, haS⟩ hbdd
  have hat₀ : a ≤ t₀ := ht₀S.1.1
  have ht₀t₁ : t₀ ≤ t₁ := ht₀S.1.2
  have ht₀nonpos : h t₀ ≤ 0 := ht₀S.2
  have ht₀lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀t₁ with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at ht₀nonpos
      linarith
  have hposIoc : ∀ t ∈ Ioc t₀ t₁, 0 < h t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have htS : t ∈ S := ⟨⟨le_trans hat₀ (le_of_lt ht.1), ht.2⟩, hneg⟩
    have := le_csSup hbdd htS
    linarith [ht.1]
  have hanti : AntitoneOn h (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact hc.mono (Icc_subset_Icc hat₀ ht₁.2)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨lt_of_le_of_lt hat₀ hx.1, lt_of_lt_of_le hx.2 ht₁.2⟩).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hpos x ⟨lt_of_le_of_lt hat₀ hx.1, lt_of_lt_of_le hx.2 ht₁.2⟩
        (hposIoc x ⟨hx.1, le_of_lt hx.2⟩)
  have hle := hanti ⟨le_refl t₀, ht₀t₁⟩ ⟨ht₀t₁, le_refl t₁⟩ ht₀t₁
  linarith

/-- Comparison principle for the continuum face map. -/
theorem envelope_le_of_monotone_slope {E Ê E' Ê' : ℝ → ℝ} {Λ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hmono : ∀ s x y, x ≤ y → Λ s x ≤ Λ s y)
    (hE : ∀ s ∈ Icc a b, HasDerivAt E (E' s) s)
    (hÊ : ∀ s ∈ Icc a b, HasDerivAt Ê (Ê' s) s)
    (hineq : ∀ s ∈ Icc a b, E' s ≤ -Λ s (E s))
    (heq : ∀ s ∈ Icc a b, Ê' s = -Λ s (Ê s))
    (ha : E a ≤ Ê a) : ∀ s ∈ Icc a b, E s ≤ Ê s := by
  have key := nonpos_of_deriv_nonpos_where_pos (h := fun s => E s - Ê s) (a := a) (b := b)
    (fun s hs => ((hE s hs).sub (hÊ s hs)).continuousAt.continuousWithinAt)
    (fun s hs => ((hE s (Ioo_subset_Icc_self hs)).sub
      (hÊ s (Ioo_subset_Icc_self hs))).differentiableAt)
    (fun s hs hp => by
      have hs' := Ioo_subset_Icc_self hs
      show deriv (E - Ê) s ≤ 0
      rw [((hE s hs').sub (hÊ s hs')).deriv]
      have h1 := hineq s hs'
      have h2 := heq s hs'
      have h3 : Λ s (Ê s) ≤ Λ s (E s) := hmono s _ _ (by linarith)
      linarith)
    (show E a - Ê a ≤ 0 by linarith)
  intro s hs
  have := key s hs
  linarith

end Lab.MaximalEnvelope
