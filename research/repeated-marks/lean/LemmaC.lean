import Mathlib

/-!
# Lemma C: common-width payment for a gain that is a minimum of monotone linear forms

Let `G` be bounded above, at the cell `(S,F)`, by every facet `A j * S + B j * F` (with
`A j, B j ≥ 0`) and by `ν * S`, and let `G L Q` be the infimum of the facets at `(L,Q)`.
If `2 * S ≤ F`, `S ≤ L + δ`, `F ≤ Q + 2 * δ` and `L, Q, δ ≥ 0`, then
`G S F ≤ G L Q + ν * δ`.
-/

namespace RepeatedMarks

/-- One facet. -/
theorem facet_payment {A B ν S F L Q δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hν : 0 ≤ ν)
    (hS : 0 ≤ S) (h2SF : 2 * S ≤ F) (hδ : 0 ≤ δ)
    (hSL : S ≤ L + δ) (hFQ : F ≤ Q + 2 * δ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    min (A * S + B * F) (ν * S) ≤ A * L + B * Q + ν * δ := by
  rcases le_total S δ with hSδ | hδS
  · -- δ ≥ S: the term ν δ already pays ν S
    have h1 : ν * S ≤ ν * δ := mul_le_mul_of_nonneg_left hSδ hν
    have h2 : 0 ≤ A * L := mul_nonneg hA hL
    have h3 : 0 ≤ B * Q := mul_nonneg hB hQ
    exact (min_le_right _ _).trans (by linarith)
  · -- δ ≤ S: monotone lower bound, affine in δ, compare with the endpoints δ = 0 and δ = S
    have h1 : A * (S - δ) ≤ A * L := mul_le_mul_of_nonneg_left (by linarith) hA
    have h2 : B * (F - 2 * δ) ≤ B * Q := mul_le_mul_of_nonneg_left (by linarith) hB
    rcases le_total (A + 2 * B) ν with hc | hc
    · -- slope condition holds: the value at δ is at least the value at 0
      have : A * S + B * F ≤ A * (S - δ) + B * (F - 2 * δ) + ν * δ := by nlinarith
      exact (min_le_left _ _).trans (by linarith)
    · -- value at δ is at least the value at S, which is B (F - 2 S) + ν S ≥ ν S
      have hval : B * (F - 2 * S) + ν * S ≤ A * (S - δ) + B * (F - 2 * δ) + ν * δ := by
        nlinarith
      have hB2 : 0 ≤ B * (F - 2 * S) := mul_nonneg hB (by linarith)
      exact (min_le_right _ _).trans (by linarith)

/-- Lemma C for an arbitrary family of facets. -/
theorem lemmaC {ι : Type*} (A B : ι → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {ν S F L Q δ GSF GLQ : ℝ} (hν : 0 ≤ ν)
    (hS : 0 ≤ S) (h2SF : 2 * S ≤ F) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ)
    (hSL : S ≤ L + δ) (hFQ : F ≤ Q + 2 * δ)
    (hGle : ∀ j, GSF ≤ A j * S + B j * F) (hGcap : GSF ≤ ν * S)
    (hGinf : ∀ ε > 0, ∃ j, A j * L + B j * Q ≤ GLQ + ε) :
    GSF ≤ GLQ + ν * δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hGinf ((GSF - (GLQ + ν * δ)) / 2) (by linarith)
  have hf := facet_payment (hA j) (hB j) hν hS h2SF hδ hSL hFQ hL hQ
  have hmin : GSF ≤ min (A j * S + B j * F) (ν * S) := le_min (hGle j) hGcap
  linarith

end RepeatedMarks
