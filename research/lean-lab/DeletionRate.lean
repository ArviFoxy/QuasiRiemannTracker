/-
Why a short factor that is not one of the two reflected plains costs `6κ` in the plain fourth
moment (research/mixed-slots/README.md; 7/8 paper Lemma 18.1, eqs. 18.38–18.39).

In the positive-slot induction a child exceeds its affine budget by at most `F ≤ 6A`, where
`A = w + ℓ` is the allowance of the amplified Gauss-row norm. The only exit for a factor that cannot
be reflected is pointwise deletion. Deleting length `d` releases `c·d` of affine room and costs
`κ·d` of squared energy. Clearing the excess `F` therefore costs `κF/c`, and the induction closes
iff this never exceeds the allowance `A`.
* `closes_iff`: for `A > 0` and `κ > 0`, the induction closes for every admissible excess iff `c ≥ 6κ`.
* `plain_cost_one_fails`: pricing a third plain factor at cost `c = 1` (no reflection, no slot
  weight) fails whenever `κ > 1/6`. In the application `κ = 2β* − 1 ≥ 3/4`.
So a squarefree-plain slot, which has the same pointwise bound as a prime slot, gets the same
cost `6κ` (improved by the source chain to `Λ`). Two independently saturable slot groups at equal
cost are then never better than one (`mixed_never_better`, a max-over-a-product inequality).
Status: proved.
-/
import Mathlib

namespace DeletionRate

/-- The energy spent to clear an excess `F` at release rate `c` (room per unit of deleted length)
and energy rate `κ`. -/
noncomputable def cost (κ c F : ℝ) : ℝ := κ * F / c

/-- The induction closes when every admissible excess `0 ≤ F ≤ 6A` is cleared within the
allowance `A`. -/
def Closes (κ c A : ℝ) : Prop := ∀ F : ℝ, 0 ≤ F → F ≤ 6 * A → cost κ c F ≤ A

theorem closes_iff {κ c A : ℝ} (hA : 0 < A) (hκ : 0 < κ) (hc : 0 < c) :
    Closes κ c A ↔ 6 * κ ≤ c := by
  constructor
  · intro h
    have h6 := h (6 * A) (by linarith) le_rfl
    unfold cost at h6
    rw [div_le_iff₀ hc] at h6
    nlinarith
  · intro h F hF0 hF
    unfold cost
    rw [div_le_iff₀ hc]
    nlinarith

/-- Cost one fails as soon as `κ > 1/6`. -/
theorem plain_cost_one_fails {κ A : ℝ} (hA : 0 < A) (hκ : 1 / 6 < κ) : ¬ Closes κ 1 A := by
  intro h
  have := (closes_iff hA (by linarith) one_pos).1 h
  linarith

/-- Splitting a resource into two independently saturable groups never lowers the adversary's
maximum: the maximum over the product of choices dominates the maximum over the diagonal. -/
theorem mixed_never_better {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ι → ℝ) :
    s.sup' hs (fun p => f p p) ≤ (s ×ˢ s).sup' (hs.product hs) (fun pq => f pq.1 pq.2) := by
  apply Finset.sup'_le
  intro p hp
  have hpp : (p, p) ∈ s ×ˢ s := Finset.mem_product.2 ⟨hp, hp⟩
  exact Finset.le_sup' (fun pq : ι × ι => f pq.1 pq.2) hpp

end DeletionRate
