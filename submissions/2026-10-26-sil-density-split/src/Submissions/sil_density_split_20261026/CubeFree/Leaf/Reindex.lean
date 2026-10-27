/- Copyright (c) 2026 Sil. Apache-2.0.
Reindexing slot data on a subtype `T` of the ambient slot type `α`.

The packed contract (Seam A) and the parent `InitialAffineAt` give their slot data as
functions on the subtype `↥T` of a `Finset α`.  The FP/OAI deletion and native
estimates take slot data as functions on the whole ambient `α`, with the slot set a
`Finset α` fixed before the constants.  `extend T f d` extends `f : T → β` by the
default `d` off `T`; on `T` it restricts back to `f` (`extend_coe`), and sums over `T`,
over the subtype, and over the whole of `α` (with default `0`) agree. Retained slot sets
are then plain `Finset α`'s `R ⊆ T`, so the parent quantifier `∀ T : Finset α` applies to
`R` directly with the restricted data `fun i : R => extend T f d i`. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree
open scoped BigOperators

section
variable {α β : Type*}

open scoped Classical in
/-- Extension of slot data on `T` to the whole ambient type, by the default `d` off `T`. -/
noncomputable def extend (T : Finset α) (f : T → β) (d : β) : α → β :=
  fun j => if h : j ∈ T then f ⟨j, h⟩ else d

@[simp] theorem extend_coe (T : Finset α) (f : T → β) (d : β) (i : T) :
    extend T f d (i : α) = f i := by
  unfold extend
  simp [i.2]

theorem extend_of_mem (T : Finset α) (f : T → β) (d : β) {j : α} (h : j ∈ T) :
    extend T f d j = f ⟨j, h⟩ := by
  unfold extend
  simp [h]

theorem extend_of_not_mem (T : Finset α) (f : T → β) (d : β) {j : α} (h : j ∉ T) :
    extend T f d j = d := by
  unfold extend
  simp [h]

/-- Restricting the extension back to the subtype gives the original data. -/
theorem extend_restrict (T : Finset α) (f : T → β) (d : β) :
    (fun i : T => extend T f d i) = f := by
  funext i
  exact extend_coe T f d i

/-- A pointwise property on `T` together with the property of the default holds
everywhere for the extension. -/
theorem extend_forall (T : Finset α) (f : T → β) (d : β) (p : β → Prop)
    (hf : ∀ i, p (f i)) (hd : p d) : ∀ j, p (extend T f d j) := by
  intro j
  by_cases h : j ∈ T
  · rw [extend_of_mem T f d h]; exact hf _
  · rw [extend_of_not_mem T f d h]; exact hd

end

section
variable {α M : Type*} [AddCommMonoid M]

/-- The sum over the subtype is the sum over `T` of the extension. -/
theorem sum_extend (T : Finset α) (f : T → M) (d : M) :
    ∑ i ∈ T, extend T f d i = ∑ i : T, f i := by
  rw [← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl (fun i _ => extend_coe T f d i)

/-- With default `0`, the sum over the whole ambient type is the sum over `T`. -/
theorem sum_univ_extend [Fintype α] (T : Finset α) (f : T → M) :
    ∑ i, extend T f 0 i = ∑ i : T, f i := by
  rw [← sum_extend T f 0]
  symm
  apply Finset.sum_subset (Finset.subset_univ T)
  intro j _ hj
  exact extend_of_not_mem T f 0 hj

/-- The sum over a subtype `R` of a function on `α` is its `Finset` sum over `R`. -/
theorem sum_subtype_eq (R : Finset α) (g : α → M) :
    ∑ i : R, g i = ∑ i ∈ R, g i :=
  Finset.sum_coe_sort R g

/-- Splitting the slot width over a retained set `R ⊆ T` and its deleted complement. -/
theorem sum_retained_add_deleted [DecidableEq α] (T R : Finset α) (hR : R ⊆ T) (g : α → M) :
    ∑ i ∈ R, g i + ∑ i ∈ T \ R, g i = ∑ i ∈ T, g i := by
  rw [add_comm]
  exact Finset.sum_sdiff hR

/-- The ambient sum of the indicator of `D` is the sum over `D`. -/
theorem sum_univ_indicator [Fintype α] [DecidableEq α] (D : Finset α) (g : α → M) :
    ∑ i, (if i ∈ D then g i else 0) = ∑ i ∈ D, g i := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end

end QRH.SilDensitySplit.CubeFree
