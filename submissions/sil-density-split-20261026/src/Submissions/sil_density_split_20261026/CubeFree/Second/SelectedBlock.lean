/- Copyright (c) 2026 Sil. Apache-2.0.
The selected marked block D of the second step, without supplier freezing (CF Section 4).
Adapted from the selected-assignment part of Candidate.FourthPower.MixedSupplierFourthRow.Data
and Candidate.FourthPower.MixedSupplierPositive (PR76, Copyright (c) 2026 Sil. Apache-2.0).
Modified by Sil (2026-10-26): the record keeps only the slot pools, the selected slot
amplitudes, the slot scales and the live/selected index sets; the first artificial divisor
`u`, the frozen supplier product and every residual-column field of the FP supplier record
are dropped (FP's u-freezing lane is not ported, design risk 1). The selected products, their
fibres and grouped weights, and the annular norm bound are verbatim.

In the cube-free skeleton the block is chosen by `Second.Selection` on the live slots of a
genuine first allocation (the only frozen slots are those of the genuine first common
factor), so `L` is the live set and `J ⊆ L` the selected block; `D = ∏_{j∈J} y_j` runs over
the products of injective supported selected assignments. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree.Second.SelectedBlock
noncomputable section
open scoped Classical BigOperators
open OAI OAI.CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The selected block: slot pools, selected slot amplitudes, slot scales, live set `L` and
selected block `J` of live slots. -/
structure SelectedBlock (α : Type*) [Fintype α] where
  pool : α → Finset Id
  prime : ∀ i, ∀ I ∈ pool i, Prime I
  amp : α → Id → ℂ
  P : α → ℝ
  L : Finset α
  J : Finset {i // i ∉ Lᶜ}

variable {α : Type*} [Fintype α]

/-- The common alphabet: the union of the actual pools. -/
def markedUniverse (pool : α → Finset Id) : Finset Id := Finset.univ.biUnion pool

abbrev Alphabet (q : SelectedBlock α) := markedUniverse q.pool
abbrev Selected (q : SelectedBlock α) := q.J → Alphabet q

/-- Slot amplitude, zero outside the slot's own pool. -/
def amplitude (q : SelectedBlock α) (i : α) (I : Alphabet q) : ℂ :=
  if I.val ∈ q.pool i then q.amp i I.val else 0

def selectedProduct (q : SelectedBlock α) (y : Selected q) : Id := ∏ j, (y j).val
def selectedWeight (q : SelectedBlock α) (y : Selected q) : ℂ :=
  ∏ j, amplitude q j.val.val (y j)

/-- Injective selected assignments with nonzero weight. -/
def activeSelected (q : SelectedBlock α) : Finset (Selected q) :=
  Finset.univ.filter (fun y => Function.Injective y ∧ selectedWeight q y ≠ 0)

theorem active_selected_mem (q : SelectedBlock α) (y : Selected q)
    (hy : y ∈ activeSelected q) (j : q.J) : (y j).val ∈ q.pool j.val.val := by
  have hw := (Finset.mem_filter.mp hy).2.2
  have hj := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  by_contra hn
  exact hj (by simp only [amplitude, if_neg hn])

theorem selected_product_upper (q : SelectedBlock α) (y : Selected q)
    (hy : y ∈ activeSelected q) (hi : α → ℝ)
    (hpool : ∀ i, ∀ I ∈ q.pool i, (Ideal.absNorm I : ℝ) ≤ hi i) :
    (Ideal.absNorm (selectedProduct q y) : ℝ) ≤ ∏ j : q.J, hi j.val.val := by
  simp only [selectedProduct, map_prod, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
    (fun j _ => hpool j.val.val (y j).val (active_selected_mem q y hy j))

theorem selected_product_annular_upper (q : SelectedBlock α) (y : Selected q)
    (hy : y ∈ activeSelected q)
    (hpool : ∀ i, ∀ I ∈ q.pool i, (Ideal.absNorm I : ℝ) ≤ 2*q.P i) :
    (Ideal.absNorm (selectedProduct q y) : ℝ) ≤
      2^(Fintype.card q.J) * ∏ j : q.J, q.P j.val.val := by
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using
    selected_product_upper q y hy (fun i => 2*q.P i) hpool

/-- Active assignments with a supported product. -/
def supportedSelected (q : SelectedBlock α) : Finset (Selected q) :=
  (activeSelected q).filter (fun y => Supported (selectedProduct q y))

/-- The selected products `D`. -/
def selectedProducts (q : SelectedBlock α) : Finset Id :=
  (supportedSelected q).image (selectedProduct q)

def selectedFiber (q : SelectedBlock α) (D : Id) : Finset (Selected q) :=
  (supportedSelected q).filter (fun y => selectedProduct q y = D)

/-- The positive weight of a selected product, from the original amplitudes. -/
def groupedWeight (q : SelectedBlock α) (D : Id) : ℝ :=
  ∑ y ∈ selectedFiber q D, ‖selectedWeight q y‖^2

theorem selected_products_supported (q : SelectedBlock α) (D : Id)
    (hD : D ∈ selectedProducts q) : Supported D := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hD
  exact (Finset.mem_filter.mp hy).2

theorem grouped_weight_nonneg (q : SelectedBlock α) (D : Id) : 0 ≤ groupedWeight q D :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Grouping the selected assignments by their product `D`. -/
theorem selected_grouping (q : SelectedBlock α) (F : Id → ℝ) :
    (∑ y ∈ supportedSelected q, ‖selectedWeight q y‖^2 * F (selectedProduct q y)) =
      ∑ D ∈ selectedProducts q, groupedWeight q D * F D := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun y hy => Finset.mem_image.mpr ⟨y, hy, rfl⟩ :
      ∀ y ∈ supportedSelected q, selectedProduct q y ∈ selectedProducts q)]
  apply Finset.sum_congr rfl
  intro D _
  rw [groupedWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [(Finset.mem_filter.mp hy).2]

/-- Every selected product is at most the padded selected scale. -/
theorem selectedProducts_norm_le (q : SelectedBlock α)
    (hpool : ∀ i, ∀ I ∈ q.pool i, (Ideal.absNorm I : ℝ) ≤ 2*q.P i)
    (D : Id) (hD : D ∈ selectedProducts q) :
    (Ideal.absNorm D : ℝ) ≤ 2^(Fintype.card q.J) * ∏ j : q.J, q.P j.val.val := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hD
  exact selected_product_annular_upper q y (Finset.mem_filter.mp hy).1 hpool

end
end QRH.SilDensitySplit.CubeFree.Second.SelectedBlock
