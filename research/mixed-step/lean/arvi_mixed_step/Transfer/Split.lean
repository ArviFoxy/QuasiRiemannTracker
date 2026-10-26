/- Mixed source step, L2 transfer: new in this submission; uses Collet's and the baseline's definitions by import.

The residual input and the tuple split.
The selected block `J` of marked slots is removed from Collet's `Input`; the
original tuple box is the product of the selected box and the residual box. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstData
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Projector

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open Record1252270103Source.Collision
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual input: the same data with the selected slots `J` removed.
The ordinary pair, both plains, the radial data and the volume parameters
`X₁,X₂,Y₁,Y₂` are unchanged; only the marked slots shrink. -/
def residualInput (s : Input ι) (J : Finset ι) : Input {i // i ∉ J} where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i => s.slots i.val
  prime := fun i I hI => s.prime i.val I hI
  ν := fun i => s.ν i.val
  W := fun i => s.W i.val
  lo := fun i => s.lo i.val
  hi := fun i => s.hi i.val
  P := fun i => s.P i.val
  lo_pos := fun i => s.lo_pos i.val
  P_pos := fun i => s.P_pos i.val
  support := fun i => s.support i.val
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i => s.M i.val
  M_ge_one := fun i => s.M_ge_one i.val
  coefficient_bound := fun i I hI => s.coefficient_bound i.val I hI
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i => s.ν_bound i.val
  W_bound := fun i => s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i => s.lower_le i.val
  upper_ge := fun i => s.upper_ge i.val

section ResidualFields
variable (s : Input ι) (J : Finset ι)
@[simp] theorem residualInput_W₁ : (residualInput s J).W₁ = s.W₁ := rfl
@[simp] theorem residualInput_W₂ : (residualInput s J).W₂ = s.W₂ := rfl
@[simp] theorem residualInput_X₁ : (residualInput s J).X₁ = s.X₁ := rfl
@[simp] theorem residualInput_X₂ : (residualInput s J).X₂ = s.X₂ := rfl
@[simp] theorem residualInput_Y₁ : (residualInput s J).Y₁ = s.Y₁ := rfl
@[simp] theorem residualInput_Y₂ : (residualInput s J).Y₂ = s.Y₂ := rfl
@[simp] theorem residualInput_slots (i : {i // i ∉ J}) :
    (residualInput s J).slots i = s.slots i.val := rfl
@[simp] theorem residualInput_ν (i : {i // i ∉ J}) : (residualInput s J).ν i = s.ν i.val := rfl
@[simp] theorem residualInput_W (i : {i // i ∉ J}) : (residualInput s J).W i = s.W i.val := rfl
@[simp] theorem residualInput_P (i : {i // i ∉ J}) : (residualInput s J).P i = s.P i.val := rfl
@[simp] theorem residualInput_hi (i : {i // i ∉ J}) : (residualInput s J).hi i = s.hi i.val := rfl
@[simp] theorem residualInput_M (i : {i // i ∉ J}) : (residualInput s J).M i = s.M i.val := rfl
@[simp] theorem residualInput_plain₁ : (residualInput s J).plain₁ = s.plain₁ := rfl
@[simp] theorem residualInput_plain₂ : (residualInput s J).plain₂ = s.plain₂ := rfl
end ResidualFields

/-- The residual volume is the original volume divided by the selected lengths. -/
theorem residual_volume (s : Input ι) (J : Finset ι) :
    (residualInput s J).X₁ * (residualInput s J).X₂ * ∏ i, (residualInput s J).P i =
      (s.X₁ * s.X₂ * ∏ i, s.P i) / ∏ j ∈ J, s.P j := by
  have hJ : (0:ℝ) < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hsplit : (∏ i, s.P i) = (∏ j ∈ J, s.P j) * ∏ i : {i // i ∉ J}, s.P i.val := by
    rw [← Finset.prod_mul_prod_compl J]
    congr 1
    exact (Finset.prod_subtype Jᶜ (fun i => by simp) (fun i => s.P i)).trans rfl
  rw [hsplit, eq_div_iff hJ.ne']
  change s.X₁ * s.X₂ * (∏ i : {i // i ∉ J}, s.P i.val) * _ = _
  ring

/-- Selected part of an original tuple. -/
def selPart (J : Finset ι) (v : Tuple ι) : J → Ideal O := fun j => v (Sum.inl j.val)

/-- Residual part of an original tuple: the unselected marked slots and the
ordinary pair. -/
def restPart (J : Finset ι) (v : Tuple ι) : Tuple {i // i ∉ J} :=
  Sum.elim (fun i => v (Sum.inl i.val)) (fun k => v (Sum.inr k))

/-- Reassembling an original tuple from its selected and residual parts. -/
def joinTuple (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) : Tuple ι :=
  Sum.elim (fun i => if h : i ∈ J then u ⟨i, h⟩ else w (Sum.inl ⟨i, h⟩))
    (fun k => w (Sum.inr k))

/-- The selected product `D`. -/
def selProduct (J : Finset ι) (u : J → Ideal O) : Ideal O := ∏ j, u j

/-- The selected box: one prime from each selected slot pool. -/
def selBox (s : Input ι) (J : Finset ι) : Finset (J → Ideal O) :=
  Fintype.piFinset (fun j : J => s.slots j.val)

@[simp] theorem joinTuple_inr (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (k : Fin 2) : joinTuple J u w (Sum.inr k) = w (Sum.inr k) := rfl

theorem joinTuple_inl_mem (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (j : ι) (h : j ∈ J) : joinTuple J u w (Sum.inl j) = u ⟨j, h⟩ := by
  simp only [joinTuple, Sum.elim_inl, h, dite_true]

theorem joinTuple_inl_not_mem (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (i : ι) (h : i ∉ J) : joinTuple J u w (Sum.inl i) = w (Sum.inl ⟨i, h⟩) := by
  simp only [joinTuple, Sum.elim_inl, h, dite_false]

theorem selPart_join (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) :
    selPart J (joinTuple J u w) = u := by
  funext j
  exact joinTuple_inl_mem J u w j.val j.property

theorem restPart_join (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) :
    restPart J (joinTuple J u w) = w := by
  funext x
  cases x with
  | inl i => exact joinTuple_inl_not_mem J u w i.val i.property
  | inr k => rfl

theorem join_parts (J : Finset ι) (v : Tuple ι) :
    joinTuple J (selPart J v) (restPart J v) = v := by
  funext x
  cases x with
  | inl i =>
    by_cases h : i ∈ J
    · rw [joinTuple_inl_mem J _ _ i h]; rfl
    · rw [joinTuple_inl_not_mem J _ _ i h]; rfl
  | inr k => rfl

/-- Products over the marked index set split along `J`. -/
theorem prod_split {M : Type*} [CommMonoid M] (J : Finset ι) (g : ι → M) :
    ∏ i, g i = (∏ j : J, g j.val) * ∏ i : {i // i ∉ J}, g i.val := by
  rw [← Finset.prod_mul_prod_compl J, Finset.prod_coe_sort J g]
  congr 1
  exact Finset.prod_subtype Jᶜ (fun i => by simp) g

theorem join_marked_prod {M : Type*} [CommMonoid M] (J : Finset ι) (u : J → Ideal O)
    (w : Tuple {i // i ∉ J}) (g : ι → Ideal O → M) :
    ∏ i, g i (joinTuple J u w (Sum.inl i)) =
      (∏ j : J, g j.val (u j)) * ∏ i : {i // i ∉ J}, g i.val (w (Sum.inl i)) := by
  rw [prod_split J]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [joinTuple_inl_mem J u w j.val j.property]
  · apply Finset.prod_congr rfl
    intro i _
    rw [joinTuple_inl_not_mem J u w i.val i.property]

theorem markedProduct_join (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) :
    markedProduct (joinTuple J u w) = selProduct J u * markedProduct w := by
  unfold markedProduct selProduct
  exact join_marked_prod J u w (fun _ I => I)

theorem finiteTupleProduct_split {κ : Type*} [Fintype κ] (v : Tuple κ) :
    finiteTupleProduct v = markedProduct v * (v (Sum.inr 0) * v (Sum.inr 1)) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two, markedProduct]

theorem finiteTupleProduct_join (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) :
    finiteTupleProduct (joinTuple J u w) = selProduct J u * finiteTupleProduct w := by
  rw [finiteTupleProduct_split, finiteTupleProduct_split, markedProduct_join]
  simp only [joinTuple_inr]
  ring

theorem sel_prod_join (J : Finset ι) (u : J → Ideal O) (w : Tuple {i // i ∉ J}) :
    ∏ j ∈ J, joinTuple J u w (Sum.inl j) = selProduct J u := by
  rw [← Finset.prod_coe_sort J]
  apply Finset.prod_congr rfl
  intro j _
  exact joinTuple_inl_mem J u w j.val j.property

theorem mem_pools_iff (s : Input ι) (v : Tuple ι) :
    (∀ x, v x ∈ s.pools x) ↔
      (∀ i, v (Sum.inl i) ∈ s.slots i) ∧ v (Sum.inr 0) ∈ s.plain₁ ∧ v (Sum.inr 1) ∈ s.plain₂ := by
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i), h (Sum.inr 0), h (Sum.inr 1)⟩
  · rintro ⟨h₁, h₂, h₃⟩ x
    cases x with
    | inl i => exact h₁ i
    | inr k =>
      fin_cases k
      · exact h₂
      · exact h₃

/-- The original box is the product of the selected box and the residual box. -/
theorem box_sum {M : Type*} [AddCommMonoid M] (s : Input ι) (J : Finset ι) (f : Tuple ι → M) :
    ∑ v ∈ Fintype.piFinset s.pools, f v =
      ∑ u ∈ selBox s J, ∑ w ∈ Fintype.piFinset (residualInput s J).pools,
        f (joinTuple J u w) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun v => (selPart J v, restPart J v)) (fun p => joinTuple J p.1 p.2)
  · intro v hv
    have hv' := (mem_pools_iff s v).mp (Fintype.mem_piFinset.mp hv)
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (fun j => hv'.1 j.val), ?_⟩
    apply Fintype.mem_piFinset.mpr
    apply (mem_pools_iff (residualInput s J) _).mpr
    exact ⟨fun i => hv'.1 i.val, hv'.2.1, hv'.2.2⟩
  · intro p hp
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hp
    have hu' := Fintype.mem_piFinset.mp hu
    have hw' := (mem_pools_iff (residualInput s J) _).mp (Fintype.mem_piFinset.mp hw)
    apply Fintype.mem_piFinset.mpr
    apply (mem_pools_iff s _).mpr
    refine ⟨?_, hw'.2.1, hw'.2.2⟩
    intro i
    by_cases h : i ∈ J
    · rw [joinTuple_inl_mem J _ _ i h]; exact hu' ⟨i, h⟩
    · rw [joinTuple_inl_not_mem J _ _ i h]; exact hw'.1 ⟨i, h⟩
  · intro v _
    exact join_parts J v
  · intro p _
    simp only [selPart_join, restPart_join]
  · intro v _
    rw [join_parts J v]

end
end QRH.MixedStep.Transfer
