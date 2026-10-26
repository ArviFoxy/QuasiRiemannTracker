/- Mixed source step, N1: new in this submission; uses Collet's and the baseline's
definitions by import.

The restricted input and allocation, and the
identification of the restricted child with the child of the restricted parent.

* `Input.restrict s J` (= `QRH.MixedStep.Transfer.residualInput s J`, a
  pointwise structure literal) removes the slots `J`.
* `allocRestrict B hJ` is the allocation `B` read on the remaining slots (the
  removed slots are live, `B = 1` there).
* `restrictChild_energy`: for every marked modifier, the source energy of
  `residualInput (child s C R B τ t) J'` equals that of
  `child (s.restrict J) C R (allocRestrict B hJ) τ' t`, where `J'` is `J` read
  inside the live slots. This is a reindexing (`SlotMatch`), proved once for
  any equivalence of slot types with matching slot data. -/
import Submissions.arvi_mixed_step.Transfer.Split
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace OAI.SevenEighths.CenteredMomentCommonRadialData

/-- The input with the slots `J` removed (design N1). -/
abbrev Input.restrict {α : Type*} [Fintype α] [DecidableEq α] (s : Input α) (J : Finset α) :
    Input {i // i ∉ J} :=
  QRH.MixedStep.Transfer.residualInput s J

end OAI.SevenEighths.CenteredMomentCommonRadialData

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O

/-- `Fintype.mem_piFinset` for an arbitrary decidable-equality instance. -/
theorem mem_piFinset_any {β : Type*} [Fintype β] {δ : β → Type*} (inst : DecidableEq β)
    (t : ∀ a, Finset (δ a)) (f : ∀ a, δ a) :
    f ∈ @Fintype.piFinset β inst _ δ t ↔ ∀ a, f a ∈ t a :=
  @Fintype.mem_piFinset β inst _ δ t f

/-- `CoupledFirst.coefficient` through the ambient tuple box. -/
theorem coefficient_eq_piFinset {μ : Type*} [Fintype μ] [DecidableEq μ] (s : Input μ)
    (modifier : Tuple μ → ℂ) (R L : Ideal O) :
    CoupledFirst.coefficient s modifier R L =
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (CoupledFirst.tupleCoefficient s modifier R L) := by
  unfold CoupledFirst.coefficient
  congr
  exact Subsingleton.elim _ _

section Restrict
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem volume_restrict (s : Input α) (J : Finset α) :
    volume (s.restrict J) = volume s / ∏ j ∈ J, s.P j :=
  residual_volume s J

theorem live_one {s : Input α} {C : Ideal O} (B : actualAllocations s.pools C) {J : Finset α}
    (hJ : J ⊆ liveIndices B.val) (j : α) (hj : j ∈ J) : B.val (Sum.inl j) = 1 :=
  (Finset.mem_filter.mp (hJ hj)).2

theorem restPart_mem_allocations (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) :
    restPart J B.val ∈ actualAllocations (s.restrict J).pools C := by
  obtain ⟨hlab, hprod⟩ := Finset.mem_filter.mp B.property
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · obtain ⟨v, hv, hvB⟩ := Finset.mem_image.mp hlab
    refine Finset.mem_image.mpr ⟨restPart J v, ?_, ?_⟩
    · have hv' := (mem_pools_iff s v).mp ((mem_piFinset_any _ _ _).mp hv)
      apply (mem_piFinset_any _ _ _).mpr
      apply (mem_pools_iff (s.restrict J) _).mpr
      exact ⟨fun i => hv'.1 i.val, hv'.2.1, hv'.2.2⟩
    · funext x
      cases x with
      | inl i => exact congrFun hvB (Sum.inl i.val)
      | inr k => exact congrFun hvB (Sum.inr k)
  · refine Eq.trans ?_ hprod
    simp only [Fintype.prod_sum_type, restPart, Sum.elim_inl, Sum.elim_inr]
    congr 1
    rw [prod_split J (fun i => B.val (Sum.inl i))]
    have h1 : ∏ j : J, B.val (Sum.inl j.val) = 1 :=
      Finset.prod_eq_one (fun j _ => live_one B hJ j.val j.property)
    rw [h1, one_mul]

/-- The allocation read on the remaining slots (design N1). -/
def allocRestrict (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) : actualAllocations (s.restrict J).pools C :=
  ⟨restPart J B.val, restPart_mem_allocations s C B J hJ⟩

@[simp] theorem allocRestrict_val (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) :
    (allocRestrict s C B J hJ).val = restPart J B.val := rfl

theorem allocRestrict_inr (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (k : Fin 2) :
    (allocRestrict s C B J hJ).val (Sum.inr k) = B.val (Sum.inr k) := rfl

theorem allocRestrict_marked (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) :
    markedProduct (allocRestrict s C B J hJ).val = markedProduct B.val := by
  unfold markedProduct
  rw [prod_split J (fun i => B.val (Sum.inl i))]
  have h1 : ∏ j : J, B.val (Sum.inl j.val) = 1 :=
    Finset.prod_eq_one (fun j _ => live_one B hJ j.val j.property)
  rw [h1, one_mul]
  rfl

/-- The block `J` read inside the live slots of `B`. -/
def liveBlock {C : Ideal O} {s : Input α} (B : actualAllocations s.pools C) (J : Finset α) :
    Finset (liveIndices B.val) :=
  J.subtype (fun i => i ∈ liveIndices B.val)

theorem mem_liveBlock {C : Ideal O} {s : Input α} (B : actualAllocations s.pools C) (J : Finset α)
    (i : liveIndices B.val) : i ∈ liveBlock B J ↔ i.val ∈ J := Finset.mem_subtype

theorem prod_liveBlock {M : Type*} [CommMonoid M] {C : Ideal O} {s : Input α}
    (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val) (f : α → M) :
    ∏ j ∈ liveBlock B J, f j.val = ∏ j ∈ J, f j := by
  unfold liveBlock
  rw [Finset.prod_subtype_eq_prod_filter, Finset.filter_true_of_mem (fun j hj => hJ hj)]

end Restrict

/-! ### Reindexing a source along an equivalence of slot types -/

section Transport
variable {κ κ' : Type*} [Fintype κ] [Fintype κ']

/-- Two inputs whose slot data match along `e` and whose ordinary data agree. -/
structure SlotMatch (e : κ ≃ κ') (s₁ : Input κ) (s₂ : Input κ') : Prop where
  slots : ∀ i, s₂.slots (e i) = s₁.slots i
  ν : ∀ i, s₂.ν (e i) = s₁.ν i
  W : ∀ i, s₂.W (e i) = s₁.W i
  P : ∀ i, s₂.P (e i) = s₁.P i
  plain₁ : s₂.plain₁ = s₁.plain₁
  plain₂ : s₂.plain₂ = s₁.plain₂
  W₁ : s₂.W₁ = s₁.W₁
  W₂ : s₂.W₂ = s₁.W₂
  X₁ : s₂.X₁ = s₁.X₁
  X₂ : s₂.X₂ = s₁.X₂
  Y₁ : s₂.Y₁ = s₁.Y₁
  Y₂ : s₂.Y₂ = s₁.Y₂

/-- Reading a tuple of `κ'` as a tuple of `κ`. -/
def tupleMap (e : κ ≃ κ') (w : Tuple κ') : Tuple κ :=
  Sum.elim (fun i => w (Sum.inl (e i))) (fun k => w (Sum.inr k))

theorem tupleMap_marked (e : κ ≃ κ') (w : Tuple κ') :
    markedProduct (tupleMap e w) = markedProduct w := by
  unfold markedProduct tupleMap
  simp only [Sum.elim_inl]
  exact Equiv.prod_comp e (fun i' => w (Sum.inl i'))

theorem tupleMap_prod (e : κ ≃ κ') (w : Tuple κ') :
    finiteTupleProduct (tupleMap e w) = finiteTupleProduct w := by
  rw [finiteTupleProduct_split, finiteTupleProduct_split, tupleMap_marked]
  rfl

theorem tupleMap_inr (e : κ ≃ κ') (w : Tuple κ') (k : Fin 2) :
    tupleMap e w (Sum.inr k) = w (Sum.inr k) := rfl

theorem tupleMap_tupleCoefficient (e : κ ≃ κ') {s₁ : Input κ} {s₂ : Input κ'}
    (h : SlotMatch e s₁ s₂) (A₁ A₂ D K : Ideal O) (F : Ideal O → ℂ) (R L : Ideal O)
    (w : Tuple κ') :
    CoupledFirst.tupleCoefficient s₁ (markedSourceModifier A₁ A₂ D K F) R L (tupleMap e w) =
      CoupledFirst.tupleCoefficient s₂ (markedSourceModifier A₁ A₂ D K F) R L w := by
  have hmod : markedSourceModifier A₁ A₂ D K F (tupleMap e w) =
      markedSourceModifier A₁ A₂ D K F w := by
    unfold markedSourceModifier sourceModifier coupledFactor
    rw [tupleMap_marked, tupleMap_prod]
    rfl
  have hslot : (∏ i, s₁.ν i (tupleMap e w (Sum.inl i)) *
      s₁.W i ((Ideal.absNorm (tupleMap e w (Sum.inl i)) : ℝ) / s₁.P i)) =
      ∏ i', s₂.ν i' (w (Sum.inl i')) * s₂.W i' ((Ideal.absNorm (w (Sum.inl i')) : ℝ) / s₂.P i') := by
    rw [← Equiv.prod_comp e (fun i' => s₂.ν i' (w (Sum.inl i')) *
      s₂.W i' ((Ideal.absNorm (w (Sum.inl i')) : ℝ) / s₂.P i'))]
    apply Finset.prod_congr rfl
    intro i _
    rw [h.ν i, h.W i, h.P i]
    rfl
  unfold CoupledFirst.tupleCoefficient
  rw [hmod]
  unfold profileCoefficient
  rw [hslot, tupleMap_prod, h.W₁, h.W₂, h.X₁, h.X₂, h.Y₁, h.Y₂]
  rfl

theorem tupleMap_mem (e : κ ≃ κ') {s₁ : Input κ} {s₂ : Input κ'} (h : SlotMatch e s₁ s₂)
    (w : Tuple κ') : (∀ x, tupleMap e w x ∈ s₁.pools x) ↔ (∀ x, w x ∈ s₂.pools x) := by
  rw [mem_pools_iff, mem_pools_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i' => ?_, ?_, ?_⟩
    · have := h1 (e.symm i')
      simp only [tupleMap, Sum.elim_inl, Equiv.apply_symm_apply] at this
      rw [← h.slots, Equiv.apply_symm_apply] at this
      exact this
    · rw [h.plain₁]; exact h2
    · rw [h.plain₂]; exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, ?_, ?_⟩
    · simp only [tupleMap, Sum.elim_inl]
      rw [← h.slots]
      exact h1 (e i)
    · rw [← h.plain₁]; exact h2
    · rw [← h.plain₂]; exact h3

/-- Reindexing sums over the two boxes. -/
theorem box_transport [DecidableEq κ] [DecidableEq κ'] (e : κ ≃ κ') {s₁ : Input κ}
    {s₂ : Input κ'} (h : SlotMatch e s₁ s₂) {M : Type*} [AddCommMonoid M] (f : Tuple κ → M) :
    ∑ v ∈ Fintype.piFinset s₁.pools, f v = ∑ w ∈ Fintype.piFinset s₂.pools, f (tupleMap e w) := by
  symm
  apply Finset.sum_nbij' (tupleMap e) (tupleMap e.symm)
  · intro w hw
    exact Fintype.mem_piFinset.mpr ((tupleMap_mem e h w).mpr (Fintype.mem_piFinset.mp hw))
  · intro v hv
    have hv' := Fintype.mem_piFinset.mp hv
    apply Fintype.mem_piFinset.mpr
    apply (tupleMap_mem e h _).mp
    have he : tupleMap e (tupleMap e.symm v) = v := by
      funext x
      cases x with
      | inl i => simp [tupleMap]
      | inr k => rfl
    rw [he]
    exact hv'
  · intro w _
    funext x
    cases x with
    | inl i => simp [tupleMap]
    | inr k => rfl
  · intro v _
    funext x
    cases x with
    | inl i => simp [tupleMap]
    | inr k => rfl
  · intro w _
    rfl

theorem coefficient_transport [DecidableEq κ] [DecidableEq κ'] (e : κ ≃ κ') {s₁ : Input κ}
    {s₂ : Input κ'} (h : SlotMatch e s₁ s₂) (A₁ A₂ D K : Ideal O) (F : Ideal O → ℂ)
    (R L : Ideal O) :
    CoupledFirst.coefficient s₁ (markedSourceModifier A₁ A₂ D K F) R L =
      CoupledFirst.coefficient s₂ (markedSourceModifier A₁ A₂ D K F) R L := by
  funext I
  rw [coefficient_eq_piFinset s₁, coefficient_eq_piFinset s₂]
  unfold finiteColumnCoefficient
  rw [Finset.sum_filter, Finset.sum_filter, box_transport e h]
  apply Finset.sum_congr rfl
  intro w _
  rw [tupleMap_prod, tupleMap_tupleCoefficient e h]

theorem columns_transport [DecidableEq κ] [DecidableEq κ'] (e : κ ≃ κ') {s₁ : Input κ}
    {s₂ : Input κ'} (h : SlotMatch e s₁ s₂) :
    finiteColumns (Fintype.piFinset s₁.pools) = finiteColumns (Fintype.piFinset s₂.pools) := by
  unfold finiteColumns
  ext I
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' := Fintype.mem_piFinset.mp hv
    refine ⟨tupleMap e.symm v, ?_, ?_⟩
    · have he : tupleMap e (tupleMap e.symm v) = v := by
        funext x
        cases x with
        | inl i => simp [tupleMap]
        | inr k => rfl
      apply Fintype.mem_piFinset.mpr
      apply (tupleMap_mem e h _).mp
      rw [he]
      exact hv'
    · rw [← tupleMap_prod e (tupleMap e.symm v)]
      congr 1
      funext x
      cases x with
      | inl i => simp [tupleMap]
      | inr k => rfl
  · rintro ⟨w, hw, rfl⟩
    exact ⟨tupleMap e w, Fintype.mem_piFinset.mpr ((tupleMap_mem e h w).mpr
      (Fintype.mem_piFinset.mp hw)), tupleMap_prod e w⟩

/-- Source energies with equal column sets and equal coefficients agree. -/
theorem gaussEnergy_columns_congr {S S' : Finset (Ideal O)} (hS : S = S') (c : Ideal O → ℂ)
    (Φ : 𝓢(ℝ, ℂ)) (H : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S => c I) Φ H =
      gaussEnergy Finset.univ (sourceGenerator S') (sourceGenerator_supported S')
        (fun I : supportedColumns S' => c I) Φ H := by
  subst hS
  rfl

/-- **Transport of source energies along a slot equivalence.** -/
theorem energy_transport [DecidableEq κ] [DecidableEq κ'] (e : κ ≃ κ') {s₁ : Input κ}
    {s₂ : Input κ'} (h : SlotMatch e s₁ s₂) (A₁ A₂ D K : Ideal O) (F : Ideal O → ℂ)
    (R L : Ideal O) (Γ : Ideal O → ℂ) (Φ : 𝓢(ℝ, ℂ)) (H : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s₁.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s₁.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s₁.pools)) =>
          CoupledFirst.coefficient s₁ (markedSourceModifier A₁ A₂ D K F) R L I * Γ I) Φ H =
      gaussEnergy Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s₂.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s₂.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s₂.pools)) =>
          CoupledFirst.coefficient s₂ (markedSourceModifier A₁ A₂ D K F) R L I * Γ I) Φ H := by
  rw [coefficient_transport e h A₁ A₂ D K F R L]
  exact gaussEnergy_columns_congr (columns_transport e h)
    (fun I => CoupledFirst.coefficient s₂ (markedSourceModifier A₁ A₂ D K F) R L I * Γ I) Φ H

end Transport

/-! ### The restricted child is the child of the restricted parent -/

section ChildRestrict
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The slot equivalence between the two constructions. -/
def childRestrictEquiv (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) :
    {i : liveIndices B.val // i ∉ liveBlock B J} ≃ liveIndices (allocRestrict s C B J hJ).val where
  toFun i := ⟨⟨i.val.val, fun h => i.property ((mem_liveBlock B J i.val).mpr h)⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp i.val.property).2⟩⟩
  invFun i := ⟨⟨i.val.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp i.property).2⟩⟩,
    fun h => i.val.property ((mem_liveBlock B J _).mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem childRestrict_match (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (τ τ' : HeckeFamily.Character) (t t' : ℝ) :
    SlotMatch (childRestrictEquiv s C B J hJ)
      (residualInput (child s C R B τ t) (liveBlock B J))
      (child (s.restrict J) C R (allocRestrict s C B J hJ) τ' t') where
  slots _ := rfl
  ν _ := rfl
  W _ := rfl
  P _ := rfl
  plain₁ := rfl
  plain₂ := rfl
  W₁ := rfl
  W₂ := rfl
  X₁ := rfl
  X₂ := rfl
  Y₁ := rfl
  Y₂ := rfl

/-- **The restricted child and the child of the restricted parent have the same
source energies**, for every marked modifier, puncture, seed and multiplier. -/
theorem restrictChild_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (J : Finset α) (hJ : J ⊆ liveIndices B.val) (τ τ' : HeckeFamily.Character) (t t' : ℝ)
    (A₁ A₂ D K : Ideal O) (F : Ideal O → ℂ) (R' L : Ideal O) (Γ : Ideal O → ℂ)
    (Φ : 𝓢(ℝ, ℂ)) (H : ℝ) :
    gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns
          (Fintype.piFinset (residualInput (child s C R B τ t) (liveBlock B J)).pools)))
        (sourceGenerator_supported (finiteColumns
          (Fintype.piFinset (residualInput (child s C R B τ t) (liveBlock B J)).pools)))
        (fun I : supportedColumns (finiteColumns
            (Fintype.piFinset (residualInput (child s C R B τ t) (liveBlock B J)).pools)) =>
          CoupledFirst.coefficient (residualInput (child s C R B τ t) (liveBlock B J))
            (markedSourceModifier A₁ A₂ D K F) R' L I * Γ I) Φ H =
      gaussEnergy Finset.univ
        (sourceGenerator (finiteColumns
          (Fintype.piFinset (child (s.restrict J) C R (allocRestrict s C B J hJ) τ' t').pools)))
        (sourceGenerator_supported (finiteColumns
          (Fintype.piFinset (child (s.restrict J) C R (allocRestrict s C B J hJ) τ' t').pools)))
        (fun I : supportedColumns (finiteColumns
            (Fintype.piFinset (child (s.restrict J) C R (allocRestrict s C B J hJ) τ' t').pools)) =>
          CoupledFirst.coefficient (child (s.restrict J) C R (allocRestrict s C B J hJ) τ' t')
            (markedSourceModifier A₁ A₂ D K F) R' L I * Γ I) Φ H :=
  energy_transport (childRestrictEquiv s C B J hJ) (childRestrict_match s C R B J hJ τ τ' t t')
    A₁ A₂ D K F R' L Γ Φ H

end ChildRestrict

end
end QRH.MixedStep.Residual
