/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M (a): the selected residual of a live source, WITHOUT supplier freezing (f = 1).

For a source `s` with trivial frozen allocation (`s.B = 1`, e.g. FP's `liveSource`) and a
set `J` of selected slots, `restSource s J` is the same canonical source on the remaining
slots `{i // i ∉ J}` (same pools, characters, profiles, ordinary pair, puncture and `R`; the
first artificial divisor is NOT frozen: it stays the seed mask). Each column tuple of `s`
splits uniquely as (selected assignment `y`, residual tuple `r`) (`sum_tuples_split`), and
(`originalTuple_join`)
  `originalTuple s u (y ⊔ r) = [y injective] · sel(y) · [(D_y, R) = 1] · [(D_y, ∏ r) = 1]
      · [u ∣ D_y ∏ r] · originalTuple (restSource s J) 1 r`,
`D_y = ∏_j y_j`. With `(D_y, ∏ r) = 1` and `u` squarefree, `u ∣ D_y ∏ r ↔ u_n ∣ ∏ r` for
`u_n = ∏_{P ∣ u, P ∤ D_y} P` (`seed_split`). -/
import Submissions.density_split_third_20261026.CubeFree.FP.MixedFirstLiveSource
import Submissions.density_split_third_20261026.CubeFree.Second.FirstDivisor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedOriginalSecondZero
open MixedTupleRows MixedFirstLiveSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The remaining slots. -/
abbrev Rest (J : Finset ι) := {i : ι // i ∉ J}

/-- **The residual source** on the unselected slots (no freezing, `R` unchanged). -/
def restSource (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) : Source (Rest J) a b where
  S := s.S
  H := s.H
  pool := fun j => s.pool j.val
  d := s.d
  hd := s.hd
  B := fun _ => 1
  hB := fun _ => one_ne_zero
  G := 1
  R := s.R
  Fhole := s.Fhole
  hprod := by simp only [finiteTupleProduct, Finset.prod_const_one]
  hR := s.hR
  hFhole := s.hFhole
  ν := fun j => s.ν j.val
  Wslot := fun j => s.Wslot j.val
  P := fun j => s.P j.val
  M := fun j => s.M j.val
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  U₁ := s.U₁
  U₂ := s.U₂
  T := s.T
  L := s.L
  hL := s.hL
  hX₁ := s.hX₁
  hX₂ := s.hX₂
  hY₁ := s.hY₁
  hY₂ := s.hY₂
  hXU₁ := s.hXU₁
  hXU₂ := s.hXU₂
  hYU₁ := s.hYU₁
  hYU₂ := s.hYU₂
  hpX := s.hpX
  hpY := s.hpY
  hP := fun j => s.hP j.val
  hM := fun j => s.hM j.val
  hpool := fun j => s.hpool j.val
  hp := fun j => s.hp j.val
  hpn := fun j => s.hpn j.val
  hν := fun j => s.hν j.val
  hWnorm := fun j => s.hWnorm j.val
  hW := fun j => s.hW j.val
  hS := s.hS
  hH := s.hH
  henclose := by
    intro I hI hi
    apply s.henclose I hI
    simpa only [hB1, mul_one] using hi

/-! ### Splitting a tuple -/

/-- Join a selected assignment and a residual tuple. -/
def joinTuple (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) : Tuple ι :=
  Sum.elim (fun i => if h : i ∈ J then y ⟨i, h⟩ else r (Sum.inl ⟨i, h⟩)) (fun e => r (Sum.inr e))

def selPart (J : Finset ι) (v : Tuple ι) : J → Id := fun j => v (Sum.inl j.val)

def restPart (J : Finset ι) (v : Tuple ι) : Tuple (Rest J) :=
  Sum.elim (fun j => v (Sum.inl j.val)) (fun e => v (Sum.inr e))

theorem join_sel_rest (J : Finset ι) (v : Tuple ι) : joinTuple J (selPart J v) (restPart J v) = v := by
  funext k
  rcases k with i | e
  · by_cases h : i ∈ J <;> simp [joinTuple, selPart, restPart, h]
  · rfl

theorem sel_join (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    selPart J (joinTuple J y r) = y := by
  funext j
  simp [selPart, joinTuple, j.property]

theorem rest_join (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    restPart J (joinTuple J y r) = r := by
  funext k
  rcases k with j | e
  · simp [restPart, joinTuple, j.property]
  · rfl

/-- `∏_{i} f i = (∏_{j ∈ J} f j) · ∏_{i ∉ J} f i` over subtypes. -/
theorem prod_split_subtype {M : Type*} [CommMonoid M] (J : Finset ι) (f : ι → M) :
    (∏ i, f i) = (∏ j : J, f j.val) * ∏ j : Rest J, f j.val := by
  rw [← Finset.prod_mul_prod_compl J f]
  congr 1
  · exact (Finset.prod_coe_sort J f).symm
  · rw [← Finset.prod_subtype (Jᶜ) (fun i => by simp) f]

theorem slotProduct_join (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    slotProduct (joinTuple J y r) = (∏ j, y j) * slotProduct r := by
  unfold slotProduct
  rw [prod_split_subtype J]
  congr 1
  · exact Finset.prod_congr rfl (fun j _ => by simp [joinTuple, j.property])
  · exact Finset.prod_congr rfl (fun j _ => by simp [joinTuple, j.property])

theorem finiteTupleProduct_split (v : Tuple ι) :
    finiteTupleProduct v = slotProduct v * (v (Sum.inr 0) * v (Sum.inr 1)) := by
  unfold finiteTupleProduct slotProduct
  rw [Fintype.prod_sum_type, Fin.prod_univ_two]

theorem finiteTupleProduct_join (J : Finset ι) (y : J → Id) (r : Tuple (Rest J)) :
    finiteTupleProduct (joinTuple J y r) = (∏ j, y j) * finiteTupleProduct r := by
  rw [finiteTupleProduct_split, finiteTupleProduct_split, slotProduct_join]
  simp only [joinTuple, Sum.elim_inr]
  ring

theorem tp_inl (s : Source ι a b) (i : ι) : tuplePools s (Sum.inl i) = s.pool i := rfl

theorem tp_rest_inl (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (j : Rest J) :
    tuplePools (restSource s hB1 J) (Sum.inl j) = s.pool j.val := rfl

theorem tp_rest_inr (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (e : Fin 2) :
    tuplePools (restSource s hB1 J) (Sum.inr e) = tuplePools s (Sum.inr e) := rfl

/-- **The tuple split.** -/
theorem sum_tuples_split {M : Type*} [AddCommMonoid M] (s : Source ι a b) (hB1 : ∀ k, s.B k = 1)
    (J : Finset ι) (F : Tuple ι → M) :
    (∑ v ∈ Fintype.piFinset (tuplePools s), F v) =
      ∑ y ∈ Fintype.piFinset (fun j : J => s.pool j.val),
        ∑ r ∈ Fintype.piFinset (tuplePools (restSource s hB1 J)), F (joinTuple J y r) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => joinTuple J p.1 p.2) (fun v => (selPart J v, restPart J v))
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    rw [Fintype.mem_piFinset] at h1 h2 ⊢
    intro k
    rcases k with i | e
    · by_cases h : i ∈ J
      · have := h1 ⟨i, h⟩
        simpa [joinTuple, h, tp_inl] using this
      · have := h2 (Sum.inl ⟨i, h⟩)
        simp only [joinTuple, Sum.elim_inl, dif_neg h]
        exact this
    · have := h2 (Sum.inr e)
      simpa [joinTuple, tp_rest_inr] using this
  · intro v hv
    rw [Fintype.mem_piFinset] at hv
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
    refine ⟨fun j => by simpa [selPart, tp_inl] using hv (Sum.inl j.val), fun k => ?_⟩
    rcases k with j | e
    · exact hv (Sum.inl j.val)
    · simpa [restPart, tp_rest_inr] using hv (Sum.inr e)
  · intro p _
    simp only [sel_join, rest_join]
  · intro v _
    exact join_sel_rest J v
  · intro p _
    rfl

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
