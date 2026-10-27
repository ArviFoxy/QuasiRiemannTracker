/- Copyright (c) 2026 Sil. Apache-2.0.
Row-level adapter of the density-split leaf (DS §§3–4).

The packed canonical energy is, after `Packet.packed_energy_le`, the energy of the natural
state `packedState` (`CubeFree/Leaf/Native`). Its rows are literally the suppliers' rows:
`positiveSlotRow`/`retainedPositiveRow` of `NaturalState.character`, `NaturalState.mask`,
with slots `normalizedSlot … primePool rayM H 2 (Z^w)`. This file provides
* the LOW/HIGH split of the energy by a row predicate (`energy_split`), monotonicity in
  the keep predicate (`energy_mono_keep`), and a finite class bound
  (`energy_le_classes`: pointwise row bound times row count, summed over finitely many
  classes, with the profile weight bounded by `diagonalControl`);
* the restricted state (`restrictState`) carrying the LOW keep predicate;
* the q-free buffered selector at base height `T₀`: the LOW predicate `lowRow` (some
  `RetainedZeroBin` lies strictly below the cut `(q+1)/2`, PR69
  `RegularRetainedNaturalBins`) and the chosen bin `selectBin` (`actual_retained_zero_partition`);
* the height bookkeeping `binIndex` (`3(p+1)·((h+1)Z^τ) = 3(binIndex p h + 1)Z^τ`). -/
import Submissions.density_split_third_20261026.CubeFree.Leaf.Native
import Submissions.density_split_third_20261026.CubeFree.Leaf.PartialDeletion
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularRetainedNaturalBins

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.DensitySplitThird.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion
open LocalMoment
local notation "O" => HeckeFamily.O

/-! ### The unit puncture in a slot -/

theorem slot_unit_mask {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) :
    normalizedSlot η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z pool β t P =
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  simp only [normalizedSlot, rowSlot, one_mul, natural_unit_mask_coefficient F]

/-! ### The profile weight -/

theorem profile_re_le_diag (Φ : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (Φ x).re ≤ QuadraticInitialBound.diagonalControl Φ := by
  have h1 : (Φ x).re ≤ ‖Φ x‖ := Complex.re_le_norm _
  have h0 : ((0:ℕ),(0:ℕ)) ∈ Finset.Iic ((2:ℕ),(0:ℕ)) := by simp
  have h2 : ‖Φ x‖ ≤ (Finset.Iic ((2:ℕ),(0:ℕ))).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ :=
    (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) h0)
  have h4 : 0 ≤ (Finset.Iic ((2:ℕ),(0:ℕ))).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ :=
    apply_nonneg _ _
  have hk : (1:ℝ) ≤ 16 * (1 + Real.pi) ^ 2 := by nlinarith [Real.pi_pos]
  unfold QuadraticInitialBound.diagonalControl
  calc (Φ x).re ≤ (Finset.Iic ((2:ℕ),(0:ℕ))).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ :=
        h1.trans h2
    _ ≤ _ := le_mul_of_one_le_left h4 hk

/-! ### Splitting and bounding the energy by row predicates -/

section Energy
variable {ι : Type*} [Fintype ι]

theorem energy_split (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep L : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      energy η m A t W₁ W₂ S β P X₁ X₂ (fun z => keep z ∧ L z) Φ K +
      energy η m A t W₁ W₂ S β P X₁ X₂ (fun z => keep z ∧ ¬ L z) Φ K := by
  unfold energy
  rw [← (compact_radial_summable _ _ Φ K b hK hs).tsum_add
    (compact_radial_summable _ _ Φ K b hK hs)]
  apply tsum_congr
  intro z
  by_cases hk : keep z <;> by_cases hl : L z <;> simp [hk, hl]

theorem energy_mono_keep (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep keep' : O → Prop) (hkk : ∀ z, keep' z → keep z) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep' Φ K ≤
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply (compact_radial_summable _ keep' Φ K b hK hs).tsum_le_tsum _
    (compact_radial_summable _ keep Φ K b hK hs)
  intro z
  by_cases hk' : keep' z
  · simp only [hk', hkk z hk', ite_true, le_refl]
  · simp only [hk', ite_false]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ z)
    · exact le_rfl

theorem energy_nonneg (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    0 ≤ energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hΦ z)
  · exact le_rfl

/-- **Finite class bound.** If every kept row of nonzero weight in class `c` has
`‖row‖² ≤ R c`, and every finite set of such rows of class `c` has at most `N c` elements,
then the energy is at most `diagonalControl Φ · ∑_c R c · N c`. -/
theorem energy_le_classes {κ : Type*} [Fintype κ] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b)
    (cls : O → κ) (R N : κ → ℝ) (hR : ∀ c, 0 ≤ R c)
    (hrow : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 →
      ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤ R (cls z))
    (hcount : ∀ c, ∀ rows : Finset O,
      (∀ z ∈ rows, keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0 ∧ cls z = c) →
        (rows.card : ℝ) ≤ N c) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * ∑ c, R c * N c := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (b*K)
  set B := ShortDraftLatticeCount.rowNormBall N₀
  let f : O → ℝ := fun z => if keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hout : ∀ z, Φ (‖eisEmbedding z‖^2/K) ≠ 0 → z ∈ B := by
    intro z hn
    have hh : ‖eisEmbedding z‖^2 ≤ (N₀:ℝ) := ((div_le_iff₀ hK).mp (hs hn)).trans hN₀
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast (show ((Ideal.span {z}).absNorm:ℝ) ≤ N₀ by
      rwa [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span])
  let G : Finset O := B.filter (fun z => keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0)
  have hzero : ∀ z ∉ G, f z = 0 := by
    intro z hz
    dsimp only [f]
    by_cases hk : keep z
    · by_cases hp : Φ (‖eisEmbedding z‖^2/K) = 0
      · simp [hk, hp]
      · exact absurd (Finset.mem_filter.mpr ⟨hout z hp, hk, hp⟩) hz
    · simp [hk]
  have he : energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = ∑ z ∈ G, f z := by
    unfold energy
    exact tsum_eq_sum (fun z hz => hzero z hz)
  rw [he]
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hpt : ∀ z ∈ G, f z ≤ R (cls z) * QuadraticInitialBound.diagonalControl Φ := by
    intro z hz
    obtain ⟨_, hk, hp⟩ := Finset.mem_filter.mp hz
    dsimp only [f]
    rw [if_pos hk]
    exact mul_le_mul (hrow z hk hp) (profile_re_le_diag Φ _) (hΦ z) (hR _)
  calc ∑ z ∈ G, f z ≤ ∑ z ∈ G, R (cls z) * QuadraticInitialBound.diagonalControl Φ :=
        Finset.sum_le_sum hpt
    _ = ∑ c, ∑ z ∈ G.filter (fun z => cls z = c),
          R (cls z) * QuadraticInitialBound.diagonalControl Φ :=
        (Finset.sum_fiberwise G cls _).symm
    _ = ∑ c, ((G.filter (fun z => cls z = c)).card : ℝ) * R c *
          QuadraticInitialBound.diagonalControl Φ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2]),
          Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ c, N c * R c * QuadraticInitialBound.diagonalControl Φ := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_right _ hdiag
        apply mul_le_mul_of_nonneg_right _ (hR c)
        apply hcount c
        intro z hz
        obtain ⟨hzG, hc⟩ := Finset.mem_filter.mp hz
        obtain ⟨_, hk, hp⟩ := Finset.mem_filter.mp hzG
        exact ⟨hk, hp, hc⟩
    _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring

end Energy

/-! ### The restricted state -/

/-- The natural state with the keep predicate cut down to the rows satisfying `L`. -/
def restrictState {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ) (L : O → Prop) :
    NaturalState Z Bmask bΦ where
  character := s.character
  fixedModulus := s.fixedModulus
  puncture := s.puncture
  radial := { s.radial with keep := fun z => s.radial.keep z ∧ L z }
  rowWidth := s.rowWidth
  characterWidth := s.characterWidth
  base_ge_one := s.base_ge_one
  row_nonneg := s.row_nonneg
  character_nonneg := s.character_nonneg
  scale_eq := s.scale_eq
  modulus_bound := s.modulus_bound
  puncture_ne_zero := s.puncture_ne_zero
  puncture_bound := s.puncture_bound
  radial_support := s.radial_support
  row_ne_zero := fun z h => s.row_ne_zero z h.1
  nonexceptional := fun z h => s.nonexceptional z h.1

/-! ### Height bookkeeping -/

/-- The supplier height index of buffer height `p` at base height `(h+1)Z^τ`. -/
def binIndex (p h : ℕ) : ℕ := (p+1)*(h+1) - 1

theorem binIndex_succ (p h : ℕ) : binIndex p h + 1 = (p+1)*(h+1) := by
  unfold binIndex
  have : 1 ≤ (p+1)*(h+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem binIndex_height (p h : ℕ) (x : ℝ) :
    3*((p+1 : ℕ) : ℝ)*(((h+1 : ℕ) : ℝ)*x) = 3*((binIndex p h + 1 : ℕ) : ℝ)*x := by
  rw [binIndex_succ]
  push_cast
  ring

theorem le_binIndex (p h : ℕ) : h ≤ binIndex p h := by
  have h1 := binIndex_succ p h
  have : h+1 ≤ (p+1)*(h+1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos p)
  omega

theorem binIndex_le (p h B : ℕ) (hp : p ≤ B) : binIndex p h + 1 ≤ (B+1)*(h+1) := by
  rw [binIndex_succ]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The slot height window at `binIndex` from the window at `h`. -/
theorem window_binIndex {x y : ℝ} (p h : ℕ) (hy : 0 ≤ y)
    (hx : x + y/2 ≤ (3*h+2 : ℕ)*y) : x + y/2 ≤ (3*binIndex p h+2 : ℕ)*y := by
  refine hx.trans (mul_le_mul_of_nonneg_right ?_ hy)
  exact_mod_cast (show 3*h+2 ≤ 3*binIndex p h+2 by have := le_binIndex p h; omega)

/-- The height gate at `binIndex` from the gate at the top buffer height. -/
theorem gate_binIndex {y G : ℝ} (p h B k : ℕ) (hy : 0 ≤ y) (hp : p ≤ B)
    (hg : (3 + 3*(((B+1)*(h+1) : ℕ) : ℝ)*y)^k ≤ G) :
    (3 + ((3*binIndex p h+2 : ℕ) : ℝ)*y)^k ≤ G := by
  refine le_trans ?_ hg
  apply pow_le_pow_left₀ (by positivity)
  have h1 : ((3*binIndex p h+2 : ℕ) : ℝ) ≤ 3*(((B+1)*(h+1) : ℕ) : ℝ) := by
    have := binIndex_le p h B hp
    exact_mod_cast (show 3*binIndex p h+2 ≤ 3*((B+1)*(h+1)) by omega)
  nlinarith

/-! ### The q-free buffered selector and the variable cut -/

section Selector
variable (rayM : Ideal O) [NeZero rayM]
local instance leafRowsQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- A LOW row at the cut `q`: some actual buffered bin at base height `T` lies strictly
below `(q+1)/2`. The bins themselves do not depend on `q`. -/
def lowRow {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (e T q : ℝ) (z : O) : Prop :=
  ∃ hz : st.radial.keep z, ∃ p : OAI.SevenEighths.LocalMoment.BufferIndex e,
    OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
      z hz e T p ∧ OAI.SevenEighths.LocalMoment.bufferValue e p < (q+1)/2

/-- The chosen (q-free) buffered bin of a kept row; an arbitrary index off the keep set
or outside the admissible range of the partition. -/
def selectBin {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (e T : ℝ) (z : O) : OAI.SevenEighths.LocalMoment.BufferIndex e :=
  if h : ∃ hz : st.radial.keep z, ∃ p : OAI.SevenEighths.LocalMoment.BufferIndex e,
      OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
        z hz e T p
  then Classical.choose h.2 else (0, 0)

theorem selectBin_spec {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (z : O) (hz : st.radial.keep z) :
    OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη z hz e T
      (selectBin rayM H hH st η₀ hQM hQη e T z) := by
  have hex : ∃ hz : st.radial.keep z, ∃ p : OAI.SevenEighths.LocalMoment.BufferIndex e,
      OAI.SevenEighths.Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
        z hz e T p :=
    ⟨hz, OAI.SevenEighths.Record1252270103Source.actual_retained_zero_partition rayM H hH
      st η₀ hQM hQη z hz e T he hT hβlo hβhi⟩
  unfold selectBin
  rw [dif_pos hex]
  exact Classical.choose_spec hex.2

/-- A kept row that is not LOW has its chosen bin at or above the cut. -/
theorem selectBin_high {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
    (e T q : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (z : O) (hz : st.radial.keep z) (hn : ¬ lowRow rayM H hH st η₀ hQM hQη e T q z) :
    (q+1)/2 ≤ OAI.SevenEighths.LocalMoment.bufferValue e
      (selectBin rayM H hH st η₀ hQM hQη e T z) := by
  by_contra hlt
  exact hn ⟨hz, _, selectBin_spec rayM H hH st η₀ hQM hQη e T he hT hβlo hβhi z hz,
    lt_of_not_ge hlt⟩

end Selector

end
end QRH.DensitySplitThird.Density
