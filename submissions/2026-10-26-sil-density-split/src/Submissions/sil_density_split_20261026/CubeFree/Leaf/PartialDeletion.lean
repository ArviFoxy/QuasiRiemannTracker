/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Modified by Sil (2026-10-26): partial slot deletion. Adapted from FP
`Candidate.FourthPower.NativeSlotDeletion` (`energy_delete`, `canonical_delete`), which
deletes every slot of a set; here only the slots of `A \ R` are deleted and the retained
slots `R` stay in the energy, by the pointwise factorization of the selected product
(as in PR69 `LowErasure/Finite.cofactor_product_erasure`). The pointwise cost is the
natural slot cost of the deleted slots only (`natural_slot_product` with the deleted
widths as an indicator on the ambient slot type).

Also the greedy choice of whole deleted slots (`greedy_deletion`): with all slot widths
in `[0, mesh]` and a need `0 ≤ need ≤ ∑_T w`, some retained `F ⊆ T` deletes width in
`[need, need + mesh]`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Reindex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QRH.SilDensitySplit.CubeFree
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRayMaskedFloor CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

/-! ### Greedy choice of the deleted slots -/

/-- **Greedy whole-slot deletion.** If every slot width lies in `[0, mesh]` and
`0 ≤ need ≤ ∑_{T} w`, then some deleted subset `D ⊆ T` has width in `[need, need+mesh]`. -/
theorem greedy_deleted {α : Type*} [DecidableEq α] (w : α → ℝ) (mesh need : ℝ)
    (hmesh : 0 ≤ mesh) (hneed : 0 ≤ need) :
    ∀ T : Finset α, (∀ i ∈ T, 0 ≤ w i) → (∀ i ∈ T, w i ≤ mesh) → need ≤ ∑ i ∈ T, w i →
      ∃ D : Finset α, D ⊆ T ∧ need ≤ ∑ i ∈ D, w i ∧ ∑ i ∈ D, w i ≤ need + mesh := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ _ h
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simpa using h
    · simp only [Finset.sum_empty]; linarith
  | insert a T ha ih =>
    intro hw hwm h
    have hwT : ∀ i ∈ T, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hwmT : ∀ i ∈ T, w i ≤ mesh := fun i hi => hwm i (Finset.mem_insert_of_mem hi)
    by_cases hT : need ≤ ∑ i ∈ T, w i
    · obtain ⟨D, hD, h1, h2⟩ := ih hwT hwmT hT
      exact ⟨D, hD.trans (Finset.subset_insert a T), h1, h2⟩
    · refine ⟨insert a T, le_rfl, h, ?_⟩
      rw [Finset.sum_insert ha]
      have := hwm a (Finset.mem_insert_self a T)
      linarith

/-- **Greedy deletion, retained form.** Under the same hypotheses some retained
`F ⊆ T` deletes the slots `T \ F` of total width in `[need, need + mesh]`. -/
theorem greedy_deletion {α : Type*} [DecidableEq α] (T : Finset α) (w : α → ℝ)
    (mesh need : ℝ) (hmesh : 0 ≤ mesh) (hneed : 0 ≤ need)
    (hw : ∀ i ∈ T, 0 ≤ w i) (hwm : ∀ i ∈ T, w i ≤ mesh) (hs : need ≤ ∑ i ∈ T, w i) :
    ∃ F : Finset α, F ⊆ T ∧ need ≤ ∑ i ∈ T \ F, w i ∧ ∑ i ∈ T \ F, w i ≤ need + mesh := by
  obtain ⟨D, hD, h1, h2⟩ := greedy_deleted w mesh need hmesh hneed T hw hwm hs
  refine ⟨T \ D, Finset.sdiff_subset, ?_, ?_⟩ <;>
    rwa [Finset.sdiff_sdiff_eq_self hD]

/-! ### Partial deletion inside the positive energy -/

/-- **Partial slot deletion.** The energy with slots `A` is at most `E` times the energy
with the retained slots `R ⊆ A`, if `E` bounds the squared product of the normalized
deleted slots `A \ R` on every kept row in the radial support. Same zero row, lengths and
radial data on both sides. (FP `energy_delete` is the case `R = ∅`.) -/
theorem energy_partial_delete {α : Type*} [DecidableEq α]
    {Z Bmask radial : ℝ} (s : NaturalState Z Bmask radial) (hu : s.puncture=1)
    (A R : Finset α) (hRA : R ⊆ A)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0≤P i) (W₁ W₂ : ℝ→ℂ) (t X₁ X₂ E : ℝ) (hX : 0≤X₁*X₂)
    (hslot : ∀z,s.radial.keep z →
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)≠0 →
      ‖∏i∈A\R,normalizedSlot s.character fixedBadMask 1 z (pool i) (β i) t (P i)‖^2≤E) :
    energy s.character s.mask 1 t W₁ W₂
      (fun i:A=>pool i) (fun i:A=>β i) (fun i:A=>P i) X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale ≤
    E*energy s.character s.mask 1 t W₁ W₂
      (fun i:R=>pool i) (fun i:R=>β i) (fun i:R=>P i) X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale := by
  have hm : s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1 := by
    rw [NaturalState.mask,hu]
  rw [hm,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  have hsA := compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂
      (fun i:A=>pool i) (fun i:A=>β i) (fun i:A=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos s.radial_support
  have hsR := compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂
      (fun i:R=>pool i) (fun i:R=>β i) (fun i:R=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale radial s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply hsA.tsum_le_tsum _ (hsR.mul_left E)
  intro z
  by_cases hk : s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · rw [←selected_eq_positive A _ _ _ _ _ _ _ _ _ _ _ _ hX hP,
        ←selected_eq_positive R _ _ _ _ _ _ _ _ _ _ _ _ hX hP]
      have hsplit : selectedProduct A s.character fixedBadMask 1 z W₁ W₂ pool β P t X₁ X₂ =
          (∏i∈A\R,normalizedSlot s.character fixedBadMask 1 z (pool i) (β i) t (P i))*
            selectedProduct R s.character fixedBadMask 1 z W₁ W₂ pool β P t X₁ X₂ := by
        unfold selectedProduct
        rw [←Finset.prod_sdiff hRA]
        ring
      rw [hsplit, norm_mul, mul_pow]
      have h1 := hslot z hk hp
      have h2 := s.radial.nonneg z
      have h3 := sq_nonneg ‖selectedProduct R s.character fixedBadMask 1 z W₁ W₂ pool β P t X₁ X₂‖
      calc _ ≤ E*‖selectedProduct R s.character fixedBadMask 1 z W₁ W₂ pool β P t X₁ X₂‖^2*
              (s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h3) h2
        _ = _ := by ring
  · simp only [ite_eq_right hk,mul_zero,le_refl]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- **Canonical partial deletion.** Canonical annular slots on the ambient slot type,
with all original frequencies and ray factors; the retained slots `R ⊆ A` stay and only
the deleted slots `A \ R` are paid, at their natural cost `κ·∑_{A\R} w`. Constants
precede the moving state, the sets `A, R`, the widths, profiles and positive lengths. -/
theorem canonical_partial_delete {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b radial Mcap Lslot loss lo hi κ : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hrad : 0≤radial) (hM : 0≤Mcap) (hL : 0≤Lslot) (hloss : 0<loss)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t V : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀Bmask : ℝ,∀s : NaturalState Z Bmask radial,s.puncture=1 → s.width≤Mcap →
    ∀Q : Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(A R : Finset α),R⊆A → ∀(W₁ W₂ : ℝ→ℂ)(X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t W₁ W₂
        (fun i:A=>primePool M H b (Z^(w i)))
        (fun (i:A) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:A=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C*(1+|t|+V)^degree*Z^(loss+κ*(∑i∈A\R,w i)))*
        energy s.character s.mask 1 t W₁ W₂
        (fun i:R=>primePool M H b (Z^(w i)))
        (fun (i:R) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:R=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hslots⟩ := natural_slot_product M H hH (Finset.univ : Finset α) W a b ha
    hWs hW (Mcap+1) Lslot loss lo hi κ (by linarith) hL hloss hβ hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [hslots η₀,eventual_state_conductor radial Mcap hrad] with Z hs hc
  refine ⟨hc.1,?_⟩
  intro θ w σ freq t V hw hwL hσ hσhi hV hfreq Bmask s hu hwidth Q hQ hQM A R hRA
    W₁ W₂ X₁ X₂ hX₁ hX₂
  apply energy_partial_delete s hu A R hRA (fun i=>primePool M H b (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) (fun _=>Real.rpow_nonneg (zero_lt_one.trans hc.1).le _)
    W₁ W₂ t X₁ X₂ _ (mul_pos hX₁ hX₂).le
  intro z hk hp
  have hn := s.row_ne_zero z hk
  let wd : α → ℝ := fun i => if i ∈ A\R then w i else 0
  have hwd0 : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ wd i := by
    intro i _; dsimp only [wd]; split_ifs
    · exact hw i
    · exact le_rfl
  have hwdL : ∀ i ∈ (Finset.univ : Finset α), wd i ≤ Lslot := by
    intro i _; dsimp only [wd]; split_ifs
    · exact hwL i
    · exact hL
  have hh := hs θ wd σ freq t V hwd0 hwdL (fun i _ => hσ i) (fun i _ => hσhi i) hV
    (fun i _ => hfreq i) s.character z hn
    (naturalRow s.character z hn) (hc.2 Bmask s hwidth z hn hp) Q hQM
    (state_unit_nonexceptional s hu _ hQ z hk) (A\R) (Finset.subset_univ _)
  have hsum : (∑ i ∈ (Finset.univ : Finset α), wd i) = ∑ i ∈ A\R, w i :=
    sum_univ_indicator (A\R) w
  have hprod : (∏i∈A\R,naturalSlot (naturalRow s.character z hn).character
      (primePool M H b (Z^(wd i)))
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(wd i)) (σ i) (freq i) I) t) (Z^(wd i))) =
      ∏i∈A\R,naturalSlot (naturalRow s.character z hn).character
      (primePool M H b (Z^(w i)))
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [wd, hi, ite_true]
  rw [hprod, hsum] at hh
  simpa only [natural_slot_eq (naturalRow s.character z hn)] using hh

end
end QRH.SilDensitySplit.CubeFree
