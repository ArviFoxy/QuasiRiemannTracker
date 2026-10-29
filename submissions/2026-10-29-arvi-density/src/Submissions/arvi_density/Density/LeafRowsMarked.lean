/- Copyright (c) 2026 Sil, ArviFoxy. Apache-2.0.
Row-level adapter of the marked HIGH branch.

`energy_le_class_sums` is the class bound of the packed energy when the pointwise row bound and
the row count of a class are replaced by a bound on the sum of the squared rows over every
finite set of rows of the class: the energy is at most `diagonalControl Φ · ∑_c R c`.

Variant of Sil's `energy_le_classes` (PR 83, `Density/LeafRows`): the hypotheses `hrow`, `hcount`
(pointwise bound times count) are replaced by the single class-sum hypothesis `hsum`; the proof
is the same fibrewise summation. -/
import Submissions.sil_density_split_20261026.Density.LeafRows

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.ArviDensity.Density
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion
open LocalMoment
local notation "O" => HeckeFamily.O

section Energy
variable {ι : Type*} [Fintype ι]

/-- **Finite class-sum bound.** If for every class `c` and every finite set of kept rows of
nonzero weight in class `c` the sum of the squared rows is at most `R c`, then the energy is at
most `diagonalControl Φ · ∑_c R c`. -/
theorem energy_le_class_sums {κ : Type*} [Fintype κ] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (hK : 0 < K) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b)
    (cls : O → κ) (R : κ → ℝ)
    (hsum : ∀ c, ∀ rows : Finset O,
      (∀ z ∈ rows, keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0 ∧ cls z = c) →
        ∑ z ∈ rows, ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤ R c) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
      QuadraticInitialBound.diagonalControl Φ * ∑ c, R c := by
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
  have hpt : ∀ z ∈ G, f z ≤
      ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 * QuadraticInitialBound.diagonalControl Φ := by
    intro z hz
    obtain ⟨_, hk, hp⟩ := Finset.mem_filter.mp hz
    dsimp only [f]
    simp only [hk, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left (profile_re_le_diag Φ _) (sq_nonneg _)
  calc ∑ z ∈ G, f z ≤ ∑ z ∈ G, ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 *
        QuadraticInitialBound.diagonalControl Φ := Finset.sum_le_sum hpt
    _ = ∑ c, ∑ z ∈ G.filter (fun z => cls z = c),
          ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 *
            QuadraticInitialBound.diagonalControl Φ :=
        (Finset.sum_fiberwise G cls _).symm
    _ = ∑ c, (∑ z ∈ G.filter (fun z => cls z = c),
          ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2) *
            QuadraticInitialBound.diagonalControl Φ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
    _ ≤ ∑ c, R c * QuadraticInitialBound.diagonalControl Φ := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_right _ hdiag
        apply hsum c
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

end
end QRH.ArviDensity.Density
