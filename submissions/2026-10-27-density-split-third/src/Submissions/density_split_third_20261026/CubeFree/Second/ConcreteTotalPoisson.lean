/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1 (htotal), part 2: the second Poisson split of the u'-summed residual energies and
the first-divisor regrouping of the nonfixed blocks.

* `physicalBlock_mono` (glue 2): enlarging the source set by columns where the coefficient
  vanishes does not change a physical block.
* `physicalBlock_zero_of_not_label` (glue 1): a block of a pair that is not a common label of
  the source vanishes (every coprime sector pair reconstructs the label,
  `reconstructed_commonParts`).
* `partEnergy_eq_labelSum`, `labelSum_mono`: OAI's `partEnergy` of a masked coefficient is the
  label sum over the common labels of the UNMASKED active source.
* `labelSum_regroup`: `∑_{v ∈ V} labelSum(β_v) = ∑_p ρ(p.1)·(block sum of β)`
  (`first_divisor_regroup`).
* `residual_poisson`: for a source `r` and a finite set `V` of squarefree seeds containing all
  squarefree divisors of every common label,
  `∑_{v∈V} E_v ≤ Z0 + Zf + Zt + ∑_{p,U,n} ρ(p.1)·‖physicalBlock (partRows false)‖`
  with `Z0, Zf, Zt` the literal per-seed zero frequency, fixed-inducing part (`partEnergy true`,
  WP-J's `residual_fixed_inducing`) and tail. -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteTotal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondLocalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ActiveSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedEnergy RayFourExpansion
open CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-! ### Physical blocks as plain double sums -/

/-- The summand of a physical block as a function of plain ideals. -/
def blockTerm (η : Character) (t : ℝ) (β : Id → ℂ) (C D : Id) (hC : Supported C)
    (hD : Supported D) (U : Finset (CommonIndex C D)) (R : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (n : Fin 4 → ℤ) (z : O) (I J : Id) : ℂ :=
  if h : Supported I ∧ Supported J then
    (if IsCoprime I J then
      idealCorrelation (C*I) (D*J) ((supported_mul_iff _ _).mpr ⟨hC, h.1⟩)
        ((supported_mul_iff _ _).mpr ⟨hD, h.2⟩)
        ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) else 0) *
      ((β (C*I) * heightCoeff η t I) * star (β (D*J) * heightCoeff η t J)) *
      (physicalKernel C D W K R ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) I J *
        ((dyadicWeight (n 0) (secondEffectiveScale C D
            (commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) K) *
          dyadicWeight (n 1) (normValue z) *
          dyadicWeight (n 2) (Ideal.absNorm I : ℝ) * dyadicWeight (n 3) (Ideal.absNorm J : ℝ) : ℝ) : ℂ))
  else 0

theorem physicalBlock_eq_sum (η : Character) (t : ℝ) (S : Finset Id) (β : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n =
      ∑ z ∈ rows, if canonicalPartition C D U (nonunitFrequencyGenerator C D U * z) then
        ∑ I ∈ sectorPool C hC.1 S, ∑ J ∈ sectorPool D hD.1 S, blockTerm η t β C D hC hD U R W K n z I J
      else 0 := by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · rw [← Finset.sum_coe_sort (sectorPool C hC.1 S)]
    apply Finset.sum_congr rfl
    intro I _
    rw [← Finset.sum_coe_sort (sectorPool D hD.1 S)]
    apply Finset.sum_congr rfl
    intro J _
    unfold blockTerm
    rw [dif_pos ⟨sectorPool_supported C hC.1 S I, sectorPool_supported D hD.1 S J⟩]
  · rfl

theorem sectorPool_mono (C : Id) (hC : C ≠ 0) {S₁ S₂ : Finset Id} (h : S₁ ⊆ S₂) :
    sectorPool C hC S₁ ⊆ sectorPool C hC S₂ := by
  intro I hI
  unfold sectorPool at *
  rw [Finset.mem_filter, mem_residualPool] at *
  refine ⟨?_, hI.2⟩
  unfold supportedColumns at *
  rw [Finset.mem_filter] at *
  exact ⟨h hI.1.1, hI.1.2⟩

theorem mem_sectorPool (C : Id) (hC : C ≠ 0) (S : Finset Id) (I : Id) :
    I ∈ sectorPool C hC S ↔ C * I ∈ S ∧ Supported (C * I) ∧ IsCoprime C I := by
  unfold sectorPool supportedColumns
  rw [Finset.mem_filter, mem_residualPool, Finset.mem_filter, and_assoc]

/-- **Glue 2.** -/
theorem physicalBlock_mono (η : Character) (t : ℝ) {S₁ S₂ : Finset Id} (h12 : S₁ ⊆ S₂)
    (β : Id → ℂ) (hβ : ∀ I ∈ S₂, I ∉ S₁ → β I = 0)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock η t S₁ β C D hC hD U R rows W K n =
      physicalBlock η t S₂ β C D hC hD U R rows W K n := by
  rw [physicalBlock_eq_sum, physicalBlock_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · rw [Finset.sum_subset (sectorPool_mono C hC.1 h12) ?_]
    · apply Finset.sum_congr rfl
      intro I _
      apply Finset.sum_subset (sectorPool_mono D hD.1 h12)
      intro J hJ2 hJ1
      have hz : β (D * J) = 0 := by
        rw [mem_sectorPool] at hJ2 hJ1
        exact hβ _ hJ2.1 (fun h => hJ1 ⟨h, hJ2.2⟩)
      unfold blockTerm
      split_ifs <;> simp [hz]
    · intro I hI2 hI1
      apply Finset.sum_eq_zero
      intro J _
      have hz : β (C * I) = 0 := by
        rw [mem_sectorPool] at hI2 hI1
        exact hβ _ hI2.1 (fun h => hI1 ⟨h, hI2.2⟩)
      unfold blockTerm
      split_ifs <;> simp [hz]
  · rfl

/-- **Glue 1.** -/
theorem physicalBlock_zero_of_not_label (η : Character) (t : ℝ) (S : Finset Id) (β : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : IdealMobiusDivisorSum.primeSupport C = IdealMobiusDivisorSum.primeSupport D)
    (hnot : (C, D) ∉ commonLabels (supportedColumns S) (supportedColumns S))
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n = 0 := by
  rw [physicalBlock_eq_sum]
  apply Finset.sum_eq_zero
  intro z _
  split_ifs
  · apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro J hJ
    have hI' := (mem_sectorPool C hC.1 S I).mp hI
    have hJ' := (mem_sectorPool D hD.1 S J).mp hJ
    have hI0 : I ≠ 0 := right_ne_zero_of_mul hI'.2.1.1
    have hJ0 : J ≠ 0 := right_ne_zero_of_mul hJ'.2.1.1
    have hCJ : IsCoprime C J :=
      (coprime_of_same_support C D J hC.1 hD.1 hJ0 hCD).mpr hJ'.2.2
    unfold blockTerm
    by_cases hc : IsCoprime I J
    · exfalso
      apply hnot
      obtain ⟨h1, h2⟩ := CenteredMomentCommonSectors.reconstructed_commonParts C D I J hC.1 hD.1
        hI0 hJ0 hCD hI'.2.2 hCJ hc
      unfold commonLabels
      rw [Finset.mem_image]
      refine ⟨(C * I, D * J), ?_, by rw [h1, h2]⟩
      show (C * I, D * J) ∈ (supportedColumns S) ×ˢ (supportedColumns S)
      rw [Finset.mem_product]
      unfold supportedColumns
      exact ⟨Finset.mem_filter.mpr ⟨hI'.1, hI'.2.1⟩, Finset.mem_filter.mpr ⟨hJ'.1, hJ'.2.1⟩⟩
    · split_ifs <;> simp [hc]
  · rfl

/-! ### Label sums -/

/-- The label sum over the common labels of a given source set (OAI's `partEnergy` without
the live-label filter). -/
def labelSum (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (S' : Finset Id) (β : Id → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℂ :=
  ∑ p : commonLabels (supportedColumns S') (supportedColumns S'),
    heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) *
    ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t S' β p.val.1 p.val.2
          (commonLabels_supported S' _ _ p.property).1
          (commonLabels_supported S' _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows b η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i => (n i : ℤ))

theorem partEnergy_eq_labelSum (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O)
    (t : ℝ) (S : Finset Id) (β : Id → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    partEnergy b η χ Q m t S β W K Tsec Z ξ H =
      labelSum b η χ Q m t (activeSource S β) β W K Tsec Z ξ H := by
  unfold partEnergy labelSum
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  rw [common_height_zero_of_not_live η t S β p hp, zero_mul]

/-- The label sum as a plain sum over a finite set of pairs. -/
def labelTerm (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (S' : Finset Id) (β : Id → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (q : Id × Id) : ℂ :=
  if h : q ∈ commonLabels (supportedColumns S') (supportedColumns S') then
    heightCoeff η t q.1 * star (heightCoeff η t q.2) *
    ∑ U : Finset (CommonIndex q.1 q.2),
      ∑ n : SourceBlocks q.1 q.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t S' β q.1 q.2
          (commonLabels_supported S' _ _ h).1 (commonLabels_supported S' _ _ h).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows b η χ Q m q.1 q.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i => (n i : ℤ))
  else 0

theorem labelSum_eq_sum (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (S' : Finset Id) (β : Id → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    labelSum b η χ Q m t S' β W K Tsec Z ξ H =
      ∑ q ∈ commonLabels (supportedColumns S') (supportedColumns S'),
        labelTerm b η χ Q m t S' β W K Tsec Z ξ H q := by
  unfold labelSum
  rw [← Finset.sum_coe_sort (commonLabels (supportedColumns S') (supportedColumns S'))]
  apply Finset.sum_congr rfl
  intro p _
  unfold labelTerm
  rw [dif_pos p.property]

theorem commonLabels_mono {S₁ S₂ : Finset Id} (h : S₁ ⊆ S₂) :
    commonLabels (supportedColumns S₁) (supportedColumns S₁) ⊆
      commonLabels (supportedColumns S₂) (supportedColumns S₂) := by
  have hs : supportedColumns S₁ ⊆ supportedColumns S₂ := Finset.filter_subset_filter _ h
  intro q hq
  unfold commonLabels at *
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, Finset.product_subset_product hs hs hp, he⟩

set_option maxHeartbeats 800000 in
/-- **The label sum does not see columns where the coefficient vanishes.** -/
theorem labelSum_mono (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    {S₁ S₂ : Finset Id} (h12 : S₁ ⊆ S₂) (β : Id → ℂ) (hβ : ∀ I ∈ S₂, I ∉ S₁ → β I = 0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    labelSum b η χ Q m t S₁ β W K Tsec Z ξ H = labelSum b η χ Q m t S₂ β W K Tsec Z ξ H := by
  rw [labelSum_eq_sum, labelSum_eq_sum]
  rw [Finset.sum_subset (commonLabels_mono h12) (fun q _ hq1 => by
    unfold labelTerm; rw [dif_neg hq1])]
  apply Finset.sum_congr rfl
  intro q hq2
  have hdata := commonLabels_data _ _ q.1 q.2 hq2
  unfold labelTerm
  rw [dif_pos hq2]
  by_cases hq1 : q ∈ commonLabels (supportedColumns S₁) (supportedColumns S₁)
  · rw [dif_pos hq1]
    refine congrArg (fun x : ℂ => heightCoeff η t q.1 * star (heightCoeff η t q.2) * x) ?_
    apply Finset.sum_congr rfl; intro U _
    apply Finset.sum_congr rfl; intro n _
    exact physicalBlock_mono η t h12 β hβ _ _ _ _ U _ _ W K _
  · rw [dif_neg hq1]
    symm
    rw [Finset.sum_eq_zero, mul_zero]
    intro U _
    apply Finset.sum_eq_zero
    intro n _
    rw [← physicalBlock_mono η t h12 β hβ]
    exact physicalBlock_zero_of_not_label η t S₁ β q.1 q.2 _ _ hdata.2.2 hq1 U _ _ W K _

/-- `ρ(C) = 2^{ω(C)}`. -/
def rhoC (C : Id) : ℂ := (2 : ℂ) ^ (CompletedGauss.primeSupport C).card

/-- **First-divisor regrouping of the label sums.** -/
theorem labelSum_regroup (b : Bool) (η : Character) (χ : RayCharacter) (Q : Id) (m : O) (t : ℝ)
    (S' : Finset Id) (β : Id → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) (V : Finset Id)
    (hV : ∀ v ∈ V, Squarefree v)
    (hVdiv : ∀ q ∈ commonLabels (supportedColumns S') (supportedColumns S'),
      ∀ u, Squarefree u → u ∣ q.1 → u ∈ V) :
    (∑ v ∈ V, labelSum b η χ Q m t S' (fun I => if v ∣ I then β I else 0) W K Tsec Z ξ H) =
      ∑ p : commonLabels (supportedColumns S') (supportedColumns S'), rhoC p.val.1 *
        (heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) *
        ∑ U : Finset (CommonIndex p.val.1 p.val.2),
          ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t S' β p.val.1 p.val.2
              (commonLabels_supported S' _ _ p.property).1
              (commonLabels_supported S' _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (partRows b η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
              W K (fun i => (n i : ℤ))) := by
  unfold labelSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.mul_sum]
  rw [show ∀ x y z : ℂ, x * (y * z) = y * (x * z) from fun x y z => by ring]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro U _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  have hdata := commonLabels_data _ _ p.val.1 p.val.2 p.property
  exact FirstDivisor.first_divisor_regroup η t S' β p.val.1 p.val.2 _ _ hdata.2.2 U _ _ W K _ V
    (hVdiv p.val p.property) hV

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
