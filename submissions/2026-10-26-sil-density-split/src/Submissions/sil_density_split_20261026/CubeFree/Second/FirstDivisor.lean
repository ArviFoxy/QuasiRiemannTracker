/- Copyright (c) 2026 Sil. Apache-2.0.
First artificial divisor inside the second physical block (cube-free argument, Sections 3-4).

* `first_divisor_regroup`: the joint-Cauchy expansion `∑_u 1_{u | n₁} 1_{u | n₂} = 2^{ω(gcd)}`
  (CF (4.2)) evaluated exactly at the level of the OAI `physicalBlock`. The block keeps the
  coprimality condition `IsCoprime I J` of the two residual columns literally, so for every
  squarefree `u` the double indicator `[u ∣ C·I] [u ∣ D·J]` equals `[u ∣ C]`. Hence restricting
  the column coefficient to multiples of `u` and summing over all squarefree `u` multiplies the
  block by `ρ(C) = 2^{ω(C)}` exactly. Only `primeSupport C = primeSupport D` is used; equal
  multiplicities of `C` and `D` are not needed.
* `idealCorrelation_unequal_zero`, `idealCorrelation_cubefree_unequal_zero`: unequal common
  multiplicities (in particular `1` and `2`) give a vanishing second Gauss correlation at every
  frequency (CF Section 3). Both are thin wrappers of OAI `actual_unequal_min_six` and
  `idealCorrelation_zero_outside_common`.
* `correlation_le_common_over_unit`: CF (3.2), `|F(G,G;j)| ≤ N G / N U` on the canonical
  unit/nonunit partition, from OAI `actual_ideal_partition_scalar`; with equal multiplicities the
  numerator is `N C` (`commonFrequency_span_of_equal`). -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondMovingSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

set_option autoImplicit false

namespace QRH.SilDensitySplit.CubeFree.Second.FirstDivisor

noncomputable section
open scoped BigOperators Classical SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

/-! ### Squarefree divisors and prime supports -/

theorem mem_primeSupport_iff {X P : Ideal O} (hX : X ≠ 0) :
    P ∈ CompletedGauss.primeSupport X ↔ P.IsPrime ∧ X ≤ P := by
  unfold CompletedGauss.primeSupport
  rw [Multiset.mem_toFinset]
  exact Ideal.mem_normalizedFactors_iff hX

/-- A squarefree ideal divides a nonzero ideal iff its primes do. -/
theorem squarefree_dvd_iff_support {u X : Ideal O} (hu : Squarefree u) (hX : X ≠ 0) :
    u ∣ X ↔ CompletedGauss.primeSupport u ⊆ CompletedGauss.primeSupport X := by
  constructor
  · exact IdealMobiusDivisorSum.squarefree_divisor_support hX hu
  · intro h
    rw [← IdealMobiusDivisorSum.squarefree_support_product_self hu]
    exact IdealMobiusDivisorSum.support_product_dvd hX h

/-- The double indicator of CF (4.2) on the coprime branch of the second correlation. -/
theorem both_dvd_iff {C D I J u : Ideal O} (hC : C ≠ 0) (hD : D ≠ 0)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (hIJ : IsCoprime I J) (hu : Squarefree u) :
    (u ∣ C * I ∧ u ∣ D * J) ↔ u ∣ C := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [squarefree_dvd_iff_support hu hC]
    intro P hP
    obtain ⟨hPp, huP⟩ := (mem_primeSupport_iff hu.ne_zero).mp hP
    have hCI : C * I ≤ P := (Ideal.le_of_dvd h1).trans huP
    have hDJ : D * J ≤ P := (Ideal.le_of_dvd h2).trans huP
    rw [mem_primeSupport_iff hC]
    refine ⟨hPp, ?_⟩
    by_contra hCP
    have hIP : I ≤ P := (hPp.mul_le.mp hCI).resolve_left hCP
    have hDP : ¬ D ≤ P := by
      intro hDP
      have hmem : P ∈ CompletedGauss.primeSupport D := (mem_primeSupport_iff hD).mpr ⟨hPp, hDP⟩
      rw [← hCD] at hmem
      exact hCP ((mem_primeSupport_iff hC).mp hmem).2
    have hJP : J ≤ P := (hPp.mul_le.mp hDJ).resolve_left hDP
    have hsup : I ⊔ J ≤ P := sup_le hIP hJP
    rw [Ideal.isCoprime_iff_sup_eq.mp hIJ] at hsup
    exact hPp.ne_top (top_le_iff.mp hsup)
  · intro h
    refine ⟨dvd_mul_of_dvd_left h I, dvd_mul_of_dvd_left ?_ J⟩
    rw [squarefree_dvd_iff_support hu hD, ← hCD]
    exact (squarefree_dvd_iff_support hu hC).mp h

/-- `ρ(C) = 2^{ω(C)}`: the number of squarefree divisors of `C` in any finite family that
contains all of them and only squarefree ideals. -/
theorem card_filter_dvd {C : Ideal O} (hC : C ≠ 0) (Us : Finset (Ideal O))
    (hUs : ∀ u, Squarefree u → u ∣ C → u ∈ Us) (hsq : ∀ u ∈ Us, Squarefree u) :
    (Us.filter (fun u => u ∣ C)).card = 2 ^ (CompletedGauss.primeSupport C).card := by
  have hC' : C ≠ ⊥ := hC
  have hset : Us.filter (fun u => u ∣ C) =
      (IdealMobiusDivisorSum.idealDivisors C).filter Squarefree := by
    ext u
    simp only [Finset.mem_filter, IdealMobiusDivisorSum.mem_idealDivisors hC']
    constructor
    · rintro ⟨hu, hd⟩
      exact ⟨hd, hsq u hu⟩
    · rintro ⟨hd, hs⟩
      exact ⟨hUs u hs hd, hd⟩
  rw [hset, IdealMobiusDivisorSum.squarefree_divisors_eq_image C hC', Finset.card_image_of_injOn,
    Finset.card_powerset]
  · rfl
  · intro S hS T hT hST
    exact IdealMobiusDivisorSum.support_product_injective
      (Finset.mem_powerset.mp (Finset.mem_coe.mp hS))
      (Finset.mem_powerset.mp (Finset.mem_coe.mp hT)) hST

/-- CF (4.2) on one coprime pair of residual columns. -/
theorem first_divisor_pair_sum {C D I J : Ideal O} (hC : C ≠ 0) (hD : D ≠ 0)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (hIJ : IsCoprime I J) (Us : Finset (Ideal O))
    (hUs : ∀ u, Squarefree u → u ∣ C → u ∈ Us) (hsq : ∀ u ∈ Us, Squarefree u) (x y : ℂ) :
    ∑ u ∈ Us, (if u ∣ C * I then x else 0) * star (if u ∣ D * J then y else 0) =
      (2 : ℂ) ^ (CompletedGauss.primeSupport C).card * (x * star y) := by
  have hterm : ∀ u ∈ Us, (if u ∣ C * I then x else 0) * star (if u ∣ D * J then y else 0) =
      if u ∣ C then x * star y else 0 := by
    intro u hu
    have hb := both_dvd_iff hC hD hCD hIJ (hsq u hu)
    by_cases h1 : u ∣ C * I <;> by_cases h2 : u ∣ D * J <;> by_cases h3 : u ∣ C <;>
      simp_all
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const,
    card_filter_dvd hC Us hUs hsq, nsmul_eq_mul]
  push_cast
  ring

/-! ### The regrouping at block level -/

private theorem pair_term_sum {C D I J : Ideal O} (hC : C ≠ 0) (hD : D ≠ 0)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (Us : Finset (Ideal O))
    (hUs : ∀ u, Squarefree u → u ∣ C → u ∈ Us) (hsq : ∀ u ∈ Us, Squarefree u)
    (β : Ideal O → ℂ) (corr hI hJ k : ℂ) :
    ∑ u ∈ Us, (if IsCoprime I J then corr else 0) *
        (((fun I => if u ∣ I then β I else 0) (C * I) * hI) *
          star ((fun I => if u ∣ I then β I else 0) (D * J) * hJ)) * k =
      (2 : ℂ) ^ (CompletedGauss.primeSupport C).card *
        ((if IsCoprime I J then corr else 0) * ((β (C * I) * hI) * star (β (D * J) * hJ)) * k) := by
  by_cases hIJ : IsCoprime I J
  · simp only [if_pos hIJ]
    have hrw : ∀ u ∈ Us, corr * (((if u ∣ C * I then β (C * I) else 0) * hI) *
          star ((if u ∣ D * J then β (D * J) else 0) * hJ)) * k =
        ((if u ∣ C * I then β (C * I) else 0) * star (if u ∣ D * J then β (D * J) else 0)) *
          (corr * (hI * star hJ) * k) := by
      intro u _
      simp only [star_mul']
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul,
      first_divisor_pair_sum hC hD hCD hIJ Us hUs hsq]
    simp only [star_mul']
    ring
  · simp only [if_neg hIJ, zero_mul, Finset.sum_const_zero, mul_zero]

/-- **First artificial divisor regrouping** (CF (4.2) at block level). Summing the second physical
block over the first artificial divisor `u` (column coefficient restricted to multiples of `u`)
gives exactly `ρ(C) = 2^{ω(C)}` times the block. -/
theorem first_divisor_regroup (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ, ℂ)) (K : ℝ)
    (n : Fin 4 → ℤ) (Us : Finset (Ideal O))
    (hUs : ∀ u, Squarefree u → u ∣ C → u ∈ Us) (hsq : ∀ u ∈ Us, Squarefree u) :
    ∑ u ∈ Us, physicalBlock η t S (fun I => if u ∣ I then β I else 0) C D hC hD U R rows W K n =
      (2 : ℂ) ^ (CompletedGauss.primeSupport C).card *
        physicalBlock η t S β C D hC hD U R rows W K n := by
  unfold physicalBlock
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U * z)
  · simp only [if_pos hp]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    exact pair_term_sum hC.1 hD.1 hCD Us hUs hsq β _ _ _ _
  · simp only [if_neg hp, Finset.sum_const_zero, mul_zero]

/-- The regrouping commutes with the second Poisson split of the rows into fixed-inducing and
nonfixed rows (OAI `physicalBlock_filter_split`): the first-divisor sum of the block is
`ρ(C)` times the sum of the fixed-inducing and nonfixed blocks of the original coefficient. -/
theorem first_divisor_regroup_split (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ, ℂ)) (K : ℝ)
    (n : Fin 4 → ℤ) (Us : Finset (Ideal O))
    (hUs : ∀ u, Squarefree u → u ∣ C → u ∈ Us) (hsq : ∀ u ∈ Us, Squarefree u) (p : O → Prop) :
    ∑ u ∈ Us, physicalBlock η t S (fun I => if u ∣ I then β I else 0) C D hC hD U R rows W K n =
      (2 : ℂ) ^ (CompletedGauss.primeSupport C).card *
        (physicalBlock η t S β C D hC hD U R (rows.filter p) W K n +
          physicalBlock η t S β C D hC hD U R (rows.filter (fun z => ¬ p z)) W K n) := by
  rw [first_divisor_regroup η t S β C D hC hD hCD U R rows W K n Us hUs hsq,
    ← CenteredMomentSecondEnergySplit.physicalBlock_filter_split]

/-! ### Unequal multiplicities and the correlation size (CF Section 3, (3.2)) -/

/-- Unequal common multiplicities whose minimum is not divisible by six give a vanishing second
correlation at every frequency. -/
theorem idealCorrelation_unequal_zero (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (P : CommonIndex C D) (hneq : leftExponent C D P ≠ rightExponent C D P)
    (hmin : ¬ 6 ∣ min (leftExponent C D P) (rightExponent C D P)) (j : O) :
    idealCorrelation C D hC hD j = 0 := by
  by_contra hne
  by_cases hdiv : commonFrequencyGenerator C D ∣ j
  · obtain ⟨w, rfl⟩ := hdiv
    exact hmin (CenteredMomentSecondMovingSupport.actual_unequal_min_six C D hC hD hCD w hne P hneq)
  · exact hne (idealCorrelation_zero_outside_common C D hC hD hCD j hdiv)

/-- Cube-free form: positive multiplicities `≤ 2` that differ (i.e. `1` and `2`) kill the
second correlation identically. -/
theorem idealCorrelation_cubefree_unequal_zero (C D : Ideal O) (hC : Supported C)
    (hD : Supported D) (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (P : CommonIndex C D) (hl : leftExponent C D P ≤ 2) (hr : rightExponent C D P ≤ 2)
    (hneq : leftExponent C D P ≠ rightExponent C D P) (j : O) :
    idealCorrelation C D hC hD j = 0 := by
  apply idealCorrelation_unequal_zero C D hC hD hCD P hneq
  have h1 := leftExponent_pos C D P
  have h2 := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P) = 1 := by omega
  rw [hm]
  norm_num

/-- Hence a nonzero second correlation of cube-free columns with equal supports has equal
multiplicities at every common prime. -/
theorem cubefree_equal_of_ne_zero (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (hl : ∀ P, leftExponent C D P ≤ 2) (hr : ∀ P, rightExponent C D P ≤ 2) (j : O)
    (hne : idealCorrelation C D hC hD j ≠ 0) (P : CommonIndex C D) :
    leftExponent C D P = rightExponent C D P := by
  by_contra hneq
  exact hne (idealCorrelation_cubefree_unequal_zero C D hC hD hCD P (hl P) (hr P) hneq j)

/-- **CF (3.2)**: on the canonical partition with unit set `U`, the second correlation at the
divided frequency is at most `N(common part) / N(∏_{P ∈ U} P)`. -/
theorem correlation_le_common_over_unit (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hpart : canonicalPartition C D U w) :
    ‖idealCorrelation C D hC hD (commonFrequencyGenerator C D * w)‖ ≤
      (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ) /
        Ideal.absNorm (∏ P ∈ U, P.val) := by
  have h := actual_ideal_partition_scalar C D hC hD hCD U w
  have hN := normalizer_pos C D hC U
  have hN' : 0 < CenteredMomentPartition.partitionNormalizer (commonPrime C D) (leftExponent C D)
      (rightExponent C D) U := hN
  rw [canonicalPartitionScalar, if_pos hpart, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hN'.le] at h
  have hle : ‖idealCorrelation C D hC hD (commonFrequencyGenerator C D * w)‖ ≤ normalizer C D U := by
    have h' : (normalizer C D U)⁻¹ * ‖idealCorrelation C D hC hD (commonFrequencyGenerator C D * w)‖
        ≤ 1 := by simpa only [normalizer] using h
    have := mul_le_mul_of_nonneg_left h' hN.le
    rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul, mul_one] at this
  rw [normalizer, actual_partitionNormalizer C D hC U] at hle
  exact hle

/-- With equal multiplicities the common frequency generator spans `C` itself, so the bound
of `correlation_le_common_over_unit` reads `N G / N U` with `G = C = D`. -/
theorem commonFrequency_span_of_equal (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (heq : ∀ P, leftExponent C D P = rightExponent C D P) :
    Ideal.span {commonFrequencyGenerator C D} = C := by
  rw [commonFrequencyGenerator_span C D hC, commonIdeal]
  simp_rw [← heq, min_self]
  conv_rhs => rw [← left_ideal_product C D hC hCD]

end

end QRH.SilDensitySplit.CubeFree.Second.FirstDivisor
