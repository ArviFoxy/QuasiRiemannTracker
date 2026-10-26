/- Copyright (c) 2026 Sil. Apache-2.0.
`ball_row_norm` adapts Sil's `frequency_norm_bound` (FourthPower/PositiveFamily.lean,
PR 74, vendored in PR 76) to the ball radius and the slot window `∏_J hi·P`. The rest
is new in this submission and uses Sil's, Collet's and the baseline's lemmas by import.

Mixed source step, transfer in the ball-energy form (the form of Collet's
`correctedChildGaussEnergy`).

For any source and any whole-column multiplier `F` with the selected-product
invariance (F), under the tuple-level seed condition (S') and (Col):

  E(H) ≤ C · ∏_{j∈J} hi_j M_j² · (max 1 H')^ε · Σ_ξ E'_ξ(H'),

where `E(H)` is the `ballProfile` energy at radius `H` (coefficient normalized
by `√T`) and `E'_ξ(H')` the residual energy (normalized by `√(T/∏_J P)`,
character `childCharacter τ ξ`), provided `2·H·(∏_J hi_j P_j)⁴ ≤ H'`.
The zero frequency is harmless: for `J ≠ ∅` the selected Gauss sum vanishes at
`0`; for `J = ∅` the pushforward is the identity. -/
import Submissions.arvi_mixed_step.Transfer.Main
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSmoothedWindowEnergy CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstColumns RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source.Collision QRH.Record1252270103Source.High QRH.Record1252270103TwoIdeal
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

/-- The frequencies on which the ball weight at radius `H` can be nonzero. -/
def ballRows (H : ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈2 * H⌉₊).filter (fun z => normValue z < 2 * H)

theorem mem_ballRows (H : ℝ) (z : O) : z ∈ ballRows H ↔ normValue z < 2 * H := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have h1 : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ ⌈2 * H⌉₊ :=
      h.le.trans (Nat.le_ceil _)
    exact_mod_cast h1

/-- The ball energy is at most the plain energy over the ball rows. -/
theorem ball_energy_le_sum {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (H : ℝ) (hH : 0 < H) :
    (gaussEnergy S a ha c ballProfile H).re ≤ ∑ z ∈ ballRows H, ‖gaussPolynomial S a ha c z‖ ^ 2 := by
  have hs := gaussEnergy_hasSum_re S a ha c ballProfile H hH
  have hz : ∀ z ∉ ballRows H, ‖gaussPolynomial S a ha c z‖ ^ 2 *
      (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / H)).re = 0 := by
    intro z hz
    have hn : ¬normValue z < 2 * H := fun h => hz ((mem_ballRows H z).mpr h)
    have h0 : ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / H) = 0 := by
      by_contra hne
      have hlt := ballProfile_support_upper _ (div_nonneg (sq_nonneg _) hH.le) hne
      rw [← normValue_eq_embedding, div_lt_iff₀ hH] at hlt
      exact hn (by linarith)
    rw [h0, Complex.zero_re, mul_zero]
  rw [hs.unique (hasSum_sum_of_ne_finset_zero hz)]
  apply Finset.sum_le_sum
  intro _ _
  exact mul_le_of_le_one_right (sq_nonneg _) (ballProfile_le_one _)

theorem ball_energy_nonneg {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (H : ℝ) (hH : 0 < H) :
    0 ≤ (gaussEnergy S a ha c ballProfile H).re :=
  (gaussEnergy_hasSum_re S a ha c ballProfile H hH).nonneg
    (fun _ => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))

/-- For a nonempty selected block the selected Gauss sum vanishes at frequency 0. -/
theorem selScalar_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (J : Finset ι)
    (K R : Ideal O) (τ : HeckeFamily.Character) (t : ℝ) (u : J → Ideal O)
    (hu : u ∈ selBox s J) (hJ : J.Nonempty) (χ : RayCharacter) :
    selScalar s J K R τ t u χ 0 = 0 := by
  by_cases hw : selWeight s J K R u = 0
  · simp only [selScalar, hw, mul_zero, zero_mul]
  by_cases hD : Supported (selProduct J u)
  · have hsq := selWeight_squarefree s J K R u hw
    obtain ⟨j₀, hj₀⟩ := hJ
    have hp0 := s.prime j₀ (u ⟨j₀, hj₀⟩) (Fintype.mem_piFinset.mp hu ⟨j₀, hj₀⟩)
    have hpf : SexticSieve.PowerFree 5 (selProduct J u) := by
      intro P hP h5
      exact hP.not_isUnit (hsq P ((pow_dvd_pow P (by norm_num : 2 ≤ 5)).trans h5 |>
        (fun h => by simpa only [pow_two] using h)))
    have hff : GaussTransfer.FifthFree (primaryGenerator (selProduct J u)) :=
      KernelWholeColumns.element_fifth_free _
        (by rw [primary_span_supported _ hD]; exact hpf)
    have hncop : ¬IsCoprime (primaryGenerator (selProduct J u)) (primaryGenerator (selProduct J u)) := by
      intro hc
      have hunit : IsUnit (primaryGenerator (selProduct J u)) := isCoprime_self.mp hc
      have htop : selProduct J u = ⊤ := by
        rw [← primary_span_supported _ hD]
        exact Ideal.span_singleton_eq_top.mpr hunit
      have hdvd : u ⟨j₀, hj₀⟩ ∣ selProduct J u :=
        Finset.dvd_prod_of_mem u (Finset.mem_univ _)
      rw [htop] at hdvd
      exact hp0.not_isUnit (isUnit_of_dvd_unit hdvd (Ideal.isUnit_iff.mpr rfl))
    have hz := GaussTransfer.fifth_free_nonunit_zero (primaryGenerator (selProduct J u))
      (MixedSelectedCommon.primary_supported _ hD) hff (primaryGenerator (selProduct J u)) 0 hncop
    have hg : primaryGaussRow (selProduct J u) 0 = 0 := by
      rw [primaryGaussRow_of_supported _ hD]
      unfold gaussRow
      rw [mul_zero] at hz
      rw [hz, zero_div]
    simp only [selScalar, hg, mul_zero]
  · simp only [selScalar, primaryGaussRow_of_not_supported _ hD, mul_zero]

/-- Norm of a pushed-forward ball frequency. -/
theorem ball_row_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (J : Finset ι)
    (K R : Ideal O) (H H' : ℝ) (hH' : 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H')
    (u : J → Ideal O) (hu : u ∈ activeSel s J K R) (z : O) (hz : z ∈ ballRows H) :
    normValue (primaryGenerator (selProduct J u) ^ 4 * z) ≤ H' := by
  obtain ⟨_, _, hD⟩ := activeSel_mem s J K R u hu
  have hspan := PositiveFamily.frequency_span (selProduct J u) hD z
  have hN : normValue (primaryGenerator (selProduct J u) ^ 4 * z) =
      (Ideal.absNorm (selProduct J u) : ℝ) ^ 4 * normValue z := by
    unfold normValue
    rw [show primaryGenerator (selProduct J u) ^ 4 * z =
      PositiveFamily.frequency (selProduct J u, z) from rfl, hspan, map_mul, map_pow]
    push_cast
    ring
  have hDn : (Ideal.absNorm (selProduct J u) : ℝ) ≤ ∏ j ∈ J, s.hi j * s.P j := by
    calc
      (Ideal.absNorm (selProduct J u) : ℝ) = ∏ j : J, (Ideal.absNorm (u j) : ℝ) := by
        unfold selProduct
        rw [map_prod, Nat.cast_prod]
      _ ≤ ∏ j : J, s.hi j.val * s.P j.val :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
          (fun j _ => (activeSel_slot_norm s J K R u hu j).2)
      _ = ∏ j ∈ J, s.hi j * s.P j := Finset.prod_coe_sort J (fun j => s.hi j * s.P j)
  have hzn : normValue z < 2 * H := (mem_ballRows H z).mp hz
  rw [hN]
  calc
    _ ≤ (∏ j ∈ J, s.hi j * s.P j) ^ 4 * (2 * H) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hDn 4) hzn.le
        (by unfold normValue; positivity) (by positivity)
    _ = 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 := by ring
    _ ≤ H' := hH'

/-- **Fourth-power transfer in the ball-energy form** (tuple-level seed condition). -/
theorem collet_main_selected_transfer_ball (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime L (∏ j ∈ J, v (Sum.inl j))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      (gaussEnergy Finset.univ
          (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter,
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R L I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re := by
  obtain ⟨Cf, hCf, hfibb⟩ := fiber_power_bound ε hε N
  refine ⟨256 * 256 * 128 ^ N * max 1 Cf, by positivity, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hS hF hCol
  -- the two polynomials
  set G := originalPolynomial s A₁ A₂ Dc K R L F τ t T with hGdef
  set G' := residualPolynomial s J A₁ A₂ Dc K R L F τ t T with hG'def
  refine (ball_energy_le_sum _ _ _ _ H hH).trans ?_
  change ∑ z ∈ ballRows H, ‖G z‖ ^ 2 ≤ _
  -- residual energies
  set E' : RayCharacter → ℝ := fun ξ =>
    (gaussEnergy Finset.univ
      (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
      (sourceGenerator_supported (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
      (fun I : supportedColumns (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
        CoupledFirst.coefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L I *
          ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
            rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re with hE'def
  change _ ≤ _ * ∑ ξ : RayCharacter, E' ξ
  have hE'0 : ∀ ξ, 0 ≤ E' ξ := fun ξ => ball_energy_nonneg _ _ _ _ H' hH'
  -- frequencies used
  let Ks : Finset O := if J.Nonempty then (ballRows H).erase 0 else ballRows H
  have hKs : Ks ⊆ ballRows H := by
    by_cases hJ : J.Nonempty
    · simp only [Ks, hJ, ↓reduceIte]; exact Finset.erase_subset _ _
    · simp only [Ks, hJ, ↓reduceIte]; exact le_refl _
  have hG : ∀ k ∈ Ks, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ activeSel s J K R, selScalar s J K R τ t u χ k *
          G' ξ (primaryGenerator (selProduct J u) ^ 4 * k) := by
    intro k _
    rw [hGdef, transfer_identity s J A₁ A₂ Dc K R L F τ t T hS hF hCol k]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro ξ _
    rw [activeSel_sum]
  have hsplit : ∑ z ∈ ballRows H, ‖G z‖ ^ 2 = ∑ z ∈ Ks, ‖G z‖ ^ 2 := by
    by_cases hJ : J.Nonempty
    · simp only [Ks, hJ, ↓reduceIte]
      by_cases h0 : (0 : O) ∈ ballRows H
      · rw [← Finset.add_sum_erase _ _ h0]
        have hG0 : G 0 = 0 := by
          rw [hGdef, transfer_identity s J A₁ A₂ Dc K R L F τ t T hS hF hCol 0]
          apply Finset.sum_eq_zero
          intro χ _
          apply Finset.sum_eq_zero
          intro ξ _
          rw [Finset.sum_eq_zero (fun u hu => by rw [selScalar_zero s J K R τ t u hu hJ χ, zero_mul]),
            mul_zero]
        rw [hG0, norm_zero, zero_pow (by norm_num), zero_add]
      · rw [Finset.erase_eq_of_notMem h0]
    · simp only [Ks, hJ, ↓reduceIte]
  rw [hsplit]
  have hα : ∀ u ∈ activeSel s J K R, ∀ χ, ∀ k ∈ Ks,
      ‖selScalar s J K R τ t u χ k‖ ≤
        (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val :=
    fun u hu χ k _ => selScalar_norm_le s J K R τ t u (activeSel_mem s J K R u hu).1 χ k
  have hJN : Fintype.card J ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ J).trans hcard
  have hrow : ∀ r ∈ ((activeSel s J K R) ×ˢ Ks).image
      (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
      normValue r ≤ H' := by
    intro r hr
    obtain ⟨⟨u, z⟩, hp, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hu, hz⟩ := Finset.mem_product.mp hp
    exact ball_row_norm s J K R H H' hrad u hu z (hKs hz)
  have hfib : ∀ r ∈ ((activeSel s J K R) ×ˢ Ks).image
      (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
      ((((activeSel s J K R) ×ˢ Ks).filter
        (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2 = r)).card : ℝ) ≤
        max 1 Cf * (max 1 H') ^ ε := by
    intro r hr
    have hpow1 : 1 ≤ (max 1 H') ^ ε := Real.one_le_rpow (le_max_left _ _) hε.le
    by_cases hJ : J.Nonempty
    · obtain ⟨⟨u, z⟩, hp, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hu, hz⟩ := Finset.mem_product.mp hp
      have hz0 : z ≠ 0 := by
        simp only [Ks, hJ, ↓reduceIte] at hz
        exact (Finset.mem_erase.mp hz).1
      have hD := (activeSel_mem s J K R u hu).2.2
      have hr0 : primaryGenerator (selProduct J u) ^ 4 * z ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (supported_primaryGenerator_ne_zero _ hD)) hz0
      have hc := selected_fiber_card (activeSel s J K R)
        (fun u hu => (activeSel_mem s J K R u hu).2.2) Ks _ hr0
      have hnorm := hrow _ hr
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors
              (Ideal.span {primaryGenerator (selProduct J u) ^ 4 * z})).card : ℝ) ^
            Fintype.card J := by
          exact_mod_cast hc
        _ ≤ Cf * (normValue (primaryGenerator (selProduct J u) ^ 4 * z)) ^ ε :=
          hfibb _ hJN _ hr0
        _ ≤ max 1 Cf * (max 1 H') ^ ε :=
          mul_le_mul (le_max_right _ _)
            (Real.rpow_le_rpow (by unfold normValue; positivity)
              (hnorm.trans (le_max_right _ _)) hε.le)
            (Real.rpow_nonneg (by unfold normValue; positivity) _) (by positivity)
    · have hJe : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      have hU1 : (activeSel s J K R).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a _ b _
        funext j
        exact absurd j.property (Finset.eq_empty_iff_forall_notMem.mp hJe j.val)
      have hsub : ((activeSel s J K R) ×ˢ Ks).filter
          (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2 = r) ⊆
          (activeSel s J K R) ×ˢ {r} := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have hsel : selProduct J p.1 = 1 := by
          unfold selProduct
          apply Finset.prod_eq_one
          intro j _
          exact absurd j.property (Finset.eq_empty_iff_forall_notMem.mp hJe j.val)
        rw [hsel, primaryGenerator_one, one_pow, one_mul] at hp2
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp1).1, Finset.mem_singleton.mpr hp2⟩
      have hcard1 : (((activeSel s J K R) ×ˢ Ks).filter
          (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2 = r)).card ≤ 1 :=
        (Finset.card_le_card hsub).trans
          (by rw [Finset.card_product, Finset.card_singleton, mul_one]; exact hU1)
      calc
        _ ≤ (1 : ℝ) := by exact_mod_cast hcard1
        _ ≤ max 1 Cf * (max 1 H') ^ ε := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow1
  have hfam := ray_family_energy (activeSel s J K R) (fun u => primaryGenerator (selProduct J u))
    Ks (fun u χ k => selScalar s J K R τ t u χ k) G G' _ _ hG hα hfib
  -- residual rows lower bound
  have hres : ∀ ξ, ∑ r ∈ ((activeSel s J K R) ×ˢ Ks).image
      (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
      ‖G' ξ r‖ ^ 2 ≤ E' ξ := by
    intro ξ
    apply finite_energy_le_gaussEnergy _ _ _ _ ballProfile H' hH'
    · intro z
      exact ballProfile_nonneg _
    · intro r hr
      exact ballProfile_majorizes H' hH' r (hrow r hr)
  have hSig : ∑ ξ : RayCharacter, ∑ r ∈ ((activeSel s J K R) ×ˢ Ks).image
      (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
      ‖G' ξ r‖ ^ 2 ≤ ∑ ξ : RayCharacter, E' ξ := Finset.sum_le_sum (fun ξ _ => hres ξ)
  have hB : 0 ≤ max 1 Cf * (max 1 H') ^ ε :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hcount : 0 ≤ ((activeSel s J K R).card : ℝ) *
      ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hprod : 0 ≤ ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
    Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj) (sq_nonneg _))
  have hEsum : 0 ≤ ∑ ξ : RayCharacter, E' ξ := Finset.sum_nonneg (fun ξ _ => hE'0 ξ)
  refine hfam.trans ?_
  have hmass' : ((activeSel s J K R).card : ℝ) *
      ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val) ^ 2 ≤
      128 ^ N * ∏ j ∈ J, s.hi j * s.M j ^ 2 := by
    by_cases hne : (activeSel s J K R).Nonempty
    · have hpow : (128:ℝ) ^ J.card ≤ 128 ^ N :=
        pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ J).trans hcard)
      exact (activeSel_mass s J K R hne).trans (mul_le_mul_of_nonneg_right hpow hprod)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
  calc
    _ ≤ 256 * 256 * (128 ^ N * ∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 Cf * (max 1 H') ^ ε) *
        ∑ ξ : RayCharacter, E' ξ := by
      apply mul_le_mul _ hSig (Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg
        (fun r _ => sq_nonneg _))) (by positivity)
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left hmass' (by norm_num)
    _ = _ := by ring

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_ball
