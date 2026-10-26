/- Mixed source step, L2 transfer: new in this submission; uses Sil's, Collet's and
the baseline's lemmas by import. `ball_from_identity` is the body of
`collet_main_selected_transfer_ball` (Ball.lean) with the identity (T) taken as a
hypothesis.

The ball-energy transfer of the no-collision part of a source, under (S') and (F)
only:

  E_noCol(H) ≤ C · ∏_{j∈J} hi_j M_j² · (max 1 H')^ε · Σ_ξ E'_ξ(H'),

with the full residual `E'_ξ` and the constant of Ball.lean. -/
import Submissions.arvi_mixed_step.Transfer.NoCollision

set_option autoImplicit false
set_option maxHeartbeats 1600000
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

/-- **The positive chain from an identity (T)**, at ball radii. -/
theorem ball_from_identity (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ) (G : O → ℂ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) →
      (∀ k, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k)) →
      ∑ z ∈ ballRows H, ‖G z‖ ^ 2 ≤
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
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' G hH hH' hrad hhi hGid
  set G' := residualPolynomial s J A₁ A₂ Dc K R L F τ t T with hG'def
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
    rw [hGid k]
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
          rw [hGid 0]
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
  have hprod : 0 ≤ ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
    Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj) (sq_nonneg _))
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

/-- **Ball transfer of the no-collision part** ((S') and (F); no (Col)). -/
theorem collet_main_selected_transfer_ball_nocol (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
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
      (gaussEnergy Finset.univ
          (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            finiteColumnCoefficient (Fintype.piFinset s.pools)
              (noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
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
  obtain ⟨C, hC, hb⟩ := ball_from_identity.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hS hF
  refine (ball_energy_le_sum _ _ _ _ H hH).trans ?_
  exact hb hcard s J A₁ A₂ Dc K R L F τ t T H H' _ hH hH' hrad hhi
    (transfer_identity_nocol s J A₁ A₂ Dc K R L F τ t T hS hF)

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_ball_nocol
