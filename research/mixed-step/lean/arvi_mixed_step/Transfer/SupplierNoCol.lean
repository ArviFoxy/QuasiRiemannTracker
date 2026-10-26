/- Mixed source step, L2/L3 transfer: new in this submission; uses the transfer's
lemmas (Transfer/) by import. `supplier_ball_from_identity` is the body of
`collet_main_selected_transfer_supplier_ball` (SupplierBall.lean) with the identity
(T) taken as a hypothesis.

The seed-supplier transfer of the no-collision part, with no (S) and no (Col):

  E_noCol(H) ≤ C · ∏_{j∈J} hi_j M_j² · (max 1 H')^ε · Σ_ξ Σ_{L' ∈ seeds} E'_{ξ,L'}(H'),

every residual seed `L' ∈ seeds` dividing `L`. The tuples of the no-collision part
factor with the residual seed `L/gcd(L, D_u)` (`tuple_factor_masked_supplier_nocol`),
and the identity (T) holds for them (`transfer_identity_supplier_nocol`). -/
import Submissions.arvi_mixed_step.Transfer.SupplierBall
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

section Factor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Factorization of the no-collision part with the residual seed** (no (S), no (Col)). -/
theorem tuple_factor_masked_supplier_nocol (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (hLsq : Squarefree L) (u : J → Ideal O) (hu : u ∈ selBox s J)
    (w : Tuple {i // i ∉ J})
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w)) :
    noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)
        (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R (residualSeed J L u) w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) := by
  unfold noColPart noColMask
  rw [sel_prod_join, joinTuple_inr, joinTuple_inr]
  by_cases hc0 : IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))
  · simp only [hc0, ↓reduceIte, mul_one]
    exact tuple_factor_masked_supplier s J A₁ A₂ Dc K R L F hLsq u hu w hF (fun _ => hc0)
  · have hn : ¬IsCoprime (selProduct J u) (finiteTupleProduct w) := by
      intro h
      apply hc0
      apply h.of_isCoprime_of_dvd_right
      rw [finiteTupleProduct_split w]
      exact dvd_mul_left _ _
    simp only [hc0, hn, ↓reduceIte, mul_zero]

/-- **The identity (T) for the no-collision part, with residual seeds** (no (S), no (Col)). -/
theorem transfer_identity_supplier_nocol (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (hLsq : Squarefree L)
    (hF : ∀ v ∈ Fintype.piFinset s.pools,
      F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v)))
    (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
          finiteColumnCoefficient (Fintype.piFinset s.pools)
            (noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R (residualSeed J L u) F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k) := by
  have hβ : ∀ u ∈ selBox s J, ∀ w ∈ Fintype.piFinset (residualInput s J).pools,
      noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)
          (joinTuple J u w) =
        selWeight s J K R u *
          CoupledFirst.tupleCoefficient (residualInput s J)
            (markedSourceModifier A₁ A₂ Dc K F) R (residualSeed J L u) w *
          (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) := by
    intro u hu w hw
    have hv : joinTuple J u w ∈ Fintype.piFinset s.pools := by
      apply Fintype.mem_piFinset.mpr
      apply (mem_pools_iff s _).mpr
      have hu' := Fintype.mem_piFinset.mp hu
      have hw' := (mem_pools_iff (residualInput s J) _).mp (Fintype.mem_piFinset.mp hw)
      refine ⟨?_, hw'.2.1, hw'.2.2⟩
      intro i
      by_cases h : i ∈ J
      · rw [joinTuple_inl_mem J _ _ i h]; exact hu' ⟨i, h⟩
      · rw [joinTuple_inl_not_mem J _ _ i h]; exact hw'.1 ⟨i, h⟩
    have hFv : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w) := by
      have h := hF _ hv
      rwa [restPart_join] at h
    exact tuple_factor_masked_supplier_nocol s J A₁ A₂ Dc K R L F hLsq u hu w hFv
  rw [gauss_tuple_sum _ _ (fun I => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) k,
    box_sum]
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw =>
    term_identity_abstract s J A₁ A₂ Dc K R (residualSeed J L u) F τ t T u w _ (hβ u hu w hw) k))]
  simp only [Finset.sum_comm (s := Fintype.piFinset (residualInput s J).pools)
    (t := (Finset.univ : Finset RayCharacter))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [residual_tuple_form, Finset.mul_sum, Finset.mul_sum]

end Factor

/-- The supplier ball chain from an identity (T) with residual seeds, at ball radii. -/
theorem supplier_ball_from_identity (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ) (G : O → ℂ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) →
      (∀ k, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R (residualSeed J L u) F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k)) →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      ∑ z ∈ ballRows H, ‖G z‖ ^ 2 ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R L' I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re := by
  obtain ⟨Cf, hCf, hfibb⟩ := fiber_power_bound ε hε N
  refine ⟨256 * 256 * 128 ^ N * max 1 Cf, by positivity, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' G hH hH' hrad hhi hGid
  set G' := fun (ξ : RayCharacter) (L' : Ideal O) =>
    residualPolynomial s J A₁ A₂ Dc K R L' F τ t T ξ with hG'def
  let Ks : Finset O := if J.Nonempty then (ballRows H).erase 0 else ballRows H
  have hKs : Ks ⊆ ballRows H := by
    by_cases hJ : J.Nonempty
    · simp only [Ks, hJ, ↓reduceIte]; exact Finset.erase_subset _ _
    · simp only [Ks, hJ, ↓reduceIte]; exact le_refl _
  let lab : (J → Ideal O) × O → Ideal O × O :=
    fun q => (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2)
  let Rs := ((activeSel s J K R) ×ˢ Ks).image lab
  refine ⟨Rs.image Prod.fst, ?_, ?_⟩
  · intro L' hL'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL'
    obtain ⟨⟨u, k⟩, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hb, hw, _⟩ := activeSel_mem s J K R u (Finset.mem_product.mp hq).1
    exact residualSeed_dvd s J L u hb (sel_injective_of_weight s J K R u hb hw)
  have hG : ∀ k ∈ Ks, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ activeSel s J K R, selScalar s J K R τ t u χ k *
          G' ξ (residualSeed J L u) (primaryGenerator (selProduct J u) ^ 4 * k) := by
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
  have hrow : ∀ p ∈ Rs, normValue p.2 ≤ H' := by
    intro p hp
    obtain ⟨⟨u, z⟩, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hu, hz⟩ := Finset.mem_product.mp hq
    exact ball_row_norm s J K R H H' hrad u hu z (hKs hz)
  have hfib : ∀ p ∈ Rs, ((((activeSel s J K R) ×ˢ Ks).filter (fun q => lab q = p)).card : ℝ) ≤
      max 1 Cf * (max 1 H') ^ ε := by
    intro p hp
    have hpow1 : 1 ≤ (max 1 H') ^ ε := Real.one_le_rpow (le_max_left _ _) hε.le
    have hsub : ((activeSel s J K R) ×ˢ Ks).filter (fun q => lab q = p) ⊆
        ((activeSel s J K R) ×ˢ Ks).filter
          (fun q : (J → Ideal O) × O => primaryGenerator (∏ j, q.1 j) ^ 4 * q.2 = p.2) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq1, (congrArg Prod.snd hq2 : _)⟩
    have hsub' := Finset.card_le_card hsub
    by_cases hJ : J.Nonempty
    · obtain ⟨⟨u, z⟩, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hu, hz⟩ := Finset.mem_product.mp hq
      have hz0 : z ≠ 0 := by
        simp only [Ks, hJ, ↓reduceIte] at hz
        exact (Finset.mem_erase.mp hz).1
      have hD := (activeSel_mem s J K R u hu).2.2
      have hr0 : primaryGenerator (selProduct J u) ^ 4 * z ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (supported_primaryGenerator_ne_zero _ hD)) hz0
      have hc := selected_fiber_card (activeSel s J K R)
        (fun u hu => (activeSel_mem s J K R u hu).2.2) Ks _ hr0
      have hnorm := hrow _ hp
      calc
        _ ≤ ((((activeSel s J K R) ×ˢ Ks).filter
            (fun q : (J → Ideal O) × O =>
              primaryGenerator (∏ j, q.1 j) ^ 4 * q.2 = primaryGenerator (selProduct J u) ^ 4 * z)).card : ℝ) := by
          exact_mod_cast hsub'
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
      have hsub2 : ((activeSel s J K R) ×ˢ Ks).filter
          (fun q : (J → Ideal O) × O => primaryGenerator (∏ j, q.1 j) ^ 4 * q.2 = p.2) ⊆
          (activeSel s J K R) ×ˢ {p.2} := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        have hsel : (∏ j, q.1 j) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          exact absurd j.property (Finset.eq_empty_iff_forall_notMem.mp hJe j.val)
        rw [hsel, primaryGenerator_one, one_pow, one_mul] at hq2
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hq1).1, Finset.mem_singleton.mpr hq2⟩
      have hcard1 : (((activeSel s J K R) ×ˢ Ks).filter (fun q => lab q = p)).card ≤ 1 :=
        hsub'.trans ((Finset.card_le_card hsub2).trans
          (by rw [Finset.card_product, Finset.card_singleton, mul_one]; exact hU1))
      calc
        _ ≤ (1 : ℝ) := by exact_mod_cast hcard1
        _ ≤ max 1 Cf * (max 1 H') ^ ε := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow1
  have hfam := ray_family_energy_labeled (activeSel s J K R)
    (fun u => primaryGenerator (selProduct J u)) (fun u => residualSeed J L u) Ks
    (fun u χ k => selScalar s J K R τ t u χ k) G G' _ _ hG hα hfib
  -- the labelled rows are regrouped by residual seed
  set E' : RayCharacter → Ideal O → ℝ := fun ξ L' =>
    (gaussEnergy Finset.univ
      (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
      (sourceGenerator_supported (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
      (fun I : supportedColumns (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
        CoupledFirst.coefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L' I *
          ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
            rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re with hE'def
  change _ ≤ _ * ∑ ξ : RayCharacter, ∑ L' ∈ Rs.image Prod.fst, E' ξ L'
  have hres : ∀ ξ, ∑ p ∈ Rs, ‖G' ξ p.1 p.2‖ ^ 2 ≤ ∑ L' ∈ Rs.image Prod.fst, E' ξ L' := by
    intro ξ
    rw [labelled_rows_sum Rs (fun L' r => ‖G' ξ L' r‖ ^ 2)]
    apply Finset.sum_le_sum
    intro L' _
    apply finite_energy_le_gaussEnergy _ _ _ _ ballProfile H' hH'
    · intro z
      exact ballProfile_nonneg _
    · intro r hr
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      exact ballProfile_majorizes H' hH' p.2 (hrow p (Finset.mem_filter.mp hp).1)
  have hSig : ∑ ξ : RayCharacter, ∑ p ∈ Rs, ‖G' ξ p.1 p.2‖ ^ 2 ≤
      ∑ ξ : RayCharacter, ∑ L' ∈ Rs.image Prod.fst, E' ξ L' :=
    Finset.sum_le_sum (fun ξ _ => hres ξ)
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
        ∑ ξ : RayCharacter, ∑ L' ∈ Rs.image Prod.fst, E' ξ L' := by
      apply mul_le_mul _ hSig (Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg
        (fun r _ => sq_nonneg _))) (by positivity)
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left hmass' (by norm_num)
    _ = _ := by ring


/-- **Seed-supplier ball transfer of the no-collision part** (no (S), no (Col)). -/
theorem collet_main_selected_transfer_supplier_ball_nocol (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) → Squarefree L →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      ∃ seeds : Finset (Ideal O), (∀ L' ∈ seeds, L' ∣ L) ∧
      (gaussEnergy Finset.univ
          (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            finiteColumnCoefficient (Fintype.piFinset s.pools)
              (noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R L' I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re := by
  obtain ⟨C, hC, hb⟩ := supplier_ball_from_identity.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hLsq hF
  obtain ⟨seeds, hseeds, hbound⟩ := hb hcard s J A₁ A₂ Dc K R L F τ t T H H' _ hH hH' hrad hhi
    (transfer_identity_supplier_nocol s J A₁ A₂ Dc K R L F τ t T hLsq hF)
  exact ⟨seeds, hseeds, (ball_energy_le_sum _ _ _ _ H hH).trans hbound⟩

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.transfer_identity_supplier_nocol
#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_supplier_ball_nocol
