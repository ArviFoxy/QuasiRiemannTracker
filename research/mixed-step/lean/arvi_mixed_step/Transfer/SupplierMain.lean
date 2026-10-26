/- Mixed source step, L2 transfer: the transfer inequality without (S).

For a squarefree seed `L`, the original first-MAIN dyadic energy is bounded by
the energies of the residual sources with residual seeds `L' ∣ L`
(`L' = L/gcd(L,D)`), on finitely many labelled rows `(L', r)`. The constant and
the booking are the same as in `collet_main_selected_transfer`: the labels are
carried through the pushforward, so no divisor count of `L` is paid. -/
import Submissions.arvi_mixed_step.Transfer.Main
import Submissions.arvi_mixed_step.Transfer.SupplierIdentity

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstColumns RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source.Collision QRH.Record1252270103Source.High
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

/-- Pushforward with a uniform fibre bound, arbitrary codomain. -/
theorem pushforward_bound_gen {κ β : Type*} [DecidableEq β] (U : Finset κ) (Ks : Finset O) (φ : κ × O → β)
    (g : β → ℝ) (hg : ∀ r, 0 ≤ g r) (B : ℝ)
    (hfib : ∀ r ∈ (U ×ˢ Ks).image φ, (((U ×ˢ Ks).filter (fun p => φ p = r)).card : ℝ) ≤ B) :
    ∑ p ∈ U ×ˢ Ks, g (φ p) ≤ B * ∑ r ∈ (U ×ˢ Ks).image φ, g r := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem φ hp),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  calc
    _ = (((U ×ˢ Ks).filter (fun p => φ p = r)).card : ℝ) * g r := by
      rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B * g r := mul_le_mul_of_nonneg_right (hfib r hr) (hg r)

/-- The positive chain for a ray family whose residual polynomial depends on a
label of the selected assignment. -/
theorem ray_family_energy_labeled {κ Λ : Type*} [DecidableEq Λ] (U : Finset κ) (d : κ → O) (lab : κ → Λ)
    (Ks : Finset O) (α : κ → RayCharacter → O → ℂ) (G : O → ℂ)
    (G' : RayCharacter → Λ → O → ℂ) (A₀ B : ℝ)
    (hG : ∀ k ∈ Ks, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
      ∑ u ∈ U, α u χ k * G' ξ (lab u) (d u ^ 4 * k))
    (hα : ∀ u ∈ U, ∀ χ, ∀ k ∈ Ks, ‖α u χ k‖ ≤ A₀)
    (hfib : ∀ p ∈ (U ×ˢ Ks).image (fun q => (lab q.1, d q.1 ^ 4 * q.2)),
      (((U ×ˢ Ks).filter (fun q => (lab q.1, d q.1 ^ 4 * q.2) = p)).card : ℝ) ≤ B) :
    ∑ k ∈ Ks, ‖G k‖^2 ≤
      256 * 256 * ((U.card : ℝ) * A₀^2) * B *
        ∑ ξ, ∑ p ∈ (U ×ˢ Ks).image (fun q => (lab q.1, d q.1 ^ 4 * q.2)), ‖G' ξ p.1 p.2‖^2 := by
  set Rs := (U ×ˢ Ks).image (fun q => (lab q.1, d q.1 ^ 4 * q.2)) with hRs
  have hcard : (0:ℝ) ≤ (U.card : ℝ) * A₀^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hk : ∀ k ∈ Ks, ‖G k‖^2 ≤ 256 * ((U.card : ℝ) * A₀^2) *
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
        ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 := by
    intro k hk
    rw [hG k hk]
    refine (MixedSupplierPositive.first_ray_sq _).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ξ _
    have hc := CubicEisenstein.norm_sum_sq_le_card U
      (fun u => α u χ k * G' ξ (lab u) (d u ^ 4 * k))
    have hb : ∑ u ∈ U, ‖α u χ k * G' ξ (lab u) (d u ^ 4 * k)‖^2 ≤
        A₀^2 * ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hα u hu χ k hk) 2) (sq_nonneg _)
    calc
      _ ≤ ‖pairCoeff firstPhaseTable χ ξ‖ *
          ((U.card : ℝ) * (A₀^2 * ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2)) :=
        mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)))
          (norm_nonneg _)
      _ = _ := by ring
  have hY : ∀ ξ, ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 ≤
      B * ∑ p ∈ Rs, ‖G' ξ p.1 p.2‖^2 := by
    intro ξ
    have h1 : ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 =
        ∑ q ∈ U ×ˢ Ks, ‖G' ξ (lab q.1, d q.1 ^ 4 * q.2).1 (lab q.1, d q.1 ^ 4 * q.2).2‖^2 := by
      rw [Finset.sum_product, Finset.sum_comm]
    rw [h1]
    exact pushforward_bound_gen U Ks (fun q => (lab q.1, d q.1 ^ 4 * q.2))
      (fun p => ‖G' ξ p.1 p.2‖^2) (fun p => sq_nonneg _) B hfib
  have hB : ∀ ξ, 0 ≤ ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 :=
    fun ξ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun u _ => sq_nonneg _))
  calc
    _ ≤ ∑ k ∈ Ks, 256 * ((U.card : ℝ) * A₀^2) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
          ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 := Finset.sum_le_sum hk
    _ = 256 * ((U.card : ℝ) * A₀^2) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
          ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [Finset.mul_sum]
    _ ≤ 256 * ((U.card : ℝ) * A₀^2) *
        (256 * ∑ ξ, ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (lab u) (d u ^ 4 * k)‖^2) :=
      mul_le_mul_of_nonneg_left (pair_mass_bound _ hB) (mul_nonneg (by norm_num) hcard)
    _ ≤ 256 * ((U.card : ℝ) * A₀^2) * (256 * ∑ ξ, B * ∑ p ∈ Rs, ‖G' ξ p.1 p.2‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hcard)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun ξ _ => hY ξ)
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- **Fourth-power transfer at Collet's first MAIN layer without (S).** The
seed is only assumed squarefree; the residual sources carry the residual
seeds `p.1 ∣ L`. Hypotheses: (F)-invariance and (Col). -/
theorem collet_main_selected_transfer_supplier (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W : ℝ),
      dyadicScale n ≤ Z ^ M → (∏ j ∈ J, s.hi j * s.P j) ≤ W → Squarefree L →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      ∃ rows : Finset (Ideal O × O),
        (∀ p ∈ rows, p.1 ∣ L ∧ p.2 ≠ 0 ∧ normValue p.2 ≤ Z ^ M * W ^ 4) ∧
        (∑' h : O, dyadicWeight n (normValue h) *
          ‖gaussPolynomial Finset.univ
            (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) h‖ ^ 2) ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
          ∑ ξ : RayCharacter, ∑ p ∈ rows,
            ‖gaussPolynomial Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R p.1 I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) p.2‖ ^ 2 := by
  obtain ⟨Cf, hCf, hfibb⟩ := fiber_power_bound ε hε N
  refine ⟨256 * 256 * 128 ^ N * Cf, by positivity, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T n Z M W hdyad hW hLsq hF hCol
  change ∃ rows : Finset (Ideal O × O),
    (∀ p ∈ rows, p.1 ∣ L ∧ p.2 ≠ 0 ∧ normValue p.2 ≤ Z ^ M * W ^ 4) ∧
    (∑' h : O, dyadicWeight n (normValue h) *
      ‖originalPolynomial s A₁ A₂ Dc K R L F τ t T h‖ ^ 2) ≤
      (256 * 256 * 128 ^ N * Cf) * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
        ∑ ξ : RayCharacter, ∑ p ∈ rows,
          ‖residualPolynomial s J A₁ A₂ Dc K R p.1 F τ t T ξ p.2‖ ^ 2
  obtain ⟨rows, hrowsdef⟩ : ∃ rows : Finset (Ideal O × O), rows =
      ((activeSel s J K R) ×ˢ (dyadRows n)).image
        (fun q : (J → Ideal O) × O =>
          (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2)) :=
    ⟨_, rfl⟩
  have hrows : ∀ p ∈ rows, p.1 ∣ L ∧ p.2 ≠ 0 ∧ normValue p.2 ≤ Z ^ M * W ^ 4 := by
    intro p hp
    rw [hrowsdef] at hp
    obtain ⟨⟨u, k⟩, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hu, hk⟩ := Finset.mem_product.mp hq
    obtain ⟨hb, hw, _⟩ := activeSel_mem s J K R u hu
    exact ⟨residualSeed_dvd s J L u hb (sel_injective_of_weight s J K R u hb hw),
      row_norm_bound s J K R n Z M W hdyad hW u hu k hk⟩
  refine ⟨rows, hrows, ?_⟩
  have hZM : 0 < Z ^ M := by
    have h2 : 0 < dyadicScale n := by unfold dyadicScale; positivity
    exact h2.trans_le hdyad
  have hJN : Fintype.card J ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ J).trans hcard
  have hG : ∀ k ∈ dyadRows n, originalPolynomial s A₁ A₂ Dc K R L F τ t T k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ activeSel s J K R, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R (residualSeed J L u) F τ t T ξ
            (primaryGenerator (selProduct J u) ^ 4 * k) := by
    intro k _
    rw [transfer_identity_supplier s J A₁ A₂ Dc K R L F τ t T hLsq hF hCol k]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro ξ _
    rw [activeSel_sum]
  have hα : ∀ u ∈ activeSel s J K R, ∀ χ, ∀ k ∈ dyadRows n,
      ‖selScalar s J K R τ t u χ k‖ ≤
        (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val :=
    fun u hu χ k _ => selScalar_norm_le s J K R τ t u (activeSel_mem s J K R u hu).1 χ k
  have hfib : ∀ p ∈ ((activeSel s J K R) ×ˢ (dyadRows n)).image
        (fun q : (J → Ideal O) × O =>
          (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2)),
      ((((activeSel s J K R) ×ˢ (dyadRows n)).filter
        (fun q : (J → Ideal O) × O =>
          (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2) = p)).card : ℝ) ≤
        Cf * (Z ^ M * W ^ 4) ^ ε := by
    intro p hp
    have hp0 := hrows p (hrowsdef ▸ hp)
    have hsub : ((activeSel s J K R) ×ˢ (dyadRows n)).filter
        (fun q : (J → Ideal O) × O =>
          (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2) = p) ⊆
        ((activeSel s J K R) ×ˢ (dyadRows n)).filter
          (fun q : (J → Ideal O) × O => primaryGenerator (∏ j, q.1 j) ^ 4 * q.2 = p.2) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq1, (congrArg Prod.snd hq2 : _)⟩
    have hc := selected_fiber_card (activeSel s J K R)
      (fun u hu => (activeSel_mem s J K R u hu).2.2) (dyadRows n) p.2 hp0.2.1
    calc
      _ ≤ ((((activeSel s J K R) ×ˢ (dyadRows n)).filter
          (fun q : (J → Ideal O) × O => primaryGenerator (∏ j, q.1 j) ^ 4 * q.2 = p.2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {p.2})).card : ℝ) ^
          Fintype.card J := by
        exact_mod_cast hc
      _ ≤ Cf * (normValue p.2) ^ ε := hfibb _ hJN p.2 hp0.2.1
      _ ≤ Cf * (Z ^ M * W ^ 4) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold normValue; positivity) hp0.2.2 hε.le) hCf.le
  have hfam : ∑ k ∈ dyadRows n, ‖originalPolynomial s A₁ A₂ Dc K R L F τ t T k‖ ^ 2 ≤
      256 * 256 * (((activeSel s J K R).card : ℝ) *
        ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val) ^ 2) *
        (Cf * (Z ^ M * W ^ 4) ^ ε) *
        ∑ ξ : RayCharacter, ∑ p ∈ ((activeSel s J K R) ×ˢ (dyadRows n)).image
            (fun q : (J → Ideal O) × O =>
              (residualSeed J L q.1, primaryGenerator (selProduct J q.1) ^ 4 * q.2)),
          ‖residualPolynomial s J A₁ A₂ Dc K R p.1 F τ t T ξ p.2‖ ^ 2 :=
    ray_family_energy_labeled (activeSel s J K R) (fun u => primaryGenerator (selProduct J u))
      (fun u => residualSeed J L u) (dyadRows n) (fun u χ k => selScalar s J K R τ t u χ k)
      (originalPolynomial s A₁ A₂ Dc K R L F τ t T)
      (fun ξ L' => residualPolynomial s J A₁ A₂ Dc K R L' F τ t T ξ) _ _ hG hα hfib
  rw [← hrowsdef] at hfam
  have hSig : 0 ≤ ∑ ξ : RayCharacter, ∑ p ∈ rows,
      ‖residualPolynomial s J A₁ A₂ Dc K R p.1 F τ t T ξ p.2‖ ^ 2 :=
    Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun r _ => sq_nonneg _))
  have hB : 0 ≤ Cf * (Z ^ M * W ^ 4) ^ ε :=
    mul_nonneg hCf.le (Real.rpow_nonneg (mul_nonneg hZM.le (by positivity)) ε)
  refine (dyadic_energy_le_sum n _).trans (hfam.trans ?_)
  by_cases hne : (activeSel s J K R).Nonempty
  · have hmass := activeSel_mass s J K R hne
    have hprod : 0 ≤ ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
      Finset.prod_nonneg (fun j hj =>
        mul_nonneg (activeSel_hi_pos s J K R hne ⟨j, hj⟩).le (sq_nonneg _))
    have hpow : (128:ℝ) ^ J.card ≤ 128 ^ N :=
      pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ J).trans hcard)
    have hmass' : ((activeSel s J K R).card : ℝ) *
        ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val) ^ 2 ≤
        128 ^ N * ∏ j ∈ J, s.hi j * s.M j ^ 2 :=
      hmass.trans (mul_le_mul_of_nonneg_right hpow hprod)
    calc
      _ ≤ 256 * 256 * (128 ^ N * ∏ j ∈ J, s.hi j * s.M j ^ 2) * (Cf * (Z ^ M * W ^ 4) ^ ε) *
          ∑ ξ : RayCharacter, ∑ p ∈ rows,
            ‖residualPolynomial s J A₁ A₂ Dc K R p.1 F τ t T ξ p.2‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hSig
        apply mul_le_mul_of_nonneg_right _ hB
        exact mul_le_mul_of_nonneg_left hmass' (by norm_num)
      _ = _ := by ring
  · have hU : activeSel s J K R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hrows0 : rows = ∅ := by
      rw [hrowsdef, hU, Finset.empty_product, Finset.image_empty]
    rw [hrows0]
    simp only [Finset.sum_empty, Finset.sum_const_zero, mul_zero, le_refl]

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_supplier
