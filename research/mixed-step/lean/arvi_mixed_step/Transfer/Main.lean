/- Copyright (c) 2026 Sil. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
`row_norm_bound` adapts Sil's `frequency_norm_bound` (FourthPower/PositiveFamily.lean,
PR 74, vendored in PR 76) to the slot window `∏_J hi·P`. The rest is new in this
submission and uses Sil's, Collet's and the baseline's lemmas by import.

Mixed source step, L2 transfer: the fourth-power transfer inequality at
Collet's first MAIN layer.

The dyadic energy of Collet's child source (coefficient normalized by `√T`)
is bounded by

  C · (∏_{j∈J} hi_j M_j²) · (Z^M W⁴)^ε · Σ_ξ Σ_{r ∈ rows} ‖G'_ξ(r)‖²,

where `G'_ξ` is the residual source on `{i // i ∉ J}` (coefficient normalized
by `√(T/∏_J P)`, Hecke character `childCharacter τ ξ`), and `rows` is a finite
set of nonzero frequencies of norm at most `Z^M W⁴`. The constant `C` depends
only on `ε` and the slot bound `N`. There is no factor `W = ∏_J P_j` in
front: the Cauchy–Schwarz count `≈ ∏_J hi_j P_j` is paid by the residual
renormalization `(√∏_J P)⁻¹²` (see `activeSel_mass`).

Hypotheses: (S) no selected slot prime divides the seed `L`; (F) the
whole-column multiplier is invariant under the selected product (trivial for
`F = 1`, the first MAIN layer); (Col) on nonzero original tuples the selected
product is coprime to the ordinary pair. -/
import Submissions.arvi_mixed_step.Transfer.Bounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

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

/-- Row norm bound for the pushed-forward frequencies. -/
theorem row_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (J : Finset ι)
    (K R : Ideal O) (n : ℤ) (Z M W : ℝ) (hdyad : dyadicScale n ≤ Z ^ M)
    (hW : (∏ j ∈ J, s.hi j * s.P j) ≤ W) (u : J → Ideal O) (hu : u ∈ activeSel s J K R)
    (k : O) (hk : k ∈ dyadRows n) :
    primaryGenerator (selProduct J u) ^ 4 * k ≠ 0 ∧
      normValue (primaryGenerator (selProduct J u) ^ 4 * k) ≤ Z ^ M * W ^ 4 := by
  obtain ⟨_, _, hD⟩ := activeSel_mem s J K R u hu
  refine ⟨mul_ne_zero (pow_ne_zero _ (supported_primaryGenerator_ne_zero _ hD))
    (dyadRows_ne_zero n k hk), ?_⟩
  have hspan := PositiveFamily.frequency_span (selProduct J u) hD k
  have hN : normValue (primaryGenerator (selProduct J u) ^ 4 * k) =
      (Ideal.absNorm (selProduct J u) : ℝ) ^ 4 * normValue k := by
    unfold normValue
    rw [show primaryGenerator (selProduct J u) ^ 4 * k =
      PositiveFamily.frequency (selProduct J u, k) from rfl, hspan, map_mul, map_pow]
    push_cast
    ring
  have hDn : (Ideal.absNorm (selProduct J u) : ℝ) ≤ W := by
    calc
      (Ideal.absNorm (selProduct J u) : ℝ) = ∏ j : J, (Ideal.absNorm (u j) : ℝ) := by
        unfold selProduct
        rw [map_prod, Nat.cast_prod]
      _ ≤ ∏ j : J, s.hi j.val * s.P j.val :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
          (fun j _ => (activeSel_slot_norm s J K R u hu j).2)
      _ = ∏ j ∈ J, s.hi j * s.P j := Finset.prod_coe_sort J (fun j => s.hi j * s.P j)
      _ ≤ W := hW
  have hkn : normValue k ≤ Z ^ M := (dyadRows_norm_lt n k hk).le.trans hdyad
  have hW0 : 0 ≤ W := (Nat.cast_nonneg _).trans hDn
  rw [hN]
  calc
    _ ≤ W ^ 4 * Z ^ M :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hDn 4) hkn
        (by unfold normValue; positivity) (by positivity)
    _ = Z ^ M * W ^ 4 := by ring

/-- **Fourth-power transfer at Collet's first MAIN layer** (statement (T) of
the mixed source step), with a general whole-column multiplier `F` and the
tuple-level seed condition (S'). -/
theorem collet_main_selected_transfer_gen (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W : ℝ),
      dyadicScale n ≤ Z ^ M → (∏ j ∈ J, s.hi j * s.P j) ≤ W →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime L (∏ j ∈ J, v (Sum.inl j))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      ∃ rows : Finset O, (∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ Z ^ M * W ^ 4) ∧
        (∑' h : O, dyadicWeight n (normValue h) *
          ‖gaussPolynomial Finset.univ
            (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) h‖ ^ 2) ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
          ∑ ξ : RayCharacter, ∑ r ∈ rows,
            ‖gaussPolynomial Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R L I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) r‖ ^ 2 := by
  obtain ⟨Cf, hCf, hfibb⟩ := fiber_power_bound ε hε N
  refine ⟨256 * 256 * 128 ^ N * Cf, by positivity, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T n Z M W hdyad hW hS hF hCol
  change ∃ rows : Finset O, (∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ Z ^ M * W ^ 4) ∧
    (∑' h : O, dyadicWeight n (normValue h) *
      ‖originalPolynomial s A₁ A₂ Dc K R L F τ t T h‖ ^ 2) ≤
      (256 * 256 * 128 ^ N * Cf) * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
        ∑ ξ : RayCharacter, ∑ r ∈ rows,
          ‖residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ r‖ ^ 2
  obtain ⟨rows, hrowsdef⟩ : ∃ rows : Finset O, rows =
      ((activeSel s J K R) ×ˢ (dyadRows n)).image
        (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2) :=
    ⟨_, rfl⟩
  have hrows : ∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ Z ^ M * W ^ 4 := by
    intro r hr
    rw [hrowsdef] at hr
    obtain ⟨⟨u, k⟩, hp, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hu, hk⟩ := Finset.mem_product.mp hp
    exact row_norm_bound s J K R n Z M W hdyad hW u hu k hk
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
          residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ
            (primaryGenerator (selProduct J u) ^ 4 * k) := by
    intro k _
    rw [transfer_identity s J A₁ A₂ Dc K R L F τ t T hS hF hCol k]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro ξ _
    rw [activeSel_sum]
  have hα : ∀ u ∈ activeSel s J K R, ∀ χ, ∀ k ∈ dyadRows n,
      ‖selScalar s J K R τ t u χ k‖ ≤
        (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val :=
    fun u hu χ k _ => selScalar_norm_le s J K R τ t u (activeSel_mem s J K R u hu).1 χ k
  have hfib : ∀ r ∈ ((activeSel s J K R) ×ˢ (dyadRows n)).image
        (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
      ((((activeSel s J K R) ×ˢ (dyadRows n)).filter
        (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2 = r)).card : ℝ) ≤
        Cf * (Z ^ M * W ^ 4) ^ ε := by
    intro r hr
    have hr0 := hrows r (hrowsdef ▸ hr)
    have hc := selected_fiber_card (activeSel s J K R)
      (fun u hu => (activeSel_mem s J K R u hu).2.2) (dyadRows n) r hr0.1
    calc
      _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {r})).card : ℝ) ^ Fintype.card J := by
        exact_mod_cast hc
      _ ≤ Cf * (normValue r) ^ ε := hfibb _ hJN r hr0.1
      _ ≤ Cf * (Z ^ M * W ^ 4) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by unfold normValue; positivity) hr0.2 hε.le) hCf.le
  have hfam : ∑ k ∈ dyadRows n, ‖originalPolynomial s A₁ A₂ Dc K R L F τ t T k‖ ^ 2 ≤
      256 * 256 * (((activeSel s J K R).card : ℝ) *
        ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val) ^ 2) *
        (Cf * (Z ^ M * W ^ 4) ^ ε) *
        ∑ ξ : RayCharacter, ∑ r ∈ ((activeSel s J K R) ×ˢ (dyadRows n)).image
            (fun p : (J → Ideal O) × O => primaryGenerator (selProduct J p.1) ^ 4 * p.2),
          ‖residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ r‖ ^ 2 :=
    ray_family_energy (activeSel s J K R) (fun u => primaryGenerator (selProduct J u))
      (dyadRows n) (fun u χ k => selScalar s J K R τ t u χ k)
      (originalPolynomial s A₁ A₂ Dc K R L F τ t T)
      (residualPolynomial s J A₁ A₂ Dc K R L F τ t T) _ _ hG hα hfib
  rw [← hrowsdef] at hfam
  have hSig : 0 ≤ ∑ ξ : RayCharacter, ∑ r ∈ rows,
      ‖residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ r‖ ^ 2 :=
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
          ∑ ξ : RayCharacter, ∑ r ∈ rows,
            ‖residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ r‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hSig
        apply mul_le_mul_of_nonneg_right _ hB
        exact mul_le_mul_of_nonneg_left hmass' (by norm_num)
      _ = _ := by ring
  · have hU : activeSel s J K R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hrows0 : rows = ∅ := by
      rw [hrowsdef, hU, Finset.empty_product, Finset.image_empty]
    rw [hrows0]
    simp only [Finset.sum_empty, Finset.sum_const_zero, mul_zero, le_refl]

/-- **Fourth-power transfer at Collet's first MAIN layer** under the pool-level
(S): no selected slot prime divides the seed `L`. -/
theorem collet_main_selected_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W : ℝ),
      dyadicScale n ≤ Z ^ M → (∏ j ∈ J, s.hi j * s.P j) ≤ W →
      (∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L) →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      ∃ rows : Finset O, (∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ Z ^ M * W ^ 4) ∧
        (∑' h : O, dyadicWeight n (normValue h) *
          ‖gaussPolynomial Finset.univ
            (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) h‖ ^ 2) ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
          ∑ ξ : RayCharacter, ∑ r ∈ rows,
            ‖gaussPolynomial Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K F) R L I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) r‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := collet_main_selected_transfer_gen.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T n Z M W hdyad hW hS hF hCol
  exact h hcard s J A₁ A₂ Dc K R L F τ t T n Z M W hdyad hW
    (fun v hv _ => seed_free_of_slots s J L hS v hv) hF hCol

/-- The first-MAIN-layer form (`F = 1`): only (S) and (Col) are assumed. -/
theorem collet_main_selected_transfer_one (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W : ℝ),
      dyadicScale n ≤ Z ^ M → (∏ j ∈ J, s.hi j * s.P j) ≤ W →
      (∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      ∃ rows : Finset O, (∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ Z ^ M * W ^ 4) ∧
        (∑' h : O, dyadicWeight n (normValue h) *
          ‖gaussPolynomial Finset.univ
            (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) h‖ ^ 2) ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
          ∑ ξ : RayCharacter, ∑ r ∈ rows,
            ‖gaussPolynomial Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                    (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) r‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := collet_main_selected_transfer.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L τ t T n Z M W hdyad hW hS hCol
  exact h hcard s J A₁ A₂ Dc K R L (fun _ => 1) τ t T n Z M W hdyad hW hS
    (fun _ _ => rfl) hCol

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_gen
#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer
#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_one
