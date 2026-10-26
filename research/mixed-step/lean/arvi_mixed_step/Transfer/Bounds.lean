/- Copyright (c) 2026 Sil. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Adapted from Sil's FourthPower (PR 74, vendored in PR 76),
MixedSupplierPositive.lean: `selScalar_norm_le` follows `selected_scalar_norm`;
`activeSel`, `activeSel_card`, `activeSel_mass` follow `activeSelected`,
`active_selected_annular_card`, `normalized_selected_card`; `selWeight_norm_le`
follows `selected_weight_norm`; `fiber_power_bound` follows `selected_fiber_subpower`.
Changes: Collet's `Input` slot data replace Sil's `Data`; the scalar bound carries
the residual renormalization `(√∏_J P)⁻¹`; the count uses the slot support window
`hi·P` (constant 128); the fibre bound uses the divisor count of the output
frequency, uniformly in `m ≤ N`.

Mixed source step, L2 transfer: the concrete bounds feeding the positive chain.

* `selScalar_norm_le`: every selected scalar is at most `(√∏_J P)⁻¹ · ∏_J M`.
* `activeSel_mass`: the active selected count times the square of that bound is
  at most `128^{|J|} · ∏_{j∈J} hi_j M_j²`. This is the booking: the count
  `≈ ∏_J P_j` of the Cauchy–Schwarz step is cancelled by the residual
  renormalization `(√∏_J P)⁻¹`, so no power of `W` survives.
* `fiber_power_bound`: divisor-type fibre bound of the pushforward. -/
import Submissions.arvi_mixed_step.Transfer.Positive
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentLiveDomain CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization
open RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source.Collision QRH.Record1252270103TwoIdeal
open IdealMobiusDivisorSum
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem squarefreeIndicator_norm_le (I : Ideal O) : ‖squarefreeIndicator I‖ ≤ 1 := by
  unfold squarefreeIndicator
  split_ifs <;> simp

theorem coprimalityIndicator_norm_le (I J : Ideal O) : ‖coprimalityIndicator I J‖ ≤ 1 := by
  unfold coprimalityIndicator
  split_ifs <;> simp

theorem ite_one_zero_norm_le (p : Prop) [Decidable p] : ‖(if p then (1:ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

theorem inj_of_squarefree_prod {κ : Type*} [Fintype κ] [DecidableEq κ] (u : κ → Ideal O)
    (hp : ∀ j, Prime (u j)) (hs : Squarefree (∏ j, u j)) : Function.Injective u := by
  intro i j hij
  by_contra hne
  have h : u i * u j ∣ ∏ k, u k := by
    rw [← Finset.mul_prod_erase Finset.univ u (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) u
        (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [hij] at h
  exact (hp j).not_isUnit (hs (u j) h)

theorem M_prod_nonneg (s : Input ι) (J : Finset ι) : 0 ≤ ∏ j : J, s.M j.val :=
  Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.M_ge_one j.val))

theorem slotAmplitude_norm_le (s : Input ι) (J : Finset ι) (u : J → Ideal O)
    (hu : u ∈ selBox s J) : ‖slotAmplitude s J u‖ ≤ ∏ j : J, s.M j.val := by
  unfold slotAmplitude
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
    (fun j _ => s.coefficient_bound j.val (u j) (Fintype.mem_piFinset.mp hu j))

theorem selWeight_norm_le (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hu : u ∈ selBox s J) : ‖selWeight s J K R u‖ ≤ ∏ j : J, s.M j.val := by
  unfold selWeight
  rw [norm_mul, norm_mul, norm_mul]
  have h0 := M_prod_nonneg s J
  calc
    _ ≤ (∏ j : J, s.M j.val) * 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul (mul_le_mul (slotAmplitude_norm_le s J u hu)
        (squarefreeIndicator_norm_le _) (norm_nonneg _) h0)
        (coprimalityIndicator_norm_le _ _) (norm_nonneg _) (by positivity))
        (ite_one_zero_norm_le _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem selWeight_squarefree (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hw : selWeight s J K R u ≠ 0) : Squarefree (selProduct J u) := by
  by_contra hn
  apply hw
  simp only [selWeight, squarefreeIndicator, hn, ↓reduceIte, mul_zero, zero_mul]

theorem selWeight_slot_ne (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hw : selWeight s J K R u ≠ 0) (j : J) :
    s.W j.val ((Ideal.absNorm (u j) : ℝ) / s.P j.val) ≠ 0 := by
  have ha : slotAmplitude s J u ≠ 0 := by
    intro h
    apply hw
    simp only [selWeight, h, zero_mul]
  have hj := (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)
  exact right_ne_zero_of_mul hj

/-- The selected scalar bound `A₀ = (√∏_J P)⁻¹ ∏_J M`. -/
theorem selScalar_norm_le (s : Input ι) (J : Finset ι) (K R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) (u : J → Ideal O) (hu : u ∈ selBox s J)
    (χ : RayCharacter) (k : O) :
    ‖selScalar s J K R τ t u χ k‖ ≤
      (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val := by
  have h0 : 0 ≤ (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (M_prod_nonneg s J)
  by_cases hw : selWeight s J K R u = 0
  · simp only [selScalar, hw, mul_zero, zero_mul, norm_zero]
    exact h0
  by_cases hD : Supported (selProduct J u)
  · have hsq := selWeight_squarefree s J K R u hw
    have hinj := inj_of_squarefree_prod u
      (fun j => s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)) hsq
    have hg : ‖primaryGaussRow (selProduct J u) k‖ ≤ 1 :=
      MixedSupplierPositive.prime_product_gauss_norm u
        (fun j => s.prime j.val (u j) (Fintype.mem_piFinset.mp hu j)) hinj Finset.univ k
    have hr := CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all τ fixedBadMask 1 1 t
      (selProduct J u)
    have hc : ‖rayCharacter χ (primaryGenerator (selProduct J u))‖ ≤ 1 :=
      FiniteRayExpansion.norm_char_le_one χ _
    have hs : ‖((Real.sqrt (∏ j ∈ J, s.P j) : ℂ))⁻¹‖ = (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    unfold selScalar
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hs]
    have hW := selWeight_norm_le s J K R u hu
    have hi : 0 ≤ (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc
      _ ≤ (Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * (∏ j : J, s.M j.val) * 1 * (1 * 1) := by
        gcongr
      _ = _ := by ring
  · simp only [selScalar, primaryGaussRow_of_not_supported _ hD, mul_zero, norm_zero]
    exact h0

/-- Active selected assignments: nonzero selected weight and supported product. -/
def activeSel (s : Input ι) (J : Finset ι) (K R : Ideal O) : Finset (J → Ideal O) :=
  (selBox s J).filter (fun u => selWeight s J K R u ≠ 0 ∧ Supported (selProduct J u))

theorem activeSel_sum (s : Input ι) (J : Finset ι) (K R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) (χ : RayCharacter) (k : O) (f : (J → Ideal O) → ℂ) :
    ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k * f u =
      ∑ u ∈ activeSel s J K R, selScalar s J K R τ t u χ k * f u := by
  unfold activeSel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hw : selWeight s J K R u = 0
  · simp only [selScalar, hw, mul_zero, zero_mul, ne_eq, not_true_eq_false, false_and,
      ↓reduceIte]
  · by_cases hD : Supported (selProduct J u)
    · simp only [ne_eq, hw, not_false_eq_true, hD, and_self, ↓reduceIte]
    · simp only [selScalar, primaryGaussRow_of_not_supported _ hD, mul_zero, zero_mul, hD,
        and_false, ↓reduceIte]

theorem activeSel_mem (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hu : u ∈ activeSel s J K R) :
    u ∈ selBox s J ∧ selWeight s J K R u ≠ 0 ∧ Supported (selProduct J u) := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
  exact ⟨h1, h2⟩

theorem activeSel_slot_norm (s : Input ι) (J : Finset ι) (K R : Ideal O) (u : J → Ideal O)
    (hu : u ∈ activeSel s J K R) (j : J) :
    s.lo j.val * s.P j.val ≤ (Ideal.absNorm (u j) : ℝ) ∧
      (Ideal.absNorm (u j) : ℝ) ≤ s.hi j.val * s.P j.val := by
  obtain ⟨_, hw, _⟩ := activeSel_mem s J K R u hu
  have hsupp := s.support j.val (selWeight_slot_ne s J K R u hw j)
  have hP := s.P_pos j.val
  constructor
  · exact (le_div_iff₀ hP).mp hsupp.1
  · exact (div_le_iff₀ hP).mp hsupp.2

theorem activeSel_hi_pos (s : Input ι) (J : Finset ι) (K R : Ideal O)
    (hne : (activeSel s J K R).Nonempty) (j : J) : 0 < s.hi j.val := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨_, hw, _⟩ := activeSel_mem s J K R u hu
  have hsupp := s.support j.val (selWeight_slot_ne s J K R u hw j)
  exact (s.lo_pos j.val).trans_le (hsupp.1.trans hsupp.2)

theorem activeSel_card (s : Input ι) (J : Finset ι) (K R : Ideal O)
    (hne : (activeSel s J K R).Nonempty) :
    ((activeSel s J K R).card : ℝ) ≤ ∏ j : J, 128 * (s.hi j.val * s.P j.val) := by
  let T := Fintype.piFinset (fun j : J =>
    (s.slots j.val).filter (fun p => s.W j.val ((Ideal.absNorm p : ℝ) / s.P j.val) ≠ 0))
  have hsub : activeSel s J K R ⊆ T := by
    intro u hu
    obtain ⟨hb, hw, _⟩ := activeSel_mem s J K R u hu
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hb j, selWeight_slot_ne s J K R u hw j⟩
  have hcount (j : J) : (((s.slots j.val).filter
      (fun p => s.W j.val ((Ideal.absNorm p : ℝ) / s.P j.val) ≠ 0)).card : ℝ) ≤
      128 * (s.hi j.val * s.P j.val) := by
    apply ProbeSelectedPrimeSums.finite_ideal_count
    · exact mul_nonneg (activeSel_hi_pos s J K R hne j).le (s.P_pos j.val).le
    · intro I hI
      exact (s.prime j.val I (Finset.mem_filter.mp hI).1).ne_zero
    · intro I hI
      have hsupp := s.support j.val (Finset.mem_filter.mp hI).2
      exact (div_le_iff₀ (s.P_pos j.val)).mp hsupp.2
  calc
    _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ∏ j : J, (((s.slots j.val).filter
          (fun p => s.W j.val ((Ideal.absNorm p : ℝ) / s.P j.val) ≠ 0)).card : ℝ) := by
      rw [Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hcount j)

/-- **The booking.** Count × (selected scalar bound)² carries no net `∏_J P`. -/
theorem activeSel_mass (s : Input ι) (J : Finset ι) (K R : Ideal O)
    (hne : (activeSel s J K R).Nonempty) :
    ((activeSel s J K R).card : ℝ) *
        ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val)^2 ≤
      128 ^ J.card * ∏ j ∈ J, s.hi j * s.M j ^ 2 := by
  have hWP : (0:ℝ) < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hsq : ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹)^2 = (∏ j ∈ J, s.P j)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hWP.le]
  have hPcoe : (∏ j ∈ J, s.P j) = ∏ j : J, s.P j.val := (Finset.prod_coe_sort J s.P).symm
  have hHcoe : (∏ j ∈ J, s.hi j * s.M j ^ 2) = ∏ j : J, s.hi j.val * s.M j.val ^ 2 :=
    (Finset.prod_coe_sort J (fun j => s.hi j * s.M j ^ 2)).symm
  calc
    _ ≤ (∏ j : J, 128 * (s.hi j.val * s.P j.val)) *
        ((Real.sqrt (∏ j ∈ J, s.P j))⁻¹ * ∏ j : J, s.M j.val)^2 :=
      mul_le_mul_of_nonneg_right (activeSel_card s J K R hne) (sq_nonneg _)
    _ = 128 ^ J.card * ∏ j ∈ J, s.hi j * s.M j ^ 2 := by
      rw [mul_pow, hsq, hHcoe, hPcoe]
      have hP' : (0:ℝ) < ∏ j : J, s.P j.val := hPcoe ▸ hWP
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow,
        Fintype.card_coe]
      field_simp

/-- Divisor-type fibre bound, uniform in the number of selected slots. -/
theorem fiber_power_bound (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ m : ℕ, m ≤ N → ∀ r : O, r ≠ 0 →
      ((idealDivisors (Ideal.span {r})).card : ℝ) ^ m ≤ Cf * (normValue r) ^ ε := by
  have hδ : 0 < ε / (N + 1) := div_pos hε (by positivity)
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / (N + 1)) hδ
  refine ⟨(max 1 C) ^ N, pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) N, ?_⟩
  intro m hm r hr
  have hI : (Ideal.span {r} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr
  have hx : 1 ≤ normValue r := normValue_ge_one r hr
  have hx0 : 0 ≤ normValue r := zero_le_one.trans hx
  have hd := hdiv _ hI
  change _ ≤ C * (normValue r) ^ (ε / (N + 1)) at hd
  have hC1 : 1 ≤ max 1 C := le_max_left _ _
  have hd' : ((idealDivisors (Ideal.span {r})).card : ℝ) ≤
      max 1 C * (normValue r) ^ (ε / (N + 1)) :=
    hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0 _))
  have hexp : ε / (N + 1) * m ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (m:ℝ) ≤ N := by exact_mod_cast hm
    nlinarith
  calc
    _ ≤ (max 1 C * (normValue r) ^ (ε / (N + 1))) ^ m :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hd' m
    _ = (max 1 C) ^ m * (normValue r) ^ (ε / (N + 1) * m) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (normValue r ^ (ε / (N + 1))) m, ← Real.rpow_mul hx0]
    _ ≤ (max 1 C) ^ N * (normValue r) ^ ε :=
      mul_le_mul (pow_le_pow_right₀ hC1 hm) (Real.rpow_le_rpow_of_exponent_le hx hexp)
        (Real.rpow_nonneg hx0 _) (pow_nonneg (zero_le_one.trans hC1) N)

end
end QRH.MixedStep.Transfer
