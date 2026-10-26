/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Sil's FourthPower (PR 74, vendored in PR 76): `ray_family_energy`
follows `fourth_family_sq` (MixedSupplierPositive.lean: `first_ray_sq`, then
Cauchy-Schwarz over the selected assignments); `pushforward_bound` follows the
fibre count of `weighted_pushforward` and `selected_fiber_card` follows `fiber_card`
(PositiveFamily.lean). Changes: stated for an abstract ray-family identity with a
uniform scalar bound `A₀` (no grouping by `D`); the fibre bound is a hypothesis;
`selected_fiber_card` counts fibres of `(u,k) ↦ d(u)⁴k` over tuples of slot primes.

Mixed source step, L2 transfer: the positive chain after the identity (T).

Given an exact ray-family identity
  G(k) = Σ_{χ,ξ} π_{χξ} Σ_{u ∈ U} α(u,χ,k) · G'_ξ(d(u)⁴ k),
weighted Cauchy–Schwarz over (χ,ξ), Cauchy–Schwarz over `u`, and the
pushforward `(u,k) ↦ d(u)⁴ k` with bounded fibres give
  Σ_k ‖G k‖² ≤ 256² · (#U · A₀²) · B · Σ_ξ Σ_{r ∈ image} ‖G'_ξ r‖².
`A₀` bounds the selected scalars and `B` the fibres; the count `#U` is paid
by `A₀²` (this is where the renormalization of the residual enters). -/
import Submissions.arvi_mixed_step.Transfer.Identity
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierPositive

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentFirstColumns RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open IdealMobiusDivisorSum
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

/-- Weighted ray mass: charging the phase table once. -/
theorem pair_mass_bound (X : RayCharacter → ℝ) (hX : ∀ ξ, 0 ≤ X ξ) :
    ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ * X ξ ≤
      256 * ∑ ξ, X ξ := by
  have hsum : 0 ≤ ∑ ξ, X ξ := Finset.sum_nonneg (fun ξ _ => hX ξ)
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ * ∑ ξ', X ξ' := by
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ξ _
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun ξ' _ => hX ξ') (Finset.mem_univ ξ)) (norm_nonneg _)
    _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖) * ∑ ξ', X ξ' := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_mul]
    _ ≤ 256 * ∑ ξ, X ξ := mul_le_mul_of_nonneg_right firstPhaseTable_mass hsum

/-- Pushforward with a uniform fibre bound. -/
theorem pushforward_bound {κ : Type*} (U : Finset κ) (Ks : Finset O) (φ : κ × O → O)
    (g : O → ℝ) (hg : ∀ r, 0 ≤ g r) (B : ℝ)
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

/-- The generic positive chain for a ray family. -/
theorem ray_family_energy {κ : Type*} (U : Finset κ) (d : κ → O) (Ks : Finset O)
    (α : κ → RayCharacter → O → ℂ) (G : O → ℂ) (G' : RayCharacter → O → ℂ) (A₀ B : ℝ)
    (hG : ∀ k ∈ Ks, G k = ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
      ∑ u ∈ U, α u χ k * G' ξ (d u ^ 4 * k))
    (hα : ∀ u ∈ U, ∀ χ, ∀ k ∈ Ks, ‖α u χ k‖ ≤ A₀)
    (hfib : ∀ r ∈ (U ×ˢ Ks).image (fun p => d p.1 ^ 4 * p.2),
      (((U ×ˢ Ks).filter (fun p => d p.1 ^ 4 * p.2 = r)).card : ℝ) ≤ B) :
    ∑ k ∈ Ks, ‖G k‖^2 ≤
      256 * 256 * ((U.card : ℝ) * A₀^2) * B *
        ∑ ξ, ∑ r ∈ (U ×ˢ Ks).image (fun p => d p.1 ^ 4 * p.2), ‖G' ξ r‖^2 := by
  set Rs := (U ×ˢ Ks).image (fun p => d p.1 ^ 4 * p.2) with hRs
  have hcard : (0:ℝ) ≤ (U.card : ℝ) * A₀^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  -- per frequency
  have hk : ∀ k ∈ Ks, ‖G k‖^2 ≤ 256 * ((U.card : ℝ) * A₀^2) *
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
        ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 := by
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
    have hc := CubicEisenstein.norm_sum_sq_le_card U (fun u => α u χ k * G' ξ (d u ^ 4 * k))
    have hb : ∑ u ∈ U, ‖α u χ k * G' ξ (d u ^ 4 * k)‖^2 ≤
        A₀^2 * ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hα u hu χ k hk) 2) (sq_nonneg _)
    calc
      _ ≤ ‖pairCoeff firstPhaseTable χ ξ‖ *
          ((U.card : ℝ) * (A₀^2 * ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2)) :=
        mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)))
          (norm_nonneg _)
      _ = _ := by ring
  -- pushforward for each ξ
  have hY : ∀ ξ, ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 ≤
      B * ∑ r ∈ Rs, ‖G' ξ r‖^2 := by
    intro ξ
    have h1 : ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 =
        ∑ p ∈ U ×ˢ Ks, ‖G' ξ (d p.1 ^ 4 * p.2)‖^2 := by
      rw [Finset.sum_product, Finset.sum_comm]
    rw [h1]
    exact pushforward_bound U Ks (fun p => d p.1 ^ 4 * p.2) (fun r => ‖G' ξ r‖^2)
      (fun r => sq_nonneg _) B hfib
  have hB : ∀ ξ, 0 ≤ ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 :=
    fun ξ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun u _ => sq_nonneg _))
  calc
    _ ≤ ∑ k ∈ Ks, 256 * ((U.card : ℝ) * A₀^2) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
          ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 := Finset.sum_le_sum hk
    _ = 256 * ((U.card : ℝ) * A₀^2) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖ *
          ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [Finset.mul_sum]
    _ ≤ 256 * ((U.card : ℝ) * A₀^2) * (256 * ∑ ξ, ∑ k ∈ Ks, ∑ u ∈ U, ‖G' ξ (d u ^ 4 * k)‖^2) :=
      mul_le_mul_of_nonneg_left (pair_mass_bound _ hB) (mul_nonneg (by norm_num) hcard)
    _ ≤ 256 * ((U.card : ℝ) * A₀^2) * (256 * ∑ ξ, B * ∑ r ∈ Rs, ‖G' ξ r‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hcard)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun ξ _ => hY ξ)
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- Fibres of `(u,k) ↦ d(u)⁴ k` over a nonzero output: every selected prime
divides the output, so the fibre is bounded by a power of the divisor count. -/
theorem selected_fiber_card {κ : Type*} [Fintype κ] (U : Finset (κ → Ideal O))
    (hU : ∀ u ∈ U, Supported (∏ j, u j)) (Ks : Finset O) (r : O) (hr : r ≠ 0) :
    ((U ×ˢ Ks).filter (fun p => (primaryGenerator (∏ j, p.1 j))^4 * p.2 = r)).card ≤
      (idealDivisors (Ideal.span {r})).card ^ Fintype.card κ := by
  have hI : (Ideal.span {r} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr
  calc
    _ ≤ (Fintype.piFinset (fun _ : κ => idealDivisors (Ideal.span {r}))).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        obtain ⟨hp, hfreq⟩ := Finset.mem_filter.mp hp
        have hs := hU p.1 (Finset.mem_product.mp hp).1
        have hspan : Ideal.span {r} = (∏ j, p.1 j)^4 * Ideal.span {p.2} := by
          rw [← hfreq]
          exact PositiveFamily.frequency_span _ hs p.2
        apply Fintype.mem_piFinset.mpr
        intro j
        apply (mem_idealDivisors hI).mpr
        rw [hspan]
        exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
          ((dvd_pow_self _ (by norm_num)).mul_right _)
      · intro p hp q hq hpq
        apply Prod.ext hpq
        have h1 := (Finset.mem_filter.mp hp).2
        have h2 := (Finset.mem_filter.mp hq).2
        have hq0 := hU q.1 (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
        rw [← h2, hpq] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (supported_primaryGenerator_ne_zero _ hq0)) h1
    _ = _ := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

end
end QRH.MixedStep.Transfer
