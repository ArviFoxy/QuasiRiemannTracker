/- Mixed source step, L3 interface: new in this submission; uses the Collision/ lemmas
(Collision/Family.lean and below, by import) and Collet's definitions.

Facts for bounding the collision part left by `transfer_waist_split`:

* `collision_family_energy_div`: in `collision_family_energy` the Cauchy-Schwarz
  over the colliding primes costs only the number of them dividing the frequency,
  because each collision polynomial vanishes off `p·O`. The factor `#T` (the count
  of colliding primes, the plan's `W_C`) becomes a bound `B` on the divisor count of
  the frequencies, i.e. `≤ C_ε N(H)^ε`.
* `divisor_assignments_card`: the same count for assignments `u` of a pattern
  (`∏ u_j ∣ H`), at most `d(H)^{|C|}`.
* `collisionWeight_sum` (the weight check of design §7): with
  `ω_C(D) = Σ_{u : D_u = D} |selWeight(u)|² / ∏_{j∈C} P_j`, one has
  `Σ_D ω_C(D) ≤ 128^{|C|} · ∏_{j∈C} hi_j M_j²`; no `Z^ε` is needed in the weights. -/
import Submissions.arvi_mixed_step.Collision.Family
import Submissions.arvi_mixed_step.Transfer.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentGaussEnergy
open CanonicalQuadraticSieve IdealMobiusDivisorSum
open QRH.MixedStep.Transfer QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O

/-- **Collision family, divisor-count Cauchy-Schwarz.** Only the colliding primes
dividing the frequency contribute, so the cost is the divisor count, not `#T`. -/
theorem collision_family_energy_div {β α : Type*} (T : Finset β) (S : β → Finset α)
    (m : β → α → O) (p : β → O) (hp : ∀ x, Prime (p x)) (hsp : ∀ x, Supported (Ideal.span {p x}))
    (hm : ∀ x i, Supported (Ideal.span {m x i})) (hcop : ∀ x i, IsCoprime (p x) (m x i))
    (hinj : Set.InjOn (fun x => Ideal.span {p x}) T)
    (c : β → α → ℂ) (R : Finset O) (w : O → ℝ) (hw : ∀ H, 0 ≤ w H) (B : ℝ) (hB0 : 0 ≤ B)
    (hR : ∀ H ∈ R, H ≠ 0)
    (hB : ∀ H ∈ R, ((idealDivisors (Ideal.span {H})).card : ℝ) ≤ B) :
    ∑ H ∈ R, w H * ‖∑ x ∈ T, gaussPolynomial (S x) (fun i => (p x)^2*m x i)
        (fun i => supported_sq_mul (p x) (m x i) (hsp x) (hm x i)) (c x) H‖^2 ≤
      B * ∑ x ∈ T, (Ideal.absNorm (Ideal.span {p x}) : ℝ) *
        ∑ H' ∈ R.preimage (fun H' => p x*H')
            ((mul_left_injective_of_ne_zero (p x) (hp x).ne_zero).injOn),
          w (p x*H') * ‖gaussPolynomial (S x) (m x) (hm x)
            (fun i => c x i * collisionPhase (p x) (m x i)) H'‖^2 := by
  set G := fun (x : β) (H : O) => gaussPolynomial (S x) (fun i => (p x)^2*m x i)
    (fun i => supported_sq_mul (p x) (m x i) (hsp x) (hm x i)) (c x) H with hGdef
  have hfreq : ∀ H ∈ R, ‖∑ x ∈ T, G x H‖^2 ≤ B * ∑ x ∈ T, ‖G x H‖^2 := by
    intro H hH
    have hsum : ∑ x ∈ T, G x H = ∑ x ∈ T.filter (fun x => p x ∣ H), G x H := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : p x ∣ H
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte, hGdef]
        exact collision_poly_zero (S x) (m x) (p x) (hp x) (hsp x) (hm x) (hcop x) (c x) H h
    have hI : (Ideal.span {H} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (hR H hH)
    have hcard : ((T.filter (fun x => p x ∣ H)).card : ℝ) ≤ B := by
      have hc : (T.filter (fun x => p x ∣ H)).card ≤ (idealDivisors (Ideal.span {H})).card := by
        apply Finset.card_le_card_of_injOn (fun x => Ideal.span {p x})
        · intro x hx
          apply (mem_idealDivisors hI).mpr
          exact Ideal.span_singleton_le_span_singleton.mpr (Finset.mem_filter.mp hx).2 |>
            Ideal.dvd_iff_le.mpr
        · exact hinj.mono (fun x hx => (Finset.mem_filter.mp hx).1)
      exact (Nat.cast_le.mpr hc).trans (hB H hH)
    have hsub : ∑ x ∈ T.filter (fun x => p x ∣ H), ‖G x H‖^2 ≤ ∑ x ∈ T, ‖G x H‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => sq_nonneg _)
    rw [hsum]
    calc
      _ ≤ ((T.filter (fun x => p x ∣ H)).card : ℝ) *
          ∑ x ∈ T.filter (fun x => p x ∣ H), ‖G x H‖^2 :=
        Collision.norm_sum_sq_le_card _ _
      _ ≤ B * ∑ x ∈ T, ‖G x H‖^2 :=
        mul_le_mul hcard hsub (Finset.sum_nonneg (fun x _ => sq_nonneg _)) hB0
  calc
    _ ≤ ∑ H ∈ R, w H * (B * ∑ x ∈ T, ‖G x H‖^2) :=
      Finset.sum_le_sum (fun H hH => mul_le_mul_of_nonneg_left (hfreq H hH) (hw H))
    _ = B * ∑ x ∈ T, ∑ H ∈ R, w H * ‖G x H‖^2 := by
      have hH : ∀ H, w H * (B * ∑ x ∈ T, ‖G x H‖^2) = B * ∑ x ∈ T, w H * ‖G x H‖^2 := by
        intro H
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [Finset.sum_congr rfl (fun H _ => hH H), ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB0
      apply Finset.sum_le_sum
      intro x _
      exact collision_energy (S x) (m x) (p x) (hp x) (hsp x) (hm x) (hcop x) (c x) R w hw

/-- Assignments of a collision pattern whose product divides a given ideal. -/
theorem divisor_assignments_card {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Finset (κ → Ideal O)) (Hc : Ideal O) (hH : Hc ≠ ⊥) :
    (U.filter (fun u => (∏ j, u j) ∣ Hc)).card ≤ (idealDivisors Hc).card ^ Fintype.card κ := by
  calc
    _ ≤ (Fintype.piFinset (fun _ : κ => idealDivisors Hc)).card := by
      apply Finset.card_le_card_of_injOn id
      · intro u hu
        apply Fintype.mem_piFinset.mpr
        intro j
        apply (mem_idealDivisors hH).mpr
        exact (Finset.dvd_prod_of_mem u (Finset.mem_univ j)).trans (Finset.mem_filter.mp hu).2
      · intro u _ v _ h
        exact h
    _ = _ := by rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The collision weight of a selected product `D` for the pattern `C`. -/
def collisionWeight (s : Input ι) (C : Finset ι) (K R D : Ideal O) : ℝ :=
  (∑ u ∈ (activeSel s C K R).filter (fun u => selProduct C u = D), ‖selWeight s C K R u‖ ^ 2) /
    ∏ j ∈ C, s.P j

/-- **The weight check.** The collision weights sum to a bounded quantity. -/
theorem collisionWeight_sum (s : Input ι) (C : Finset ι) (K R : Ideal O)
    (hhi : ∀ j ∈ C, 0 ≤ s.hi j) :
    ∑ D ∈ (activeSel s C K R).image (selProduct C), collisionWeight s C K R D ≤
      128 ^ C.card * ∏ j ∈ C, s.hi j * s.M j ^ 2 := by
  have hP : 0 < ∏ j ∈ C, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  unfold collisionWeight
  rw [← Finset.sum_div, Finset.sum_fiberwise_of_maps_to
    (fun u hu => Finset.mem_image_of_mem (selProduct C) hu)]
  by_cases hne : (activeSel s C K R).Nonempty
  · have hmass := activeSel_mass s C K R hne
    have hle : ∑ u ∈ activeSel s C K R, ‖selWeight s C K R u‖ ^ 2 ≤
        ((activeSel s C K R).card : ℝ) * (∏ j : C, s.M j.val) ^ 2 := by
      have h := Finset.sum_le_card_nsmul (activeSel s C K R) (fun u => ‖selWeight s C K R u‖ ^ 2)
        ((∏ j : C, s.M j.val) ^ 2) (fun u hu => pow_le_pow_left₀ (norm_nonneg _)
          (selWeight_norm_le s C K R u (activeSel_mem s C K R u hu).1) 2)
      simpa only [nsmul_eq_mul] using h
    calc
      _ ≤ ((activeSel s C K R).card : ℝ) * (∏ j : C, s.M j.val) ^ 2 / ∏ j ∈ C, s.P j :=
        div_le_div_of_nonneg_right hle hP.le
      _ = ((activeSel s C K R).card : ℝ) *
          ((Real.sqrt (∏ j ∈ C, s.P j))⁻¹ * ∏ j : C, s.M j.val) ^ 2 := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hP.le]
        field_simp
      _ ≤ _ := hmass
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, zero_div]
    exact mul_nonneg (by positivity)
      (Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj) (sq_nonneg _)))

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.collision_family_energy_div
#print axioms QRH.MixedStep.Residual.collisionWeight_sum
#print axioms QRH.MixedStep.Residual.divisor_assignments_card
