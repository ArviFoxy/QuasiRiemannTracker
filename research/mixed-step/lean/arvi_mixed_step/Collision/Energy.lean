/- Mixed source step, collisions: energy of the collision columns for one colliding prime `p`.

On any finite set of frequencies `R` with weights `w ≥ 0`, the collision polynomial's energy is at
most `N(p)` times the twisted residual polynomial's energy on the preimage `{H' | p·H' ∈ R}`, with
weights `w(p·H')`. (The collision polynomial vanishes off `p·O`; on `p·O` its factor has norm at
most `√N(p)`.) -/
import Submissions.arvi_mixed_step.Collision.Factor
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Collision
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve CubicEisenstein ConcreteTraceCRT
open ProbePrimePower ProbePhysical CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

theorem mul_left_injective_of_ne_zero (p : O) (hp : p ≠ 0) : Function.Injective (fun H' : O => p*H') :=
  fun _ _ h => mul_left_cancel₀ hp h

theorem collision_energy {α : Type*} (S : Finset α) (m : α → O) (p : O) (hp : Prime p)
    (hsp : Supported (Ideal.span {p})) (hm : ∀ i, Supported (Ideal.span {m i}))
    (hcop : ∀ i, IsCoprime p (m i)) (c : α → ℂ) (R : Finset O) (w : O → ℝ) (hw : ∀ H, 0 ≤ w H) :
    ∑ H ∈ R, w H * ‖gaussPolynomial S (fun i => p^2*m i)
        (fun i => supported_sq_mul p (m i) hsp (hm i)) c H‖^2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) *
        ∑ H' ∈ R.preimage (fun H' => p*H') ((mul_left_injective_of_ne_zero p hp.ne_zero).injOn),
          w (p*H') * ‖gaussPolynomial S m hm (fun i => c i * collisionPhase p (m i)) H'‖^2 := by
  set P := fun H => gaussPolynomial S (fun i => p^2*m i)
    (fun i => supported_sq_mul p (m i) hsp (hm i)) c H with hP
  have hinj := mul_left_injective_of_ne_zero p hp.ne_zero
  -- split R into the multiples of p (image of the preimage) and the rest (where P vanishes)
  have hsplit : ∑ H ∈ R, w H * ‖P H‖^2 =
      ∑ H ∈ (R.preimage (fun H' => p*H') hinj.injOn).image (fun H' => p*H'), w H * ‖P H‖^2 := by
    symm
    apply Finset.sum_subset
    · intro H hH
      obtain ⟨H', hH', rfl⟩ := Finset.mem_image.mp hH
      exact Finset.mem_preimage.mp hH'
    · intro H hR hnot
      have hdiv : ¬p ∣ H := by
        rintro ⟨H', rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨H', Finset.mem_preimage.mpr hR, rfl⟩)
      rw [hP]
      simp only
      rw [collision_poly_zero S m p hp hsp hm hcop c H hdiv, norm_zero]
      ring
  rw [hsplit, Finset.sum_image (fun x _ y _ h => hinj h), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro H' _
  rw [hP]
  simp only
  rw [collision_poly_lift S m p hp hsp hm hcop c H', norm_mul, mul_pow]
  have hf := collisionFactor_norm_le p hp hsp H'
  have hf2 : ‖collisionFactor p hp hsp H'‖^2 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    calc ‖collisionFactor p hp hsp H'‖^2 ≤ (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hf 2
      _ = (Ideal.absNorm (Ideal.span {p}) : ℝ) := Real.sq_sqrt (by positivity)
  have hw' := hw (p*H')
  have hq := sq_nonneg ‖gaussPolynomial S m hm (fun i => c i * collisionPhase p (m i)) H'‖
  nlinarith [mul_le_mul_of_nonneg_right hf2 (mul_nonneg hw' hq)]

end
end QRH.MixedStep.Collision
#print axioms QRH.MixedStep.Collision.collision_energy
