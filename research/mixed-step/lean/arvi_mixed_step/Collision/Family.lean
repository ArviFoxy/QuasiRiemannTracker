/- Mixed source step, collisions: a family of collision patterns.

Cauchy–Schwarz over a finite family of polynomials: the energy of a sum of `k` polynomials is at
most `k` times the sum of their energies. Combined with `collision_energy` this bounds the collision
part of a source (one polynomial per value of the colliding prime) by the sum over the values of
`N(p)` times the residual energies on the preimages. -/
import Submissions.arvi_mixed_step.Collision.Energy
import Mathlib.Algebra.Order.Chebyshev
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

/-- Cauchy–Schwarz for a finite sum of complex numbers. -/
theorem norm_sum_sq_le_card {β : Type*} (T : Finset β) (f : β → ℂ) :
    ‖∑ x ∈ T, f x‖^2 ≤ (T.card : ℝ) * ∑ x ∈ T, ‖f x‖^2 := by
  have h1 : ‖∑ x ∈ T, f x‖ ≤ ∑ x ∈ T, ‖f x‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun x => ‖f x‖)
  calc ‖∑ x ∈ T, f x‖^2 ≤ (∑ x ∈ T, ‖f x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (T.card : ℝ) * ∑ x ∈ T, ‖f x‖^2 := by simpa using h2

/-- Energy of a sum of polynomials over a weighted finite frequency set. -/
theorem energy_sum_le {β : Type*} (T : Finset β) (P : β → O → ℂ) (R : Finset O) (w : O → ℝ)
    (hw : ∀ H, 0 ≤ w H) :
    ∑ H ∈ R, w H * ‖∑ x ∈ T, P x H‖^2 ≤ (T.card : ℝ) * ∑ x ∈ T, ∑ H ∈ R, w H * ‖P x H‖^2 := by
  calc ∑ H ∈ R, w H * ‖∑ x ∈ T, P x H‖^2
      ≤ ∑ H ∈ R, w H * ((T.card : ℝ) * ∑ x ∈ T, ‖P x H‖^2) := by
        apply Finset.sum_le_sum
        intro H _
        exact mul_le_mul_of_nonneg_left (norm_sum_sq_le_card T (fun x => P x H)) (hw H)
    _ = (T.card : ℝ) * ∑ H ∈ R, ∑ x ∈ T, w H * ‖P x H‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro H _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = (T.card : ℝ) * ∑ x ∈ T, ∑ H ∈ R, w H * ‖P x H‖^2 := by rw [Finset.sum_comm]

/-- The collision part of a source, one colliding prime per value `x ∈ T`: its energy is at most
`#T · Σ_x N(p_x) · (twisted residual energy of x on the preimage of R under p_x·)`. -/
theorem collision_family_energy {β α : Type*} (T : Finset β) (S : β → Finset α) (m : β → α → O)
    (p : β → O) (hp : ∀ x, Prime (p x)) (hsp : ∀ x, Supported (Ideal.span {p x}))
    (hm : ∀ x i, Supported (Ideal.span {m x i})) (hcop : ∀ x i, IsCoprime (p x) (m x i))
    (c : β → α → ℂ) (R : Finset O) (w : O → ℝ) (hw : ∀ H, 0 ≤ w H) :
    ∑ H ∈ R, w H * ‖∑ x ∈ T, gaussPolynomial (S x) (fun i => (p x)^2*m x i)
        (fun i => supported_sq_mul (p x) (m x i) (hsp x) (hm x i)) (c x) H‖^2 ≤
      (T.card : ℝ) * ∑ x ∈ T, (Ideal.absNorm (Ideal.span {p x}) : ℝ) *
        ∑ H' ∈ R.preimage (fun H' => p x*H')
            ((mul_left_injective_of_ne_zero (p x) (hp x).ne_zero).injOn),
          w (p x*H') * ‖gaussPolynomial (S x) (m x) (hm x)
            (fun i => c x i * collisionPhase (p x) (m x i)) H'‖^2 := by
  refine (energy_sum_le T _ R w hw).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  exact collision_energy (S x) (m x) (p x) (hp x) (hsp x) (hm x) (hcop x) (c x) R w hw

end
end QRH.MixedStep.Collision
#print axioms QRH.MixedStep.Collision.collision_family_energy
