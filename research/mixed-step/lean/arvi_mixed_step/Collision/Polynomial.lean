/- Mixed source step, collisions at the level of Gauss polynomials.

For a family of residual columns `m i`, all coprime to the colliding prime `p`, the polynomial of
the collision columns `p²·m i` vanishes off `p·O`, and on it equals the prime Gauss sum
`primeGauss p (χ_p²) H'` (independent of the column) times the residual polynomial with
the unimodular column phases `φ_p(m)`. The prime Gauss sum of a nonprincipal character has norm at
most `√N(p)` at every frequency, so the collision polynomial's square is at most
`N(p)·|residual polynomial|²` on the sublattice. -/
import Submissions.arvi_mixed_step.Collision.Column
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

/-- The unimodular column phase of a collision column. -/
def collisionPhase (p m : O) : ℂ :=
  idealRowHom m (Ideal.span {p^2}) * idealRowHom (p^2) (Ideal.span {m}) *
    (idealRowHom p (Ideal.span {m}))⁻¹

/-- The colliding prime's Gauss factor at `H'`. -/
def collisionFactor (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H' : O) : ℂ :=
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) H'

theorem absNorm_sq_mul (p m : O) :
    (Ideal.absNorm (Ideal.span {p^2*m}) : ℝ) =
      (Ideal.absNorm (Ideal.span {p}) : ℝ)^2 * Ideal.absNorm (Ideal.span {m}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, map_mul, map_pow]
  push_cast; ring

/-- Normalized collision row on the sublattice. -/
theorem collision_row_lift (p m : O) (hp : Prime p) (hsp : Supported (Ideal.span {p}))
    (hm : Supported (Ideal.span {m})) (hcop : IsCoprime p m) (H' : O) :
    gaussRow (p^2*m) (supported_sq_mul p m hsp hm) (p*H') =
      collisionPhase p m * collisionFactor p hp hsp H' * gaussRow m hm H' := by
  unfold gaussRow collisionPhase collisionFactor
  rw [collision_sextic_lift p m hp hsp hm hcop H']
  have hN : (0:ℝ) < Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hsq : Real.sqrt (Ideal.absNorm (Ideal.span {p^2*m}) : ℝ) =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) * Real.sqrt (Ideal.absNorm (Ideal.span {m}) : ℝ) := by
    rw [absNorm_sq_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  rw [hsq]
  push_cast
  have hN' : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Normalized collision row off the sublattice. -/
theorem collision_row_zero (p m : O) (hp : Prime p) (hsp : Supported (Ideal.span {p}))
    (hm : Supported (Ideal.span {m})) (hcop : IsCoprime p m) (H : O) (hH : ¬p ∣ H) :
    gaussRow (p^2*m) (supported_sq_mul p m hsp hm) H = 0 := by
  unfold gaussRow
  rw [collision_sextic_zero p m hp hsp hm hcop H hH, zero_div]

/-- Collision polynomial off the sublattice. -/
theorem collision_poly_zero {α : Type*} (S : Finset α) (m : α → O) (p : O) (hp : Prime p)
    (hsp : Supported (Ideal.span {p})) (hm : ∀ i, Supported (Ideal.span {m i}))
    (hcop : ∀ i, IsCoprime p (m i)) (c : α → ℂ) (H : O) (hH : ¬p ∣ H) :
    gaussPolynomial S (fun i => p^2*m i) (fun i => supported_sq_mul p (m i) hsp (hm i)) c H = 0 := by
  unfold gaussPolynomial
  apply Finset.sum_eq_zero
  intro i _
  rw [collision_row_zero p (m i) hp hsp (hm i) (hcop i) H hH, mul_zero]

/-- Collision polynomial on the sublattice: the common prime factor times the twisted residual
polynomial. -/
theorem collision_poly_lift {α : Type*} (S : Finset α) (m : α → O) (p : O) (hp : Prime p)
    (hsp : Supported (Ideal.span {p})) (hm : ∀ i, Supported (Ideal.span {m i}))
    (hcop : ∀ i, IsCoprime p (m i)) (c : α → ℂ) (H' : O) :
    gaussPolynomial S (fun i => p^2*m i) (fun i => supported_sq_mul p (m i) hsp (hm i)) c (p*H') =
      collisionFactor p hp hsp H' *
        gaussPolynomial S m hm (fun i => c i * collisionPhase p (m i)) H' := by
  unfold gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [collision_row_lift p (m i) hp hsp (hm i) (hcop i) H']
  ring

end
end QRH.MixedStep.Collision
#print axioms QRH.MixedStep.Collision.collision_poly_lift
#print axioms QRH.MixedStep.Collision.collision_poly_zero
