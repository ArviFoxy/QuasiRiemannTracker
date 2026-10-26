/- Mixed source step, collisions: a selected slot prime `p` that also divides the ordinary pair
makes the column `p²·m`. Its Gauss row vanishes off the sublattice `p·O`, and on it the `p²`
factor is a prime Gauss sum of the cubic character `χ_p²` at `H'`, common to every `m`:

  `gaussRow (p²m) (pH') = φ_p(m) · primeGauss p (χ_p²) H' · gaussRow m H'`,

with the unimodular column phase `φ_p(m) = (m/p²)·(p²/m)·(p/m)⁻¹`. Only the baseline's local
lemmas are used: the sextic prime-power Gauss sum (`sexticGauss_prime_power`), its support and lift
(`primePowerGauss_zero_off_support`, `primePowerGauss_lift`), the CRT product
(`sexticGauss_coprime_product`) and unit scaling (`sexticGauss_unit_scale`). -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.GaussTransfer
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

theorem supported_sq_mul (p m : O) (hsp : Supported (Ideal.span {p}))
    (hm : Supported (Ideal.span {m})) : Supported (Ideal.span {p^2*m}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, supported_mul_iff]
  refine ⟨?_, hm⟩
  rw [← Ideal.span_singleton_pow, pow_two, supported_mul_iff]
  exact ⟨hsp, hsp⟩

theorem supported_sq (p : O) (hsp : Supported (Ideal.span {p})) : Supported (Ideal.span {p^2}) := by
  rw [← Ideal.span_singleton_pow, pow_two, supported_mul_iff]
  exact ⟨hsp, hsp⟩

/-- The `p²`-factor Gauss sum is the prime-power Gauss sum of `χ_p²` at level one. -/
theorem sextic_sq (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H : O) :
    letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    sexticGauss (p^2) (pow_ne_zero _ hp.ne_zero) H =
      primePowerGauss p hp.ne_zero
        (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) 1 H := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact sexticGauss_prime_power p hp (supported_prime_data p hp hsp).1 1 H

/-- Off the sublattice `p·O` the collision column's Gauss sum vanishes. -/
theorem collision_sextic_zero (p m : O) (hp : Prime p) (hsp : Supported (Ideal.span {p}))
    (hm : Supported (Ideal.span {m})) (hcop : IsCoprime p m) (H : O) (hH : ¬p ∣ H) :
    sexticGauss (p^2*m) (supportedElement_ne_zero _ (supported_sq_mul p m hsp hm)) H = 0 := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have h := sexticGauss_coprime_product (p^2) m (supported_sq p hsp) hm hcop.pow_left H
  rw [h]
  have hz : sexticGauss (p^2) (supportedElement_ne_zero (p^2) (supported_sq p hsp)) H = 0 := by
    rw [sextic_sq p hp hsp H]
    apply primePowerGauss_zero_off_support
    simpa using hH
  rw [hz]; ring

/-- On the sublattice: the exact lift. -/
theorem collision_sextic_lift (p m : O) (hp : Prime p) (hsp : Supported (Ideal.span {p}))
    (hm : Supported (Ideal.span {m})) (hcop : IsCoprime p m) (H' : O) :
    letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    sexticGauss (p^2*m) (supportedElement_ne_zero _ (supported_sq_mul p m hsp hm)) (p*H') =
      (idealRowHom m (Ideal.span {p^2}) * idealRowHom (p^2) (Ideal.span {m}) *
        (idealRowHom p (Ideal.span {m}))⁻¹) *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) H') *
      sexticGauss m (supportedElement_ne_zero m hm) H' := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have h := sexticGauss_coprime_product (p^2) m (supported_sq p hsp) hm hcop.pow_left (p*H')
  rw [h]
  have hs : sexticGauss (p^2) (supportedElement_ne_zero (p^2) (supported_sq p hsp)) (p*H') =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) H' := by
    rw [sextic_sq p hp hsp (p*H')]
    have := primePowerGauss_lift p hp.ne_zero
      (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) 1 H'
    simpa only [pow_one] using this
  have hu := sexticGauss_unit_scale m hm p H' hcop
  rw [hs, hu]
  ring

end
end QRH.MixedStep.Collision
#print axioms QRH.MixedStep.Collision.collision_sextic_lift
#print axioms QRH.MixedStep.Collision.collision_sextic_zero
