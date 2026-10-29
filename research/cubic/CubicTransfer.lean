/- Scratch (research only): the two places where a "cubic" transfer meets the sextic Gauss sums `sexticGauss`.

(1) `cubic_dilation_leaves_quadratic`: the cubic transfer exponent `D¹` applied to a simple sextic column leaves the
    quadratic symbol `χ_D(n)³ = (n/D)₂`:  g(D n, h) = χ_D(n)³ · g(D, h) · g(n, D h).
(2) `squared_residual_transfer`: on SQUARED columns (sextic symbols of `m²` are cubic) a squared block is peeled with
    NO dilation of the residual:  g(D² m², D H) = g(D², D H) · g(m², H)   (scale cost 2·2 − 1 = 3 per unit of block volume).
Both follow from CRT (`sexticGauss_coprime_product`), sextic reciprocity (`idealRowHom_primary_reciprocity`) and the
dilation law (`sexticGauss_unit_scale`). -/
import Submissions.arvi_newpowers.Rigidity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationShortening

set_option autoImplicit false

namespace QRH.Scratch.CubicTransfer
noncomputable section
open OAI OAI.SevenEighths
open ProbePhysical ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge QuadraticAllOddCRT CompletedGauss
open QRH.ArviNewpowers
local notation "O" => ActualEisensteinCubic.O

/-- (1) The cubic exponent `D¹` on a simple sextic column leaves `χ_D(n)³ = (n/D)₂`. -/
theorem cubic_dilation_leaves_quadratic (D n : O) (hD : Supported (Ideal.span {D}))
    (hn : Supported (Ideal.span {n})) (hDp : goodLambda ^ 2 ∣ D - 1) (hnp : goodLambda ^ 2 ∣ n - 1)
    (hcop : IsCoprime D n) (h : O) :
    sexticGauss (D * n) (mul_ne_zero (supportedElement_ne_zero D hD) (supportedElement_ne_zero n hn)) h =
      idealRowHom n (Ideal.span {D}) ^ 3 * sexticGauss D (supportedElement_ne_zero D hD) h *
        sexticGauss n (supportedElement_ne_zero n hn) (D * h) := by
  have ht : idealRowHom D (Ideal.span {n}) ≠ 0 := idealRowHom_ne_zero_of_coprime n D hn hcop.symm
  have hε : sexticReciprocityPhase D n ^ 2 = 1 :=
    CenteredMomentAmplificationShortening.supported_phase_sq D n hD hn
  have hinv : idealRowHom D (Ideal.span {n}) * (idealRowHom D (Ideal.span {n}))⁻¹ = 1 := mul_inv_cancel₀ ht
  rw [sexticGauss_coprime_product D n hD hn hcop, sexticGauss_unit_scale n hn D h hcop,
    idealRowHom_primary_reciprocity D n hDp hnp hD hn]
  linear_combination
    (-(sexticReciprocityPhase D n) * idealRowHom D (Ideal.span {n}) ^ 2 *
      sexticGauss D (supportedElement_ne_zero D hD) h * sexticGauss n (supportedElement_ne_zero n hn) h) * hε +
    (-(sexticReciprocityPhase D n) ^ 3 * idealRowHom D (Ideal.span {n}) ^ 2 *
      sexticGauss D (supportedElement_ne_zero D hD) h * sexticGauss n (supportedElement_ne_zero n hn) h) * hinv

/-- (2) Squared block peeled from a squared column: the residual frequency is not dilated at all. -/
theorem squared_residual_transfer (D m : O) (hD : Supported (Ideal.span {D}))
    (hm : Supported (Ideal.span {m})) (hDp : goodLambda ^ 2 ∣ D - 1) (hmp : goodLambda ^ 2 ∣ m - 1)
    (hcop : IsCoprime D m) (H : O) :
    sexticGauss (D ^ 2 * m ^ 2)
        (mul_ne_zero (supportedElement_ne_zero _ (Rigidity.supported_pow hD 2))
          (supportedElement_ne_zero _ (Rigidity.supported_pow hm 2))) (D * H) =
      sexticGauss (D ^ 2) (supportedElement_ne_zero _ (Rigidity.supported_pow hD 2)) (D * H) *
        sexticGauss (m ^ 2) (supportedElement_ne_zero _ (Rigidity.supported_pow hm 2)) H := by
  have hD2 := Rigidity.supported_pow hD 2
  have hm2 := Rigidity.supported_pow hm 2
  have hcop2 : IsCoprime (D ^ 2) (m ^ 2) := hcop.pow
  have hcopDm2 : IsCoprime D (m ^ 2) := hcop.pow_right
  -- the cubic value t = χ_{m²}(D) = χ_m(D)², with t³ = χ_m(D)⁶ = 1
  set t := idealRowHom D (Ideal.span {m ^ 2}) with ht_def
  have ht0 : t ≠ 0 := idealRowHom_ne_zero_of_coprime (m ^ 2) D hm2 hcopDm2.symm
  have ht_sq : t = idealRowHom D (Ideal.span {m}) ^ 2 := by
    rw [ht_def, ← Ideal.span_singleton_pow, map_pow]
  have h6 : idealRowHom D (Ideal.span {m}) ^ 6 = 1 := by
    rw [← idealRowHom_argument_pow D 6 _ hm]
    exact supported_sixth_value m D hm hcop.symm
  have ht3 : t ^ 3 = 1 := by rw [ht_sq, ← pow_mul]; exact h6
  -- the ray sign of the squared pair is 1
  have hε : sexticReciprocityPhase (D ^ 2) (m ^ 2) = 1 := by
    have hDm : sexticReciprocityPhase D m ^ 2 = 1 :=
      CenteredMomentAmplificationShortening.supported_phase_sq D m hD hm
    simp only [pow_two, sexticReciprocityPhase_mul_left, sexticReciprocityPhase_mul_right]
    linear_combination (sexticReciprocityPhase D m ^ 2 + 1) * hDm
  have hrec := idealRowHom_primary_reciprocity (D ^ 2) (m ^ 2) (Rigidity.primary_pow hDp 2)
    (Rigidity.primary_pow hmp 2) hD2 hm2
  rw [hε, one_mul, idealRowHom_argument_pow D 2 _ hm2, ← ht_def] at hrec
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  rw [sexticGauss_coprime_product (D ^ 2) (m ^ 2) hD2 hm2 hcop2,
    sexticGauss_unit_scale (m ^ 2) hm2 D H hcopDm2, hrec, idealRowHom_argument_pow D 2 _ hm2, ← ht_def]
  linear_combination
    (t * t⁻¹ * sexticGauss (D ^ 2) (supportedElement_ne_zero _ hD2) (D * H) *
      sexticGauss (m ^ 2) (supportedElement_ne_zero _ hm2) H) * ht3 +
    (sexticGauss (D ^ 2) (supportedElement_ne_zero _ hD2) (D * H) *
      sexticGauss (m ^ 2) (supportedElement_ne_zero _ hm2) H) * hinv

end
end QRH.Scratch.CubicTransfer

#print axioms QRH.Scratch.CubicTransfer.cubic_dilation_leaves_quadratic
#print axioms QRH.Scratch.CubicTransfer.squared_residual_transfer
