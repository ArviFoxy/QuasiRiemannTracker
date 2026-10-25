/-
A conserved quantity of the continuum source chain (research/chain-ode/README.md, 2026-10-25).

In the continuum limit the source chain's envelope `E(s)` (largest certified plain length at slot
width `s`) obeys `E' = −6qE/(1 − 6qs)` with `q = (15 − 10/X)/6` and `X = E + (1 − g)s`, where `g` is
the HIGH gain as a fraction of its cap. When the gain is at its cap (`g = 1`, the late chain),
`6q = 15 − 10/E` and the flow is

  `E' = f(s, E) = −E(15E − 10)/(E − 15sE + 10s)`.

It has the integrating factor `1/(E²(3E − 2))`, which gives the first integral

  `F(s, E) = 10s/E + log(3 − 2/E)`.

* `lie_derivative_zero`: `∂ₛF + ∂_E F · f = 0` wherever `E > 2/3` and the denominator is nonzero.
* `first_integral_const`: along any solution with `E > 2/3`, `F(s, E(s))` is constant.

So the continuum chain is a level curve of an explicit function. Its ceiling involves a logarithm
and is therefore not expected to be algebraic.
Status: proved.
-/
import Mathlib

namespace ChainFirstIntegral

/-- The late-chain vector field. -/
noncomputable def f (s E : ℝ) : ℝ := -(E * (15 * E - 10)) / (E - 15 * s * E + 10 * s)

/-- The first integral. -/
noncomputable def F (s E : ℝ) : ℝ := 10 * s / E + Real.log (3 - 2 / E)

/-- Core algebra: with `D = E − 15sE + 10s`, the Lie derivative of `F` along `f` vanishes. -/
theorem lie_derivative_zero (s E : ℝ) (hE : 2 / 3 < E) (hD : E - 15 * s * E + 10 * s ≠ 0) :
    10 / E + (-(10 * s) / E ^ 2 + (2 / E ^ 2) / (3 - 2 / E)) * f s E = 0 := by
  have hE0 : E ≠ 0 := by
    have : (0 : ℝ) < E := by linarith
    exact ne_of_gt this
  have h3E : 3 * E - 2 ≠ 0 := by
    have : (0 : ℝ) < 3 * E - 2 := by linarith
    exact ne_of_gt this
  have hq : 3 - 2 / E = (3 * E - 2) / E := by
    field_simp
  rw [hq]
  unfold f
  rw [div_div_eq_mul_div]
  have key : (2 / E ^ 2 * E / (3 * E - 2)) = 2 / (E * (3 * E - 2)) := by
    field_simp
  rw [key]
  rw [div_add_div _ _ (pow_ne_zero 2 hE0) (mul_ne_zero hE0 h3E)]
  rw [div_mul_div_comm, div_add_div _ _ hE0 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hE0)
    (mul_ne_zero hE0 h3E)) hD)]
  rw [div_eq_zero_iff]
  left
  ring

/-- The chain-rule expression for `d/ds F(s, E(s))`, rewritten in the form of
`lie_derivative_zero`. -/
theorem chain_rule_form (s e fv : ℝ) (he : e ≠ 0) (h3e : 3 * e - 2 ≠ 0) :
    (10 * 1 * e - 10 * s * fv) / e ^ 2 + -((0 * e - 2 * fv) / e ^ 2) / (3 - 2 / e) =
      10 / e + (-(10 * s) / e ^ 2 + 2 / e ^ 2 / (3 - 2 / e)) * fv := by
  have hq : 3 - 2 / e = (3 * e - 2) / e := by
    field_simp
  rw [hq]
  field_simp
  ring

/-- Along a solution of `E' = f(s, E)` that stays above `2/3`, the first integral is constant. -/
theorem first_integral_const {E : ℝ → ℝ} (hE : ∀ s, 2 / 3 < E s)
    (hD : ∀ s, E s - 15 * s * E s + 10 * s ≠ 0)
    (hderiv : ∀ s, HasDerivAt E (f s (E s)) s) (a b : ℝ) :
    F a (E a) = F b (E b) := by
  have hpos : ∀ s, 0 < E s := fun s => by linarith [hE s]
  have hlogarg : ∀ s, 0 < 3 - 2 / E s := by
    intro s
    have h1 : 2 / E s < 3 := by
      rw [div_lt_iff₀ (hpos s)]
      linarith [hE s]
    linarith
  have hfun : (fun t => F t (E t)) = (fun y => 10 * id y / E y + Real.log (3 - 2 / E y)) := by
    funext y
    simp [F]
  have hG : ∀ s, HasDerivAt (fun t => F t (E t)) 0 s := by
    intro s
    have hEs0 : E s ≠ 0 := ne_of_gt (hpos s)
    have h1 := ((hasDerivAt_id s).const_mul 10).div (hderiv s) hEs0
    have h2 := ((hasDerivAt_const s (2 : ℝ)).div (hderiv s) hEs0).const_sub 3
    have h3 := h2.log (ne_of_gt (hlogarg s))
    have h4 := h1.add h3
    rw [hfun]
    convert h4 using 1
    have hz := lie_derivative_zero s (E s) (hE s) (hD s)
    have h3e : 3 * E s - 2 ≠ 0 := by
      have := hE s
      intro h
      linarith
    simp only [id, Pi.div_apply]
    rw [chain_rule_form s (E s) (f s (E s)) hEs0 h3e, hz]
  have hdiff : Differentiable ℝ (fun t => F t (E t)) := fun s => (hG s).differentiableAt
  have hderiv0 : ∀ s, deriv (fun t => F t (E t)) s = 0 := fun s => (hG s).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv0 a b

end ChainFirstIntegral
