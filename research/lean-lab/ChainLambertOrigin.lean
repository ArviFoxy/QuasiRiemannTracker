/-
Where the Lambert W solutions of the class flows come from (research/chain-structure/README.md).

The class-`p` flow `E' = −6q_pE/(1 − 6q_ps)` with `6q_p = 5A/D` is, after a change of time, the
quadratic polynomial vector field

  `X = (ṡ, Ė) = (D − 5As, −5AE)`,
  `A = (3 − p)E + 4ps − 2`, `D = (1 + p)E + 4p²s − 2p`.

* `cutoff_forms`: with the cutoff root `ξ = E + 2ps`, `A = (1 − p)E − 2(1 − ξ)` and
  `D = (1 − p)E − 2p(1 − ξ)`, so `6q_p = 5(e − 2m)/(e − 2pm)` with `e = (1 − p)E`, `m = 1 − ξ`.
* `den_sub_num`: `D − pA = (1 − p)²E`. On the line `E = 0` the denominator is `p` times the
  numerator.
* `exp_factor`: hence `X((5s − p)/E) = 5(1 − p)²` is constant (cleared form below). So
  `exp((5s − p)/E)` is an exponential factor: the zero-length line `E = 0` is an invariant line of
  multiplicity two (its extactic polynomial is `10(1 − p)²E²L_p`, `chain-structure/lambert_origin.py`).
* `E_invariant`, `Lp_invariant`: `E = 0` and `L_p = 0` are invariant lines with cofactors `−5A` and
  `−5A − 2(5 − 2p²)`.
* So along the flow, in its own time, `(5s − p)/E` grows linearly (rate `5(1 − p)²`) while `L_p/E`
  decays exponentially (rate `2(5 − 2p²)`). Their combination
  `log(L_p/E) + κ(5s − p)/E`, `κ = 2(5 − 2p²)/(5(1 − p)²)`, is the first integral of
  `ChainFamilyIntegrable.lean`, and solving it for `E` is `x·eˣ = c`, i.e. Lambert W.
* A quadratic field with three invariant lines counted with multiplicity (`E` twice, `L_p` once) has
  a Darboux integrating factor (Darboux–Jouanolou count `m(m+1)/2 = 3`); here it is `1/(E²L_p)`.
Status: proved (algebra).
-/
import Mathlib

namespace ChainLambertOrigin

def numA (p s E : ℝ) : ℝ := (3 - p) * E + 4 * p * s - 2
def denD (p s E : ℝ) : ℝ := (1 + p) * E + 4 * p ^ 2 * s - 2 * p
def Lp (p s E : ℝ) : ℝ := (3 - 2 * p) * (5 + p) * E + 4 * p * (5 - 2 * p ^ 2) * s - 2 * (5 - 2 * p ^ 2)

/-- The class vector field (after a change of time). -/
def Xs (p s E : ℝ) : ℝ := denD p s E - 5 * numA p s E * s
def XE (p s E : ℝ) : ℝ := -5 * numA p s E * E

/-- Lie derivative of a polynomial given by its partials. -/
def lie (p s E fs fE : ℝ) : ℝ := fs * Xs p s E + fE * XE p s E

theorem cutoff_forms (p s E : ℝ) :
    numA p s E = (1 - p) * E - 2 * (1 - (E + 2 * p * s)) ∧
      denD p s E = (1 - p) * E - 2 * p * (1 - (E + 2 * p * s)) := by
  unfold numA denD; constructor <;> ring

theorem den_sub_num (p s E : ℝ) : denD p s E - p * numA p s E = (1 - p) ^ 2 * E := by
  unfold denD numA; ring

/-- `X((5s − p)/E) = 5(1 − p)²`, cleared of the denominator `E²`: the quotient rule numerator
`X(5s − p)·E − (5s − p)·X(E)` equals `5(1 − p)²E²`. -/
theorem exp_factor (p s E : ℝ) :
    5 * Xs p s E * E - (5 * s - p) * XE p s E = 5 * (1 - p) ^ 2 * E ^ 2 := by
  unfold Xs XE denD numA; ring

/-- The same statement as a Lie derivative of the function `(5s − p)/E`. -/
theorem exp_factor_lie (p s E : ℝ) (hE : E ≠ 0) :
    lie p s E (5 / E) (-(5 * s - p) / E ^ 2) = 5 * (1 - p) ^ 2 := by
  unfold lie
  have h := exp_factor p s E
  field_simp
  linear_combination h

theorem E_invariant (p s E : ℝ) : lie p s E 0 1 = -5 * numA p s E * E := by
  unfold lie XE; ring

theorem Lp_invariant (p s E : ℝ) :
    lie p s E (4 * p * (5 - 2 * p ^ 2)) ((3 - 2 * p) * (5 + p))
      = (-5 * numA p s E - 2 * (5 - 2 * p ^ 2)) * Lp p s E := by
  unfold lie Xs XE denD numA Lp; ring

/-- The rates combine to zero: `X(log(L_p/E)) + κ·X((5s − p)/E) = 0` with
`κ = 2(5 − 2p²)/(5(1 − p)²)`; cofactors `(−5A − 2(5 − 2p²)) − (−5A) + κ·5(1 − p)² = 0`. -/
theorem cofactors_cancel (p s E : ℝ) (hp : 1 - p ≠ 0) :
    (-5 * numA p s E - 2 * (5 - 2 * p ^ 2)) - (-5 * numA p s E)
      + 2 * (5 - 2 * p ^ 2) / (5 * (1 - p) ^ 2) * (5 * (1 - p) ^ 2) = 0 := by
  field_simp
  ring

end ChainLambertOrigin
