/-
The switching chain flow has a closed-form threshold (research/chain-ode/README.md,
"The faces are tangent lines of one explicit curve", 2026-10-25).

For amplitude class `p` the HIGH gate gives `6q_p = 5A/B` (`ChainFamilyIntegrable.lean`), with
`A = (3 − p)E + 4ps − 2` and `B = (1 + p)E + 4p²s − 2p`. Write `E = a²` and `s = b²` with `a, b > 0`.
The binding class is the critical point of `p ↦ 5A/B`:

  `p* = [s(3E − 2) − ab(1 − E − 2s)] / (s(E − 4s))`.

* `pstar_critical`: `p*` solves `A_p·B − A·B_p = 0`, i.e. `∂_p(A/B) = 0`.
* `pstar_denominator`: `(2 − E − 8p*s)(E − 4s) = (a + 2b)²(2 − a² − 4ab)`.
* `qstar_closed_form`: at `p*`, `5A/B = 5(a − 2b)²/(2 − a² − 4ab)`, that is
  `6q* = 5(√E − 2√s)²/(2 − E − 4√(Es))`.

So the whole continuum chain is the single algebraic ODE `E′ = −6q*E/(1 − 6q*s)`, clipped to
`p ∈ [0, 1/2]` and capped by the natural face.
Status: proved (algebra).
-/
import Mathlib

namespace ChainSwitching

/-- Numerator and denominator of `6q_p/5`. -/
def numA (p s E : ℝ) : ℝ := (3 - p) * E + 4 * p * s - 2
def denB (p s E : ℝ) : ℝ := (1 + p) * E + 4 * p ^ 2 * s - 2 * p

/-- The binding class. -/
noncomputable def pstar (a b : ℝ) : ℝ :=
  (b ^ 2 * (3 * a ^ 2 - 2) - a * b * (1 - a ^ 2 - 2 * b ^ 2)) / (b ^ 2 * (a ^ 2 - 4 * b ^ 2))

/-- `p*` is a critical point: `A_p B − A B_p = 0` with `A_p = 4s − E`, `B_p = E + 8ps − 2`. -/
theorem pstar_critical (a b : ℝ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ^ 2 ≠ 0) :
    (4 * b ^ 2 - a ^ 2) * denB (pstar a b) (b ^ 2) (a ^ 2)
      - numA (pstar a b) (b ^ 2) (a ^ 2) * (a ^ 2 + 8 * pstar a b * b ^ 2 - 2) = 0 := by
  unfold numA denB pstar
  field_simp
  ring

/-- The denominator identity behind the closed form. -/
theorem pstar_denominator (a b : ℝ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ^ 2 ≠ 0) :
    (2 - a ^ 2 - 8 * pstar a b * b ^ 2) * (a ^ 2 - 4 * b ^ 2)
      = (a + 2 * b) ^ 2 * (2 - a ^ 2 - 4 * a * b) := by
  have hab' : a ^ 2 - b ^ 2 * 4 ≠ 0 := by intro h; apply hab; linarith
  unfold pstar
  field_simp
  ring

/-- The closed form of the binding threshold: `5A/B = 5(a − 2b)²/(2 − a² − 4ab)` at `p*`. -/
theorem qstar_closed_form (a b : ℝ) (hb : b ≠ 0) (hab : a ^ 2 - 4 * b ^ 2 ≠ 0)
    (hB : denB (pstar a b) (b ^ 2) (a ^ 2) ≠ 0) (hD : 2 - a ^ 2 - 4 * a * b ≠ 0) :
    5 * numA (pstar a b) (b ^ 2) (a ^ 2) / denB (pstar a b) (b ^ 2) (a ^ 2)
      = 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b) := by
  have hab' : a ^ 2 - b ^ 2 * 4 ≠ 0 := by intro h; apply hab; linarith
  rw [div_eq_div_iff hB hD]
  unfold numA denB pstar
  field_simp
  ring

end ChainSwitching
