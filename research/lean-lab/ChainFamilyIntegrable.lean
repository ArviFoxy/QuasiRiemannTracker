/-
The continuum source chain is, class by class, an integrable planar flow
(research/chain-ode/README.md, "The p-family", 2026-10-25).

Fix the binding amplitude class `p ∈ [0, 1/2)` of the HIGH count, with its two binding facets
(the marked-inverse budget and the slot supply). Write `E` for the envelope at slot width `s` and
`q` for the HIGH threshold at the pivot (gain normalized as in `repeated-marks/gain_fast.py`,
`F = 1`, `α = 5/6`).

* `gate_reduction`: the ρ-terms of the HIGH gate cancel identically. The gate
  `1 − ρ(q) − q(E + s) + (1 − 2p)qs + q(ξ − αF/(q + 3k/2)) = 0`, with `ρ(q) = 1 − 10q/(15 − 6q)` and
  `k = 5/6 − q`, is `q·(ξ − E − 2ps) = 0`. So the cutoff root is `ξ = E + 2ps` (the agent's
  "`ξ_{p*} = t + 2p*S`").
* `threshold_formula`: with the root `ξ = (5/6 + kp(1/(1−p) + s))/(5/6 + k(1/(1−p) − 1/2))`, the
  equation `ξ = E + 2ps` gives `6q = 5((3−p)E + 4ps − 2)/((1+p)E + 4p²s − 2p)` (stated in
  cross-multiplied form).
* `lie_derivative_zero`: the chain flow `E' = −M/N`, with `M = 5E((3−p)E + 4ps − 2)` and
  `N = (1+p)E + 4p²s − 2p − 5s((3−p)E + 4ps − 2)` (that is `E' = −6qE/(1 − 6qs)`), conserves
    `I_p(s, E) = log(L_p/E) + 2(5 − 2p²)(5s − p)/(5(1 − p)²E)`,
    `L_p = (3 − 2p)(5 + p)E + 4p(5 − 2p²)s − 2(5 − 2p²)`.
  The invariant lines are `E = 0` and `L_p = 0`, and `1/(E² L_p)` is a Darboux integrating factor.
  At `p = 0` this is the late-chain integral of `ChainFirstIntegral.lean`
  (`L₀ = 15E − 10`); at `p = 1/2` it is `log((11E + 9s − 9)/E) + (36s − 3.6)/E`.
Status: proved (pure algebra; the analytic reading is in the chain-ode note).
-/
import Mathlib

namespace ChainFamilyIntegrable

/-- The HIGH gate with the unmarked count `ρ(q) = 1 − 10q/(15 − 6q)` reduces to `ξ = E + 2ps`. -/
theorem gate_reduction (q E s p ξ : ℝ) (_hq : 15 - 6 * q ≠ 0) :
    (1 - (1 - 10 * q / (15 - 6 * q))) - q * (E + s) + (1 - 2 * p) * q * s
      + q * (ξ - (5 / 6) / (q + 3 / 2 * (5 / 6 - q))) = q * (ξ - E - 2 * p * s) := by
  have h2 : q + 3 / 2 * (5 / 6 - q) = (15 - 6 * q) / 12 := by ring
  rw [h2]
  field_simp
  ring

/-- Solving `ξ = E + 2ps` for the threshold: cross-multiplied form of
`6q = 5((3−p)E + 4ps − 2)/((1+p)E + 4p²s − 2p)`. -/
theorem threshold_formula (q E s p : ℝ) (hp : 1 - p ≠ 0)
    (hden : 5 / 6 + (5 / 6 - q) * (1 / (1 - p) - 1 / 2) ≠ 0)
    (hroot : (5 / 6 + (5 / 6 - q) * p * (1 / (1 - p) + s))
        / (5 / 6 + (5 / 6 - q) * (1 / (1 - p) - 1 / 2)) = E + 2 * p * s) :
    6 * q * ((1 + p) * E + 4 * p ^ 2 * s - 2 * p) = 5 * ((3 - p) * E + 4 * p * s - 2) := by
  rw [div_eq_iff hden] at hroot
  field_simp at hroot
  linear_combination hroot

/-- The invariant line `L_p`. -/
noncomputable def Lp (p s E : ℝ) : ℝ :=
  (3 - 2 * p) * (5 + p) * E + 4 * p * (5 - 2 * p ^ 2) * s - 2 * (5 - 2 * p ^ 2)

/-- `M` and `N` of the flow `E' = −M/N`. -/
noncomputable def Mf (p s E : ℝ) : ℝ := 5 * E * ((3 - p) * E + 4 * p * s - 2)
noncomputable def Nf (p s E : ℝ) : ℝ :=
  (1 + p) * E + 4 * p ^ 2 * s - 2 * p - 5 * s * ((3 - p) * E + 4 * p * s - 2)

/-- Partial derivatives of `I_p = log(L_p/E) + 2(5 − 2p²)(5s − p)/(5(1 − p)²E)`. -/
noncomputable def dIds (p s E : ℝ) : ℝ :=
  4 * p * (5 - 2 * p ^ 2) / Lp p s E + 2 * (5 - 2 * p ^ 2) / ((1 - p) ^ 2 * E)
noncomputable def dIdE (p s E : ℝ) : ℝ :=
  (3 - 2 * p) * (5 + p) / Lp p s E - 1 / E
    - 2 * (5 - 2 * p ^ 2) * (5 * s - p) / (5 * (1 - p) ^ 2 * E ^ 2)

/-- The Lie derivative of `I_p` along `N ∂ₛ − M ∂_E` vanishes. -/
theorem lie_derivative_zero (p s E : ℝ) (hp : 1 - p ≠ 0) (hE : E ≠ 0) (hL : Lp p s E ≠ 0) :
    Nf p s E * dIds p s E - Mf p s E * dIdE p s E = 0 := by
  unfold dIds dIdE Nf Mf
  field_simp
  unfold Lp
  ring

/-- The two partials are those of `I_p` (sanity check: `dIds` is `∂ₛ` of the explicit formula). -/
theorem dIds_correct (p E : ℝ) (hp : 1 - p ≠ 0) (hE : 0 < E) (s : ℝ) (hL : 0 < Lp p s E) :
    HasDerivAt (fun t => Real.log (Lp p t E / E)
        + 2 * (5 - 2 * p ^ 2) * (5 * t - p) / (5 * (1 - p) ^ 2 * E)) (dIds p s E) s := by
  have hLt : HasDerivAt (fun t => Lp p t E) (4 * p * (5 - 2 * p ^ 2)) s := by
    unfold Lp
    have := ((hasDerivAt_id s).const_mul (4 * p * (5 - 2 * p ^ 2))).add_const
      ((3 - 2 * p) * (5 + p) * E - 2 * (5 - 2 * p ^ 2))
    convert this using 1
    · funext t; simp; ring
    · simp
  have h1 := (hLt.div_const E).log (by positivity)
  have h2 : HasDerivAt (fun t => 2 * (5 - 2 * p ^ 2) * (5 * t - p) / (5 * (1 - p) ^ 2 * E))
      (2 * (5 - 2 * p ^ 2) * 5 / (5 * (1 - p) ^ 2 * E)) s := by
    have := (((hasDerivAt_id' s).const_mul 5).sub_const p).const_mul (2 * (5 - 2 * p ^ 2))
    have := this.div_const (5 * (1 - p) ^ 2 * E)
    convert this using 1
    ring
  convert h1.add h2 using 1
  unfold dIds
  have hE0 : E ≠ 0 := ne_of_gt hE
  have hL0 : Lp p s E ≠ 0 := ne_of_gt hL
  field_simp

end ChainFamilyIntegrable
