/-
The low side's sextic bias is the signal channel (research/LOG.md, "Atom 4 is the signal channel").

In the probe's low separation, Poisson in the row pairs the Gauss-sum polynomial `A` with the
completed row `B` through dual frequencies `k`. At the sixth-power frequencies `k = a⁶e₀` the dual
coefficient of `B` is the target's inverse L-function, so with the zero-free hypothesis at `β` the
exceptional pairing is the Cauchy–Schwarz bound times `Z^{gap}`, where (logarithms base `Z`)
  `gap = (Nstar + ly − M)/6 + (β − 1) − (2·ly − M)/12`:
`K_× = Z^{Nstar + ly − M}` frequencies carry `K_×^{1/6}` sixth powers, `Z^{β − 1}` is the dual
coefficient, and `P_a^{1/12} = Z^{(2·ly − M)/12}` is the Cauchy–Schwarz bias.
* `gap_eq`: with the completed length `Nstar = 1 + ℓ` and the tight marked energy `M = 1 − ℓ`,
  `gap = β − θ_low` where `θ_low = 11/12 − ℓ/4`, for every `ℓ` and `ly`.
* `gap_seven_eighths`: in OpenAI's 7/8 geometry (`ℓ = 1/6`, `ly = 23/48`, `M = 5/6`) the gap is
  `0` at `β = 7/8`.
So the exceptional channel has exactly the size of the signal `Z^{C(β)}`; no bound on the pairing
can beat it, and only the energies `‖A‖`, `‖B‖` can move atom 4.
Status: proved (exponent algebra; the analytic identification is in the log).
-/
import Mathlib

namespace SignalChannel

/-- Exponent of the exceptional pairing relative to the Cauchy–Schwarz bound. -/
noncomputable def gap (Nstar ly M β : ℝ) : ℝ :=
  (Nstar + ly - M) / 6 + (β - 1) - (2 * ly - M) / 12

/-- The low side's own threshold `θ_low = 11/12 − ℓ/4`. -/
noncomputable def thetaLow (ℓ : ℝ) : ℝ := 11 / 12 - ℓ / 4

theorem gap_eq (ℓ ly β : ℝ) : gap (1 + ℓ) ly (1 - ℓ) β = β - thetaLow ℓ := by
  unfold gap thetaLow
  ring

theorem gap_seven_eighths : gap (1 + 1 / 6) (23 / 48) (5 / 6) (7 / 8) = 0 := by
  unfold gap
  norm_num

/-- The gap is negative exactly below the threshold: the channel is smaller than the
Cauchy–Schwarz bound iff `β < θ_low`. -/
theorem gap_neg_iff (ℓ ly β : ℝ) : gap (1 + ℓ) ly (1 - ℓ) β < 0 ↔ β < thetaLow ℓ := by
  rw [gap_eq]
  constructor <;> intro h <;> linarith

end SignalChannel
