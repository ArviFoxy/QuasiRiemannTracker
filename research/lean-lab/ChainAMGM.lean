/-
Why the binding threshold of the source chain has a square root (research/chain-structure/README.md).

Amplitude class `p` of the HIGH count gives the threshold `6q_p = 5A/D`
(`ChainFamilyIntegrable.lean`), with

  `A = (3 − p)E + 4ps − 2`,  `D = (1 + p)E + 4p²s − 2p`.

* `mixture`: `D = p·A + (1 − p)²E`, so `5/(6q_p) = p + (1 − p)²E/A`.
* `sos`: with `E = a²` and `s = b²`,
  `(a + 2b)²·((a − 2b)²D − (2 − a² − 4ab)A) = 4(bA − a(1 − a² − 2b²))²`.
  This is AM–GM in `v = A`: `5/(6q_p)` is, up to a constant, `4s·v/c² + E·d²/(c²·v)` with
  `c = E − 4s` and `d = 2(1 − E − 2s)`. The geometric mean of the slot term `4s` and the
  plain term `E` is where `√(Es)` comes from.
* `threshold_le`: every class has `6q_p ≤ 5(a − 2b)²/(2 − a² − 4ab)` — for all real `p`, not only
  at a critical point. So the closed form of `ChainSwitching.lean` is the supremum over classes.
* `threshold_eq`: equality holds exactly when `bA = a(1 − a² − 2b²)`, the binding class
  `p* = (a² + ab − 1)/(b(a − 2b))`.
Status: proved (algebra).
-/
import Mathlib

namespace ChainAMGM

/-- Numerator and denominator of `6q_p/5`. -/
def numA (p s E : ℝ) : ℝ := (3 - p) * E + 4 * p * s - 2
def denD (p s E : ℝ) : ℝ := (1 + p) * E + 4 * p ^ 2 * s - 2 * p

/-- The class denominator is a mixture of the numerator and the plain length. -/
theorem mixture (p s E : ℝ) : denD p s E = p * numA p s E + (1 - p) ^ 2 * E := by
  unfold denD numA; ring

/-- The sum-of-squares identity behind the closed form. -/
theorem sos (p a b : ℝ) :
    (a + 2 * b) ^ 2 * ((a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
        - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2))
      = 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 := by
  unfold denD numA; ring

/-- Cleared form of the class bound, valid for every real `p`. -/
theorem cleared_le (p a b : ℝ) (hab : a + 2 * b ≠ 0) :
    (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2)
      ≤ (a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2) := by
  have h := sos p a b
  have hpos : 0 < (a + 2 * b) ^ 2 := by positivity
  have hsq : 0 ≤ 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 := by positivity
  have : 0 ≤ (a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
      - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2) := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  linarith

/-- Every amplitude class has threshold at most the closed form `5(√E − 2√s)²/(2 − E − 4√(Es))`. -/
theorem threshold_le (p a b : ℝ) (hab : a + 2 * b ≠ 0) (hD : 0 < denD p (b ^ 2) (a ^ 2))
    (hW : 0 < 2 - a ^ 2 - 4 * a * b) :
    5 * numA p (b ^ 2) (a ^ 2) / denD p (b ^ 2) (a ^ 2)
      ≤ 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b) := by
  rw [div_le_div_iff₀ hD hW]
  nlinarith [cleared_le p a b hab]

/-- Equality holds exactly at the binding class `bA = a(1 − a² − 2b²)`. -/
theorem threshold_eq (p a b : ℝ) (hab : a + 2 * b ≠ 0) (hD : 0 < denD p (b ^ 2) (a ^ 2))
    (hW : 0 < 2 - a ^ 2 - 4 * a * b) :
    5 * numA p (b ^ 2) (a ^ 2) / denD p (b ^ 2) (a ^ 2)
        = 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b)
      ↔ b * numA p (b ^ 2) (a ^ 2) = a * (1 - a ^ 2 - 2 * b ^ 2) := by
  rw [div_eq_div_iff hD.ne' hW.ne']
  have h := sos p a b
  have hpos : (a + 2 * b) ^ 2 ≠ 0 := by positivity
  constructor
  · intro heq
    have h0 : (a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
        - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2) = 0 := by linarith
    rw [h0, mul_zero] at h
    have : (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro heq
    have h1 : 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 = 0 := by
      rw [heq]; ring
    rw [h1] at h
    have h2 := (mul_eq_zero.mp h).resolve_left hpos
    linarith

/-- The binding class solves the equality condition. -/
theorem pstar_eq (a b : ℝ) (hb : b ≠ 0) (h2 : a - 2 * b ≠ 0) :
    b * numA ((a ^ 2 + a * b - 1) / (b * (a - 2 * b))) (b ^ 2) (a ^ 2)
      = a * (1 - a ^ 2 - 2 * b ^ 2) := by
  have h2' : a - b * 2 ≠ 0 := by intro h; apply h2; linarith
  unfold numA
  field_simp
  ring

end ChainAMGM
