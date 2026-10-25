/-
Mixed fourth/sixth-power source step: the LOW payment algebra (research/mixed-step/README.md).

Collet's LOW branch (paper69 (G9)) pays the slot excess `X` beyond the parent's capacity at
rate `q` with a sixth-power pool of width `a`; the pool shrinks the parent's capacity by
`6aB₀/Λ₀`, so `a(1 - 6qβ) ≥ qX₀ + r` with `β = B₀/Λ₀`. A selected block of width `d`, taken
from the excess and absorbed by a fourth-power transfer, saves `e` per unit (energy), avoids its
own erasure (`q` per unit) and costs `c` per unit of row scale. Then

  `a(1 - 6qβ) + d(e + q - cqβ) ≥ qX₀ + r`.

Readings: `e = 1, c = 6` (Sil's ledger: dilation 4 plus the reference shift 2), `e = 1, c = 4`,
and `e = 0, c = 4` (a transfer that only moves the block into the frequency).
-/
import Mathlib

namespace MixedStepLedger

/-- The mixed LOW payment condition. -/
def Pays (q β e c a d X₀ r : ℝ) : Prop :=
  q * X₀ + r ≤ a * (1 - 6 * q * β) + d * (e + q - c * q * β)

/-- The excess after the amplifiers, `X = X₀ + (6a + cd)β`, as in (G9)–(G10). -/
def excess (β c a d X₀ : ℝ) : ℝ := X₀ + (6 * a + c * d) * β

/-- The payment condition is exactly "savings cover the erasure of the unselected excess":
`a + e·d ≥ q·(X − d) + r`. -/
theorem pays_iff (q β e c a d X₀ r : ℝ) :
    Pays q β e c a d X₀ r ↔ q * (excess β c a d X₀ - d) + r ≤ a + e * d := by
  unfold Pays excess
  constructor <;> intro h <;> nlinarith

/-- With a positive selection coefficient, a selection alone (no pool) pays any excess. -/
theorem selection_pays {q β e c X₀ r : ℝ} (hcoef : 0 < e + q - c * q * β) :
    Pays q β e c 0 ((q * X₀ + r) / (e + q - c * q * β)) X₀ r := by
  unfold Pays
  rw [div_mul_cancel₀ _ hcoef.ne']
  simp

/-- Sil's reading (`e = 1`, `c = 6`): the regress breaks exactly when `Λ₀/B₀ > 6q/(1 + q)`,
against `Λ₀/B₀ > 6q` for the pool. -/
theorem sil_reading_threshold {q B₀ Λ₀ : ℝ} (hq : 0 < q) (hB : 0 < B₀) (hΛ : 0 < Λ₀) :
    0 < 1 + q - 6 * q * (B₀ / Λ₀) ↔ 6 * q / (1 + q) < Λ₀ / B₀ := by
  have h1q : 0 < 1 + q := by linarith
  rw [div_lt_div_iff₀ h1q hB, sub_pos, mul_div_assoc']
  rw [div_lt_iff₀ hΛ]
  constructor <;> intro h <;> nlinarith

/-- The pool's threshold, for comparison: `1 - 6qβ > 0 ↔ Λ₀/B₀ > 6q`. -/
theorem pool_threshold {q B₀ Λ₀ : ℝ} (hB : 0 < B₀) (hΛ : 0 < Λ₀) :
    0 < 1 - 6 * q * (B₀ / Λ₀) ↔ 6 * q < Λ₀ / B₀ := by
  rw [sub_pos, lt_div_iff₀ hB, mul_div_assoc', div_lt_iff₀ hΛ]
  constructor <;> intro h <;> linarith

/-- Per unit of excess, the selection's row-scale cost is `c·q/(e + q)`; at `e = 1, c = 6` this is
the pool's `6q` divided by `1 + q`. -/
theorem exchange_rate (q : ℝ) (hq : 0 < q) : 6 * q / (1 + q) = (6 * q) * (1 / (1 + q)) := by
  have : (1 + q) ≠ 0 := by linarith
  field_simp

/-- A transfer without a saving (`e = 0`) has coefficient `q(1 − cβ)`, positive only when
`Λ₀ > c·B₀`; for `c = 4` it never helps on the family's range `Λ₀/B₀ ≤ 4`. -/
theorem no_saving_useless {q β c : ℝ} (hq : 0 < q) (hcβ : 1 ≤ c * β) :
    0 + q - c * q * β ≤ 0 := by nlinarith

/-- The selection never exceeds the excess it is taken from when `cβ ≥ 1`: `d ≤ X₀ + cdβ`. -/
theorem selection_within_excess {β c d X₀ : ℝ} (hX : 0 ≤ X₀) (hd : 0 ≤ d) (hcβ : 1 ≤ c * β) :
    d ≤ excess β c 0 d X₀ := by
  unfold excess; nlinarith

/-- Sil's initial-face ledger: live width costs `2` (row) and `κ` (native), selected width costs
`6` (row) and saves `1`. With the native gate `κ·S ≤ d`, the cost per unit of total width is at
least `(2 + 6κ)/(1 + κ)`. -/
theorem sil_face_floor {κ S d : ℝ} (hκ : 0 ≤ κ) (_hS : 0 ≤ S) (_hd : 0 ≤ d) (hpos : 0 < S + d)
    (hgate : κ * S ≤ d) :
    (2 + 6 * κ) / (1 + κ) ≤ (2 * S + 6 * d) / (S + d) := by
  have h1κ : 0 < 1 + κ := by linarith
  rw [div_le_div_iff₀ h1κ hpos]
  nlinarith

/-- That floor beats the pool's `6κ` iff `3κ² > 1` (κ > 1/√3); at κ = 3/4 it is 26/7. -/
theorem sil_beats_pool_iff {κ : ℝ} (hκ : 0 < κ) :
    (2 + 6 * κ) / (1 + κ) < 6 * κ ↔ 1 < 3 * κ ^ 2 := by
  have h1κ : 0 < 1 + κ := by linarith
  rw [div_lt_iff₀ h1κ]
  constructor <;> intro h <;> nlinarith

theorem sil_floor_at_three_quarters : (2 + 6 * (3 / 4 : ℝ)) / (1 + 3 / 4) = 26 / 7 := by
  norm_num

/-- The step's analogue with native rate `q` (Sil-LOW): `(2 + 6q)/(1 + q)` beats the pool's `6q`
iff `3q² > 1`, so only on the early part of the family (`q > 0.577`); the erase reading's
`6q/(1 + q)` beats it for every `q > 0`. -/
theorem erase_beats_pool {q : ℝ} (hq : 0 < q) : 6 * q / (1 + q) < 6 * q := by
  have h1q : 1 < 1 + q := by linarith
  exact div_lt_self (by linarith) h1q

end MixedStepLedger
