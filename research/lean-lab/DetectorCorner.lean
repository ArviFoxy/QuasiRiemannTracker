/-
The count's corner is triple-tight (research/LOG.md, "Round-5 detector agent").

Collet's return (return.tex NR1–NR2) defines the three same-zero witness lines
  `I(r) = 1 − δ(p + (1 − p)r)`, `P(m) = 1 − 2δm − 2δp(B − 2m)/Λ`, `L(t) = 1/6 + (5/6 − δ)t`
and, through the auxiliary quantities `D, A, C₀, U, J, N, T, R_n, M_n` (written here with
`w = 1/Λ`), the corner
  `R = N/J`, `t* = T/J`, `r* = R_n/(DJ)`, `m* = M_n/(DJ)`.
* `corner_sum`: `r* + m* = t*`. So the corner block `M_{r*} S_{m*}`, counted as one polynomial, has
  exactly the cutoff length `t*`, and a perfect mixed moment for it costs exactly `L(t*)`.
* `corner_L`, `corner_I`, `corner_P`: `L(t*) = I(r*) = P(m*) = R`.
* `straddle`: for `n > 1`, `Σ_{l | n} μ(l) V(l) = −Σ_{l | n} μ(l) (1 − V(l))` for every weight `V`.
  With `V = 1` on `[0, D]` and `V = 0` on `[2D, ∞)` the left sum lives on `l ≤ 2D` and the right on
  `l ≥ D`, so the tail carried by every level has a saturated pair on each side of the cutoff.
Status: proved (algebra and the Möbius identity; the analytic reading is in the log).
-/
import Mathlib

namespace DetectorCorner

/-- The inverse, plain and long witness lines of NR1 (affine plain branch), with `w = 1/Λ`. -/
noncomputable def lineI (δ p r : ℝ) : ℝ := 1 - δ * (p + (1 - p) * r)
noncomputable def lineP (δ p B w m : ℝ) : ℝ := 1 - 2 * δ * m - 2 * δ * p * ((B - 2 * m) * w)
noncomputable def lineL (δ t : ℝ) : ℝ := 1 / 6 + (5 / 6 - δ) * t

/-- The auxiliary quantities of NR2, written with `w = 1/Λ`. -/
noncomputable def Vv (δ : ℝ) : ℝ := 5 / 6 - δ
noncomputable def Dv (p w : ℝ) : ℝ := 3 - p - 4 * p * w
noncomputable def Av (p w : ℝ) : ℝ := 2 - 4 * p * w
noncomputable def C0v (p B w : ℝ) : ℝ := 1 - 2 * p * B * w
noncomputable def Uv (p B w : ℝ) : ℝ := (1 - p) * C0v p B w
noncomputable def Jv (δ p w : ℝ) : ℝ := Vv δ * Dv p w + δ * (1 - p) * Av p w
noncomputable def Nv (δ p B w : ℝ) : ℝ := (1 - δ) * Jv δ p w + Vv δ * δ * Uv p B w
noncomputable def Tv (δ p B w : ℝ) : ℝ := Jv δ p w + δ * Uv p B w
noncomputable def Rnv (δ p B w : ℝ) : ℝ :=
  Av p w * Tv δ p B w + (2 * p * B * w - p) * Jv δ p w
noncomputable def Mnv (δ p B w : ℝ) : ℝ := Dv p w * Tv δ p B w - Rnv δ p B w

/-- The corner: count `R`, cutoff `t*`, inverse length `r*`, plain length `m*`. -/
noncomputable def cornerR (δ p B w : ℝ) : ℝ := Nv δ p B w / Jv δ p w
noncomputable def cornerT (δ p B w : ℝ) : ℝ := Tv δ p B w / Jv δ p w
noncomputable def cornerr (δ p B w : ℝ) : ℝ := Rnv δ p B w / (Dv p w * Jv δ p w)
noncomputable def cornerm (δ p B w : ℝ) : ℝ := Mnv δ p B w / (Dv p w * Jv δ p w)

theorem corner_sum (δ p B w : ℝ) (hD : Dv p w ≠ 0) (hJ : Jv δ p w ≠ 0) :
    cornerr δ p B w + cornerm δ p B w = cornerT δ p B w := by
  unfold cornerr cornerm cornerT Mnv
  field_simp
  ring

theorem corner_L (δ p B w : ℝ) (hJ : Jv δ p w ≠ 0) :
    lineL δ (cornerT δ p B w) = cornerR δ p B w := by
  unfold lineL cornerT cornerR
  rw [eq_div_iff hJ]
  field_simp
  unfold Nv Tv Vv
  ring

theorem corner_I (δ p B w : ℝ) (hD : Dv p w ≠ 0) (hJ : Jv δ p w ≠ 0) :
    lineI δ p (cornerr δ p B w) = cornerR δ p B w := by
  unfold lineI cornerr cornerR
  rw [eq_div_iff hJ]
  field_simp
  unfold Rnv Nv Tv Jv Uv C0v Av Dv Vv
  ring

theorem corner_P (δ p B w : ℝ) (hD : Dv p w ≠ 0) (hJ : Jv δ p w ≠ 0) :
    lineP δ p B w (cornerm δ p B w) = cornerR δ p B w := by
  unfold lineP cornerm cornerR
  rw [eq_div_iff hJ]
  field_simp
  unfold Mnv Rnv Nv Tv Jv Uv C0v Av Dv Vv
  ring

/-- The straddle identity: for `n > 1` the Möbius sum over divisors vanishes, so a smooth cutoff
`V` can be traded for its complement `1 − V`. -/
theorem straddle (n : ℕ) (hn : 1 < n) (V : ℕ → ℝ) :
    ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) * V l =
      -∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) * (1 - V l) := by
  have h0 : ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) = 0 := by
    have h1 : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n = (1 : ArithmeticFunction ℝ) n := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne (by omega)] at h1
    simpa [ArithmeticFunction.intCoe_apply] using h1
  have hsplit : ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) * (1 - V l) =
      ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) -
        ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℝ) * V l := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    ring
  rw [hsplit, h0]
  ring

end DetectorCorner
