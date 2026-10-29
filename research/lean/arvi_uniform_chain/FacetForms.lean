/-
Explicit forms of the six facets of the repeated-mark gain (`Gain/Gain.lean`, `K = 8`) and the
reduction of the infimum over the amplitude class `p ∈ [0, 1/2]` to the single facet `(1,2)` at
`p = 1/2`.

Notation: `w = 5 - 6ν`; a facet per unit `ν` is `φ = facetVal / ν`;
`D(X) = (X - 1)(25 - 18ν) + (5 - 6ν) = (25 - 18ν)(X - 1 + y(ν))`, so the binding-pair hypothesis
`Q (B0 - 1 + y) ≤ S (L0 - 1 + y)` reads `Q·D(B0) ≤ S·D(L0)` (`sigma_clear`).

Main result `facets_ge_facet12`: for `ν ∈ [1/2, 3/4]`, `p ∈ [0, 1/2]`, `B0 ∈ [22/23, 1]`,
`L0 ∈ [19/10, 13/5]`, `S ∈ [1/50, 1/10]`, `Q ∈ [9/10, 1]`, `S ≤ Q/10`, the binding-pair hypothesis
and two polynomial conditions `hP10`, `hP12`, every facet is at least the facet `(1,2)` at
`p = 1/2`.

* `hP12 : 0 ≤ S D(L0)² + w Q E` is exactly `N₁₂(1/2) ≤ 0` (facet `(1,2)` is non-increasing at
  `p = 1/2`); it is necessary for the conclusion at `k = (1,2)`.
* `hP10` is `P₁₀ ≥ 0` with `P₁₀ = w (w+10) (S D(L0) - Q D(B0)) + 2 D(L0) N₁₀(1/2)`; it follows from
  `N₁₀(1/2) ≥ 0` and the binding-pair hypothesis (`hP10_of_N10`).
* Not needed as hypotheses: `N₁₀(0) ≥ 0` (implied by `N₁₀(1/2) ≥ 0`, and superseded by `hP10`),
  `N₁₁(0), N₁₁(1/2) ≥ 0` (`φ₁₁ ≥ φ₁₀` for every `p` as soon as `S ≤ h Q`), `C0, C00, C01, C02`
  (`φ₀ⱼ ≥ φ₁ⱼ` for every `p` as soon as `S ≥ 1/50`, `Q ≤ 1`), `N₁₂(0) ≤ 0` and `N₁₂'(1/2) ≥ 0`
  (consequences of `hP12` on the box, via a Bernstein certificate).
* `facets_ge_facet12_of_N10`: `hP10` replaced by the simpler `N₁₀(1/2) ≥ 0`;
  `facets_ge_facet12_of_ratio`: if moreover `Q ≤ 13 S`, then `hP10` and `hP12` hold automatically.

The identities are re-checked independently in
`research/face-region/uniform/facets_lean_check.py`.
-/
import Submissions.arvi_uniform_chain.BindingPair

set_option autoImplicit false

namespace QRH.ArviUniformChain
noncomputable section

open QRH.RepeatedMarks

-- Abbreviations (expanded at parse time): `w = 5 - 6ν`, `D(X)`, `E`, `a`, `bb`, `V(p)`.
/-- `D(ν, X) = (X - 1)(25 - 18ν) + (5 - 6ν)`. -/
local notation:max "Dp[" ν ", " X "]" => ((X - 1) * (25 - 18 * ν) + (5 - 6 * ν))
/-- `E(ν, B, L)`: `N₁₂(1/2) = -(D(L)² S + w Q E)/2`. -/
local notation:max "Ep[" ν ", " B ", " L "]" =>
  (B * L * (5 - 6 * ν) - 10 * B * L - 4 * B * (5 - 6 * ν) - 4 * L ^ 2 * (5 - 6 * ν) +
    6 * L * (5 - 6 * ν) + 10 * L)
/-- `a(ν, L) = 10 L + 4w - L w`. -/
local notation:max "Ap[" ν ", " L "]" => (10 * L + 4 * (5 - 6 * ν) - L * (5 - 6 * ν))
/-- `bb(ν, B, L) = 3BLw + 10BL - 4Bw + 2Lw - 10L`. -/
local notation:max "Bp[" ν ", " B ", " L "]" =>
  (3 * B * L * (5 - 6 * ν) + 10 * B * L - 4 * B * (5 - 6 * ν) + 2 * L * (5 - 6 * ν) - 10 * L)
/-- `V(p)`: the denominator of the root of facet `(1,2)`, `V(1/2) = D(L)/2`. -/
local notation:max "Vp[" ν ", " p ", " L "]" =>
  (12 * ν * (1 - p) * (L - 2 * p) + (5 - 6 * ν) * (2 * (L - 2 * p) + L * (1 - p)))

/-! ### Closed forms of the facets `(1,0)` and `(1,2)` -/

set_option linter.unusedVariables false in
/-- Facet `(1,0)` (one inverse copy, plain width branch) in closed form. -/
theorem facetVal_10 (ν p K B lam h S Q : ℝ) (hp : p < 1) :
    facetVal ν p K B lam h S Q ((1 : Fin 2), (0 : Fin 3)) =
      (1 - 2*p)*ν*S + ν*((5*Q + (5 - 6*ν)*(p*Q/(1 - p) + p*S)) /
        (6*ν + (5 - 6*ν)*(1/(1 - p) + 1/2)) - 10/(15 - 6*ν)*Q) := by
  simp only [facetVal, branchRoot, branchOffset, branchSlope, invSlope, invOffset, plainSlope,
    plainOffset, w, baseXi, densityDenom, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- Facet `(1,0)` with polynomial denominators (independent of `K`, `B`, `lam`, `h`). -/
theorem facet10_closed {ν p K B lam h S Q : ℝ} (hν : ν ≤ 3/4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) :
    facetVal ν p K B lam h S Q ((1 : Fin 2), (0 : Fin 3)) =
      ν*((1 - 2*p)*S + 2*(5*Q*(1-p) + (5-6*ν)*p*Q + (5-6*ν)*p*S*(1-p)) /
        (10*(1-p) + (5-6*ν)*(1+p)) - 10/(15 - 6*ν)*Q) := by
  rw [facetVal_10 ν p K B lam h S Q (by linarith)]
  have h1p : (1:ℝ) - p ≠ 0 := by linarith
  have hD : (10:ℝ)*(1-p) + (5-6*ν)*(1+p) ≠ 0 := by nlinarith
  have hs : 6*ν + (5 - 6*ν)*(1/(1 - p) + 1/2) ≠ 0 := by
    have : 6*ν + (5 - 6*ν)*(1/(1 - p) + 1/2) = (10*(1-p) + (5-6*ν)*(1+p))/(2*(1-p)) := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero hD (by linarith)
  have h15 : (15:ℝ) - 6*ν ≠ 0 := by linarith
  field_simp
  ring

/-- Facet `(1,2)` with polynomial denominators (independent of `K`, `h`). -/
theorem facet12_closed {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hp1 : p ≤ 1/2)
    (hL : 1 < L) :
    facetVal ν p K B L h S Q ((1 : Fin 2), (2 : Fin 3)) =
      ν*((1 - 2*p)*S + 2*Q*(5*(1-p)*(L-2*p) + (5-6*ν)*p*(L-2*p+B*(1-p))) / Vp[ν, p, L]
        - 10/(15 - 6*ν)*Q) := by
  have h1p : (1:ℝ) - p ≠ 0 := by linarith
  have hL0 : L ≠ 0 := by linarith
  have hLp : L - 2*p ≠ 0 := by linarith
  have hLp' : L - p*2 ≠ 0 := by linarith
  have e1 : (1:ℝ) - 2*p/L = (L - 2*p)/L := by field_simp
  have h15 : (15:ℝ) - 6*ν ≠ 0 := by linarith
  have hw : (0:ℝ) < 5 - 6*ν := by linarith
  have h1 : 0 < 1 - p := by linarith
  have h2 : 0 < L - 2*p := by linarith
  have h3 : 0 < ν := by linarith
  have hV : Vp[ν, p, L] ≠ 0 := by
    have : 0 < L := by linarith
    positivity
  have hs : 6*ν + (5 - 6*ν)*(1/(1 - p) + 1/((L - 2*p)/L)/2) ≠ 0 := by
    have : 6*ν + (5 - 6*ν)*(1/(1 - p) + 1/((L - 2*p)/L)/2) =
        Vp[ν, p, L]/(2*(1-p)*(L-2*p)) := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero hV (by positivity)
  simp only [facetVal, branchRoot, branchOffset, branchSlope, invSlope, invOffset, plainSlope,
    plainOffset, w, baseXi, densityDenom, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [e1]
  have hV' : 12*ν*(1-p)*(L-p*2) + (5-6*ν)*(2*(L-p*2) + L*(1-p)) ≠ 0 := by
    have := hV; ring_nf at this ⊢; exact this
  field_simp
  ring

/-- Facet `(1,2)` at `p = 1/2`: `ν (Q R - 10 Q/(15-6ν))` with `R = Rn/D(L)`. -/
theorem facet12_half_closed {ν K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hL : 1 < L) :
    facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) =
      ν*(Q*((L-1)*(20-12*ν) + (5-6*ν)*B)/Dp[ν, L] - 10/(15 - 6*ν)*Q) := by
  rw [facet12_closed hν hν' le_rfl hL]
  have hD1 : Dp[ν, L] ≠ 0 := by nlinarith
  have hV : 12*ν*(1-1/2)*(L-2*(1/2)) + (5-6*ν)*(2*(L-2*(1/2)) + L*(1-1/2)) ≠ 0 := by nlinarith
  have e : 2*Q*(5*(1-1/2)*(L-2*(1/2)) + (5-6*ν)*(1/2)*(L-2*(1/2)+B*(1-1/2))) /
      (12*ν*(1-1/2)*(L-2*(1/2)) + (5-6*ν)*(2*(L-2*(1/2)) + L*(1-1/2))) =
      Q*((L-1)*(20-12*ν) + (5-6*ν)*B)/Dp[ν, L] := by
    rw [div_eq_div_iff hV hD1]
    ring
  rw [e]
  ring

/-! ### Facet `(1,0)` -/

/-- Facet `(1,0)` at `p` minus the binding facet `(1,2)` at `p = 1/2`, in closed form:
numerator `w g M + 2 (1-2p) N₁₀(p) D(L)` over `(25-18ν) D(L) M`, with `g = S D(L) - Q D(B)`,
`M = 10(1-p) + w(1+p)` and `N₁₀ = S[(3w²-5w-50)p + w²+15w+50] - Q w²`. -/
theorem facet10_sub_facet12 {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hL : 1 < L) :
    facetVal ν p K B L h S Q ((1 : Fin 2), (0 : Fin 3)) -
        facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) =
      ν * ((5 - 6*ν) * (S*Dp[ν, L] - Q*Dp[ν, B]) * (10*(1-p) + (5-6*ν)*(1+p))
            + 2*(1-2*p)*(S*((3*(5-6*ν)^2 - 5*(5-6*ν) - 50)*p + (5-6*ν)^2 + 15*(5-6*ν) + 50)
                - Q*(5-6*ν)^2) * Dp[ν, L]) /
        ((25 - 18*ν) * Dp[ν, L] * (10*(1-p) + (5-6*ν)*(1+p))) := by
  rw [facet10_closed hν' hp0 hp1, facet12_half_closed hν hν' hL]
  have hM : (10:ℝ)*(1-p) + (5-6*ν)*(1+p) ≠ 0 := by nlinarith
  have hU : (25:ℝ) - 18*ν ≠ 0 := by linarith
  have h15 : (15:ℝ) - 6*ν ≠ 0 := by linarith
  have hD1 : Dp[ν, L] ≠ 0 := by nlinarith
  generalize hMdef : (10:ℝ)*(1-p) + (5-6*ν)*(1+p) = M at hM ⊢
  generalize hDdef : Dp[ν, L] = D1 at hD1 ⊢
  generalize hUdef : (25:ℝ) - 18*ν = U at hU ⊢
  generalize hVdef : (15:ℝ) - 6*ν = V at h15 ⊢
  field_simp
  subst hMdef hUdef hVdef hDdef
  ring

/-- **Facet `(1,0)` stays above the binding facet `(1,2)` at `p = 1/2`.**
`hg` is the binding-pair hypothesis `σ ≤ S/Q` cleared of denominators (`sigma_clear`), and `hP10`
is the quantitative companion `P₁₀ ≥ 0` (for `p → 1/2` it controls the derivative of facet `(1,0)`).
-/
theorem facet10_ge {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hL : 1 < L) (hS : 0 ≤ S)
    (hg : Q*Dp[ν, B] ≤ S*Dp[ν, L])
    (hP10 : Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) ≤
      S*Dp[ν, L]*((15-12*ν)*(25-18*ν))) :
    facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p K B L h S Q ((1 : Fin 2), (0 : Fin 3)) := by
  have hid := facet10_sub_facet12 (K := K) (B := B) (h := h) (S := S) (Q := Q) hν hν' hp0 hp1 hL
  have hw : 0 < 5 - 6*ν := by linarith
  have hU : 0 < 25 - 18*ν := by linarith
  have hD1 : 0 < Dp[ν, L] := by nlinarith
  have hM : 0 < 10*(1-p) + (5-6*ν)*(1+p) := by nlinarith
  have hq : 0 ≤ 1 - 2*p := by linarith
  have hν1 : 0 ≤ S*(50 + 5*(5-6*ν) - 3*(5-6*ν)^2) := by
    apply mul_nonneg hS; nlinarith
  have hg' : 0 ≤ S*Dp[ν, L] - Q*Dp[ν, B] := by linarith
  have hP' : 0 ≤ S*Dp[ν, L]*((15-12*ν)*(25-18*ν))
      - Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) := by
    linarith
  -- decomposition of the numerator: `p w g (25-18ν) + (1-2p) P₁₀ + S(50+5w-3w²) D (1-2p)²`
  have hΦ : (5 - 6*ν) * (S*Dp[ν, L] - Q*Dp[ν, B]) * (10*(1-p) + (5-6*ν)*(1+p))
            + 2*(1-2*p)*(S*((3*(5-6*ν)^2 - 5*(5-6*ν) - 50)*p + (5-6*ν)^2 + 15*(5-6*ν) + 50)
                - Q*(5-6*ν)^2) * Dp[ν, L] =
      p*(5-6*ν)*(S*Dp[ν, L] - Q*Dp[ν, B])*(25-18*ν)
      + (1-2*p)*(S*Dp[ν, L]*((15-12*ν)*(25-18*ν))
        - Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]))
      + S*(50 + 5*(5-6*ν) - 3*(5-6*ν)^2)*Dp[ν, L]*(1-2*p)^2 := by
    ring
  have hnn : 0 ≤ facetVal ν p K B L h S Q ((1 : Fin 2), (0 : Fin 3)) -
      facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) := by
    rw [hid]
    apply div_nonneg
    · apply mul_nonneg (by linarith)
      rw [hΦ]
      have t1 := mul_nonneg (mul_nonneg (mul_nonneg hp0 hw.le) hg') hU.le
      have t2 := mul_nonneg hq hP'
      have t3 := mul_nonneg (mul_nonneg hν1 hD1.le) (sq_nonneg (1-2*p))
      linarith
    · positivity
  linarith

/-! ### Facet `(1,1)` -/

/-- Facet `(1,1)` dominates facet `(1,0)` at every `p ∈ [0,1/2]` as soon as `S ≤ h Q`
(same slope, plain offset `-2phQ` instead of `-2pS`). -/
theorem facet10_le_facet11 {ν p K B lam h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hlam : 1 < lam) (hSQ : S ≤ h*Q) :
    facetVal ν p K B lam h S Q ((1 : Fin 2), (0 : Fin 3)) ≤
      facetVal ν p K B lam h S Q ((1 : Fin 2), (1 : Fin 3)) := by
  have hw : 0 < 5 - 6*ν := by linarith
  have hs : branchSlope ν p lam ((1 : Fin 2), (1 : Fin 3)) =
      branchSlope ν p lam ((1 : Fin 2), (0 : Fin 3)) := by
    simp only [branchSlope, plainSlope, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hpos : 0 < branchSlope ν p lam ((1 : Fin 2), (0 : Fin 3)) :=
    branchSlope_pos (by linarith) hν' (by linarith) (by linarith) (by linarith) _
  have ho : branchOffset ν p K B lam h S Q ((1 : Fin 2), (1 : Fin 3)) ≤
      branchOffset ν p K B lam h S Q ((1 : Fin 2), (0 : Fin 3)) := by
    simp only [branchOffset, invOffset, plainOffset, w, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith [mul_nonneg (mul_nonneg hw.le hp0) (sub_nonneg.2 hSQ)]
  have hr : branchRoot ν p K B lam h S Q ((1 : Fin 2), (0 : Fin 3)) ≤
      branchRoot ν p K B lam h S Q ((1 : Fin 2), (1 : Fin 3)) := by
    unfold branchRoot
    rw [hs]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  unfold facetVal
  nlinarith [hr, mul_le_mul_of_nonneg_left hr (by linarith : (0:ℝ) ≤ ν)]

/-- Facet `(1,1)` stays above the binding facet `(1,2)` at `p = 1/2`. -/
theorem facet11_ge {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hL : 1 < L) (hS : 0 ≤ S) (hSQ : S ≤ h*Q)
    (hg : Q*Dp[ν, B] ≤ S*Dp[ν, L])
    (hP10 : Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) ≤
      S*Dp[ν, L]*((15-12*ν)*(25-18*ν))) :
    facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p K B L h S Q ((1 : Fin 2), (1 : Fin 3)) :=
  (facet10_ge hν hν' hp0 hp1 hL hS hg hP10).trans (facet10_le_facet11 hν hν' hp0 hp1 hL hSQ)

/-! ### Facet `(1,2)` -/

/-- Basis element of the Bernstein certificates below. -/
private theorem bern3_nonneg {a b c d e f : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (i1 i2 j1 j2 k1 k2 : ℕ) :
    0 ≤ a ^ i1 * b ^ i2 * (c ^ j1 * d ^ j2) * (e ^ k1 * f ^ k2) := by
  positivity

/-- Polynomial positivity on the box (Bernstein certificate): `-a·E - bb·D(L) ≥ 0`
(with `w = 5 - 6ν`); it makes `N₁₂'(1/2) ≥ 0` follow from `N₁₂(1/2) ≤ 0`. -/
theorem poly12_nonneg {ν B L : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hB1 : 22/23 ≤ B) (hB2 : B ≤ 1)
    (hL1 : 19/10 ≤ L) (hL2 : L ≤ 13/5) :
    0 ≤ -(Ap[ν, L]*Ep[ν, B, L]) - Bp[ν, B, L]*Dp[ν, L] := by
  have s0 : 0 ≤ (5-6*ν) - 1/2 := by linarith
  have s1 : 0 ≤ 2 - (5-6*ν) := by linarith
  have t0 : 0 ≤ L - 19/10 := by linarith
  have t1 : 0 ≤ 13/5 - L := by linarith
  have b0 : 0 ≤ B - 22/23 := by linarith
  have b1 : 0 ≤ 1 - B := by linarith
  linarith [bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 0 3 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 0 3 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 1 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 1 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 2 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 2 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 3 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 3 0 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 0 3 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 0 3 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 1 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 1 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 2 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 2 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 3 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 3 0 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 0 3 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 0 3 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 1 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 1 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 2 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 2 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 3 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 3 0 1 0]

/-- Facet `(1,2)` at `p` minus facet `(1,2)` at `p = 1/2`: a quadratic Taylor form in `p - 1/2`,
`2ν(1-2p)(F₀ + F₁ (p-1/2) + F₂ (p-1/2)²) / (D V(p))` with `D = D(L)`,
`F₀ = (S D² + w Q E)/4`, `F₁ = -(a D S - w bb Q)/2`, `F₂ = 12 ν S D`. -/
theorem facet12_sub_half {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hp1 : p ≤ 1/2)
    (hL : 1 < L) :
    facetVal ν p K B L h S Q ((1 : Fin 2), (2 : Fin 3)) -
        facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) =
      2*ν*(1-2*p)*((Dp[ν, L]^2*S + (5-6*ν)*Q*Ep[ν, B, L])/4
        + (-(Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q)/2)*(p-1/2)
        + (12*ν*S*Dp[ν, L])*(p-1/2)^2) / (Dp[ν, L] * Vp[ν, p, L]) := by
  rw [facet12_closed hν hν' hp1 hL, facet12_half_closed hν hν' hL]
  have hD1 : Dp[ν, L] ≠ 0 := by nlinarith
  have hV : Vp[ν, p, L] ≠ 0 := by
    have h1 : 0 < 1 - p := by linarith
    have h2 : 0 < L - 2*p := by linarith
    have h3 : 0 < ν := by linarith
    have hw : 0 < 5 - 6*ν := by linarith
    have : 0 < L := by linarith
    positivity
  have h15 : (15:ℝ) - 6*ν ≠ 0 := by linarith
  generalize hVdef : Vp[ν, p, L] = V at hV ⊢
  generalize hDdef : Dp[ν, L] = D at hD1 ⊢
  generalize h15def : (15:ℝ) - 6*ν = U at h15 ⊢
  field_simp
  subst hVdef hDdef h15def
  ring

/-- **Facet `(1,2)` is non-increasing on `[0,1/2]`** (its value at `p` is at least its value at
`1/2`) provided `S D(L)² + w Q E ≥ 0`, i.e. `N₁₂(1/2) ≤ 0`: the facet is non-increasing at
`p = 1/2`.  (This condition is also necessary.) -/
theorem facet12_ge {ν p K B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hp1 : p ≤ 1/2)
    (hB : 22/23 ≤ B) (hB' : B ≤ 1) (hL : 19/10 ≤ L) (hL' : L ≤ 13/5)
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hP12 : 0 ≤ S*Dp[ν, L]^2 + (5-6*ν)*Q*Ep[ν, B, L]) :
    facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p K B L h S Q ((1 : Fin 2), (2 : Fin 3)) := by
  have hL1 : 1 < L := by linarith
  have hid := facet12_sub_half (K := K) (B := B) (h := h) (S := S) (Q := Q) hν hν' hp1 hL1
  have hw : 0 < 5 - 6*ν := by linarith
  have hD1 : 0 < Dp[ν, L] := by
    have := mul_pos (sub_pos.2 hL1) (by linarith : (0:ℝ) < 25 - 18*ν)
    linarith
  have hV : 0 < Vp[ν, p, L] := by
    have h1 : 0 < 1 - p := by linarith
    have h2 : 0 < L - 2*p := by linarith
    have h3 : 0 < ν := by linarith
    have : 0 < L := by linarith
    positivity
  have ha : 0 ≤ Ap[ν, L] := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L) (by linarith : (0:ℝ) ≤ 2 - (5-6*ν))]
  have hpoly := poly12_nonneg hν hν' hB hB' hL hL'
  -- the derivative at `1/2` has the right sign:
  -- `D · N₁₂'(1/2) = a (S D² + w Q E) + w Q (-a E - bb D)`
  have hN : 0 ≤ Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q := by
    have h1 : 0 ≤ Ap[ν, L]*(S*Dp[ν, L]^2 + (5-6*ν)*Q*Ep[ν, B, L]) := mul_nonneg ha hP12
    have h2 : Dp[ν, L]*(Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q) =
        Ap[ν, L]*(S*Dp[ν, L]^2 + (5-6*ν)*Q*Ep[ν, B, L])
          + (5-6*ν)*Q*(-(Ap[ν, L]*Ep[ν, B, L]) - Bp[ν, B, L]*Dp[ν, L]) := by ring
    have h3 : 0 ≤ (5-6*ν)*Q*(-(Ap[ν, L]*Ep[ν, B, L]) - Bp[ν, B, L]*Dp[ν, L]) :=
      mul_nonneg (mul_nonneg hw.le hQ) hpoly
    have h4 : 0 ≤ Dp[ν, L]*(Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q) := by
      rw [h2]; exact add_nonneg h1 h3
    exact (mul_nonneg_iff_of_pos_left hD1).1 h4
  have hF : 0 ≤ (Dp[ν, L]^2*S + (5-6*ν)*Q*Ep[ν, B, L])/4
        + (-(Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q)/2)*(p-1/2)
        + (12*ν*S*Dp[ν, L])*(p-1/2)^2 := by
    have e1 : 0 ≤ (Dp[ν, L]^2*S + (5-6*ν)*Q*Ep[ν, B, L])/4 := by linarith
    have e2 : 0 ≤ (-(Ap[ν, L]*Dp[ν, L]*S - (5-6*ν)*Bp[ν, B, L]*Q)/2)*(p-1/2) := by
      apply mul_nonneg_of_nonpos_of_nonpos _ (by linarith)
      linarith
    have e3 : 0 ≤ (12*ν*S*Dp[ν, L])*(p-1/2)^2 := by positivity
    linarith
  have hnn : 0 ≤ facetVal ν p K B L h S Q ((1 : Fin 2), (2 : Fin 3)) -
      facetVal ν (1/2) K B L h S Q ((1 : Fin 2), (2 : Fin 3)) := by
    rw [hid]
    apply div_nonneg
    · apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hF
    · positivity
  linarith

/-! ### The eight-copy facets are never binding -/

/-- Root comparison between the single-copy inverse witness (slope `1/(1-p)`, offset `-pQ/(1-p)`)
and the `K`-copy one (slope `1`, offset `-2pKS`), for an arbitrary plain witness `(t, q)`:
the difference of the cross products is `w p/(1-p) · g` with
`g = 2KS((6ν + w t/2)(1-p) + w) - (w/2)(q + Q t)`. -/
theorem root_cmp_aux {ν p K S Q t q : ℝ} (hw : 0 < 5 - 6*ν) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hA : 0 < 6*ν + (5-6*ν)*t/2)
    (hg : (5-6*ν)/2*(q + Q*t) ≤ 2*K*S*((6*ν + (5-6*ν)*t/2)*(1-p) + (5-6*ν))) :
    (5*Q - (5-6*ν)*(-(p*Q)/(1-p) + q/2)) / (6*ν + (5-6*ν)*(1/(1-p) + t/2)) ≤
      (5*Q - (5-6*ν)*(-(2*p*K*S) + q/2)) / (6*ν + (5-6*ν)*(1 + t/2)) := by
  have h1p : 0 < 1 - p := by linarith
  have h1p' : 1 - p ≠ 0 := h1p.ne'
  have hd2 : 0 < 6*ν + (5-6*ν)*(1 + t/2) := by nlinarith
  have hd1 : 0 < 6*ν + (5-6*ν)*(1/(1-p) + t/2) := by
    have : 0 < (5-6*ν)*(1/(1-p)) := by positivity
    nlinarith
  rw [div_le_div_iff₀ hd1 hd2]
  have key : (5*Q - (5-6*ν)*(-(2*p*K*S) + q/2)) * (6*ν + (5-6*ν)*(1/(1-p) + t/2)) -
      (5*Q - (5-6*ν)*(-(p*Q)/(1-p) + q/2)) * (6*ν + (5-6*ν)*(1 + t/2)) =
      (5-6*ν)*p/(1-p) * (2*K*S*((6*ν + (5-6*ν)*t/2)*(1-p) + (5-6*ν)) - (5-6*ν)/2*(q + Q*t)) := by
    field_simp
    ring
  have hnn : 0 ≤ (5-6*ν)*p/(1-p) *
      (2*K*S*((6*ν + (5-6*ν)*t/2)*(1-p) + (5-6*ν)) - (5-6*ν)/2*(q + Q*t)) :=
    mul_nonneg (div_nonneg (mul_nonneg hw.le hp0) h1p.le) (by linarith)
  linarith

/-- Branch-root comparison `(1,j)` versus `(0,j)`. -/
theorem branchRoot_cmp {ν p K B lam h S Q : ℝ} (j : Fin 3) (hw : 0 < 5 - 6*ν) (hp0 : 0 ≤ p)
    (hp1 : p < 1) (hA : 0 < 6*ν + (5-6*ν)*plainSlope p lam j/2)
    (hg : (5-6*ν)/2*(plainOffset p B lam h S Q j + Q*plainSlope p lam j) ≤
      2*K*S*((6*ν + (5-6*ν)*plainSlope p lam j/2)*(1-p) + (5-6*ν))) :
    branchRoot ν p K B lam h S Q ((1 : Fin 2), j) ≤
      branchRoot ν p K B lam h S Q ((0 : Fin 2), j) := by
  have := root_cmp_aux (K := K) (S := S) (Q := Q) hw hp0 hp1 hA hg
  simpa [branchRoot, branchOffset, branchSlope, invSlope, invOffset, w] using this

/-- Facets are monotone in the branch root. -/
theorem facetVal_le_of_root {ν p K B lam h S Q : ℝ} {k k' : Fin 2 × Fin 3} (hν : 0 ≤ ν)
    (hr : branchRoot ν p K B lam h S Q k ≤ branchRoot ν p K B lam h S Q k') :
    facetVal ν p K B lam h S Q k ≤ facetVal ν p K B lam h S Q k' := by
  unfold facetVal
  nlinarith [mul_le_mul_of_nonneg_left hr hν]

/-- Facet `(0,0)` lies above facet `(1,0)` on the box (`S ≥ 1/50`, `Q ≤ 1`). -/
theorem facet10_le_facet00 {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hS : 1/50 ≤ S) (hQ1 : Q ≤ 1) :
    facetVal ν p 8 B L h S Q ((1 : Fin 2), (0 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (0 : Fin 3)) := by
  have hw : 0 < 5 - 6*ν := by linarith
  have hw2 : 5 - 6*ν ≤ 2 := by linarith
  have hX0 : 2 + (5 - 6*ν) ≤ (6*ν + (5-6*ν)*1/2)*(1-p) + (5-6*ν) := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*1/2) - 4)
      (by linarith : (0:ℝ) ≤ 1 - p)]
  apply facetVal_le_of_root (by linarith)
  apply branchRoot_cmp (0 : Fin 3) hw hp0 (by linarith)
  · simp only [plainSlope, Matrix.cons_val_zero]; linarith
  · simp only [plainSlope, plainOffset, Matrix.cons_val_zero]
    linarith [mul_nonneg (sub_nonneg.2 hS)
        (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*1/2)*(1-p) + (5-6*ν)),
      mul_nonneg (mul_nonneg hw.le hp0) (by linarith : (0:ℝ) ≤ S),
      mul_nonneg hw.le (sub_nonneg.2 hQ1)]

/-- Facet `(0,1)` lies above facet `(1,1)` on the box. -/
theorem facet11_le_facet01 {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hh : 0 ≤ h) (hS : 1/50 ≤ S) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    facetVal ν p 8 B L h S Q ((1 : Fin 2), (1 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (1 : Fin 3)) := by
  have hw : 0 < 5 - 6*ν := by linarith
  have hw2 : 5 - 6*ν ≤ 2 := by linarith
  have hX0 : 2 + (5 - 6*ν) ≤ (6*ν + (5-6*ν)*1/2)*(1-p) + (5-6*ν) := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*1/2) - 4)
      (by linarith : (0:ℝ) ≤ 1 - p)]
  apply facetVal_le_of_root (by linarith)
  apply branchRoot_cmp (1 : Fin 3) hw hp0 (by linarith)
  · simp only [plainSlope, Matrix.cons_val_one, Matrix.cons_val_zero]; linarith
  · simp only [plainSlope, plainOffset, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [mul_nonneg (sub_nonneg.2 hS)
        (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*1/2)*(1-p) + (5-6*ν)),
      mul_nonneg (mul_nonneg (mul_nonneg hw.le hp0) hh) hQ0,
      mul_nonneg hw.le (sub_nonneg.2 hQ1)]

/-- Facet `(0,2)` lies above facet `(1,2)` on the box. -/
theorem facet12_le_facet02 {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hB : 22/23 ≤ B) (hL : 19/10 ≤ L)
    (hS : 1/50 ≤ S) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    facetVal ν p 8 B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (2 : Fin 3)) := by
  have hw : 0 < 5 - 6*ν := by linarith
  have hw2 : 5 - 6*ν ≤ 2 := by linarith
  have hlam : 2*p < L := by linarith
  have hL0 : 0 < L := by linarith
  have hd : 0 < 1 - 2*p/L := by
    rw [sub_pos, div_lt_one hL0]; exact hlam
  have hd1 : 1 - 2*p/L ≤ 1 := by
    have : 0 ≤ 2*p/L := div_nonneg (by linarith) hL0.le
    linarith
  have ht : 1 ≤ 1/(1 - 2*p/L) := one_le_one_div hd hd1
  have hu : 2*p/L ≤ 10/19 := by rw [div_le_iff₀ hL0]; linarith
  have hu0 : 0 ≤ 2*p/L := div_nonneg (by linarith) hL0.le
  -- `q + Q t ≤ (11/10) Q` for the third plain witness
  have hqt : -(2*p*B*Q/L)/(1 - 2*p/L) + Q*(1/(1 - 2*p/L)) ≤ 11/10*Q := by
    have e : -(2*p*B*Q/L)/(1 - 2*p/L) + Q*(1/(1 - 2*p/L)) =
        (Q - (2*p/L)*B*Q)/(1 - 2*p/L) := by
      field_simp
      ring
    rw [e, div_le_iff₀ hd]
    linarith [mul_nonneg hQ0 (sub_nonneg.2 hu), mul_nonneg hQ0 hu0,
      mul_nonneg (mul_nonneg hQ0 hu0) (sub_nonneg.2 hB)]
  have hX0 : 2 + (5 - 6*ν) ≤ (6*ν + (5-6*ν)*1/2)*(1-p) + (5-6*ν) := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*1/2) - 4)
      (by linarith : (0:ℝ) ≤ 1 - p)]
  have hX2 : 2 + (5-6*ν) ≤ (6*ν + (5-6*ν)*(1/(1 - 2*p/L))/2)*(1-p) + (5-6*ν) := by
    linarith [mul_nonneg (mul_nonneg hw.le (sub_nonneg.2 ht)) (by linarith : (0:ℝ) ≤ 1 - p)]
  apply facetVal_le_of_root (by linarith)
  apply branchRoot_cmp (2 : Fin 3) hw hp0 (by linarith)
  · simp only [plainSlope, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have h1 : 0 < 1/(1 - 2*p/L) := by positivity
    have h2 := mul_pos hw h1
    linarith
  · simp only [plainSlope, plainOffset, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linarith [mul_nonneg (sub_nonneg.2 hS)
        (by linarith : (0:ℝ) ≤ (6*ν + (5-6*ν)*(1/(1 - 2*p/L))/2)*(1-p) + (5-6*ν)),
      mul_le_mul_of_nonneg_left hqt hw.le, mul_nonneg hw.le (sub_nonneg.2 hQ1)]

/-- Facet `(0,0)` stays above the binding facet `(1,2)` at `p = 1/2`. -/
theorem facet00_ge {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hL : 1 < L) (hS1 : 1/50 ≤ S) (hQ1 : Q ≤ 1)
    (hg : Q*Dp[ν, B] ≤ S*Dp[ν, L])
    (hP10 : Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) ≤
      S*Dp[ν, L]*((15-12*ν)*(25-18*ν))) :
    facetVal ν (1/2) 8 B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (0 : Fin 3)) :=
  (facet10_ge hν hν' hp0 hp1 hL (by linarith) hg hP10).trans
    (facet10_le_facet00 hν hν' hp0 hp1 hS1 hQ1)

/-- Facet `(0,1)` stays above the binding facet `(1,2)` at `p = 1/2`. -/
theorem facet01_ge {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hL : 1 < L) (hh : 0 ≤ h) (hSQ : S ≤ h*Q)
    (hS1 : 1/50 ≤ S) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hg : Q*Dp[ν, B] ≤ S*Dp[ν, L])
    (hP10 : Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) ≤
      S*Dp[ν, L]*((15-12*ν)*(25-18*ν))) :
    facetVal ν (1/2) 8 B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (1 : Fin 3)) :=
  (facet11_ge hν hν' hp0 hp1 hL (by linarith) hSQ hg hP10).trans
    (facet11_le_facet01 hν hν' hp0 hp1 hh hS1 hQ0 hQ1)

/-- Facet `(0,2)` stays above the binding facet `(1,2)` at `p = 1/2`. -/
theorem facet02_ge {ν p B L h S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1/2) (hB : 22/23 ≤ B) (hB' : B ≤ 1) (hL : 19/10 ≤ L)
    (hL' : L ≤ 13/5) (hS1 : 1/50 ≤ S) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hP12 : 0 ≤ S*Dp[ν, L]^2 + (5-6*ν)*Q*Ep[ν, B, L]) :
    facetVal ν (1/2) 8 B L h S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B L h S Q ((0 : Fin 2), (2 : Fin 3)) :=
  (facet12_ge hν hν' hp1 hB hB' hL hL' (by linarith) hQ0 hP12).trans
    (facet12_le_facet02 hν hν' hp0 hp1 hB hL hS1 hQ0 hQ1)

/-! ### Assembly -/

/-- The binding-pair hypothesis `σ ≤ S/Q` of `facet12_le_facet10`, cleared of denominators. -/
theorem sigma_clear {ν B L S Q : ℝ} (hν' : ν ≤ 3/4)
    (hSσ : Q * (B - 1 + yOf ν) ≤ S * (L - 1 + yOf ν)) :
    Q*Dp[ν, B] ≤ S*Dp[ν, L] := by
  have h25 : (0:ℝ) < 25 - 18*ν := by linarith
  have e : ∀ X : ℝ, (X-1)*(25-18*ν) + (5-6*ν) = (25-18*ν)*(X - 1 + yOf ν) := by
    intro X
    unfold yOf
    field_simp
  rw [e B, e L]
  nlinarith [mul_le_mul_of_nonneg_left hSσ h25.le]

set_option linter.unusedVariables false in
/-- **Every facet at every `p ∈ [0,1/2]` is at least the binding facet `(1,2)` at `p = 1/2`.**

Hypotheses beyond the box: `hSQ` (`φ₁₁(1/2) ≥ φ₁₀(1/2)`), `hSσ` (`φ₁₀(1/2) ≥ φ₁₂(1/2)`), `hP10`
(`P₁₀ ≥ 0`, which controls `φ₁₀` for `p < 1/2`) and `hP12` (`N₁₂(1/2) ≤ 0`, which controls `φ₁₂`).
Written out, with `w = 5 - 6ν`, `D(X) = (X-1)(25-18ν) + w`:
* `hP10 : Q w ((w+10) D(B0) + 2 w D(L0)) ≤ S D(L0) (2w+5)(3w+10)`,
* `hP12 : 0 ≤ S D(L0)² + w Q (B0 L0 w - 10 B0 L0 - 4 B0 w - 4 L0² w + 6 L0 w + 10 L0)`. -/
theorem facets_ge_facet12 {ν p B0 L0 S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hp : 0 ≤ p)
    (hp' : p ≤ 1/2) (hL : 19/10 ≤ L0) (hL' : L0 ≤ 13/5) (hB : 22/23 ≤ B0) (hB' : B0 ≤ 1)
    (hS : 1/50 ≤ S) (hS' : S ≤ 1/10) (hQ : 9/10 ≤ Q) (hQ' : Q ≤ 1)
    (hSQ : S ≤ Q/10)
    (hSσ : Q * (B0 - 1 + yOf ν) ≤ S * (L0 - 1 + yOf ν))
    (hP10 : Q*(5-6*ν)*((15-6*ν)*((B0-1)*(25-18*ν) + (5-6*ν)) +
        2*(5-6*ν)*((L0-1)*(25-18*ν) + (5-6*ν))) ≤
      S*((L0-1)*(25-18*ν) + (5-6*ν))*((15-12*ν)*(25-18*ν)))
    (hP12 : 0 ≤ S*((L0-1)*(25-18*ν) + (5-6*ν))^2 + (5-6*ν)*Q*(B0*L0*(5-6*ν) - 10*B0*L0 -
        4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0))
    (k : Fin 2 × Fin 3) :
    facetVal ν (1/2) 8 B0 L0 (1/10) S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B0 L0 (1/10) S Q k := by
  have hL1 : 1 < L0 := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hg := sigma_clear hν' hSσ
  have hSQ' : S ≤ 1/10*Q := by linarith
  obtain ⟨i, j⟩ := k
  fin_cases i <;> fin_cases j
  · exact facet00_ge hν hν' hp hp' hL1 hS hQ' hg hP10
  · exact facet01_ge hν hν' hp hp' hL1 (by norm_num) hSQ' hS hQ0 hQ' hg hP10
  · exact facet02_ge hν hν' hp hp' hB hB' hL hL' hS hQ0 hQ' hP12
  · exact facet10_ge hν hν' hp hp' hL1 hS0 hg hP10
  · exact facet11_ge hν hν' hp hp' hL1 hS0 hSQ' hg hP10
  · exact facet12_ge hν hν' hp' hB hB' hL hL' hS0 hQ0 hP12

/-! ### Simple sufficient conditions for `hP10` and `hP12` -/

/-- `hP10` follows from the binding-pair hypothesis and `N₁₀(1/2) ≥ 0`, i.e.
`2 Q w² ≤ 5 S (w² + 5w + 10)` (this also gives `N₁₀(0) ≥ 0`). -/
theorem hP10_of_N10 {ν B L S Q : ℝ} (hν' : ν ≤ 3/4) (hL : 1 < L)
    (hg : Q*Dp[ν, B] ≤ S*Dp[ν, L])
    (hN : 2*Q*(5-6*ν)^2 ≤ 5*S*((5-6*ν)^2 + 5*(5-6*ν) + 10)) :
    Q*(5-6*ν)*((15-6*ν)*Dp[ν, B] + 2*(5-6*ν)*Dp[ν, L]) ≤
      S*Dp[ν, L]*((15-12*ν)*(25-18*ν)) := by
  have hw : 0 < 5 - 6*ν := by linarith
  have hD1 : 0 < Dp[ν, L] := by nlinarith
  have t1 := mul_nonneg (mul_nonneg hw.le (by linarith : (0:ℝ) ≤ (5-6*ν) + 10))
    (sub_nonneg.2 hg)
  have t2 := mul_nonneg hD1.le (sub_nonneg.2 hN)
  nlinarith [t1, t2]

/-- `N₁₀(1/2) ≥ 0` holds as soon as `Q ≤ 15 S` (sharp at `ν = 1/2`). -/
theorem N10_of_ratio {ν S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hQ0 : 0 ≤ Q) (hr : Q ≤ 15*S) :
    2*Q*(5-6*ν)^2 ≤ 5*S*((5-6*ν)^2 + 5*(5-6*ν) + 10) := by
  have hw0 : 0 ≤ 5 - 6*ν := by linarith
  have hw2 : 5 - 6*ν ≤ 2 := by linarith
  have h1 : 0 ≤ (5-6*ν)^2 + 5*(5-6*ν) + 10 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hr) h1, mul_nonneg hQ0 (mul_nonneg hw0 (sub_nonneg.2 hw2)),
    mul_nonneg hQ0 hw0]

/-- Polynomial positivity on the box (Bernstein certificate): `D(L)²/13 + w E ≥ 0`, i.e. `S ≥ Q/13`
makes `hP12` automatic. -/
theorem poly12_ratio {ν B L : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hB1 : 22/23 ≤ B) (hB2 : B ≤ 1)
    (hL1 : 19/10 ≤ L) (hL2 : L ≤ 13/5) :
    0 ≤ Dp[ν, L]^2/13 + (5-6*ν)*Ep[ν, B, L] := by
  have s0 : 0 ≤ (5-6*ν) - 1/2 := by linarith
  have s1 : 0 ≤ 2 - (5-6*ν) := by linarith
  have t0 : 0 ≤ L - 19/10 := by linarith
  have t1 : 0 ≤ 13/5 - L := by linarith
  have b0 : 0 ≤ B - 22/23 := by linarith
  have b1 : 0 ≤ 1 - B := by linarith
  linarith [bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 0 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 0 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 1 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 1 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 2 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 0 2 2 0 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 0 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 0 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 1 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 1 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 2 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 1 1 2 0 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 0 2 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 0 2 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 1 1 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 1 1 1 0,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 2 0 0 1,
    bern3_nonneg s0 s1 t0 t1 b0 b1 2 0 2 0 1 0]

/-- `hP12` holds as soon as `Q ≤ 13 S`. -/
theorem hP12_of_ratio {ν B L S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hB : 22/23 ≤ B)
    (hB' : B ≤ 1) (hL : 19/10 ≤ L) (hL' : L ≤ 13/5) (hQ0 : 0 ≤ Q) (hr : Q ≤ 13*S) :
    0 ≤ S*Dp[ν, L]^2 + (5-6*ν)*Q*Ep[ν, B, L] := by
  have hpoly := poly12_ratio hν hν' hB hB' hL hL'
  nlinarith [mul_nonneg hQ0 hpoly, mul_nonneg (sub_nonneg.2 hr) (sq_nonneg Dp[ν, L])]

set_option linter.unusedVariables false in
/-- The same with the simpler (and stronger) condition `N₁₀(1/2) ≥ 0`, i.e.
`2 Q w² ≤ 5 S (w² + 5w + 10)`, which involves only `ν`, `S`, `Q`, in place of `hP10`. -/
theorem facets_ge_facet12_of_N10 {ν p B0 L0 S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hp : 0 ≤ p)
    (hp' : p ≤ 1/2) (hL : 19/10 ≤ L0) (hL' : L0 ≤ 13/5) (hB : 22/23 ≤ B0) (hB' : B0 ≤ 1)
    (hS : 1/50 ≤ S) (hS' : S ≤ 1/10) (hQ : 9/10 ≤ Q) (hQ' : Q ≤ 1)
    (hSQ : S ≤ Q/10)
    (hSσ : Q * (B0 - 1 + yOf ν) ≤ S * (L0 - 1 + yOf ν))
    (hN10 : 2*Q*(5-6*ν)^2 ≤ 5*S*((5-6*ν)^2 + 5*(5-6*ν) + 10))
    (hP12 : 0 ≤ S*((L0-1)*(25-18*ν) + (5-6*ν))^2 + (5-6*ν)*Q*(B0*L0*(5-6*ν) - 10*B0*L0 -
        4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0))
    (k : Fin 2 × Fin 3) :
    facetVal ν (1/2) 8 B0 L0 (1/10) S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B0 L0 (1/10) S Q k :=
  facets_ge_facet12 hν hν' hp hp' hL hL' hB hB' hS hS' hQ hQ' hSQ hSσ
    (hP10_of_N10 hν' (by linarith) (sigma_clear hν' hSσ) hN10) hP12 k

set_option linter.unusedVariables false in
/-- If `Q ≤ 13 S`, the conditions `hP10` and `hP12` are automatic. -/
theorem facets_ge_facet12_of_ratio {ν p B0 L0 S Q : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4)
    (hp : 0 ≤ p) (hp' : p ≤ 1/2) (hL : 19/10 ≤ L0) (hL' : L0 ≤ 13/5) (hB : 22/23 ≤ B0)
    (hB' : B0 ≤ 1) (hS : 1/50 ≤ S) (hS' : S ≤ 1/10) (hQ : 9/10 ≤ Q) (hQ' : Q ≤ 1)
    (hSQ : S ≤ Q/10)
    (hSσ : Q * (B0 - 1 + yOf ν) ≤ S * (L0 - 1 + yOf ν))
    (hr : Q ≤ 13*S)
    (k : Fin 2 × Fin 3) :
    facetVal ν (1/2) 8 B0 L0 (1/10) S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν p 8 B0 L0 (1/10) S Q k := by
  have hQ0 : 0 ≤ Q := by linarith
  have hg := sigma_clear hν' hSσ
  exact facets_ge_facet12 hν hν' hp hp' hL hL' hB hB' hS hS' hQ hQ' hSQ hSσ
    (hP10_of_N10 hν' (by linarith) hg (N10_of_ratio hν hν' hQ0 (by linarith)))
    (hP12_of_ratio hν hν' hB hB' hL hL' hQ0 hr) k

end
end QRH.ArviUniformChain

#print axioms QRH.ArviUniformChain.facets_ge_facet12
#print axioms QRH.ArviUniformChain.facets_ge_facet12_of_ratio
#print axioms QRH.ArviUniformChain.facets_ge_facet12_of_N10
