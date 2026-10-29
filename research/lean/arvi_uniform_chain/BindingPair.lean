/-
The binding facet of the marked HIGH gate at `p = 1/2` in closed form.

For a density step from the parent `(B0, L0)` to the child `(B0 - s0*h, L0 - h)` at excess `v`, selection `u`,
retained width `S = s0 + v - u` and packed radius `Q = 1 - 6u`,
`highJ + facet(1,2)(p = 1/2) = Γ₁₂ = ν(L0-1)(s0 - σ(ν)) + ν(L0-1-h)v - u·C₁₂(ν)`,
with `σ(ν) = (B0 - 1 + y)/(L0 - 1 + y)`, `y = w/(10+3w)`, `w = 5 - 6ν`, and
`C₁₂ = 6νR - ν - 1`, `R = (L0 - 1 + xB0)/(L0 - 1 + xL0)`, `x = w/(2(5+w))`.
-/
import Submissions.arvi_density.Source.HybridGatesMarked

set_option autoImplicit false

namespace QRH.ArviUniformChain
noncomputable section

open QRH.RepeatedMarks QRH.ArviDensity QRH.ArviDensity.Hybrid

/-- `y(ν) = w/(10+3w)` with `w = 5 - 6ν`. -/
def yOf (ν : ℝ) : ℝ := (5 - 6*ν)/(25 - 18*ν)

/-- `x(ν) = w/(2(5+w))` with `w = 5 - 6ν`. -/
def xOf (ν : ℝ) : ℝ := (5 - 6*ν)/(20 - 12*ν)

/-- The continuum slope at density `ν`: the slope of the segment from `(L0, B0)` to `(1-y, 1-y)`. -/
def sigmaOf (B0 L0 ν : ℝ) : ℝ := (B0 - 1 + yOf ν)/(L0 - 1 + yOf ν)

/-- The root of facet `(1,2)` at `p = 1/2`, per unit `Q`. -/
def ROf (B0 L0 ν : ℝ) : ℝ := (L0 - 1 + xOf ν * B0)/(L0 - 1 + xOf ν * L0)

/-- The selection cost coefficient of the binding facet. -/
def C12 (B0 L0 ν : ℝ) : ℝ := 6*ν*ROf B0 L0 ν - ν - 1

/-- The binding gate `Γ₁₂`. -/
def gamma12 (B0 L0 h s0 v u ν : ℝ) : ℝ :=
  ν*(L0 - 1)*(s0 - sigmaOf B0 L0 ν) + ν*(L0 - 1 - h)*v - u*C12 B0 L0 ν

theorem gamma12_eq {B0 L0 h s0 v u ν h0 : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hL : 1 < L0) :
    highJ (B0 - s0*h) (L0 - h) (s0 + v) u ν +
      facetVal ν (1/2) 8 B0 L0 h0 (s0 + v - u) (1 - 6*u) ((1 : Fin 2), (2 : Fin 3)) =
      gamma12 B0 L0 h s0 v u ν := by
  have h15 : (15:ℝ) - 6*ν ≠ 0 := by linarith
  have h25 : (25:ℝ) - 18*ν ≠ 0 := by linarith
  have h20 : (20:ℝ) - 12*ν ≠ 0 := by linarith
  have hL1 : L0 - 1 ≠ 0 := by linarith
  have hL0 : L0 ≠ 0 := by linarith
  simp only [highJ, rhoOf, facetVal, branchRoot, branchOffset, branchSlope, invSlope, invOffset,
    plainSlope, plainOffset, w, baseXi, densityDenom, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, gamma12, C12, ROf, sigmaOf, yOf, xOf]
  have e1 : (1:ℝ) - 2*(1/2)/L0 = (L0 - 1)/L0 := by field_simp
  rw [e1]
  have ey : L0 - 1 + (5 - 6*ν)/(25 - 18*ν) = ((L0 - 1)*(25 - 18*ν) + (5 - 6*ν))/(25 - 18*ν) := by
    rw [eq_div_iff h25, add_mul, div_mul_cancel₀ _ h25]
  have ex : L0 - 1 + (5 - 6*ν)/(20 - 12*ν)*L0 = ((L0 - 1)*(20 - 12*ν) + (5 - 6*ν)*L0)/(20 - 12*ν) := by
    rw [eq_div_iff h20, add_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ h20]
  have ex' : L0 - 1 + (5 - 6*ν)/(20 - 12*ν)*B0 = ((L0 - 1)*(20 - 12*ν) + (5 - 6*ν)*B0)/(20 - 12*ν) := by
    rw [eq_div_iff h20, add_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ h20]
  have ey' : B0 - 1 + (5 - 6*ν)/(25 - 18*ν) = ((B0 - 1)*(25 - 18*ν) + (5 - 6*ν))/(25 - 18*ν) := by
    rw [eq_div_iff h25, add_mul, div_mul_cancel₀ _ h25]
  rw [ey, ex, ex', ey']
  have hY : (L0 - 1)*(25 - 18*ν) + (5 - 6*ν) ≠ 0 := by nlinarith
  have hX : (L0 - 1)*(20 - 12*ν) + (5 - 6*ν)*L0 ≠ 0 := by nlinarith
  have hS : 6*ν + (5 - 6*ν)*(1/(1 - 1/2) + 1/((L0 - 1)/L0)/2) =
      (6*ν*(L0 - 1) + (5 - 6*ν)*(2*(L0 - 1) + L0/2))/(L0 - 1) := by
    field_simp
    ring
  rw [hS]
  have hS' : 6*ν*(L0 - 1) + (5 - 6*ν)*(2*(L0 - 1) + L0/2) ≠ 0 := by nlinarith
  have hD5 : -20 + ν*12 - ν*L0*18 + L0*25 ≠ 0 := by nlinarith
  have hD15 : -500 + ν*660 - ν*L0*900 - ν^2*216 + ν^2*L0*324 + L0*625 ≠ 0 := by
    have : -500 + ν*660 - ν*L0*900 - ν^2*216 + ν^2*L0*324 + L0*625 =
        (25 - 18*ν)*(-20 + ν*12 - ν*L0*18 + L0*25) := by ring
    rw [this]; exact mul_ne_zero h25 hD5
  have hY' := hY; have hX' := hX; have hS'' := hS'
  ring_nf at hY' hX' hS''
  field_simp
  have d1 : (15:ℝ) - ν*6 ≠ 0 := by linarith
  have d2 : ν*6*2*(L0 - 1) + (5 - ν*6)*(2^2*(L0 - 1) + L0) ≠ 0 := by nlinarith
  have d3 : (25:ℝ) - ν*18 ≠ 0 := by linarith
  have d4 : (L0 - 1)*(25 - ν*18) + (5 - ν*6) ≠ 0 := by nlinarith
  have d5 : (20:ℝ) - ν*12 ≠ 0 := by linarith
  have d6 : (L0 - 1)*(20 - ν*12) + L0*(5 - ν*6) ≠ 0 := by nlinarith
  field_simp
  ring

theorem xOf_bounds' (ν : ℝ) (h1 : 1/2 ≤ ν) (h2 : ν ≤ 3/4) : 1/22 ≤ xOf ν ∧ xOf ν ≤ 1/7 := by
  unfold xOf
  have hd : (0:ℝ) < 20 - 12*ν := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- Root of facet `(1,0)` at `p = 1/2`. -/
theorem root10_half {B0 L0 S Q ν h0 : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) :
    branchRoot ν (1/2) 8 B0 L0 h0 S Q ((1 : Fin 2), (0 : Fin 3)) =
      (2*(10 - 6*ν)*Q + (5 - 6*ν)*S)/(25 - 18*ν) := by
  simp only [branchRoot, branchOffset, branchSlope, invSlope, invOffset, plainSlope, plainOffset, w,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  have h1 : (6:ℝ)*ν + (5 - 6*ν)*(1/(1 - 1/2) + 1/2) ≠ 0 := by norm_num; nlinarith
  have h2 : (25:ℝ) - 18*ν ≠ 0 := by linarith
  rw [div_eq_div_iff h1 h2]
  ring

/-- Root of facet `(1,2)` at `p = 1/2`: `Q·R(ν)`. -/
theorem root12_half {B0 L0 S Q ν h0 : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hL : 1 < L0) :
    branchRoot ν (1/2) 8 B0 L0 h0 S Q ((1 : Fin 2), (2 : Fin 3)) = Q * ROf B0 L0 ν := by
  have hL1 : L0 - 1 ≠ 0 := by linarith
  have hL0 : L0 ≠ 0 := by linarith
  simp only [branchRoot, branchOffset, branchSlope, invSlope, invOffset, plainSlope, plainOffset, w,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    ROf, xOf]
  have e1 : (1:ℝ) - 2*(1/2)/L0 = (L0 - 1)/L0 := by field_simp
  have e2 : 1/((L0 - 1)/L0) = L0/(L0 - 1) := by rw [one_div_div]
  have e3 : -(2*(1/2)*B0*Q/L0)/((L0 - 1)/L0) = -(B0*Q/(L0 - 1)) := by
    rw [neg_div, div_div_div_cancel_right₀ hL0]; ring_nf
  rw [e1, e2, e3]
  have h20 : (20:ℝ) - 12*ν ≠ 0 := by linarith
  have hx : (5 - 6*ν)/(20 - 12*ν) = (5 - 6*ν)/(20 - 12*ν) := rfl
  have hden : (6:ℝ)*ν + (5 - 6*ν)*(1/(1 - 1/2) + L0/(L0 - 1)/2) =
      (6*ν*(L0 - 1) + (5 - 6*ν)*(2*(L0 - 1) + L0/2))/(L0 - 1) := by
    field_simp; ring
  have hnum : 5*Q - (5 - 6*ν)*(-(1/2*Q)/(1 - 1/2) + -(B0*Q/(L0 - 1))/2) =
      (5*Q*(L0 - 1) + (5 - 6*ν)*(Q*(L0 - 1) + B0*Q/2))/(L0 - 1) := by
    field_simp; ring
  rw [hden, hnum, div_div_div_cancel_right₀ hL1]
  have hD1 : 6*ν*(L0 - 1) + (5 - 6*ν)*(2*(L0 - 1) + L0/2) ≠ 0 := by nlinarith
  have hR1 : L0 - 1 + (5 - 6*ν)/(20 - 12*ν)*L0 ≠ 0 := by
    have : 0 ≤ (5 - 6*ν)/(20 - 12*ν)*L0 := mul_nonneg (div_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have h20' : (20:ℝ) - ν*12 ≠ 0 := by linarith
  rw [mul_div_assoc', div_eq_div_iff hD1 hR1]
  field_simp
  ring

theorem one_add_xOf (ν : ℝ) (hν' : ν ≤ 3/4) : 1 + xOf ν = (25 - 18*ν)/(20 - 12*ν) := by
  have h : (20:ℝ) - 12*ν ≠ 0 := by linarith
  unfold xOf
  rw [eq_div_iff h, add_mul, div_mul_cancel₀ _ h]
  ring

theorem yOf_mul (ν : ℝ) (hν' : ν ≤ 3/4) : yOf ν * (1 + xOf ν) = xOf ν := by
  have h25 : (25:ℝ) - 18*ν ≠ 0 := by linarith
  have h20 : (20:ℝ) - 12*ν ≠ 0 := by linarith
  rw [one_add_xOf ν hν']
  unfold yOf xOf
  rw [div_mul_div_comm, mul_comm (5 - 6*ν) (25 - 18*ν), ← div_mul_div_comm, div_self h25, one_mul]

/-- The root of facet `(1,0)` at `p = 1/2` in the form `(Q + xS)/(1 + x)`. -/
theorem root10_half' {B0 L0 S Q ν h0 : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) :
    branchRoot ν (1/2) 8 B0 L0 h0 S Q ((1 : Fin 2), (0 : Fin 3)) = (Q + xOf ν * S)/(1 + xOf ν) := by
  rw [root10_half hν hν', one_add_xOf ν hν']
  have h25 : (25:ℝ) - 18*ν ≠ 0 := by linarith
  have h20 : (20:ℝ) - 12*ν ≠ 0 := by linarith
  unfold xOf
  rw [div_div_eq_mul_div, div_eq_div_iff h25 h25]
  have e : (Q + (5 - 6*ν)/(20 - 12*ν)*S)*(20 - 12*ν) = Q*(20 - 12*ν) + (5 - 6*ν)*S := by
    rw [add_mul, mul_assoc, mul_comm S, ← mul_assoc, div_mul_cancel₀ _ h20]
  rw [e]
  ring

/-- The facet order at `p = 1/2`: facet `(1,0)` dominates facet `(1,2)` as soon as `S ≥ Q·σ(ν)`. -/
theorem facet12_le_facet10 {B0 L0 S Q ν h0 : ℝ} (hν : 1/2 ≤ ν) (hν' : ν ≤ 3/4) (hL : 1 < L0)
    (hSQ : Q * (B0 - 1 + yOf ν) ≤ S * (L0 - 1 + yOf ν)) :
    facetVal ν (1/2) 8 B0 L0 h0 S Q ((1 : Fin 2), (2 : Fin 3)) ≤
      facetVal ν (1/2) 8 B0 L0 h0 S Q ((1 : Fin 2), (0 : Fin 3)) := by
  simp only [facetVal]
  rw [root10_half' hν hν', root12_half hν hν' hL]
  have hn : 0 ≤ ν := by linarith
  suffices h : Q * ROf B0 L0 ν ≤ (Q + xOf ν * S)/(1 + xOf ν) by nlinarith
  obtain ⟨x1, x2⟩ := xOf_bounds' ν hν hν'
  have hy := yOf_mul ν hν'
  set x := xOf ν with hxdef
  set y := yOf ν with hydef
  have h1x : 0 < 1 + x := by linarith
  have hA : 0 < L0 - 1 + x * L0 := by nlinarith
  -- x-form of the hypothesis: multiply by (1 + x)
  have hSQx : Q * (B0 - 1 + x * B0) ≤ S * (L0 - 1 + x * L0) := by
    have eB : B0 - 1 + x * B0 = (1 + x) * (B0 - 1 + y) := by nlinarith
    have eL : L0 - 1 + x * L0 = (1 + x) * (L0 - 1 + y) := by nlinarith
    rw [eB, eL]
    nlinarith
  unfold ROf
  rw [← hxdef, mul_div_assoc', div_le_div_iff₀ hA h1x]
  nlinarith

end
end QRH.ArviUniformChain
