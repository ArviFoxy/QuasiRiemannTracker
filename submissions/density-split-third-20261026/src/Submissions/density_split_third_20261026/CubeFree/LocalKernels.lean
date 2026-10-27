/- Copyright (c) 2026 Sil. Apache-2.0.
Local cube-free restoration algebra: the ordinary pair (a,b) has valuation < 3.
With B=(1-x)(1-y) and T₃=Σ_{i+j<3} xⁱyʲ, the restricted local factor is H₃=B·T₃.
The square-zero marked identities K₃=H₃+z(B-H₃), K₃⁻¹=H₃⁻¹+z(H₃-B)H₃⁻²,
K₃(F+zF)=T₃+z and K₃⁻¹(T₃+z)=F+zF are the generic operator identities of
`Candidate.FourthPower.LocalKernels` (forward_operator, inverse_operator) at T=T₃.
At central exponent 1/2 the restricted factor is a small perturbation of 1
at every prime of norm at least 4. Global mass bounds are separate obligations. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.LocalKernels
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.LocalKernels
open Candidate.FourthPower.LocalKernels (base markedMul forward_operator inverse_operator)

/-- Truncation of the two-variable geometric series to total degree < 3. -/
def truncated {R : Type*} [CommRing R] (x y : R) : R :=
  1 + x + y + x^2 + x*y + y^2

/-- The cube-free restricted local ordinary factor `H₃ = B·T₃`. -/
def ordinary {R : Type*} [CommRing R] (x y : R) : R :=
  base x y * truncated x y

theorem ordinary_expansion {R : Type*} [CommRing R] (x y : R) :
    ordinary x y =
      1 - (x^3+x^2*y+x*y^2+y^3) + (x^3*y+x^2*y^2+x*y^3) := by
  dsimp [ordinary, base, truncated]
  ring

/-- Forward cube-free operator: `K₃(F+zF)=T₃+z`. -/
theorem forward_cube {K : Type*} [Field K] (x y : K) (hB : base x y ≠ 0) :
    markedMul (base x y * truncated x y, base x y - base x y * truncated x y)
      ((base x y)⁻¹, (base x y)⁻¹) = (truncated x y, 1) :=
  forward_operator (base x y) (truncated x y) hB

/-- Inverse cube-free operator: `K₃⁻¹(T₃+z)=F+zF`. -/
theorem inverse_cube {K : Type*} [Field K] (x y : K) (hB : base x y ≠ 0)
    (hT : truncated x y ≠ 0) :
    markedMul ((base x y * truncated x y)⁻¹,
        (base x y * truncated x y - base x y)*(base x y * truncated x y)⁻¹^2)
      (truncated x y, 1) = ((base x y)⁻¹, (base x y)⁻¹) :=
  inverse_operator (base x y) (truncated x y) hB hT

/-- Central size of the restricted perturbation: with `|x|,|y| ≤ r`,
`|H₃-1| ≤ 4r³+3r⁴`. -/
theorem ordinary_sub_one_le (x y : ℂ) (r : ℝ) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖ordinary x y - 1‖ ≤ 4*r^3 + 3*r^4 := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  rw [ordinary_expansion]
  have h3 : ‖x^3+x^2*y+x*y^2+y^3‖ ≤ 4*r^3 := by
    calc ‖x^3+x^2*y+x*y^2+y^3‖ ≤ ‖x‖^3+‖x‖^2*‖y‖+‖x‖*‖y‖^2+‖y‖^3 := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (le_of_eq (norm_pow _ _)) ?_)) ?_)) (le_of_eq (norm_pow _ _))
          · rw [norm_mul, norm_pow]
          · rw [norm_mul, norm_pow]
      _ ≤ r^3+r^2*r+r*r^2+r^3 := by gcongr
      _ = 4*r^3 := by ring
  have h4 : ‖x^3*y+x^2*y^2+x*y^3‖ ≤ 3*r^4 := by
    calc ‖x^3*y+x^2*y^2+x*y^3‖ ≤ ‖x‖^3*‖y‖+‖x‖^2*‖y‖^2+‖x‖*‖y‖^3 := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add ?_ ?_)) ?_) <;> simp only [norm_mul, norm_pow, le_refl]
      _ ≤ r^3*r+r^2*r^2+r*r^3 := by gcongr
      _ = 3*r^4 := by ring
  calc ‖1 - (x^3+x^2*y+x*y^2+y^3) + (x^3*y+x^2*y^2+x*y^3) - 1‖
      = ‖-(x^3+x^2*y+x*y^2+y^3) + (x^3*y+x^2*y^2+x*y^3)‖ := by ring_nf
    _ ≤ ‖x^3+x^2*y+x*y^2+y^3‖ + ‖x^3*y+x^2*y^2+x*y^3‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ 4*r^3 + 3*r^4 := add_le_add h3 h4

/-- At central exponent 1/2 and any prime norm `N ≥ 4`, `r = N^{-1/2} ≤ 1/2`
and the perturbation is strictly below one: `4r³+3r⁴ ≤ 1/2+3/16 < 1`. -/
theorem central_small (r : ℝ) (hr : 0 ≤ r) (hr2 : r ≤ 1/2) : 4*r^3 + 3*r^4 < 1 := by
  have h3 : r^3 ≤ (1/2)^3 := pow_le_pow_left₀ hr hr2 3
  have h4 : r^4 ≤ (1/2)^4 := pow_le_pow_left₀ hr hr2 4
  nlinarith

end QRH.DensitySplitThird.CubeFree.LocalKernels
