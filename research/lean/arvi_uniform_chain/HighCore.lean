/-
Abstract inequalities behind the marked HIGH gate of one density step, in closed-form parameters.

* `gamma_lower`: the dip bound.  If the selection cost never beats the width gain (`A·C₀ ≤ q_lo·β`), the
  binding gate at the density threshold `q(v)` stays above `q_lo·m0` for every excess `v`.
* `gamma_nu_mono`: the binding gate is nondecreasing in the density `ν` on `[q(v), 3/4]`, from the exact
  differences of `σ` and `C₁₂`.
-/
import Mathlib

set_option autoImplicit false

namespace QRH.ArviUniformChain
noncomputable section

/-- The dip bound with abstract parameters: `qv = q(v) ∈ [q_lo, q0]`, `σv = σ(q(v))`, `Cv = C₁₂(q(v))`. -/
theorem gamma_lower {L0 h s0 v u qv q_lo q0 σv σ0 Ls Cv C0 A D E0 : ℝ}
    (hL : 1 < L0) (hh : 0 ≤ h) (hv : 0 ≤ v) (hu0 : 0 ≤ u) (huA : u ≤ A * v)
    (hqlo : q_lo ≤ qv) (hqlo0 : 0 ≤ q_lo) (hqv0 : qv ≤ q0)
    (hLs : 0 ≤ Ls) (hσ : σv ≤ σ0 + Ls * (q0 - qv))
    (hE0 : 0 < E0) (hq0 : 0 ≤ q0) (hD : 0 ≤ D) (hqdrop : q0 - qv ≤ q0 * h * D * v / E0)
    (hCv0 : 0 ≤ Cv) (hCv : Cv ≤ C0)
    (hm0 : 0 ≤ (L0 - 1) * (s0 - σ0))
    (hβ : 0 ≤ (L0 - 1 - h) - (L0 - 1) * Ls * q0 * h * D / E0)
    (hnodip : A * C0 ≤ q_lo * ((L0 - 1 - h) - (L0 - 1) * Ls * q0 * h * D / E0)) :
    q_lo * ((L0 - 1) * (s0 - σ0)) ≤
      qv * (L0 - 1) * (s0 - σv) + qv * (L0 - 1 - h) * v - u * Cv := by
  set m0 := (L0 - 1) * (s0 - σ0) with hm0def
  set β := (L0 - 1 - h) - (L0 - 1) * Ls * q0 * h * D / E0 with hβdef
  have hL1 : 0 < L0 - 1 := by linarith
  -- the width-corrected slope margin at v
  have hdrop : (L0 - 1) * Ls * (q0 - qv) ≤ (L0 - 1) * Ls * q0 * h * D / E0 * v := by
    have := mul_le_mul_of_nonneg_left hqdrop (mul_nonneg hL1.le hLs)
    calc (L0 - 1) * Ls * (q0 - qv) ≤ (L0 - 1) * Ls * (q0 * h * D * v / E0) := this
      _ = (L0 - 1) * Ls * q0 * h * D / E0 * v := by ring
  have hX : m0 + β * v ≤ (L0 - 1) * (s0 - σv) + (L0 - 1 - h) * v := by
    have h1 : (L0 - 1) * (s0 - σv) ≥ m0 - (L0 - 1) * Ls * (q0 - qv) := by
      have := mul_le_mul_of_nonneg_left hσ hL1.le
      simp only [hm0def]; nlinarith
    simp only [hβdef]
    nlinarith
  have hX0 : 0 ≤ m0 + β * v := by nlinarith
  -- q(v) ≥ q_lo on a nonnegative factor
  have hq : q_lo * (m0 + β * v) ≤ qv * ((L0 - 1) * (s0 - σv) + (L0 - 1 - h) * v) := by
    calc q_lo * (m0 + β * v) ≤ qv * (m0 + β * v) := mul_le_mul_of_nonneg_right hqlo hX0
      _ ≤ qv * ((L0 - 1) * (s0 - σv) + (L0 - 1 - h) * v) :=
          mul_le_mul_of_nonneg_left hX (le_trans hqlo0 hqlo)
  -- selection cost
  have hcost : u * Cv ≤ A * v * C0 := by
    calc u * Cv ≤ u * C0 := mul_le_mul_of_nonneg_left hCv hu0
      _ ≤ A * v * C0 := mul_le_mul_of_nonneg_right huA (le_trans hCv0 hCv)
  have hgain : A * C0 * v ≤ q_lo * β * v := mul_le_mul_of_nonneg_right hnodip hv
  nlinarith

/-- `ν`-monotonicity of the binding gate with abstract parameters.  `σ` decreases and `R` increases with
known exact differences `σ(q) - σ(ν) = (ν - q)·Kσ`, `R(ν) - R(q) = (ν - q)·KR`. -/
theorem gamma_nu_mono {L0 h s0 v u q ν σq σν Rq Rν Kσ KR e Klo KRhi umax : ℝ}
    (hqν : q ≤ ν) (hσ : σq - σν = (ν - q) * Kσ) (hR : Rν - Rq = (ν - q) * KR)
    (hRν : Rν ≤ 1) (hKσ : Klo ≤ (L0 - 1) * q * Kσ) (hKR0 : 0 ≤ KR) (hKR : 6 * q * KR ≤ KRhi)
    (hu0 : 0 ≤ u) (hu : u ≤ umax) (hv : 0 ≤ v) (hLh : 0 ≤ L0 - 1 - h)
    (he : -e ≤ (L0 - 1) * (s0 - σν)) (hcond : e + umax * (5 + KRhi) ≤ Klo) (hKRhi : 0 ≤ KRhi) :
    q * (L0 - 1) * (s0 - σq) + q * (L0 - 1 - h) * v - u * (6 * q * Rq - q - 1) ≤
      ν * (L0 - 1) * (s0 - σν) + ν * (L0 - 1 - h) * v - u * (6 * ν * Rν - ν - 1) := by
  have hdq : 0 ≤ ν - q := sub_nonneg.mpr hqν
  -- the bracket
  have hb : 0 ≤ (L0 - 1) * (s0 - σν) + (L0 - 1 - h) * v - u * (6 * Rν - 1) + (L0 - 1) * q * Kσ
      - 6 * q * u * KR := by
    have h1 : u * (6 * Rν - 1) ≤ 5 * umax := by nlinarith
    have h2 : 6 * q * u * KR ≤ umax * KRhi := by
      have : 6 * q * KR * u ≤ KRhi * u := mul_le_mul_of_nonneg_right hKR hu0
      nlinarith
    have h3 : 0 ≤ (L0 - 1 - h) * v := mul_nonneg hLh hv
    nlinarith
  have key : (ν * (L0 - 1) * (s0 - σν) + ν * (L0 - 1 - h) * v - u * (6 * ν * Rν - ν - 1)) -
      (q * (L0 - 1) * (s0 - σq) + q * (L0 - 1 - h) * v - u * (6 * q * Rq - q - 1)) =
      (ν - q) * ((L0 - 1) * (s0 - σν) + (L0 - 1 - h) * v - u * (6 * Rν - 1) + (L0 - 1) * q * Kσ
        - 6 * q * u * KR) := by
    have eσ : σq = σν + (ν - q) * Kσ := by linarith
    have eR : Rq = Rν - (ν - q) * KR := by linarith
    rw [eσ, eR]; ring
  nlinarith [mul_nonneg hdq hb]

end
end QRH.ArviUniformChain
