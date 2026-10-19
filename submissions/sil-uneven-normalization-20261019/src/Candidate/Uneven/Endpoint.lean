import Mathlib

/- Copyright (c) 2026 Sil. Apache-2.0.
   Prepared with OpenAI Codex assistance.
   This file proves the algebraic endpoint and rounding, not L-function nonvanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Sil.Uneven
noncomputable section

def quadA : ℝ := 6093050555534740855143533085201471
def quadB : ℝ := 11216192073911255069710427525384691
def quadC : ℝ := 5149081167263611203406370372027234
def discriminant : ℝ := quadB ^ 2 - 4 * quadA * quadC
def endpoint : ℝ := (quadB - Real.sqrt discriminant) / (2 * quadA)
def submittedBound : ℝ := 874828524351 / 1000000000000
def lower : ℝ := 8748285243509452822184826547948 / 10000000000000000000000000000000
def upper : ℝ := 8748285243509452822184826547950 / 10000000000000000000000000000000

theorem quadA_pos : 0 < quadA := by norm_num [quadA]
theorem discriminant_pos : 0 < discriminant := by
  norm_num [discriminant, quadA, quadB, quadC]

theorem endpoint_polynomial :
    quadA * endpoint ^ 2 - quadB * endpoint + quadC = 0 := by
  have hs := Real.sq_sqrt (le_of_lt discriminant_pos)
  have ha : quadA ≠ 0 := ne_of_gt quadA_pos
  dsimp only [endpoint]
  field_simp
  change Real.sqrt discriminant ^ 2 = quadB ^ 2 - 4 * quadA * quadC at hs
  nlinarith only [hs]

theorem endpoint_isolation : lower < endpoint ∧ endpoint < upper := by
  have hs := Real.sq_sqrt (le_of_lt discriminant_pos)
  have hn := Real.sqrt_nonneg discriminant
  have hlowpos : 0 < quadB - 2 * quadA * lower := by
    norm_num [quadB, quadA, lower]
  have huppos : 0 < quadB - 2 * quadA * upper := by
    norm_num [quadB, quadA, upper]
  have hlow : discriminant < (quadB - 2 * quadA * lower)^2 := by
    norm_num [discriminant, quadA, quadB, quadC, lower]
  have hupp : (quadB - 2 * quadA * upper)^2 < discriminant := by
    norm_num [discriminant, quadA, quadB, quadC, upper]
  have hslo : Real.sqrt discriminant < quadB - 2 * quadA * lower := by
    nlinarith only [hs, hn, hlowpos, hlow]
  have hshi : quadB - 2 * quadA * upper < Real.sqrt discriminant := by
    nlinarith only [hs, hn, huppos, hupp]
  constructor
  · unfold endpoint
    rw [lt_div_iff₀ (by exact mul_pos (by norm_num) quadA_pos : 0 < 2 * quadA)]
    linarith only [hslo]
  · unfold endpoint
    rw [div_lt_iff₀ (by exact mul_pos (by norm_num) quadA_pos : 0 < 2 * quadA)]
    linarith only [hshi]

theorem endpoint_lt_submitted : endpoint < submittedBound := by
  have h := endpoint_isolation.2
  have hu : upper < submittedBound := by norm_num [upper, submittedBound]
  exact h.trans hu

theorem submitted_improves_pr63 : submittedBound < (87483 / 100000 : ℝ) := by
  norm_num [submittedBound]

theorem endpoint_is_smaller_root {x : ℝ}
    (hx : quadA * x ^ 2 - quadB * x + quadC = 0) : endpoint ≤ x := by
  have hfactor : quadA * (x - endpoint) * (x + endpoint - quadB / quadA) = 0 := by
    have ha : quadA ≠ 0 := ne_of_gt quadA_pos
    field_simp
    nlinarith only [hx, endpoint_polynomial]
  rcases mul_eq_zero.mp hfactor with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact False.elim ((ne_of_gt quadA_pos) h)
    · exact le_of_eq (sub_eq_zero.mp h).symm
  · have he : endpoint < quadB / (2 * quadA) := by
      have hs : 0 < Real.sqrt discriminant := Real.sqrt_pos.mpr discriminant_pos
      unfold endpoint
      apply (div_lt_div_iff_of_pos_right (by exact mul_pos (by norm_num) quadA_pos : 0 < 2 * quadA)).mpr
      linarith only [hs]
    have hb : quadB / quadA = 2 * (quadB / (2 * quadA)) := by ring
    linarith only [h, he, hb]

/-- Taking the limiting boundary does not require nonvanishing on its boundary. -/
theorem le_endpoint_of_all_larger {beta : ℝ}
    (h : ∀ t : ℝ, endpoint < t → beta ≤ t) : beta ≤ endpoint := by
  by_contra hb
  have hb' : endpoint < beta := lt_of_not_ge hb
  have hm := h ((endpoint + beta) / 2) (by linarith)
  linarith

end
end Sil.Uneven

#print axioms Sil.Uneven.endpoint_polynomial
#print axioms Sil.Uneven.endpoint_isolation
#print axioms Sil.Uneven.endpoint_is_smaller_root
#print axioms Sil.Uneven.endpoint_lt_submitted
#print axioms Sil.Uneven.le_endpoint_of_all_larger
