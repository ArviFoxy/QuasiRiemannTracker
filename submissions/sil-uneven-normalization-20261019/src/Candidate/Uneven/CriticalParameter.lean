/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.CriticalHalf
import Candidate.Uneven.Endpoint

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Sil.Uneven.Critical
noncomputable section

def parameterA : ℝ := 91804891419376373332989
def parameterB : ℝ := 191011230531473313491625
def parameterC : ℝ := 68829760479687653132500
def parameterDiscriminant : ℝ := parameterB^2-4*parameterA*parameterC
def criticalParameter : ℝ := (parameterB-Real.sqrt parameterDiscriminant)/(2*parameterA)
def parameterLower : ℝ := 4636766567303565669606137753427/10000000000000000000000000000000
def parameterUpper : ℝ := 4636766567303565669606137753428/10000000000000000000000000000000

theorem parameter_a_pos : 0 < parameterA := by norm_num [parameterA]
theorem parameter_discriminant_pos : 0 < parameterDiscriminant := by
  norm_num [parameterDiscriminant,parameterA,parameterB,parameterC]

theorem critical_parameter_polynomial : parameterPolynomial criticalParameter = 0 := by
  have hs := Real.sq_sqrt parameter_discriminant_pos.le
  have ha : parameterA ≠ 0 := parameter_a_pos.ne'
  have hmain : parameterA*criticalParameter^2-parameterB*criticalParameter+parameterC=0 := by
    dsimp only [criticalParameter]
    field_simp
    change Real.sqrt parameterDiscriminant^2=parameterB^2-4*parameterA*parameterC at hs
    nlinarith only [hs]
  simpa only [parameterPolynomial,parameterA,parameterB,parameterC,sub_eq_add_neg,
    neg_mul,add_assoc,add_comm,add_left_comm] using hmain

theorem critical_parameter_isolation : parameterLower < criticalParameter ∧
    criticalParameter < parameterUpper := by
  have hs := Real.sq_sqrt parameter_discriminant_pos.le
  have hn := Real.sqrt_nonneg parameterDiscriminant
  have hlo0 : 0 < parameterB-2*parameterA*parameterLower := by
    norm_num [parameterA,parameterB,parameterLower]
  have hhi0 : 0 < parameterB-2*parameterA*parameterUpper := by
    norm_num [parameterA,parameterB,parameterUpper]
  have hlo : parameterDiscriminant < (parameterB-2*parameterA*parameterLower)^2 := by
    norm_num [parameterDiscriminant,parameterA,parameterB,parameterC,parameterLower]
  have hhi : (parameterB-2*parameterA*parameterUpper)^2 < parameterDiscriminant := by
    norm_num [parameterDiscriminant,parameterA,parameterB,parameterC,parameterUpper]
  have hslo : Real.sqrt parameterDiscriminant < parameterB-2*parameterA*parameterLower := by
    nlinarith only [hs,hn,hlo0,hlo]
  have hshi : parameterB-2*parameterA*parameterUpper < Real.sqrt parameterDiscriminant := by
    nlinarith only [hs,hn,hhi0,hhi]
  constructor
  · unfold criticalParameter
    rw [lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) parameter_a_pos)]
    linarith only [hslo]
  · unfold criticalParameter
    rw [div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) parameter_a_pos)]
    linarith only [hshi]

theorem theta_endpoint_polynomial {v : ℝ} (hroot : parameterPolynomial v = 0) :
    quadA*(criticalTheta v)^2-quadB*criticalTheta v+quadC=0 := by
  unfold quadA quadB quadC criticalTheta
  unfold parameterPolynomial at hroot
  linear_combination (31193771087113702371801295290000808181469/75222846364626430310413988706191:ℝ)*hroot

theorem critical_theta_eq_endpoint : criticalTheta criticalParameter = endpoint := by
  have hguard := critical_parameter_guards
    ⟨critical_parameter_isolation.1.le,critical_parameter_isolation.2.le⟩
  have ht : criticalTheta criticalParameter < (9/10:ℝ) :=
    hguard.2.1.trans (by norm_num)
  have he : endpoint < (9/10:ℝ) := endpoint_isolation.2.trans (by norm_num [upper])
  have hp := theta_endpoint_polynomial critical_parameter_polynomial
  have hfactor : (criticalTheta criticalParameter-endpoint)*
      (quadA*(criticalTheta criticalParameter+endpoint)-quadB)=0 := by
    nlinarith only [hp,endpoint_polynomial]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hsum : criticalTheta criticalParameter+endpoint < (9/5:ℝ) := by linarith
    have hlt := mul_lt_mul_of_pos_left hsum quadA_pos
    have hconst : quadA*(9/5:ℝ) < quadB := by norm_num [quadA,quadB]
    linarith only [hlt,hconst,h]

/-- An unconditional algebraic inequality for the critical half-amplitude row.
    The analytic source hypotheses and complementary parameter cover are separate. -/
theorem endpoint_critical_half_bound {d : ℝ} (hd : d ≤ 1/2) :
    criticalRow endpoint (criticalHeight criticalParameter) d (1/2) ≤ endpoint := by
  have h := critical_half_bound
    ⟨critical_parameter_isolation.1.le,critical_parameter_isolation.2.le⟩
    critical_parameter_polynomial hd
  simpa only [critical_theta_eq_endpoint] using h

end
end Sil.Uneven.Critical
#print axioms Sil.Uneven.Critical.critical_parameter_polynomial
#print axioms Sil.Uneven.Critical.critical_theta_eq_endpoint
#print axioms Sil.Uneven.Critical.endpoint_critical_half_bound
