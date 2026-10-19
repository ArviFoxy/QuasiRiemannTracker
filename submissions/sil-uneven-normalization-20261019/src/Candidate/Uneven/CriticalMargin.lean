/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.CriticalAmplitude

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Sil.Uneven.Critical

/-- Exact dependence on the proposed boundary, before any losses are chosen. -/
theorem critical_row_parameter_shift (a t h d p : ℝ) :
    t-criticalRow t h d p = a-criticalRow a h d p+
      (t-a)*(3+4*d*p+8*d*p/physicalLambda) := by
  unfold criticalRow physicalLambda
  ring

/-- Every larger boundary leaves a uniform positive margin on the critical
rectangle. The equality at the endpoint therefore causes no missing reserve. -/
theorem critical_rectangle_uniform_margin {t d p : ℝ}
    (ht : endpoint < t)
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow t (criticalHeight criticalParameter) d p ≤
      t-3*(t-endpoint) := by
  have hb := endpoint_critical_rectangle hd hp
  have hdp : 0 ≤ d*p := mul_nonneg (by linarith only [hd.1])
    (by linarith only [hp.1])
  have hcoef : 3 ≤ 3+4*d*p+8*d*p/physicalLambda := by
    have hl : 0 < physicalLambda := by norm_num [physicalLambda]
    have h₁ : 0 ≤ 4*(d*p) := mul_nonneg (by norm_num) hdp
    have h₂ : 0 ≤ 8*(d*p)/physicalLambda := div_nonneg
      (mul_nonneg (by norm_num) hdp) hl.le
    simp only [mul_assoc]
    linarith only [h₁,h₂]
  have hm := mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr ht.le)
  have hi := critical_row_parameter_shift endpoint t
    (criticalHeight criticalParameter) d p
  linarith only [hb,hm,hi]

/-- A positive reserve, fixed before the point in the critical rectangle,
can simultaneously pay any nonnegative additive loss below that reserve. -/
theorem critical_rectangle_reserve {t : ℝ} (ht : endpoint < t) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ d p loss : ℝ,
      (117/256:ℝ) ≤ d → d ≤ 63/128 →
      (63/128:ℝ) ≤ p → p ≤ 1/2 →
      0 ≤ loss → loss ≤ reserve →
      criticalRow t (criticalHeight criticalParameter) d p+loss ≤ t-reserve := by
  refine ⟨t-endpoint,sub_pos.mpr ht,?_⟩
  intro d p loss hd₀ hd₁ hp₀ hp₁ _hl₀ hl₁
  have hh := critical_rectangle_uniform_margin ht ⟨hd₀,hd₁⟩ ⟨hp₀,hp₁⟩
  linarith only [hh,hl₁,ht]

end Sil.Uneven.Critical
#print axioms Sil.Uneven.Critical.critical_rectangle_reserve
