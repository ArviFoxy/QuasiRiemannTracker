/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.CriticalMargin

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Sil.Uneven.Critical

def roundedHeight : ℝ :=
  797070601673337477249729489432/1000000000000000000000000000000
def roundedPadding : ℝ := 1/10000000000000000
def roundedReserve : ℝ := 1/20000000000000

theorem critical_product_bounds {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ d*p ∧ d*p ≤ 1 := by
  have hd0 : 0 ≤ d := by linarith only [hd.1]
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  refine ⟨mul_nonneg hd0 hp0,?_⟩
  exact (mul_le_mul hd.2 hp.2 hp0 (by norm_num)).trans (by norm_num)

theorem critical_count_bounds {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    0 ≤ countNumerator d p/countDenominator d p ∧
      countNumerator d p/countDenominator d p ≤ 1 := by
  have hJ := count_denominator_pos hd hp
  have hd0 : 0 ≤ d := by linarith only [hd.1]
  have hd1 : 0 ≤ 1-d := by linarith only [hd.2]
  have hdt : 0 ≤ 5/6-d := by linarith only [hd.2]
  have hp0 : 0 ≤ p := by linarith only [hp.1]
  have hp1 : 0 ≤ 1-p := by linarith only [hp.2]
  let C := 1-2*p*countB/countLambda
  let A := 2-4*p/countLambda
  let D := 3-p-4*p/countLambda
  have hC : 0 ≤ C ∧ C ≤ 1 := by
    dsimp [C,countB,countLambda]
    constructor <;> linarith only [hp0,hp.2]
  have hA : 0 ≤ A := by dsimp [A,countLambda]; linarith only [hp.2]
  have hD : 1-p ≤ D := by dsimp [D,countLambda]; linarith only [hp.2]
  have hsmall : (5/6-d)*(1-p)*C ≤ countDenominator d p := by
    have h₁ := mul_le_mul_of_nonneg_left hC.2 hp1
    have h₂ := mul_le_mul_of_nonneg_left
      ((by simpa only [mul_one] using h₁ : (1-p)*C ≤ 1-p).trans hD) hdt
    have h₃ := mul_nonneg (mul_nonneg hd0 hp1) hA
    change 0 ≤ d*(1-p)*(2-4*p/countLambda) at h₃
    change (5/6-d)*((1-p)*C) ≤ (5/6-d)*(3-p-4*p/countLambda) at h₂
    unfold countDenominator
    nlinarith only [h₂,h₃]
  have hN : countNumerator d p = (1-d)*countDenominator d p+
      d*((5/6-d)*(1-p)*C) := by dsimp [countNumerator,C]; ring
  have hn0 : 0 ≤ countNumerator d p := by
    rw [hN]
    exact add_nonneg (mul_nonneg hd1 hJ.le)
      (mul_nonneg hd0 (mul_nonneg (mul_nonneg hdt hp1) hC.1))
  have hn1 : countNumerator d p ≤ countDenominator d p := by
    have hm := mul_le_mul_of_nonneg_left hsmall hd0
    rw [hN]
    nlinarith only [hm]
  exact ⟨div_nonneg hn0 hJ.le,(div_le_one hJ).mpr hn1⟩

theorem critical_height_shift (t h₀ h₁ d p : ℝ) :
    criticalRow t h₁ d p-criticalRow t h₀ d p =
      (h₁-h₀)*(-5/12-d*p*physicalB/(2*physicalLambda)+
        3/4*(countNumerator d p/countDenominator d p)) := by
  unfold criticalRow physicalLambda
  ring

theorem critical_height_coefficient_bound {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    |(-5/12-d*p*physicalB/(2*physicalLambda)+
        3/4*(countNumerator d p/countDenominator d p))| ≤ 2 := by
  have hx := critical_product_bounds hd hp
  have hr := critical_count_bounds hd hp
  have hb : 0 ≤ physicalB/(2*physicalLambda) ∧ physicalB/(2*physicalLambda) ≤ 1 := by
    norm_num [physicalB,physicalLambda]
  have h₀ := mul_nonneg hx.1 hb.1
  have h₁ := mul_le_mul hx.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)
  have he : d*p*physicalB/(2*physicalLambda)=d*p*(physicalB/(2*physicalLambda)) := by ring
  rw [he,abs_le]
  constructor <;> linarith only [h₀,h₁,hr.1,hr.2]

theorem rounded_height_close :
    |roundedHeight-criticalHeight criticalParameter| ≤
      1/100000000000000000000000000 := by
  have hl := critical_parameter_isolation.1
  have hu := critical_parameter_isolation.2
  norm_num [parameterLower,parameterUpper] at hl hu
  rw [abs_le]
  norm_num [roundedHeight,criticalHeight]
  constructor <;> linarith only [hl,hu]

theorem rounded_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    criticalRow submittedBound roundedHeight d p ≤
      submittedBound-1/10000000000000 := by
  have hm := critical_rectangle_uniform_margin endpoint_lt_submitted hd hp
  have hh : |criticalRow submittedBound roundedHeight d p-
      criticalRow submittedBound (criticalHeight criticalParameter) d p| ≤
        (1/100000000000000000000000000)*2 := by
    rw [critical_height_shift,abs_mul]
    exact mul_le_mul rounded_height_close (critical_height_coefficient_bound hd hp)
      (abs_nonneg _) (by norm_num)
  have he := endpoint_isolation.2
  have hgap : (1/20000000000000:ℝ) ≤ submittedBound-endpoint := by
    norm_num [upper] at he
    norm_num [submittedBound]
    linarith only [he]
  have hdiff := (abs_le.mp hh).2
  linarith only [hm,hgap,hdiff]

/-- The upper physical row with its strictly positive padding, on the linear
capacity branch. Its agreement with the actual min-capacity row is separate. -/
def paddedCriticalRow (t h pad d p : ℝ) : ℝ :=
  criticalRow t h d p+pad*(-9/100+d*p*(2-physicalB)/(2*physicalLambda)+
    3/4*(countNumerator d p/countDenominator d p))

theorem rounded_padded_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    paddedCriticalRow submittedBound roundedHeight roundedPadding d p ≤
      submittedBound-roundedReserve := by
  have hm := rounded_critical_margin hd hp
  have hx := critical_product_bounds hd hp
  have hr := critical_count_bounds hd hp
  have hb : 0 ≤ (2-physicalB)/(2*physicalLambda) ∧
      (2-physicalB)/(2*physicalLambda) ≤ 1 := by norm_num [physicalB,physicalLambda]
  have h₁ := mul_le_mul hx.2 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)
  have hc : -9/100+d*p*(2-physicalB)/(2*physicalLambda)+
      3/4*(countNumerator d p/countDenominator d p) ≤ 2 := by
    have he : d*p*(2-physicalB)/(2*physicalLambda)=d*p*((2-physicalB)/(2*physicalLambda)) := by ring
    rw [he]
    linarith only [h₁,hr.2]
  have hpad := mul_le_mul_of_nonneg_left hc (show 0 ≤ roundedPadding by norm_num [roundedPadding])
  unfold paddedCriticalRow
  norm_num [roundedPadding,roundedReserve] at hpad ⊢
  linarith only [hm,hpad]

end Sil.Uneven.Critical
#print axioms Sil.Uneven.Critical.rounded_padded_critical_margin
