/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   This file is only the critical-row algebra; it is not an analytic source proof. -/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Sil.Uneven.Critical
noncomputable section

def parameterPolynomial (v : ℝ) : ℝ := (68829760479687653132500 + (-191011230531473313491625 * v) + (91804891419376373332989 * (v ^ 2)))

def criticalTheta (v : ℝ) : ℝ := ((1/677005617281637872793725898355719:ℝ) * (567450664717496215205934736498337 + (53513930593943064798030058210029 * v)))

def criticalHeight (v : ℝ) : ℝ := ((6994912332/49968722309439657004318790966985043884232644046099976816135970525060125549:ℝ) * (7557749495571114292507544377461412922157493616026381864542400775 + (-4019635498657897742511108248017721263274119229323182364458666606 * v)))

def halfDenominator (d : ℝ) : ℝ := ((1/222692807916:ℝ) * (363943349825 + (-274039211874 * d)))

def halfNumerator (d : ℝ) : ℝ := ((1/4453856158320:ℝ) * (7278866996500 + (-11393134690085 * d) + (3840964384806 * (d ^ 2))))

def squareCoefficient (v : ℝ) : ℝ := ((582909361/30910208552955526252376912497889322987100696504485953294577280370765145008984169571900:ℝ) * (7523203541522138545083732423005053576604149679946576882719597385241377646775 + (5909712235488191390397393563708703934495592639548882228890480482347153986306 * v)))

def physicalB : ℝ := 49061544613/50000000000
def physicalLambda : ℝ := 1891221821/500000000
def countB : ℝ := 97851371081/100000000000
def countLambda : ℝ := 18557733993/5000000000

def countDenominator (d p : ℝ) : ℝ :=
  (5/6-d)*(3-p-4*p/countLambda)+d*(1-p)*(2-4*p/countLambda)
def countNumerator (d p : ℝ) : ℝ :=
  (1-d)*countDenominator d p+(5/6-d)*d*(1-p)*(1-2*p*countB/countLambda)
def criticalRow (theta height d p : ℝ) : ℝ :=
  (1+d)/2+(11/3-4*theta)*(1/2+d*p)-5/12*height-
    d*p*((physicalB*height-4*(11/3-4*theta))/physicalLambda)/2+
    3/4*height*(countNumerator d p/countDenominator d p)
def halfRowNumerator (v d : ℝ) : ℝ :=
  ((1+d)/2+(11/3-4*criticalTheta v)*(1/2+d/2)-5/12*criticalHeight v-
    d*((physicalB*criticalHeight v-4*(11/3-4*criticalTheta v))/physicalLambda)/4)*
      halfDenominator d+3/4*criticalHeight v*halfNumerator d

theorem half_denominator_eq (d : ℝ) :
    countDenominator d (1/2) = halfDenominator d := by
  unfold countDenominator countLambda halfDenominator
  ring

theorem half_numerator_eq (d : ℝ) :
    countNumerator d (1/2) = halfNumerator d := by
  unfold countNumerator countDenominator countLambda countB halfNumerator
  ring

theorem half_row_eq (v d : ℝ) (hd : halfDenominator d ≠ 0) :
    criticalRow (criticalTheta v) (criticalHeight v) d (1/2) =
      halfRowNumerator v d/halfDenominator d := by
  unfold criticalRow halfRowNumerator
  rw [half_denominator_eq, half_numerator_eq]
  field_simp
  <;> ring

theorem critical_half_factorization (v d : ℝ)
    (hroot : parameterPolynomial v = 0) :
    criticalTheta v*halfDenominator d-halfRowNumerator v d =
      squareCoefficient v*(d-v)^2 := by
  dsimp only [criticalTheta, halfDenominator, halfRowNumerator, criticalHeight,
    squareCoefficient, physicalB, physicalLambda, halfNumerator]
  unfold parameterPolynomial at hroot
  linear_combination (((582909361/92730625658866578757130737493667968961302089513457859883731841112295435026952508715700:ℝ) * (-647647773920692213208414358559023658975235954831132175 + (-193117560865854433271506040398124131023525521751262462 * v) + (386235121731708866543012080796248262047051043502524924 * d)))) * hroot

theorem critical_parameter_guards {v : ℝ}
    (hv : (4636766567303565669606137753427/10000000000000000000000000000000:ℝ) ≤ v ∧
      v ≤ 4636766567303565669606137753428/10000000000000000000000000000000) :
    87482852/100000000 < criticalTheta v ∧ criticalTheta v < 87482853/100000000 ∧
    7970705/10000000 < criticalHeight v ∧ criticalHeight v < 7970707/10000000 ∧
    0 < squareCoefficient v := by
  rcases hv with ⟨hlo,hhi⟩
  norm_num [criticalTheta,criticalHeight,squareCoefficient]
  constructor
  · linarith only [hlo,hhi]
  constructor
  · linarith only [hlo,hhi]
  constructor
  · linarith only [hlo,hhi]
  constructor <;> linarith only [hlo,hhi]

theorem half_denominator_pos {d : ℝ} (hd : d ≤ 1/2) :
    0 < halfDenominator d := by
  norm_num [halfDenominator]
  linarith only [hd]

/-- The touching critical row has a positive quadratic-square deficit.
    Every denominator and parameter sign used here is explicit. -/
theorem critical_half_bound {v d : ℝ}
    (hv : (4636766567303565669606137753427/10000000000000000000000000000000:ℝ) ≤ v ∧
      v ≤ 4636766567303565669606137753428/10000000000000000000000000000000)
    (hroot : parameterPolynomial v = 0) (hd : d ≤ 1/2) :
    criticalRow (criticalTheta v) (criticalHeight v) d (1/2) ≤ criticalTheta v := by
  have hj := half_denominator_pos hd
  rw [half_row_eq v d hj.ne']
  apply (div_le_iff₀ hj).mpr
  have hfactor := critical_half_factorization v d hroot
  have hpos := mul_nonneg (critical_parameter_guards hv).2.2.2.2.le (sq_nonneg (d-v))
  linarith only [hfactor,hpos]

end
end Sil.Uneven.Critical
#print axioms Sil.Uneven.Critical.critical_half_bound
