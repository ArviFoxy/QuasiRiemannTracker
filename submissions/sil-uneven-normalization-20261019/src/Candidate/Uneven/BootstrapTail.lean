/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.BootstrapCoefficients

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem tail_reserve {d : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) :
    offset d 4+1/1000 ≤ (6*(Saturated.rho d-3/200)-1-1/1000)/100 := by
  have hlo : 0 ≤ d-31/50 := by linarith
  have hhi : 0 ≤ 33/50-d := by linarith
  have hn : (0:ℝ) ≤ (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2))) := by
    have he : (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2)))=469456465036100*(d-31/50)^0*(33/50-d)^3+1834792222980700*(d-31/50)^1*(33/50-d)^2+2272901589251000*(d-31/50)^2*(33/50-d)^1+881010854306400*(d-31/50)^3*(33/50-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (127168237500000+(-146028426000000*d)+(38064452400000*(d^2))) := by
    have he : (127168237500000+(-146028426000000*d)+(38064452400000*(d^2)))=47370351805440+2432648173200000*(d-31/50)^0*(33/50-d)^2+2394583720800000*(d-31/50)^1*(33/50-d)^1 := by ring
    rw [he]
    positivity
  have hsmall : 0 < 2543364750-2920568520*d+761289048*d^2 := by
    nlinarith only [hden]
  have he : (6*(Saturated.rho d-3/200)-1-1/1000)/100-offset d 4-1/1000=
      (6115520541375+(-30520575256340*d)+(-26554977000000*(d^3))+(49859718755916*(d^2)))/(127168237500000+(-146028426000000*d)+(38064452400000*(d^2))) := by
    norm_num [Saturated.rho,offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have h := div_nonneg hn hden.le
  rw [←he] at h
  linarith only [h]

theorem tail_absorbs_gain {d S D loss tail : ℝ} (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hD : 0 ≤ D) (hloss : 0 ≤ loss) (htail : tail ≤ 1/1000) :
    physicalGain d S D ≤ D*(1/100)*(6*(Saturated.rho d+loss-3/200)-1-tail) := by
  have hg := FiniteGain.gain_le (slope d) (offset d) S D 4
  have hz : slope d 4=0 := by norm_num [slope]
  rw [hz,zero_mul,zero_add] at hg
  have ht : offset d 4 ≤ (6*(Saturated.rho d+loss-3/200)-1-tail)/100 := by
    linarith [tail_reserve hd0 hd1]
  have hmul := mul_le_mul_of_nonneg_right ht hD
  apply hg.trans
  nlinarith only [hmul]

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.tail_absorbs_gain
