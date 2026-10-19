/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedGain

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem tail_reserve {d : ℝ} (hd0 : 31/50≤ d) (hd : d≤3/4) :
    offset d 3+1/1000≤(6*(rho d-3/200)-1-1/1000)/100 := by
  have hlo : 0≤ d-31/50 := by linarith
  have hhi : 0≤3/4-d := by linarith
  have h2 : 0<5-2*d := by linarith
  have h5 : 0<185-138*d := by linarith
  have hp : 0≤(13344975+(-66392620*d)+(-57600000*(d^3))+(108261852*(d^2))) := by
    have he : (13344975+(-66392620*d)+(-57600000*(d^3))+(108261852*(d^2)))=(69713708800/2197:ℝ)*(d-31/50)^0*(3/4-d)^3+(394749468800/2197:ℝ)*(d-31/50)^1*(3/4-d)^2+(599384710000/2197:ℝ)*(d-31/50)^2*(3/4-d)^1+(147801750000/2197:ℝ)*(d-31/50)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hh : 0≤((6*(rho d-3/200)-1-1/1000)/100-offset d 3-1/1000)*
      (300000*(5-2*d)*(185-138*d)) := by
    have he : ((6*(rho d-3/200)-1-1/1000)/100-offset d 3-1/1000)*
        (300000*(5-2*d)*(185-138*d))=(13344975+(-66392620*d)+(-57600000*(d^3))+(108261852*(d^2))) := by
      dsimp [rho,offset]
      field_simp (disch := first | linarith | positivity) <;> ring
    rw [he]
    exact hp
  have hpden : 0<300000*(5-2*d)*(185-138*d) := by positivity
  have hz := (mul_nonneg_iff_of_pos_right hpden).mp hh
  linarith

theorem tail_absorbs_gain {d S D loss tail : ℝ}
    (hd0 : 31/50≤ d) (hd : d≤3/4) (hD : 0≤ D)
    (hloss : 0≤ loss) (htail : tail≤1/1000) :
    physicalGain d S D≤ D*(1/100)*(6*(rho d+loss-3/200)-1-tail) := by
  have hh := fourGain_le (slope d) (offset d) S D 3
  norm_num [slope] at hh
  have hb := tail_reserve hd0 hd
  have hp := mul_le_mul_of_nonneg_right
    (show offset d 3≤(1/100)*(6*(rho d+loss-3/200)-1-tail) by linarith) hD
  exact hh.trans (by nlinarith only [hp])

end Sil.Uneven.Saturated
#print axioms Sil.Uneven.Saturated.tail_absorbs_gain
