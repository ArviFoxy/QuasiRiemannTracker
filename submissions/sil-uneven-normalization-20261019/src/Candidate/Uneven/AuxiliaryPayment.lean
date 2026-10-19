/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.AuxiliaryChannels
import Candidate.Uneven.SaturatedGeneralPayment

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.AuxiliarySource

def gamma (d : ℝ) : ℝ := d-max (3/19) (4*Saturated.rho d-5/4)

theorem gamma_bounds {d : ℝ} (hd : q ≤ d) (hu : d ≤ 3/4) :
    0 ≤ gamma d ∧ gamma d ≤ d ∧ 0 ≤ 5-6*Saturated.rho d := by
  have hlo : 70467/100000 ≤ d := hd
  have hden : 0 < 3*(5-2*d) := by linarith
  have hp : 27/50 ≤ 10*d/(3*(5-2*d)) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hr : Saturated.rho d ≤ 23/50 := by unfold Saturated.rho;linarith only [hp]
  have hm : max (3/19:ℝ) (4*Saturated.rho d-5/4) ≤ d := max_le (by linarith) (by linarith)
  have hm0 : 0 ≤ max (3/19:ℝ) (4*Saturated.rho d-5/4) :=
    (by norm_num : (0:ℝ) ≤ 3/19).trans (le_max_left _ _)
  unfold gamma
  exact ⟨by linarith only [hm],by linarith only [hm0],by linarith only [hr]⟩

theorem channel_reserves {b d : ℝ} (hb : b∈Set.Icc widthLo widthHi)
    (hd : q ≤ d) (hu : d ≤ 3/4) :
    highReserve ≤ highBase b d+gamma d*supplied b ∧
    ∀i : Fin 4,highReserve ≤ highBase b d+Saturated.slope d i*supplied b+
      Saturated.offset d i*frequency b := by
  have h (i : Fin 6) := all_channels hb hd hu i
  constructor
  · by_cases hc : (3/19:ℝ) ≤ 4*Saturated.rho d-5/4
    · have hh := h 1
      change highReserve ≤ highBase b d+(d-4*Saturated.rho d+5/4)*supplied b at hh
      unfold gamma
      rw [max_eq_right hc]
      convert hh using 1 <;> ring
    · simpa [gamma,channel,max_eq_left (le_of_not_ge hc)] using h 0
  · intro i
    fin_cases i
    · simpa [channel] using h 2
    · simpa [channel] using h 3
    · simpa [channel] using h 4
    · simpa [channel] using h 5

theorem retained_payment {b d c c2 live freq error high : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : q ≤ d) (hu : d ≤ 3/4)
    (hc : 0 ≤ c) (hc2 : 0 ≤ c2) (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : supplied b ≤ c+c2+live) (hfrequency : frequency b ≤ 2*(c+c2)+freq)
    (hhigh : high ≤ error-highBase b d-gamma d*c-d*c2) :
    high-Saturated.physicalGain d live freq ≤ error-highReserve := by
  have hg := gamma_bounds hd hu
  have hs := source_guards hb
  have hr := channel_reserves hb hd hu
  apply Saturated.retained_high_payment_general (by norm_num [q] at hd;linarith) hu hg.1 hg.2.1
    hc hc2 hs.2.2.2.2.2.1.le hs.2.2.2.2.2.2.2.1.le hlive hfreq hsupply hfrequency hr.1 hr.2 hhigh

end Sil.Uneven.AuxiliarySource
#print axioms Sil.Uneven.AuxiliarySource.retained_payment
