/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.BootstrapCoefficients

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Bootstrap

theorem retained_high_payment_general {d gamma r1 r2 S F live freq base fee error high : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 33/50) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ d)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : S ≤ r1+r2+live) (hfrequency : F ≤ 2*(r1+r2)+freq)
    (hremoved : fee ≤ base+gamma*S)
    (hfaces : ∀i,fee ≤ base+slope d i*S+offset d i*F)
    (hhigh : high ≤ error-base-gamma*r1-d*r2) :
    high-physicalGain d live freq ≤ error-fee := by
  have hc := coefficient_nonneg hd0 hd
  have hp := FiniteGain.channel_payment hc.1 hc.2 hg0 (add_nonneg hr1 hr2)
    hlive hfreq hS hF hsupply hfrequency hremoved hfaces
  have hr := mul_le_mul_of_nonneg_right hg1 hr2
  change fee ≤ base+gamma*(r1+r2)+physicalGain d live freq at hp
  nlinarith only [hp,hhigh,hr]

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.retained_high_payment_general
