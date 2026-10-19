/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.MainChannelPayment

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.MainSource

theorem removed_channel_reserve (P : Plane) {b d : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : P.q ≤ d) (hu : d ≤ 3/4) :
    highReserve ≤ highBase P b d+gamma d*supplied b := by
  rcases le_total d (33/50) with h | h
  · exact (bootstrap_channel_reserves P hb hd h).1
  · exact (saturated_channel_reserves P hb h hu).1

theorem unmarked_payment (P : Plane) {b d c c2 error high : ℝ}
    (hb : b∈Set.Icc widthLo widthHi) (hd : P.q ≤ d) (hu : d ≤ 3/4)
    (hc2 : 0 ≤ c2) (hsupply : supplied b ≤ c+c2)
    (hhigh : high ≤ error-highBase P b d-gamma d*c-d*c2) :
    high ≤ error-highReserve := by
  have hg := gamma_bounds ((parameter_gates P).1.trans hd) hu
  have hr := removed_channel_reserve P hb hd hu
  have hm := mul_le_mul_of_nonneg_left hsupply hg.1
  have hc := mul_le_mul_of_nonneg_right hg.2.1 hc2
  nlinarith only [hhigh,hr,hm,hc]

end Sil.Uneven.MainSource
#print axioms Sil.Uneven.MainSource.unmarked_payment
