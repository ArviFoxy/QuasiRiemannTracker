/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedScalar

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem count_from_saturated_powers {B A U d p S r m loss eps : ℝ}
    (hA : 0 < A) (hU : 1 < U) (hd0 : 31/50 ≤ d) (hd : d ≤ 3/4)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : B ≤ A*U^(max 1 ((1+5*r)/6)-d*r+loss))
    (hP : B ≤ A*U^(1-2*d*m+loss))
    (hIM : r < 1 → B ≤ A*U^(1-d*r-2*d*p*min S ((1-r)/2)+loss))
    (hPM : m ≤ 1/2 → B ≤ A*U^(1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss)) :
    B ≤ A*U^(fullCount d S+d*S-2*d*p*S+loss+eps) := by
  by_cases hB : 0 < B
  · have hBA : 0 < B/A := div_pos hB hA
    have hlog (e : ℝ) (he : B ≤ A*U^e) : Real.logb U (B/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    have hh := fiber_exponent hd0 hd hp0 hp hS heps hlen hrcap
      (hlog _ hI) (hlog _ hP) (fun hr=>hlog _ (hIM hr)) (fun hm=>hlog _ (hPM hm))
    have he : Real.logb U (B/A) ≤ fullCount d S+d*S-2*d*p*S+loss+eps := by linarith only [hh]
    have hb := (div_le_iff₀ hA).mp ((Real.logb_le_iff_le_rpow hU hBA).mp he)
    simpa only [mul_comm] using hb
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

end Sil.Uneven.Saturated
#print axioms Sil.Uneven.Saturated.count_from_saturated_powers
