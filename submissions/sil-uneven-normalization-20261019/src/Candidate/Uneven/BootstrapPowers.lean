/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.BootstrapSmallWidth

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Bootstrap

/-- Keep the detector length error explicit in the seven-case bound. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r < 1 → E ≤ 1-d*r-2*d*p*min S ((1-r)/2)+loss)
    (hPM : m ≤ 1/2 → E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss)
    (haux : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
      E ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))+loss) :
    E+2*d*p*S ≤ count d S+d*S+loss+eps := by
  have hd : 0 ≤ d := by linarith
  have hdp : 0 ≤ 2*d*p := by positivity
  have hde : 0 ≤ d*eps := mul_nonneg hd heps
  by_cases hr : r < 1
  · have hi := hIM hr
    have hmin : min S ((1-(r+eps))/2) ≤ min S ((1-r)/2) :=
      min_le_min_left S (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hmin hdp
    have hi' : E-loss-d*eps ≤ 1-d*(r+eps)-2*d*p*min S ((1-(r+eps))/2) := by
      nlinarith only [hi,hmul]
    have ho : E-loss-d*eps ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9) := by
      by_cases hm : m ≤ 1/2
      · linarith only [hPM hm,hde]
      · have hn : min S (2*(1-2*m)/9) ≤ 0 := (min_le_right _ _).trans (by linarith)
        have hh := mul_nonpos_of_nonneg_of_nonpos hdp hn
        linarith only [hP,hde,hh]
    have ha : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
        E-loss-d*eps ≤ 1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda)) := by
      intro hS' hm0 hm1
      linarith only [haux hS' hm0 hm1,hde]
    have hh := weighted_short_fiber hd0 hd1 hp
      (show cutoff d S ≤ (r+eps)+m by linarith only [hlen]) hi' ho ha
    have hfee := mul_le_mul_of_nonneg_right (show d ≤ 1 by linarith) heps
    linarith only [hh,hfee]
  · rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have he : E-loss-(5/6-d)*eps ≤ 1/6+(5/6-d)*(r-eps) := by
      nlinarith only [hI]
    have hh := weighted_long_fiber hd0 hd1 hp hS
      (show r-eps ≤ cutoff d S by linarith only [hrcap]) he
    have hfee := mul_le_mul_of_nonneg_right (show 5/6-d ≤ 1 by linarith) heps
    linarith only [hh,hfee]

theorem count_from_powers {B A U d p S r m loss eps : ℝ}
    (hA : 0 < A) (hU : 1 < U) (hd0 : 31/50 ≤ d) (hd1 : d ≤ 33/50)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : B ≤ A*U^(max 1 ((1+5*r)/6)-d*r+loss))
    (hP : B ≤ A*U^(1-2*d*m+loss))
    (hIM : r < 1 → B ≤ A*U^(1-d*r-2*d*p*min S ((1-r)/2)+loss))
    (hPM : m ≤ 1/2 → B ≤ A*U^(1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss))
    (haux : auxLower ≤ S → 81/200 ≤ m → m ≤ auxCutoff →
      B ≤ A*U^(1-2*d*m-2*d*p*min S (min auxUpper ((auxB-2*m)/auxLambda))+loss)) :
    B ≤ A*U^(count d S+d*S-2*d*p*S+loss+eps) := by
  by_cases hB : 0 < B
  · have hBA : 0 < B/A := div_pos hB hA
    have hlog (e : ℝ) (he : B ≤ A*U^e) : Real.logb U (B/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    have hh := fiber_exponent hd0 hd1 hp0 hp hS heps hlen hrcap
      (hlog _ hI) (hlog _ hP) (fun hr=>hlog _ (hIM hr)) (fun hm=>hlog _ (hPM hm))
      (fun hS' hm0 hm1=>hlog _ (haux hS' hm0 hm1))
    have he : Real.logb U (B/A) ≤ count d S+d*S-2*d*p*S+loss+eps := by linarith only [hh]
    have hb := (div_le_iff₀ hA).mp ((Real.logb_le_iff_le_rpow hU hBA).mp he)
    simpa only [mul_comm] using hb
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

end Sil.Uneven.Bootstrap
#print axioms Sil.Uneven.Bootstrap.count_from_powers
