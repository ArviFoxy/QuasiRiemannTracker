/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
   Complete numerical row cover. Analytic source transfer is separate. -/
import Candidate.Uneven.RoundedCoarse0
import Candidate.Uneven.RoundedCoarse1
import Candidate.Uneven.RoundedCoarse2
import Candidate.Uneven.RoundedCover3
import Candidate.Uneven.RoundedCriticalBridge
import Candidate.Uneven.RoundedAvailability

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

theorem full_rows {r : ℕ} (hr : r ≤ 3) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧
      row r i d p ≤ theta-1/20000000000000 := by
  have hreserve : (1/20000000000000:ℝ) ≤ reserve := by norm_num [reserve]
  interval_cases r
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_0 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_1 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · obtain ⟨i,hi,ha,hb⟩ := coarse_row_2 hd hp
    exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩
  · by_cases hc : (117/256:ℝ) ≤ d ∧ d ≤ 63/128 ∧ (63/128:ℝ) ≤ p ∧ p ≤ 1/2
    · exact ⟨7,by norm_num,critical_plane_available ⟨hc.1,hc.2.1⟩ hc.2.2,
        upper_row_critical_margin ⟨hc.1,hc.2.1⟩ hc.2.2⟩
    · obtain ⟨i,hi,ha,hb⟩ := complement_row_3 hd hp hc
      exact ⟨i,hi,ha,by linarith only [hb,hreserve]⟩

end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.full_rows
