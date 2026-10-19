/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.WarmupCover0
import Candidate.Uneven.WarmupCover1
import Candidate.Uneven.WarmupCover2
import Candidate.Uneven.WarmupCover3

set_option autoImplicit false
noncomputable section
namespace Sil.Uneven.WarmupRows

theorem full_rows {r : ℕ} (hr : r ≤ 3) {d p : ℝ}
    (hd : 0 ≤ d ∧ d ≤ 3/4) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    ∃ i : ℕ, i ≤ 7 ∧ available i d p ∧ row r i d p ≤ theta-reserve := by
  interval_cases r
  · exact full_row_0 hd hp
  · exact full_row_1 hd hp
  · exact full_row_2 hd hp
  · exact full_row_3 hd hp

def actualCapacity (r : ℕ) : ℝ :=
  if r ≤ 1 then min (rowHeight r) (2*y-rowHeight r)/(6*frozen_kappa)
  else min ((399999/10000000)*rowHeight r)
    ((2*y-(2-planeB 6)*rowHeight r)/planeLambda 6)

theorem row_capacity_eq_actual {r : ℕ} (hr : r ≤ 3) :
    rowCapacity r = actualCapacity r := by
  interval_cases r <;>
    norm_num [rowCapacity,actualCapacity,rowHeight,y,frozen_kappa,planeB,planeLambda,min_def]

/-- The preliminary numerical boundary supplies exactly the later incumbent.
This implication retains the preliminary bound as a hypothesis. -/
theorem final_incumbent_of_preliminary {beta : ℝ} (hb : beta ≤ theta) :
    2*beta-1 ≤ (1874143/2500000:ℝ) := by
  norm_num [theta] at hb
  linarith only [hb]

end Sil.Uneven.WarmupRows
#print axioms Sil.Uneven.WarmupRows.full_rows
#print axioms Sil.Uneven.WarmupRows.row_capacity_eq_actual
#print axioms Sil.Uneven.WarmupRows.final_incumbent_of_preliminary
