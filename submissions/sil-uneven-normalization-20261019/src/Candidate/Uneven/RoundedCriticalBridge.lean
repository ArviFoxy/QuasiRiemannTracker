/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.RoundedRowsBase
import Candidate.Uneven.CriticalRounded

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.RoundedRows

/-- The actual minimum of the two physical-capacity branches. -/
def actualCapacity (r : ℕ) : ℝ :=
  if r ≤ 1 then min (rowHeight r) (2*y-rowHeight r)/(6*frozen_kappa)
  else min ((399999/10000000)*rowHeight r)
    ((2*y-(2-Critical.physicalB)*rowHeight r)/Critical.physicalLambda)

theorem row_capacity_eq_actual {r : ℕ} (hr : r ≤ 3) :
    rowCapacity r = actualCapacity r := by
  interval_cases r <;>
    norm_num [rowCapacity,actualCapacity,rowHeight,y,frozen_kappa,
      Critical.physicalB,Critical.physicalLambda,min_def]

theorem upper_row_eq_padded_critical (d p : ℝ) :
    row 3 7 d p = Critical.paddedCriticalRow submittedBound
      Critical.roundedHeight Critical.roundedPadding d p := by
  have hJ : denominator 7 d p = Critical.countDenominator d p := by
    norm_num [denominator,planeLambda,Critical.countDenominator,Critical.countLambda]
  have hN : numerator 7 d p = Critical.countNumerator d p := by
    unfold numerator Critical.countNumerator
    rw [hJ]
    norm_num [planeB,planeLambda,Critical.countB,Critical.countLambda]
  unfold row
  rw [hJ,hN]
  unfold base Critical.paddedCriticalRow Critical.criticalRow
  norm_num [rowHeight,rowCapacity,h,y,ell,submittedBound,
    Critical.roundedHeight,Critical.roundedPadding,Critical.physicalB,Critical.physicalLambda]
  ring

theorem upper_row_critical_margin {d p : ℝ}
    (hd : (117/256:ℝ) ≤ d ∧ d ≤ 63/128)
    (hp : (63/128:ℝ) ≤ p ∧ p ≤ 1/2) :
    row 3 7 d p ≤ theta-1/20000000000000 := by
  rw [upper_row_eq_padded_critical]
  simpa only [theta,submittedBound,Critical.roundedReserve] using
    Critical.rounded_padded_critical_margin hd hp

end Sil.Uneven.RoundedRows
#print axioms Sil.Uneven.RoundedRows.upper_row_critical_margin
