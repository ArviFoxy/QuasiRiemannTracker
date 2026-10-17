/- The top of the slot window of Collet's affine moment: the balance point of the marked ledger and
the capped plain line of the detector count. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.WindowSecondStep

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-- Top of the slot window of Collet's affine moment: the balanced top at the bin split for
`windowTopFirst`, rounded up to the cell grid. -/
bracket_up slotTop (digits := 8) : balancedTopAt (splitIn windowTopFirst) windowTopFirst
  using [slopeFirst_enclosure, interceptFirst_enclosure, boundFirst_enclosure, rowFirst_enclosure]
  unfolding [balancedTopAt, balancedTop, tangentA, tangentB, tangentC, cappedQuadA, cappedQuadB,
    cappedQuadC, cappedLevelSlope, cappedLevelConst, ellAt]

theorem slotTop_le_one : slotTop ≤ 1 := by norm_num [slotTop]

/-- The number of cells of the slot window. -/
def cellCount : ℕ := ⌈(slotTop - slotFloor)/cellMesh⌉₊

/-- The cells tile the slot window. -/
theorem cellCount_mul : (cellCount : ℝ)*cellMesh = slotTop - slotFloor := by
  unfold cellCount
  norm_num [slotTop, slotFloor, cellMesh, allowanceUnit, Nat.ceil_ofNat]

theorem one_le_cellCount : 1 ≤ cellCount := by
  have h := cellCount_mul
  have hm := cellMesh_pos
  have hpos : (0:ℝ) < cellCount := by
    by_contra hc
    have h0 : (cellCount : ℝ) ≤ 0 := not_lt.mp hc
    have : (cellCount : ℝ)*cellMesh ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hm.le
    unfold slotTop slotFloor at h
    linarith
  exact_mod_cast hpos

end

end Cycle63.Optimization

namespace Cycle63.Physical

noncomputable section

/-- The share of a width `M` left for the padding in the comparison branch of Collet's moment,
after the lengths `M/4` and `M/2` and the slot capacity `(9/2) slotTop M`. -/
def comparisonPadding : ℝ := 1/4 - (9/2)*Cycle63.Optimization.slotTop

/-- The padding share covers the padding `M/100` of the comparison branch. -/
theorem comparisonPadding_ge : 1/100 ≤ comparisonPadding := by
  norm_num [comparisonPadding, Cycle63.Optimization.slotTop]

end

end Cycle63.Physical
