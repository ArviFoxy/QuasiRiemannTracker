/- The balanced window top: the closed form of the window top at which the capped plain line of the
detector count is tight, and the monotonicity of the cap residual for a window top.
Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.MarkedCaps

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The detector count caps the slot capacity of its plain line at the window top `s`:
`zS m = min s ((B - 2 m)/λ)`. Where the cap binds, the count is the closed form of the capped
line, whose top-row margin at slot amplitude `1/2`, cleared of the denominator `25/12 - 3 δ/2`, is
a quadratic in the zero parameter `δ`. Its coefficient of `δ²` falls and its coefficient of `δ`
rises linearly with `s`, and its constant term does not depend on `s`, so its discriminant is a
quadratic in `s`. The smallest window top at which the quadratic stays nonnegative at the class
bound is the one at which it has a double root: the smaller root of the discriminant
(`balancedTop`).

The marked ledger pays every cell up to the window top, so a smaller window top raises the class
bound less; but its bin split, and with it the intercept, the class bound and the row length of
the top row, depend on the window top through the top cell and through the marked loss, whose slot
sums are bounded by the window top. The window top is therefore the fixed point of
`s ↦ balancedTopAt (splitIn s) s`. The map moves little with `s`: two steps from
the smallest window top, the first cell (`firstCellTop`), each rounded up to the cell grid, give the
window top `slotTop`. That the capped line holds there with the ledger's own bin
split is checked in `Arithmetic.Bernstein.top_capped_half`. -/

/-- The plain-length allowance `11/3 - 4 θ` at the bound `θ`. -/
def ellAt (θ : ℝ) : ℝ := 11/3 - 4*θ

/-- The constant term of the part of the capped top-row margin at slot amplitude `1/2` that is
affine in the zero parameter, at the bound `θ` and the row length `h`. -/
def cappedLevelConst (θ h : ℝ) : ℝ :=
  θ - 1/2 - 13*h/75 + (h - 2*ellAt θ)/2 + ellAt θ/2 - h/4 + 17*h/50 - h/8

/-- Its coefficient of the zero parameter, for the slope `lam` and the intercept `B` of the affine
moment. -/
def cappedLevelSlope (lam B θ h : ℝ) : ℝ :=
  -1/2 - ellAt θ/2 + (2*(h - 2*ellAt θ) - (2 - B)*h)/lam/4

/-- The coefficient of `δ²` of the capped top-row margin cleared of `25/12 - 3 δ/2`, for the window
top `s`. -/
def cappedQuadA (lam B θ h s : ℝ) : ℝ := -3/2*cappedLevelSlope lam B θ h - 3*h/4*(1 + s/2)

/-- Its coefficient of `δ`. -/
def cappedQuadB (lam B θ h s : ℝ) : ℝ :=
  25/12*cappedLevelSlope lam B θ h - 3/2*cappedLevelConst θ h + 3*h/4*(5/6*(1 + s/2) + 25/12)

/-- Its constant term, which does not depend on the window top. -/
def cappedQuadC (θ h : ℝ) : ℝ := 25/12*cappedLevelConst θ h - 3*h/4*(125/72)

/-- The coefficient of `s²` of the discriminant in `δ` of the cleared capped margin. -/
def tangentA (h : ℝ) : ℝ := 25*h^2/256

/-- The coefficient of `s` of that discriminant. -/
def tangentB (lam B θ h : ℝ) : ℝ := 5*h/8*cappedQuadB lam B θ h 0 + 3*h/2*cappedQuadC θ h

/-- The constant term of that discriminant. -/
def tangentC (lam B θ h : ℝ) : ℝ :=
  cappedQuadB lam B θ h 0^2 - 4*cappedQuadA lam B θ h 0*cappedQuadC θ h

/-- The smallest window top at which the cleared capped margin at the bound `θ` has a double root
in `δ`: the smaller root of its discriminant. -/
def balancedTop (lam B θ h : ℝ) : ℝ :=
  (-tangentB lam B θ h - Real.sqrt (tangentB lam B θ h^2 - 4*tangentA h*tangentC lam B θ h)) /
    (2*tangentA h)

/-- The balanced window top of the top row at the bin split `q`: at its intercept, class
bound and optimal row length. -/
def balancedTopAt (q s : ℝ) : ℝ :=
  balancedTop (movingSlope q) (priceInterceptIn q s)
    (thetaMin (movingSlope q) (priceInterceptIn q s)) (hStar (movingSlope q) (priceInterceptIn q s))

/-- The residual of the caps increases on the split range when, for the window top `s`, the
balancing core cap and the bin top of the price end increase and the core cap falls on the bin tops
of the range. -/
theorem capResidualIn_mono_of {s : ℝ}
    (hB : StrictMonoOn (fun q => balancedCoreCapIn q s) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => balancedCoreCapIn q s) (Set.Icc (1/2) (37/50)))
    (hD : StrictMonoOn (fun q => priceEndBinTopIn q s) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => priceEndBinTopIn q s) (Set.Icc (1/2) (37/50)))
    (hC : StrictAntiOn (fun d => coreCapAt d) (Set.Icc (priceEndBinTopIn (1/2) s) (priceEndBinTopIn (37/50) s)) ∧
      ContinuousOn (fun d => coreCapAt d) (Set.Icc (priceEndBinTopIn (1/2) s) (priceEndBinTopIn (37/50) s))) :
    StrictMonoOn (fun q => capResidualIn q s) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => capResidualIn q s) (Set.Icc (1/2) (37/50)) := by
  obtain ⟨hBm, hBc⟩ := hB
  obtain ⟨hDm, hDc⟩ := hD
  obtain ⟨hCm, hCc⟩ := hC
  have hmaps : Set.MapsTo (fun q => priceEndBinTopIn q s) (Set.Icc (1/2) (37/50))
      (Set.Icc (priceEndBinTopIn (1/2) s) (priceEndBinTopIn (37/50) s)) := fun q hq =>
    ⟨hDm.monotoneOn ⟨le_rfl, by norm_num⟩ hq hq.1, hDm.monotoneOn hq ⟨by norm_num, le_rfl⟩ hq.2⟩
  refine ⟨fun x hx y hy hxy => ?_, ?_⟩
  · have hCxy := hCm (hmaps hx) (hmaps hy) (hDm hx hy hxy)
    have hBxy := hBm hx hy hxy
    simp only at hCxy hBxy ⊢
    unfold capResidualIn
    linarith
  · unfold capResidualIn
    exact hBc.sub (hCc.comp hDc hmaps)

/-- Unfolds the top-cell quantities of the marked ledger to rational expressions in the bin split
and the window top. -/
macro "unfold_top_ledger" : tactic => `(tactic|
  (simp only [Cycle63.Optimization.balancedCoreCapIn, Cycle63.Optimization.frequencyFactorIn,
    Cycle63.Optimization.priceEndBinTopIn, Cycle63.Optimization.priceEndGrowthIn,
    Cycle63.Optimization.cellAmplifier, Cycle63.Optimization.cellHigh,
    Cycle63.Optimization.priceInterceptIn, Cycle63.Optimization.interceptNum, Cycle63.Optimization.interceptDen, Cycle63.Optimization.lowReserveAt,
    Cycle63.Optimization.movingSlope, Cycle63.Optimization.slopeNum, Cycle63.Optimization.slopeDen, Cycle63.Optimization.suppliedAt,
    Cycle63.Optimization.priceEndRate, Cycle63.Optimization.weight,
    Cycle63.Optimization.amplifierRatio, Cycle63.Optimization.density,
    Cycle63.Optimization.cellMesh, Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.markedLossAt, Cycle63.Optimization.markedRate,
    Cycle63.Optimization.markedPad, Cycle63.Optimization.supplyLoss,
    Cycle63.Optimization.commonAllocationLoss, Cycle63.Optimization.tinySlotLoss,
    Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.markedBinWidth,
    Cycle63.Optimization.allowanceUnit,
    Cycle63.Optimization.liveRate, Cycle63.Optimization.liveRatio,
    Cycle63.Optimization.chosenPerUnit, Cycle63.Optimization.plainCapacityCost,
    Cycle63.Optimization.halfGain, Cycle63.Optimization.frequencyLossCap]))

/-- Unfolds the core cap of the marked count to a rational expression in the bin top. -/
macro "unfold_core_cap" : tactic => `(tactic|
  (simp only [Cycle63.Optimization.coreCapAt, Cycle63.Optimization.capUnitAt,
    Cycle63.Optimization.rootCutoffAt, Cycle63.Optimization.tailSlack,
    Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.liveRate,
    Cycle63.Optimization.liveRatio, Cycle63.Optimization.chosenPerUnit,
    Cycle63.Optimization.plainCapacityCost, Cycle63.Optimization.halfGain,
    Cycle63.Optimization.density]))

end

end Cycle63.Optimization
