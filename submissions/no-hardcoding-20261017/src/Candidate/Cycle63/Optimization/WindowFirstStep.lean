/- The first step of the window-top iteration: the bin split for the window top `firstCellTop` and
the balanced top of its affine moment. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.WindowTangency

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The first step: the bin split for the window top `firstCellTop`. -/

theorem balancedCoreCapIn_mono_floor :
    StrictMonoOn (fun q => balancedCoreCapIn q firstCellTop) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => balancedCoreCapIn q firstCellTop) (Set.Icc (1/2) (37/50)) := by
  simp only [firstCellTop, slotFloor]
  unfold_top_ledger
  rat_mono []

theorem priceEndBinTopIn_mono_floor :
    StrictMonoOn (fun q => priceEndBinTopIn q firstCellTop) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => priceEndBinTopIn q firstCellTop) (Set.Icc (1/2) (37/50)) := by
  simp only [firstCellTop, slotFloor]
  unfold_top_ledger
  rat_mono []

bracket binTopLow_floor (digits := 6) : priceEndBinTopIn (1/2) firstCellTop
  unfolding [priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh, priceInterceptIn, interceptNum, interceptDen,
    lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density,
    firstCellTop, slotFloor, cellMesh, lowReserveWeight, markedLossAt, markedRate, markedPad, supplyLoss,
    commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

bracket binTopHigh_floor (digits := 6) : priceEndBinTopIn (37/50) firstCellTop
  unfolding [priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh, priceInterceptIn, interceptNum, interceptDen,
    lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density,
    firstCellTop, slotFloor, cellMesh, lowReserveWeight, markedLossAt, markedRate, markedPad, supplyLoss,
    commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

theorem coreCapAt_anti_floor :
    StrictAntiOn (fun d => coreCapAt d)
        (Set.Icc (priceEndBinTopIn (1/2) firstCellTop) (priceEndBinTopIn (37/50) firstCellTop)) ∧
      ContinuousOn (fun d => coreCapAt d)
        (Set.Icc (priceEndBinTopIn (1/2) firstCellTop) (priceEndBinTopIn (37/50) firstCellTop)) := by
  unfold_core_cap
  rat_mono [binTopLow_floor, binTopHigh_floor]

bracket_root splitFloor_spec (digits := 14) : (fun q => capResidualIn q firstCellTop) on (1/2) (37/50)
  by (capResidualIn_mono_of balancedCoreCapIn_mono_floor priceEndBinTopIn_mono_floor coreCapAt_anti_floor)
  unfolding [capResidualIn, balancedCoreCapIn, frequencyFactorIn, coreCapAt, capUnitAt, rootCutoffAt,
    tailSlack, allowanceUnit, priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh,
    priceInterceptIn, interceptNum, interceptDen, lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, weight,
    amplifierRatio, density, firstCellTop, slotFloor, cellMesh, lowReserveWeight,
    markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]

bracket splitFloor_enclosure (digits := 14) : splitIn firstCellTop using [splitFloor_spec.1]
  unfolding [splitIn]

bracket slopeFloor_enclosure (digits := 14) : movingSlope (splitIn firstCellTop)
  using [splitFloor_enclosure] unfolding [movingSlope, slopeNum, slopeDen]

bracket interceptFloor_enclosure (digits := 14) : priceInterceptIn (splitIn firstCellTop) firstCellTop
  using [splitFloor_enclosure]
  unfolding [priceInterceptIn, interceptNum, interceptDen, firstCellTop, slotFloor, markedLossAt, markedRate, markedPad, cellMesh, lowReserveWeight,
    supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

bracket rootFloor_enclosure (digits := 13) :
    deltaStar (movingSlope (splitIn firstCellTop)) (priceInterceptIn (splitIn firstCellTop) firstCellTop)
  using [slopeFloor_enclosure, interceptFloor_enclosure]
  unfolding [deltaStar, rootA2, rootA1, rootA0, rootDisc, discrim]

bracket boundFloor_enclosure (digits := 12) :
    thetaMin (movingSlope (splitIn firstCellTop)) (priceInterceptIn (splitIn firstCellTop) firstCellTop)
  using [slopeFloor_enclosure, rootFloor_enclosure] unfolding [thetaMin, boundAt]

bracket rowFloor_enclosure (digits := 12) :
    hStar (movingSlope (splitIn firstCellTop)) (priceInterceptIn (splitIn firstCellTop) firstCellTop)
  using [slopeFloor_enclosure, interceptFloor_enclosure, rootFloor_enclosure]
  unfolding [hStar, cutoffDen, thetaMin, boundAt, rootDisc, discrim, rootA2, rootA1, rootA0]

/-- The window top after the first step: the balanced top at the bin split for `firstCellTop`,
rounded up to the cell grid. -/
bracket_up windowTopFirst (digits := 8) : balancedTopAt (splitIn firstCellTop) firstCellTop
  using [slopeFloor_enclosure, interceptFloor_enclosure, boundFloor_enclosure, rowFloor_enclosure]
  unfolding [balancedTopAt, balancedTop, tangentA, tangentB, tangentC, cappedQuadA, cappedQuadB,
    cappedQuadC, cappedLevelSlope, cappedLevelConst, ellAt]

end

end Cycle63.Optimization
