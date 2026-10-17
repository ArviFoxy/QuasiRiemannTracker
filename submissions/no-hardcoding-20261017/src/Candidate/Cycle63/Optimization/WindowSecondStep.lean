/- The second step of the window-top iteration: the bin split for the window top `windowTopFirst`
and the balanced top of its affine moment, the window top. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.WindowFirstStep

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The second step: the bin split for the window top `windowTopFirst`. -/

theorem balancedCoreCapIn_mono_first :
    StrictMonoOn (fun q => balancedCoreCapIn q windowTopFirst) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => balancedCoreCapIn q windowTopFirst) (Set.Icc (1/2) (37/50)) := by
  unfold_top_ledger
  simp only [windowTopFirst]
  rat_mono []

theorem priceEndBinTopIn_mono_first :
    StrictMonoOn (fun q => priceEndBinTopIn q windowTopFirst) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => priceEndBinTopIn q windowTopFirst) (Set.Icc (1/2) (37/50)) := by
  unfold_top_ledger
  simp only [windowTopFirst]
  rat_mono []

bracket binTopLow_first (digits := 6) : priceEndBinTopIn (1/2) windowTopFirst
  unfolding [priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh, priceInterceptIn, interceptNum, interceptDen,
    lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density,
    windowTopFirst, cellMesh, lowReserveWeight, markedLossAt, markedRate, markedPad,
    supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

bracket binTopHigh_first (digits := 6) : priceEndBinTopIn (37/50) windowTopFirst
  unfolding [priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh, priceInterceptIn, interceptNum, interceptDen,
    lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density,
    windowTopFirst, cellMesh, lowReserveWeight, markedLossAt, markedRate, markedPad,
    supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

theorem coreCapAt_anti_first :
    StrictAntiOn (fun d => coreCapAt d)
        (Set.Icc (priceEndBinTopIn (1/2) windowTopFirst) (priceEndBinTopIn (37/50) windowTopFirst)) ∧
      ContinuousOn (fun d => coreCapAt d)
        (Set.Icc (priceEndBinTopIn (1/2) windowTopFirst) (priceEndBinTopIn (37/50) windowTopFirst)) := by
  unfold_core_cap
  rat_mono [binTopLow_first, binTopHigh_first]

bracket_root splitFirst_spec (digits := 14) :
    (fun q => capResidualIn q windowTopFirst) on (1/2) (37/50)
  by (capResidualIn_mono_of balancedCoreCapIn_mono_first priceEndBinTopIn_mono_first
    coreCapAt_anti_first)
  unfolding [capResidualIn, balancedCoreCapIn, frequencyFactorIn, coreCapAt, capUnitAt, rootCutoffAt,
    tailSlack, allowanceUnit, priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, cellHigh,
    priceInterceptIn, interceptNum, interceptDen, lowReserveAt, movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, weight,
    amplifierRatio, density, windowTopFirst, cellMesh, lowReserveWeight, markedLossAt,
    markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain,
    frequencyLossCap]

bracket splitFirst_enclosure (digits := 14) : splitIn windowTopFirst using [splitFirst_spec.1]
  unfolding [splitIn]

bracket slopeFirst_enclosure (digits := 14) : movingSlope (splitIn windowTopFirst)
  using [splitFirst_enclosure] unfolding [movingSlope, slopeNum, slopeDen]

bracket interceptFirst_enclosure (digits := 14) : priceInterceptIn (splitIn windowTopFirst) windowTopFirst
  using [splitFirst_enclosure]
  unfolding [priceInterceptIn, interceptNum, interceptDen, windowTopFirst, markedLossAt, markedRate, markedPad, cellMesh, lowReserveWeight,
    supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap, markedBinWidth, allowanceUnit]

bracket rootFirst_enclosure (digits := 13) :
    deltaStar (movingSlope (splitIn windowTopFirst)) (priceInterceptIn (splitIn windowTopFirst) windowTopFirst)
  using [slopeFirst_enclosure, interceptFirst_enclosure]
  unfolding [deltaStar, rootA2, rootA1, rootA0, rootDisc, discrim]

bracket boundFirst_enclosure (digits := 12) :
    thetaMin (movingSlope (splitIn windowTopFirst)) (priceInterceptIn (splitIn windowTopFirst) windowTopFirst)
  using [slopeFirst_enclosure, rootFirst_enclosure] unfolding [thetaMin, boundAt]

bracket rowFirst_enclosure (digits := 12) :
    hStar (movingSlope (splitIn windowTopFirst)) (priceInterceptIn (splitIn windowTopFirst) windowTopFirst)
  using [slopeFirst_enclosure, interceptFirst_enclosure, rootFirst_enclosure]
  unfolding [hStar, cutoffDen, thetaMin, boundAt, rootDisc, discrim, rootA2, rootA1, rootA0]

end

end Cycle63.Optimization
