/- The bin split and the caps of the marked count: the residual of the caps increases on the split
range, so the bin split is its root, and the constraints the caps meet with equality.
Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.WindowTop
import Candidate.Cycle63.Certificate.MonoTactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-! The marked ledger at the window top `slotTop`. -/

/-- The analytic loss charged to the marked saving, for slot sums up to the window top. -/
def markedLoss : ℝ := markedLossAt slotTop

theorem markedLoss_pos : 0 < markedLoss := markedLossAt_pos (by norm_num [slotTop])

/-- The price intercept at the bin split `q`, for the window top. -/
def priceIntercept (q : ℝ) : ℝ := priceInterceptIn q slotTop

/-- The price intercept before its denominators are cleared. -/
theorem priceIntercept_eq {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) :
    priceIntercept q =
      (1 - density q + weight q - q*(movingSlope q - 1)*cellMesh - lowReserveWeight*(5 - 6*density q)
        - priceEndRate q*(cellMesh + supplyLoss) - markedLoss - lowReserveAt q)/(q + weight q) :=
  priceInterceptIn_eq h0 h1 slotTop

/-- The growth rate of the HIGH reserve per unit of zero parameter above the bin split `q`, in the
top cell of the slot window, at the price intercept. -/
def priceEndGrowth (q : ℝ) : ℝ := priceEndGrowthIn q slotTop

/-- The smallest bin top at which the growth of the HIGH reserve above the bin split `q` pays the
net saving of the price end in the top cell. -/
def priceEndBinTop (q : ℝ) : ℝ := priceEndBinTopIn q slotTop

/-- The frequency factor of the live slots at the top cell, at the price intercept of the bin
split `q`. -/
def frequencyFactorAt (q : ℝ) : ℝ := frequencyFactorIn q slotTop

/-- The product of the inverse width cap and the core factor at which the capped live channel keeps
the loss and the LOW reserve in the top cell at the price intercept of the bin split `q`. -/
def balancedCoreCap (q : ℝ) : ℝ := balancedCoreCapIn q slotTop

/-- The residual of the caps in the top cell of the slot window. -/
def capResidual (q : ℝ) : ℝ := capResidualIn q slotTop

/-- The bin split: the point of the split range at which the capped live channel and the price
channel of the marked saving meet in the top cell, with the caps that the count provides. -/
def markedSplit : ℝ := splitIn slotTop

/-- The top of the range of bins in which the marked count is used. -/
def markedBinTop : ℝ := priceEndBinTop markedSplit

/-- The cap unit `1 - c_L` at the bin top. -/
def capUnit : ℝ := capUnitAt markedBinTop

/-- Width cap of the inverse slots. -/
def inverseWidthCap : ℝ := capUnit/2

/-- Width cap of the plain slots. -/
def plainWidthCap : ℝ := capUnit/(6*plainCapacityCost)

/-- The chosen width at the caps: the inverse cap counted twice and the plain cap once. -/
def chosenWidthCap : ℝ := (2*inverseWidthCap + plainWidthCap)/3

/-- Slope `c_L` of the lower bound `1 - c_L δ` of the marked count. -/
def countSlope : ℝ := 1 - capUnit

/-- Length cap of the inverse fibers. -/
def inverseLengthCap : ℝ := countSlope

/-- Length cap of the plain fibers. -/
def plainLengthCap : ℝ := countSlope/2

/-- The large-root cutoff of the marked count. -/
def markedRootCutoff : ℝ := rootCutoffAt markedBinTop inverseWidthCap

/-- The core factor `1 - 6 κ` of the live frequency, for the root cutoff `κ`. -/
def coreFactor : ℝ := 1 - 6*markedRootCutoff

/-- The largest amplifier length on the cell range: the one of the top cell. -/
def amplifierCap : ℝ := cellAmplifier markedSplit (priceIntercept markedSplit) slotTop

/-- The frequency factor of the live slots at the largest amplifier length. -/
def frequencyFactor : ℝ := 1 - 6*amplifierCap - frequencyLossCap

/-- The frequency of the live slots: the core factor times the frequency factor. -/
def liveFrequency : ℝ := coreFactor*frequencyFactor

/-- The live width cap: the inverse width cap at the live frequency. -/
def liveCap : ℝ := inverseWidthCap*liveFrequency

/-- The smallest growth rate of the HIGH reserve per unit of zero parameter above the bin split on
the cell range: the one of the top cell. -/
def reserveGrowth : ℝ := priceEndGrowth markedSplit

/-- The balancing core cap increases with the bin split. -/
theorem balancedCoreCap_mono :
    StrictMonoOn (fun q => balancedCoreCap q) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => balancedCoreCap q) (Set.Icc (1/2) (37/50)) := by
  simp only [balancedCoreCap, balancedCoreCapIn, frequencyFactorIn, cellAmplifier, cellHigh, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]
  rat_mono []

/-- The bin top of the price end increases with the bin split. -/
theorem priceEndBinTop_mono :
    StrictMonoOn (fun q => priceEndBinTop q) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => priceEndBinTop q) (Set.Icc (1/2) (37/50)) := by
  simp only [priceEndBinTop, priceEndBinTopIn, priceEndGrowthIn, cellAmplifier, priceInterceptIn, interceptNum, interceptDen,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]
  rat_mono []

/-- The bin top of the price end at the bottom of the split range. -/
bracket priceEndBinTop_low (digits := 6) : priceEndBinTop (1/2)
  unfolding [priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The bin top of the price end at the top of the split range. -/
bracket priceEndBinTop_high (digits := 6) : priceEndBinTop (37/50)
  unfolding [priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The bin tops of the split range. -/
def binTopRange : Set ℝ := Set.Icc (priceEndBinTop (1/2)) (priceEndBinTop (37/50))

/-- The core cap falls with the bin top: the cap unit falls and the root cutoff rises. -/
theorem coreCapAt_anti :
    StrictAntiOn (fun d => coreCapAt d) binTopRange ∧
      ContinuousOn (fun d => coreCapAt d) binTopRange := by
  simp only [binTopRange, coreCapAt, capUnitAt, rootCutoffAt, tailSlack, allowanceUnit, liveRate, liveRatio, chosenPerUnit,
    plainCapacityCost, halfGain, density]
  rat_mono [priceEndBinTop_low, priceEndBinTop_high]

/-- The residual of the caps increases on the split range: the balancing core cap rises, and the
core cap that the count provides falls since the bin top rises. -/
theorem capResidual_mono :
    StrictMonoOn (fun q => capResidualIn q slotTop) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => capResidualIn q slotTop) (Set.Icc (1/2) (37/50)) :=
  capResidualIn_mono_of balancedCoreCap_mono priceEndBinTop_mono coreCapAt_anti

/-- The bin split is the root of the residual of the caps. -/
bracket_root markedSplit_spec (digits := 14) : (fun q => capResidualIn q slotTop) on (1/2) (37/50)
  by capResidual_mono
  unfolding [capResidual, capResidualIn, balancedCoreCap, balancedCoreCapIn, frequencyFactorAt, frequencyFactorIn, coreCapAt, capUnitAt, rootCutoffAt, tailSlack, priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]

/-- An enclosure of the bin split. -/
bracket markedSplit_enclosure (digits := 14) : markedSplit using [markedSplit_spec.1]
  unfolding [markedSplit, splitIn]

theorem capResidual_markedSplit : capResidual markedSplit = 0 := markedSplit_spec.2

/-! The constants at the bin split: enclosures, and the constraints met with equality. -/

bracket markedBinTop_bounds (digits := 9) : markedBinTop using [markedSplit_enclosure]
  unfolding [markedBinTop, priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

bracket capUnit_bounds (digits := 9) : capUnit using [markedBinTop_bounds]
  unfolding [capUnit, capUnitAt, chosenPerUnit, plainCapacityCost]

bracket inverseWidthCap_bounds (digits := 9) : inverseWidthCap using [capUnit_bounds]
  unfolding [inverseWidthCap]

bracket plainWidthCap_bounds (digits := 9) : plainWidthCap using [capUnit_bounds]
  unfolding [plainWidthCap, plainCapacityCost]

bracket chosenWidthCap_bounds (digits := 9) : chosenWidthCap using [capUnit_bounds]
  unfolding [chosenWidthCap, inverseWidthCap, plainWidthCap, plainCapacityCost]

bracket countSlope_bounds (digits := 9) : countSlope using [capUnit_bounds] unfolding [countSlope]

bracket markedRootCutoff_bounds (digits := 9) : markedRootCutoff
  using [markedBinTop_bounds, inverseWidthCap_bounds]
  unfolding [markedRootCutoff, rootCutoffAt, liveRate, liveRatio, chosenPerUnit,
    plainCapacityCost, halfGain, density, tailSlack, allowanceUnit]

bracket amplifierCap_bounds (digits := 9) : amplifierCap using [markedSplit_enclosure]
  unfolding [amplifierCap, priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

bracket coreFactor_bounds (digits := 9) : coreFactor using [markedRootCutoff_bounds]
  unfolding [coreFactor]

bracket frequencyFactor_bounds (digits := 9) : frequencyFactor using [amplifierCap_bounds]
  unfolding [frequencyFactor, frequencyLossCap, geometryLossCap, lowReserveWeight, allowanceUnit]

bracket liveFrequency_bounds (digits := 9) : liveFrequency
  using [coreFactor_bounds, frequencyFactor_bounds] unfolding [liveFrequency]

bracket reserveGrowth_bounds (digits := 9) : reserveGrowth using [markedSplit_enclosure]
  unfolding [reserveGrowth, priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The live cap is the one at which the capped live channel is tight in the top cell. -/
theorem liveCap_eq_balanced :
    liveCap = balancedCoreCap markedSplit*frequencyFactorAt markedSplit := by
  have h := capResidual_markedSplit
  have hcore : coreCapAt (priceEndBinTop markedSplit) = inverseWidthCap*coreFactor := rfl
  have hb : balancedCoreCap markedSplit = inverseWidthCap*coreFactor := by
    change balancedCoreCap markedSplit - coreCapAt (priceEndBinTop markedSplit) = 0 at h
    rw [← hcore]
    linarith
  have hf : frequencyFactor = frequencyFactorAt markedSplit := rfl
  rw [hb, ← hf]
  unfold liveCap liveFrequency
  ring

/-- An enclosure of the live cap, through the balancing core cap of the bin split. -/
bracket liveCap_bounds (digits := 13) : liveCap via liveCap_eq_balanced
  using [markedSplit_enclosure]
  unfolding [balancedCoreCap, balancedCoreCapIn, frequencyFactorAt, frequencyFactorIn, priceEndBinTop, priceEndBinTopIn, priceEndGrowth, priceEndGrowthIn, cellAmplifier, cellHigh, priceIntercept, priceInterceptIn, interceptNum, interceptDen, lowReserveAt,
    movingSlope, slopeNum, slopeDen, suppliedAt, priceEndRate, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]

theorem capUnit_pos : 0 < capUnit := by linarith [capUnit_bounds.1]

theorem inverseWidthCap_pos : 0 < inverseWidthCap := by
  unfold inverseWidthCap; linarith [capUnit_pos]

theorem plainWidthCap_pos : 0 < plainWidthCap := by
  have hu := capUnit_pos
  unfold plainWidthCap plainCapacityCost
  positivity

theorem liveRatio_eq : liveRatio = 22/27 := by
  unfold liveRatio chosenPerUnit plainCapacityCost; norm_num

theorem plainWidthCap_le_inverse : plainWidthCap ≤ inverseWidthCap := by
  have hu := capUnit_bounds
  unfold plainWidthCap inverseWidthCap plainCapacityCost
  norm_num
  linarith

/-- The inverse moment is used up to its capacity: `r_cap + 2 w_I = 1`. -/
theorem inverse_caps_sum : inverseLengthCap + 2*inverseWidthCap = 1 := by
  unfold inverseLengthCap countSlope inverseWidthCap; ring

/-- The plain moment is used up to its capacity: `2 m_cap + 6 κ_p w_P = 1`. -/
theorem plain_caps_sum : 2*plainLengthCap + 6*plainCapacityCost*plainWidthCap = 1 := by
  unfold plainLengthCap countSlope plainWidthCap plainCapacityCost; ring

/-- The count bound holds with equality at the bin top. -/
theorem count_slope_identity :
    (5 - 2*markedBinTop)*countSlope = 10/3 + chosenWidthCap*(5 - 6*markedBinTop) := by
  have hd := markedBinTop_bounds
  have hD : 0 < 5 - 2*markedBinTop + chosenPerUnit*(5 - 6*markedBinTop) := by
    unfold chosenPerUnit plainCapacityCost
    rat_pos [hd]
  have hu : capUnit*(5 - 2*markedBinTop + chosenPerUnit*(5 - 6*markedBinTop)) =
      5/3 - 2*markedBinTop := by
    unfold capUnit capUnitAt
    exact div_mul_cancel₀ _ hD.ne'
  have hk : chosenWidthCap = chosenPerUnit*capUnit := by
    unfold chosenWidthCap inverseWidthCap plainWidthCap chosenPerUnit
    ring
  rw [hk]
  unfold countSlope
  linear_combination (-1 : ℝ)*hu

/-- The large-root tail equals the live gain at the bin top. -/
theorem root_cutoff_balance :
    liveRate markedBinTop*(inverseWidthCap*coreFactor) =
      markedRootCutoff*(6*density markedBinTop - 1 - tailSlack) := by
  have hd := markedBinTop_bounds
  have hw := inverseWidthCap_bounds
  have hD : (6*density markedBinTop - 1 - tailSlack) + 6*liveRate markedBinTop*inverseWidthCap ≠ 0 := by
    apply ne_of_gt
    unfold liveRate liveRatio chosenPerUnit plainCapacityCost halfGain density tailSlack allowanceUnit
    rat_pos [hd, hw]
  have hκ : markedRootCutoff*((6*density markedBinTop - 1 - tailSlack) +
      6*liveRate markedBinTop*inverseWidthCap) = liveRate markedBinTop*inverseWidthCap := by
    unfold markedRootCutoff rootCutoffAt
    exact div_mul_cancel₀ _ hD
  unfold coreFactor
  linear_combination (-1 : ℝ)*hκ

/-- The bin top is where the growth of the HIGH reserve pays the net saving of the price end in the
top cell. -/
theorem bin_top_growth :
    priceEndRate markedSplit*suppliedAt slotTop - markedLoss =
      (markedBinTop - markedSplit)*reserveGrowth := by
  have hg := reserveGrowth_bounds
  have hg' : priceEndGrowth markedSplit ≠ 0 := by
    have : 0 < reserveGrowth := by linarith [hg.1]
    exact this.ne'
  unfold markedBinTop reserveGrowth priceEndBinTop priceEndBinTopIn priceEndGrowth markedLoss
  unfold priceEndGrowth at hg'
  rw [add_sub_cancel_left, div_mul_cancel₀ _ hg']

/-- With the moving the price channel is tight in every cell at the price intercept. -/
theorem price_tight {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (b : ℝ) :
    cellHigh q (priceIntercept q) b + priceEndRate q*suppliedAt b - markedLoss - lowReserveAt q = 0 := by
  have hq := (plane_sum_pos h0 h1).ne'
  have hB : priceIntercept q*(q + weight q) =
      1 - density q + weight q - q*(movingSlope q - 1)*cellMesh - lowReserveWeight*(5 - 6*density q)
        - priceEndRate q*(cellMesh + supplyLoss) - markedLoss - lowReserveAt q := by
    rw [priceIntercept_eq h0 h1]
    exact div_mul_cancel₀ _ hq
  have hlam : movingSlope q*(q + weight q) = q + 9/2*weight q - priceEndRate q := by
    rw [movingSlope_eq h0 h1]
    unfold slope
    rw [sub_mul, div_mul_cancel₀ _ hq, div_mul_cancel₀ _ hq]
  have hW : weight q = amplifierRatio q*(5 - 6*density q) := rfl
  unfold cellHigh cellAmplifier suppliedAt
  linear_combination (-1 : ℝ)*hB + b*hlam +
    (priceIntercept q - 1 + (9/2 - movingSlope q)*b)*hW

/-- At the bin split the capped live channel is tight in the top cell. -/
theorem cap_tight :
    cellHigh markedSplit (priceIntercept markedSplit) slotTop + liveRate markedSplit*liveCap
      - markedLoss - lowReserveAt markedSplit = 0 := by
  have hq := markedSplit_enclosure
  have hr : 0 < liveRate markedSplit := by
    unfold liveRate liveRatio chosenPerUnit plainCapacityCost halfGain
    rat_pos [hq]
  have hF : 0 < frequencyFactorAt markedSplit := by
    simp only [frequencyFactorAt, frequencyFactorIn, cellAmplifier, priceInterceptIn, interceptNum, interceptDen,
      movingSlope, slopeNum, slopeDen, amplifierRatio, slotTop,
      cellMesh, lowReserveWeight, markedLossAt, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss,
      geometryLossCap, markedBinWidth, allowanceUnit, frequencyLossCap]
    rat_pos [hq]
  rw [liveCap_eq_balanced]
  unfold balancedCoreCap balancedCoreCapIn frequencyFactorAt priceIntercept markedLoss
  unfold frequencyFactorAt at hF
  field_simp [hr.ne', hF.ne']
  ring

/-- At the bin split the price channel and the capped live channel are equal in the top cell. -/
theorem price_eq_live_top : priceEndRate markedSplit*suppliedAt slotTop = liveRate markedSplit*liveCap := by
  have hq := markedSplit_enclosure
  have h1 := price_tight (by linarith [hq.1]) (by linarith [hq.2]) slotTop
  have h2 := cap_tight
  linarith

end

end Cycle63.Optimization
