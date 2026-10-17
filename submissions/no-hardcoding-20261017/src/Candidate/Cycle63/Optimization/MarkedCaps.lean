/- The caps of the marked count, its bin top, its root cutoff and the bin split, each defined by the
constraint it meets with equality. Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.Plane
import Candidate.Cycle63.Optimization.Slacks
import Candidate.Cycle63.Certificate.Root

set_option autoImplicit false

namespace Cycle63.Optimization

noncomputable section

/-! The marked count is used in the bins `δ = 2a - 1` from the bin split `q` up to the bin top `d`.
There it is at least `1 - c_L δ` (`VariableSupply.count_lower`), and its inverse and plain moment
estimates select slots of total widths at most `w_I` and `w_P`. Larger caps raise the live gain of
the marked count, so each cap is the largest one its constraint allows:

* the inverse length cap is `c_L` and the plain length cap `c_L/2` (`VariableSupply.fiber_exponent`);
* the inverse moment needs `c_L + 2 w_I ≤ 1`, so `w_I = u/2` with the cap unit `u = 1 - c_L`;
* the plain moment needs `c_L + 6 κ_p w_P ≤ 1` for the plain capacity cost `κ_p`, so
  `w_P = u/(6 κ_p)`;
* the count bound at the bin top `d` for the chosen width `s = (2 w_I + w_P)/3 = k u`, with
  `k = (1 + 1/(6 κ_p))/3`, needs `(5 - 2d) c_L ≥ 10/3 + s (5 - 6d)`, so
  `u = (5/3 - 2d)/(5 - 2d + k (5 - 6d))` (`capUnitAt`).

The caps fall as the bin top rises, so the bin top is the smallest one for which the growth of the
HIGH reserve above the bin split pays the net marked saving (`priceEndBinTop`), and the root cutoff
`κ` is the smallest one for which the large-root tail dominates the live gain at the bin top
(`rootCutoffAt`).

The marked saving in the cell `b` of the slot sum (`b - cellMesh ≤ Σ w ≤ b`) is the smaller of the
price channel, the price times the supplied width `b - cellMesh - supplyLoss`, and the capped live
channel, the live rate times the live cap. The slope `movingSlope` makes the HIGH reserve plus the
price channel the same in every cell, so the intercept of the price channel is one number
(`priceInterceptIn`); the capped live channel binds only in the top cell `s` of the slot window. For a
window top `s` the bin split is the point where both channels are tight in the top cell: the root
of `capResidualIn · s`, the product of the inverse width cap and the core factor that balances the
capped live channel at `q`, less the one that the count provides with the bin top of `q`. The window
top itself is computed in `WindowTop`. -/

/-- Capacity cost per unit of plain slot width in the plain moment: `2 β - 1 ≤ 3/4` for the zeros
of real part `β ≤ 7/8` of the baseline region. -/
def plainCapacityCost : ℝ := 3/4

/-- The chosen width `(2 w_I + w_P)/3` per unit of the cap unit `u`, for `w_I = u/2` and
`w_P = u/(6 κ_p)`. -/
def chosenPerUnit : ℝ := (1 + 1/(6*plainCapacityCost))/3

/-- The ratio of the chosen width to the inverse width at the caps. -/
def liveRatio : ℝ := 2*chosenPerUnit

/-- The saving per unit of live slot width at slot amplitude `1/2` in the bin with zero
parameter `d`. -/
def halfGain (d : ℝ) : ℝ := d*(5 - 6*d)/(5 - 2*d)

/-- The live rate of the marked count in the bin `d`: the half-amplitude gain per unit of the
inverse width at the caps. -/
def liveRate (d : ℝ) : ℝ := liveRatio*halfGain d

/-- The common-prime rate `q - (4 ρ - 1)` of the valuation estimate at the bin split `q` where
`ρ ≥ 23/62`, so that `4 ρ - 1` is the larger of its two rates (`ledgerPrice`). -/
def priceEndRate (q : ℝ) : ℝ := q - (4*density q - 1)

/-- Numerator of the moving slope. -/
def slopeNum (q : ℝ) : ℝ := 430*q^2 - 399*q + 135

/-- Denominator of the moving slope. -/
def slopeDen (q : ℝ) : ℝ := q*(24*q^2 - 34*q + 35)

/-- The slope of the affine plain moment at the bin split `q` for which the price bound of the HIGH
reserve is the same in every cell: the cancellation slope lowered by the price over `q + W`
(`movingSlope_eq`), as one fraction. -/
def movingSlope (q : ℝ) : ℝ := slopeNum q/slopeDen q

/-- The sum of the bin split and the weight of the amplified slots is positive below `3/4`. -/
theorem plane_sum_pos {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) : 0 < q + weight q := by
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  have h9 : (9:ℝ) - 12*q ≠ 0 := by linarith
  have hw := plane_sum_closed h5 h9 1
  rw [one_mul] at hw
  have hN : (9 - 12*q)*(5 - 2*q) + 2*1*(22*q - 5) = planeQuadratic q := by unfold planeQuadratic; ring
  rw [hw, hN]
  exact div_pos (mul_pos h0 (planeQuadratic_pos q)) (mul_pos (by linarith) (by linarith))

/-- The moving slope is the cancellation slope lowered by the price over `q + W`. -/
theorem movingSlope_eq {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) :
    movingSlope q = slope q - priceEndRate q/(q + weight q) := by
  have hE : (0:ℝ) < 24*q^2 - 34*q + 35 := planeQuadratic_pos q
  have h5' : (5:ℝ) - q*2 ≠ 0 := by linarith
  have h9' : (9:ℝ) - q*12 ≠ 0 := by linarith
  have hsum : (q + weight q)*((9 - 12*q)*(5 - 2*q)) = q*(24*q^2 - 34*q + 35) := by
    unfold weight amplifierRatio density
    field_simp
    ring
  have hW := plane_sum_pos h0 h1
  have hγ : priceEndRate q*(3*(5 - 2*q)) = -(6*q^2 - 73*q + 45) := by
    unfold priceEndRate density
    field_simp
    ring
  unfold movingSlope slopeNum slopeDen
  rw [slope_closed h0 h1]
  unfold planeQuadratic
  symm
  rw [eq_div_iff (by positivity), sub_mul]
  have e1 : 24*q*(q + 5)/(24*q^2 - 34*q + 35)*(q*(24*q^2 - 34*q + 35)) = 24*q^2*(q + 5) := by
    rw [div_mul_eq_mul_div, div_eq_iff hE.ne']
    ring
  have e2 : priceEndRate q/(q + weight q)*(q*(24*q^2 - 34*q + 35)) =
      priceEndRate q*((9 - 12*q)*(5 - 2*q)) := by
    rw [← hsum, div_mul_eq_mul_div, div_eq_iff hW.ne']
    ring
  rw [e1, e2]
  linear_combination (-(3 - 4*q))*hγ

/-- The slot width that the marked count credits in the cell with upper edge `b`: the cell's lower
edge less the width lost to the two common allocations and to the tiny-slot discard. -/
def suppliedAt (b : ℝ) : ℝ := b - cellMesh - supplyLoss

/-- The amplifier length of the cell `b` at the bin split `q` for the intercept `B`. -/
def cellAmplifier (q B b : ℝ) : ℝ :=
  amplifierRatio q*(B - 1 + (9/2 - movingSlope q)*b) + lowReserveWeight

/-- The HIGH reserve before savings at the bin split `q` in the cell `b`, for the intercept `B`. -/
def cellHigh (q B b : ℝ) : ℝ :=
  1 - density q - q*(B - (movingSlope q - 1)*(b - cellMesh)) - cellAmplifier q B b*(5 - 6*density q)

/-- The LOW reserve `alpha (1 - 4 q/3)` at the bin split `q`. -/
def lowReserveAt (q : ℝ) : ℝ := lowReserveWeight*(1 - 4*q/3)

/-- Numerator of the price intercept over `q (24 q^2 - 34 q + 35)^2`, for slot sums up to
`s`. -/
def interceptNum (q s : ℝ) : ℝ :=
  96*q^4 + 344*q^3 - 540*q^2 + 700*q
    + cellMesh*(-4752*q^4 + 26732*q^3 - 30316*q^2 + 11505*q - 1350)
    + lowReserveWeight*(768*q^5 + 2176*q^4 - 6384*q^3 + 8840*q^2 - 4200*q)
    + supplyLoss*(-576*q^5 + 8256*q^4 - 20956*q^3 + 27656*q^2 - 18555*q + 4725)
    + markedLossAt s*(-576*q^4 + 2688*q^3 - 4572*q^2 + 4260*q - 1575)

/-- Denominator of the price intercept. -/
def interceptDen (q : ℝ) : ℝ := q*(24*q^2 - 34*q + 35)^2

/-- The intercept at which the HIGH reserve, credited with the supplied width at the price, keeps
the loss for slot sums up to `s` and the LOW reserve in every cell (`priceInterceptIn_eq`; with
the moving slope this is one number), as one fraction. -/
def priceInterceptIn (q s : ℝ) : ℝ := interceptNum q s/interceptDen q

/-- The price intercept before its denominators are cleared. -/
theorem priceInterceptIn_eq {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (s : ℝ) :
    priceInterceptIn q s =
      (1 - density q + weight q - q*(movingSlope q - 1)*cellMesh - lowReserveWeight*(5 - 6*density q)
        - priceEndRate q*(cellMesh + supplyLoss) - markedLossAt s - lowReserveAt q)/(q + weight q) := by
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  have h9 : (9:ℝ) - 12*q ≠ 0 := by linarith
  have hq : q ≠ 0 := h0.ne'
  have hE := (planeQuadratic_pos q).ne'
  have hw := plane_sum_closed h5 h9 1
  rw [one_mul] at hw
  have hN : (9 - 12*q)*(5 - 2*q) + 2*1*(22*q - 5) = planeQuadratic q := by unfold planeQuadratic; ring
  rw [hN] at hw
  have hsl : movingSlope q = (430*q^2 - 399*q + 135)/(q*planeQuadratic q) := rfl
  have h5' := h5; ring_nf at h5'
  have h9' := h9; ring_nf at h9'
  have hd : interceptDen q = q*planeQuadratic q^2 := by unfold interceptDen planeQuadratic; ring
  rw [show priceInterceptIn q s = interceptNum q s/interceptDen q from rfl]
  symm
  unfold lowReserveAt priceEndRate
  rw [hw, hsl, weight_closed h5 h9, hd]
  unfold density
  field_simp
  unfold interceptNum planeQuadratic
  ring

/-- The growth rate of the HIGH reserve per unit of zero parameter above the bin split `q`, in the
top cell `s` of the slot window, at the price intercept. -/
def priceEndGrowthIn (q s : ℝ) : ℝ :=
  50*(1 - 6*cellAmplifier q (priceInterceptIn q s) s)/(3*(5 - 2*q)^2)
    - (priceInterceptIn q s - (movingSlope q - 1)*(s - cellMesh))

/-- The smallest bin top at which the growth of the HIGH reserve above the bin split `q` pays the
net saving of the price end in the top cell `s`. -/
def priceEndBinTopIn (q s : ℝ) : ℝ :=
  q + (priceEndRate q*suppliedAt s - markedLossAt s)/priceEndGrowthIn q s

/-- The cap unit `u = 1 - c_L` at the bin top `d`: the largest one for which the count bound holds
at `d` with the caps `w_I = u/2` and `w_P = u/(6 κ_p)`. -/
def capUnitAt (d : ℝ) : ℝ := (5/3 - 2*d)/(5 - 2*d + chosenPerUnit*(5 - 6*d))

/-- The smallest root cutoff at which the large-root tail `κ (6 ρ(d) - 1 - tailSlack)` dominates
the live gain at the inverse width cap `w` and the core factor `1 - 6 κ` in the bin `d`. -/
def rootCutoffAt (d w : ℝ) : ℝ :=
  liveRate d*w/((6*density d - 1 - tailSlack) + 6*liveRate d*w)

/-- The inverse width cap times the core factor at the bin top `d`. -/
def coreCapAt (d : ℝ) : ℝ := capUnitAt d/2*(1 - 6*rootCutoffAt d (capUnitAt d/2))

/-- The frequency factor `1 - 6 amp - ω` of the live slots at the top cell `s`, at the price
intercept of the bin split `q`. -/
def frequencyFactorIn (q s : ℝ) : ℝ :=
  1 - 6*cellAmplifier q (priceInterceptIn q s) s - frequencyLossCap

/-- The product of the inverse width cap and the core factor at which the capped live channel keeps
the loss and the LOW reserve in the top cell `s` at the price intercept of the bin split `q`. -/
def balancedCoreCapIn (q s : ℝ) : ℝ :=
  (lowReserveAt q + markedLossAt s - cellHigh q (priceInterceptIn q s) s)/
    (liveRate q*frequencyFactorIn q s)

/-- The product of the inverse width cap and the core factor that balances the capped live channel
in the top cell `s` at the bin split `q`, less the one that the marked count provides with the bin
top of `q`. -/
def capResidualIn (q s : ℝ) : ℝ := balancedCoreCapIn q s - coreCapAt (priceEndBinTopIn q s)

/-- The bin split for the window top `s`: the point of the split range at which the capped live
channel and the price channel of the marked saving meet in the top cell `s`, with the caps that the
count provides. -/
def splitIn (s : ℝ) : ℝ := Certificate.firstNonneg (fun q => capResidualIn q s) (1/2) (37/50)

end

end Cycle63.Optimization
