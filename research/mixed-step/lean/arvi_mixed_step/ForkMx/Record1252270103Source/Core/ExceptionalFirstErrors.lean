/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F6): fork of Record1252270103Source.Core.ExceptionalFirstErrors
(Hailey Collet, Apache-2.0; inherited notices retained). Original note: the pre-cardinality node
step pays the exceptional centered scalar's errors; only thresholds for fixed profile/cardinality
constants may depend on N.

Collet's guard bounds the errors by `sourceAReal n low b` through `RealGeometry.a_allowance`. The
mixed guard stops one step earlier, at one allowance `e = n.allowance` (from `step_budget` alone),
so that it needs no node geometry; the consumer adds `20e < a` (`MixedGeometry.fee_allowance`) or
the centered slack `2·Amix - a`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalFirstErrors

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open Filter Record1252270103Finite
open OAI OAI.SevenEighths CenteredMomentSectorLocalization

/-- The centered errors cost at most one allowance. -/
theorem node_centered_error_guard_mx (n : Source) (width frequency reserve loss : ℝ)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hf0 : 0≤frequency) (hr0 : 0≤reserve)
    (hw : width≤PhysicalLowGuard.step n) (hf : frequency≤PhysicalLowGuard.step n)
    (hr : reserve≤PhysicalLowGuard.step n) (hl : loss≤PhysicalLowGuard.step n) :
    (n.L:ℝ)*width+5*(frequency+reserve)/6+loss≤(n.allowance:ℝ) := by
  have hs : 0≤PhysicalLowGuard.step n := by unfold PhysicalLowGuard.step;positivity
  have hh:=PhysicalLowGuard.step_budget n he hL width frequency reserve loss 0 hw hf hr hl hs
  linarith

theorem eventually_centered_error_guard_mx (n : Source) (ξ reserve loss width : ℝ)
    (he : 0<(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ)) (hξ : 0<ξ)
    (hξstep : ξ≤PhysicalLowGuard.step n) (hr0 : 0≤reserve)
    (hr : reserve≤PhysicalLowGuard.step n) (hl : loss≤PhysicalLowGuard.step n)
    (hw : width≤PhysicalLowGuard.step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      (n.L:ℝ)*width+5*(frequencyLoss Z 32 ξ+reserve)/6+loss≤(n.allowance:ℝ) := by
  filter_upwards [OAI.SevenEighths.CenteredMomentFirstAmplificationChoice.eventually_frequency_loss 32 ξ
    (by norm_num) hξ] with Z hz
  exact ⟨hz.1,node_centered_error_guard_mx n width _ reserve loss he.le hL hz.2.1 hr0 hw
    (hz.2.2.le.trans hξstep) hr hl⟩

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.node_centered_error_guard_mx
#print axioms QRH.Record1252270103Source.ExceptionalPrice.eventually_centered_error_guard_mx
