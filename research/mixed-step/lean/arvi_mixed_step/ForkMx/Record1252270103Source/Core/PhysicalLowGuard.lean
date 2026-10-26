/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Mixed step (L4/L5, F3): fork of Record1252270103Source.Core.PhysicalLowGuard; changes: the node
facts `NodeGeometry_mx` (the ledger's `RealGeometryLow` at a virtual node) replace `RealGeometry`;
only `parent_budget_room` is used, as in Collet's proof. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowGuard
import Submissions.arvi_mixed_step.Downstream.Node
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowGuard
noncomputable section
open Filter Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open OAI OAI.SevenEighths QRH.Record1252270103Low
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open QRH.MixedStep.Downstream

theorem guard_slack_of_geometry_mx (n low : Source) (b : ℝ)
    (hg : NodeGeometry_mx n low b) (hB0 : 0≤(low.B:ℝ)) (hB1 : (low.B:ℝ)≤1)
    (t F slots width frequency reserve rho plainRound logarithmic : ℝ)
    (hfrequency : 0≤frequency) (hreserve : 0≤reserve) (hrho : 0≤rho)
    (ht : t≤sourceTReal n b+(n.L:ℝ)*width)
    (hF : sourceFReal n low b-frequency-reserve≤F) (hslots : slots≤b)
    (hlog : logarithmic≤(n.allowance:ℝ))
    (hsmall : (n.L:ℝ)*width+frequency+reserve+rho+2*plainRound≤(n.allowance:ℝ)) :
    logarithmic+2*plainRound+(low.B:ℝ)*rho+2*(n.allowance:ℝ) ≤
      (low.B:ℝ)*F-t-slots := by
  have hbase := hg.parent_budget_room
  have hF' := mul_le_mul_of_nonneg_left hF hB0
  have hfreq := mul_le_mul_of_nonneg_right hB1 hfrequency
  have hres := mul_le_mul_of_nonneg_right hB1 hreserve
  have hr := mul_le_mul_of_nonneg_right hB1 hrho
  nlinarith only [hbase,hF',hfreq,hres,hr,ht,hslots,hlog,hsmall]

theorem eventually_geometry_guard_mx (n low : Source) (N : ℕ) (upper plainUpper ξ : ℝ)
    (he : 0<(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hB0 : 0≤(low.B:ℝ)) (hB1 : (low.B:ℝ)≤1)
    (hupper : 1≤upper) (hξ : 0<ξ) (hξstep : ξ≤step n) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(b : ℝ),NodeGeometry_mx n low b →
      ∀(t F slots width reserve rho plainRound : ℝ),
      0≤reserve → 0≤rho → width≤step n → reserve≤step n → rho≤step n → plainRound≤step n →
      t≤sourceTReal n b+(n.L:ℝ)*width →
      sourceFReal n low b-frequencyLoss Z 32 ξ-reserve≤F → slots≤b →
      (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
        (low.B:ℝ)*rho+2*(n.allowance:ℝ)≤(low.B:ℝ)*F-t-slots := by
  filter_upwards [eventually_fixed_losses n N upper plainUpper ξ he hupper hξ hξstep] with Z hz
  refine ⟨hz.1,?_⟩
  intro b hg t F slots width reserve rho plainRound hreserve hrho hw hr hρ hp ht hF hslots
  exact guard_slack_of_geometry_mx n low b hg hB0 hB1 t F slots width
    (frequencyLoss Z 32 ξ) reserve rho plainRound
    (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper))
    hz.2.2.1 hreserve hrho ht hF hslots hz.2.1
    (step_budget n he.le hL width _ reserve rho plainRound hw hz.2.2.2 hr hρ hp)

end
end QRH.Record1252270103Source.PhysicalLowGuard
#print axioms QRH.Record1252270103Source.PhysicalLowGuard.eventually_geometry_guard_mx
