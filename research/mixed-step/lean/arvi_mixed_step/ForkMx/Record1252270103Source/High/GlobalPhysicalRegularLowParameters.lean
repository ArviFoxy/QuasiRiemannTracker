/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
Mixed step (L4/L5, F3): fork of Record1252270103Source.High.GlobalPhysicalRegularLowParameters;
changes: the LOW mesh and the slot supply are taken from the two-parent family
`global_selected_regular_low_buffered_positive_family_mx`, under the node price
`MixedNodePrice n low b φ` instead of `RealGeometry`/`ParentGood n`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularLowParameters
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularLowSource
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open Cycle61Moment Record1252270103Finite Record1252270103StepScalar
open CenteredMomentNaturalFixedRaySource
open QRH.Record1252270103Low QRH.Record1252270103Graph PhysicalAnalytic
open Set Admission.SelectedRegularLowSource
local notation "O"=>HeckeFamily.O
variable (n low:Source)(b φ θ:ℝ)
variable (hprice:QRH.MixedStep.Ledger.MixedNodePrice n low b φ)(hlow:ParentGood low)
variable (ha:0<(n.allowance:ℝ))(hqhalf:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
variable (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hθ:0<θ)

def regularLowMesh_mx:ℝ:=Classical.choose
  (global_selected_regular_low_buffered_positive_family_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ)

theorem regular_low_mesh_positive_mx:0<regularLowMesh_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ:=
  (Classical.choose_spec
    (global_selected_regular_low_buffered_positive_family_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ)).1

variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
variable (hH:RayOrthogonality.globalUnits M≤H)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (Mslot:α→ℝ)(hMslot:∀i,0≤Mslot i)
variable (mesh:ℝ)(hmesh:mesh≤regularLowMesh_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ)
variable (N:ℕ)(wmin rmin εslot τ:ℝ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (hτ:0<τ)(hτheight:2*τ<100*(εslot/4))
variable (ηanchor η₀:Character)(Q:Ideal O)(hQM:Q≤M)
variable (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
local instance regularLowParametersQuotientFinite_mx : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def regular_low_slot_supply_mx :=
  (Classical.choose_spec
    (global_selected_regular_low_buffered_positive_family_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ)).2
    mesh hmesh α M H hH Mslot hMslot 6 θ (θ/100) (by norm_num) hθ (by positivity)
    W hWs hW 1 100 τ εslot (highBuffer 1 1 εslot (θ/16)) (highKappa εslot (θ/16))
    (εslot/4) 2 40 20 1 100 (by norm_num) (by norm_num) hτ hc.slot_pos hc.buffer_pos hc.buffer_small
    hc.kappa_pos (div_nonneg hc.slot_pos.le (by norm_num)) hc.slot_budget (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl hτheight ηanchor η₀ Q hQM hQ hQt hQ72

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_low_mesh_positive_mx
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_low_slot_supply_mx
