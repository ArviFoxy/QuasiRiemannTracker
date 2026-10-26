/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
The actual complete family retains one common Mellin height and the full
original marked-pool avoidance required by both source branches. -/
/- Mixed step (L4/L5, F5): fork of Record1252270103Source.High.GlobalPhysicalRegularDictionary
(Hailey Collet); changes: the family is `Family_mx` over `Anchor_mx` (two parents). Only the
two family-level height lemmas are restated; `regular_original_newton_avoidance` and
`regular_selected_plain_upper` are generic and reused verbatim. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularDictionary
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.High.GlobalPhysicalRegularNormalized
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildInput CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeExpansion
open Record1252270103Second Cycle61Moment
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open Admission.SelectedRegularSourceData Admission.SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance regularDictionaryDecidable_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem regular_datum_height_mx {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(r:F.Rows):
    (F.datum r.val.1).input.t=(F.stage r.val.1.1).t:=rfl

theorem regular_common_residual_height_mx {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(origin t u:ℝ)(second:Bool)
    (hstage:∀l,(F.stage l).t=origin)(r:F.Rows):
    residualHeight second F.datum t u r.val=mellinShift origin second t u:=by
  change (F.datum r.val.1).input.t+2*Real.pi*(u-(if second then -t else t))=_
  rw [regular_datum_height_mx F r,hstage]
  rfl

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_common_residual_height_mx
