/- Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.
The columns and allocations returned by the first MAIN selection construct
one literal regular second family, with a common first Mellin height. -/
/- Mixed step (L4/L5, F5): fork of Record1252270103Source.High.GlobalPhysicalRegularFamily
(Hailey Collet); changes: `allocatedRegularFamily_mx` builds a `Family_mx` over `Anchor_mx`
(two parents). The columns `a.Column`, their live gates, ideals, characters and seeds read the first layer
`a.s₀`/`a.modifier₀`; the allocations run over the second-layer pools `a.s.pools`, and the MAIN Fourier
scale is read at the second-layer volume `volume a.s` with the node amplitude `amp`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularFamily
import Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.Admission.SelectedRegularSourceData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic RayFourExpansion
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open SecondRemainder
open Admission OAI.SevenEighths.Record1252270103Source.Collision
open Admission.SelectedRegularSourceData Admission.SelectedSecondPhase
local notation "O"=>HeckeFamily.O
local instance regularFamilyDecidable_mx {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}(a:Anchor_mx α₀ α Z)
variable (column:Label→a.Column)
variable (hLive:∀l,column l∈firstLiveColumns
  (CoupledFirst.geometryFirstSource a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
  (fun _=>logAnnulus))
variable (alloc:∀l,actualAllocations a.s.pools
  (FirstFamily.columnIdeal a.reflected a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l)))
variable (P:Finset (Ideal O))(amp ht:ℝ)(N:ℕ)(χ₀:Label→RayCharacter)

def allocatedRegularFamily_mx:Family_mx a Label where
  column:=column
  data l:={
    stage:={ B:=alloc l,τ:=a.character (column l),t:=ht }
    stage_character:=rfl
    childModifier:=correctedModifier P ((alloc l).val (Sum.inr 0)) ((alloc l).val (Sum.inr 1))
      1 (markedProduct (alloc l).val) (fun _=>1)
    childSeed_sf:=FirstFamily.live_projector_squarefree a.s₀ a.modifier₀ a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin
      (fun _=>logAnnulus) (column l) (hLive l)
    Tsec:=firstMainFourierScale a.reflected (Z^a.D) (volume a.s) Z a.ξ (3*amp) a.reserve 2 N (a.label (column l))
    amp:=amp
    χ₀:=χ₀ l }

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.allocatedRegularFamily_mx
