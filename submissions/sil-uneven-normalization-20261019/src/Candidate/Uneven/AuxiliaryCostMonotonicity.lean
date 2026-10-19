/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.High.BalancedMass
import Candidate.Uneven.AuxiliaryMainLowPhysicalCost

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.AuxiliaryHigh
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondEnergySplit
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
open CenteredMomentSectorLocalization LocalMoment Cycle63Moment Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

theorem main_low_complete_cost_mono {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap) (second : Bool)
    (d : Label→SecondInputDatum α) (c c' : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (hcc : ∀l,c l≤c' l) :
    AuxiliaryPhysical.mainLowPhysicalCompleteCost N a ap second d c t u select ≤
      AuxiliaryPhysical.mainLowPhysicalCompleteCost N a ap second d c' t u select := by
  unfold AuxiliaryPhysical.mainLowPhysicalCompleteCost
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  split_ifs
  · unfold mainNormalizedPhysicalCost
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right (hcc r.1)
        exact div_nonneg (d r.1).K_pos.le (lowerFactor_pos N a ap ha hap).le
      · exact (normalizer_pos (d r.1).C (d r.1).D (d r.1).hC (d r.1).inactive).le
    · split_ifs <;> exact sq_nonneg _
  · exact le_rfl

end
end OAI.SevenEighths.AuxiliaryHigh
#print axioms OAI.SevenEighths.AuxiliaryHigh.main_low_complete_cost_mono
