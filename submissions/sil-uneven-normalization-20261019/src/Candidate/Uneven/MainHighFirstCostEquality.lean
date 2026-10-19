/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.SelectionCostReduction

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.MainHigh
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum Cycle63InitialMass
local notation "O" => HeckeFamily.O
attribute [local irreducible] Finset.univ

/-- The adapted selection retains precisely the predecessor's second-block
cost; only its external first-allocation weight has changed. -/
theorem uneven_first_cost_eq {α : Type*} [Fintype α] [DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    UnevenSelection.geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j =
    Cycle63InitialMass.geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j := by
  unfold UnevenSelection.geometryMainFirstCost Cycle63InitialMass.geometryMainFirstCost
  apply congrArg (fun x : ℝ => x /
    volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j))
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> rfl

end
end OAI.SevenEighths.MainHigh
#print axioms OAI.SevenEighths.MainHigh.uneven_first_cost_eq
