/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryLowTarget
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryPhysical
noncomputable section
open Cycle63InitialMass

/-- The existing physical scheduler already satisfies the extra allowance
gates; no further restriction on the requested final error is needed. -/
theorem low_target_le_accepted_of_schedule (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh epsilon : ℝ)
    (hmu : g.μ = geometryLossUnit 1 epsilon)
    (homega : omega ≤ 33*g.μ/128) (hmesh : mesh ≤ g.μ/8) :
    lowTarget g N amp omega mesh ≤ geometryAffineLowTarget g N amp omega mesh := by
  have hcap : g.μ ≤ (7/30000000)/128 := by
    rw [hmu]
    unfold geometryLossUnit
    simp only [mul_one]
    exact (min_le_right _ _).trans (min_le_left _ _)
  apply low_target_le_accepted g N amp omega mesh <;> linarith


end
end OAI.SevenEighths.AuxiliaryPhysical
#print axioms OAI.SevenEighths.AuxiliaryPhysical.low_target_le_accepted_of_schedule
