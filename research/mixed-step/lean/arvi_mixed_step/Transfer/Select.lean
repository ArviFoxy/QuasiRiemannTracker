/- Mixed source step, L2 transfer: new in this submission; uses Sil's `upward_subset` by import.

Choosing the selected block under (S).

Step 8 of the plan: the block `J` is chosen greedily (Sil's `upward_subset`)
among the slots allowed by (S), i.e. slots none of whose primes divides the
seed `L`. Any width function `w` (e.g. `log_Z` of the slot window) with
`0 ≤ w ≤ mesh` works; the block reaches the target width up to one mesh. -/
import Submissions.arvi_mixed_step.Transfer.Split
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.GlobalSlotSelection

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Slots allowed by (S): no prime of the slot pool divides the seed. -/
def allowedSlots (s : Input ι) (L : Ideal O) : Finset ι :=
  Finset.univ.filter (fun i => ∀ p ∈ s.slots i, ¬p ∣ L)

/-- A selected block satisfying (S) whose width is within one mesh above the
target, provided the allowed slots carry at least the target width. -/
theorem select_block (s : Input ι) (L : Ideal O) (w : ι → ℝ) (target mesh : ℝ)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh) (ht : 0 ≤ target)
    (hfull : target ≤ ∑ i ∈ allowedSlots s L, w i) :
    ∃ J : Finset ι, (∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L) ∧
      target ≤ ∑ j ∈ J, w j ∧ (∑ j ∈ J, w j) ≤ target + mesh := by
  obtain ⟨J, hJ, hlo, hhi⟩ := Candidate.FourthPower.GlobalSlotSelection.upward_subset
    (allowedSlots s L) w target mesh hm (fun i _ => hw i) (fun i _ => hwm i) ht hfull
  refine ⟨J, ?_, hlo, hhi.trans (min_le_right _ _)⟩
  intro j hj
  exact (Finset.mem_filter.mp (hJ hj)).2

end
end QRH.MixedStep.Transfer
