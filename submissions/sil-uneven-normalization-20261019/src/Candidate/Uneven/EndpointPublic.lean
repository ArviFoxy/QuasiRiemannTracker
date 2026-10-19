/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointActive
import Candidate.Uneven.EndpointActualBin
import Candidate.Uneven.EndpointSelection

noncomputable section
set_option autoImplicit false

namespace OAI.SevenEighths.UnevenEndpoint.Physical
variable [config : Configuration]

/-- The original positive physical slot dictionary is fine enough after every
allowed row-scale rescaling. No total-width or cardinality loss is added. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

end OAI.SevenEighths.UnevenEndpoint.Physical

#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.affine_active_box_fourth
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.Packet.actual_label_packet_bin_bound
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.scheduled_whole_slots
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.rescaled_slot_mesh
