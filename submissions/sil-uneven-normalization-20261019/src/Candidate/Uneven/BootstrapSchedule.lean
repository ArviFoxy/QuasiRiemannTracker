/- Copyright (c) 2026 Sil. Apache-2.0. Adapted from PR63 with OpenAI Codex assistance. -/
import Candidate.Uneven.FineSchedule
import Candidate.Uneven.AuxiliaryAssemblySourceMesh

set_option autoImplicit false
namespace OAI.SevenEighths.BootstrapPlain
noncomputable section
open SaturatedPlain Cycle63Moment Cycle63MarkedPlain

/-- Both moment sources admit this one fixed mesh. -/
def bootstrapRawMesh : ℝ := min fineRawMesh (AuxiliaryAssembly.sourceMesh fineRawRate)

theorem bootstrap_raw_mesh_gates : 0<bootstrapRawMesh ∧
    bootstrapRawMesh ≤ markedPlainMesh (3/4) fineRawRate ∧
    bootstrapRawMesh ≤ fineRawRate ∧
    bootstrapRawMesh ≤ AuxiliaryAssembly.sourceMesh fineRawRate := by
  have hA := AuxiliaryAssembly.source_mesh_pos (show 0<fineRawRate by norm_num [fineRawRate])
  have hm : bootstrapRawMesh ≤ fineRawMesh := min_le_left _ _
  exact ⟨lt_min fine_raw_mesh_gates.1 hA, hm.trans fine_raw_mesh_gates.2.1,
    hm.trans fine_raw_mesh_gates.2.2, min_le_right _ _⟩

def bootstrapGeometryMesh (oldMesh : ℝ) : ℝ := min oldMesh (bootstrapRawMesh*fineRawCore/64)

theorem bootstrap_geometry_mesh_gates (oldMesh : ℝ) (hold : 0<oldMesh) :
    0<bootstrapGeometryMesh oldMesh ∧ bootstrapGeometryMesh oldMesh ≤ oldMesh ∧
      31*bootstrapGeometryMesh oldMesh ≤ bootstrapRawMesh*fineRawCore := by
  have hm := bootstrap_raw_mesh_gates.1
  have hc : 0<fineRawCore := by norm_num [fineRawCore]
  have hcap : bootstrapGeometryMesh oldMesh ≤ bootstrapRawMesh*fineRawCore/64 := min_le_right _ _
  exact ⟨lt_min hold (by positivity),min_le_left _ _,by nlinarith⟩

theorem bootstrap_width_cap {P : HighSourceParameters} {N : ℕ}
    {W : ℝ→ℂ} {lo hi mesh oldMesh w : ℝ}
    (h : FineMarkedSchedule P N W lo hi) (hm : mesh ≤ bootstrapGeometryMesh oldMesh)
    (hw : w ≤ P.d*mesh) : w ≤ bootstrapRawMesh*fineRawCore := by
  rw [h.degree] at hw
  have hc : bootstrapGeometryMesh oldMesh ≤ bootstrapRawMesh*fineRawCore/64 := min_le_right _ _
  have hp : 0 ≤ bootstrapRawMesh*fineRawCore :=
    mul_nonneg bootstrap_raw_mesh_gates.1.le (by norm_num [fineRawCore])
  nlinarith

end
end OAI.SevenEighths.BootstrapPlain
#print axioms OAI.SevenEighths.BootstrapPlain.bootstrap_raw_mesh_gates
#print axioms OAI.SevenEighths.BootstrapPlain.bootstrap_width_cap
