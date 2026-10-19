/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointStageParameters
import Candidate.Uneven.MainActualLabelMoments
import Candidate.Uneven.MainNinePlaneFields
import Candidate.Target830.Source.Assembly.InitialSupplier

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.UnevenEndpoint
noncomputable section
variable [config : Configuration]
open HeckeFamily Cycle25ProbeFinalAssembly

def sourceMesh (ε : ℝ) : ℝ :=
  min (Target830.Source.Assembly.sourceMesh ε) (MainAssembly.sourceMesh ε)

theorem source_mesh_pos {ε : ℝ} (hε : 0 < ε) : 0 < sourceMesh ε :=
  lt_min (Target830.Source.Assembly.source_mesh_pos hε) (MainAssembly.source_mesh_pos hε)

theorem main_source_incumbent (P : SourcePlane)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    2*HeckeZeroSupremum.beta-1 ≤ P.mainPlane.incumbent := by
  rw [SourcePlane.mainPlane_incumbent]
  unfold frozenKappa
  linarith only [hinc]

/-- Each stage uses exactly its two newly proved source estimates. -/
theorem actual_stage_fields {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (hdetector : ∀ j, D.ell j ≤ DetectorAffine.detectorMesh D.t/200)
    (mesh : ℝ) (hm : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t)
    (hfine : ∀ j, D.ell j ≤ mesh/200) :
    ∀ P : MainCount.Plane, config.stage.Supports P →
      MainInitialTransport.weighted_AffineFineInputAt P S := by
  have hmold : mesh ≤ Target830.Source.Assembly.sourceMesh D.t :=
    hmesh.trans (min_le_left _ _)
  have hmnew : mesh ≤ MainAssembly.sourceMesh D.t := hmesh.trans (min_le_right _ _)
  have holdlabels : ∀ P : Target830.SourcePlane,
      Target830.Physical.InitialTransport.LabelInitialMoments P S mesh :=
    fun P => Target830.Source.Assembly.actual_label_initial_moments P S hβlo hβhi
      mesh hm hmold
  have hold := Target830.Physical.InitialTransport.actual_five_plane_fields S hβlo hβhi
    hdetector mesh hm hfine holdlabels
  have hnew (P : SourcePlane) :
      MainInitialTransport.weighted_AffineFineInputAt
        (MainInitialTransport.countPlane P.mainPlane) S :=
    MainInitialTransport.actual_detector_affine_input_of_initial P.mainPlane S mesh hm hfine
      (MainAssembly.actual_label_initial_moments P.mainPlane S hβlo hβhi
        (main_source_incumbent P hinc) mesh hm hmnew)
  apply MainInitialTransport.stage_plane_fields S config.stage hold
  · have hh := hnew .A
    have he : MainInitialTransport.countPlane SourcePlane.A.mainPlane=config.stage.aPlane := by
      cases config with
      | mk stage => cases stage <;> rfl
    simpa only [he] using hh
  · have hh := hnew .C
    have he : MainInitialTransport.countPlane SourcePlane.C.mainPlane=config.stage.cPlane := by
      cases config with
      | mk stage => cases stage <;> rfl
    simpa only [he] using hh

end
end OAI.SevenEighths.UnevenEndpoint
#print axioms OAI.SevenEighths.UnevenEndpoint.actual_stage_fields
