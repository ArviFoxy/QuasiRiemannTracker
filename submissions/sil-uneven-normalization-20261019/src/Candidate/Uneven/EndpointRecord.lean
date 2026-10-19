/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0.
Two-stage endpoint assembly with explicit incumbent bounds. -/
import Candidate.Uneven.EndpointInitialLabels
import Candidate.Uneven.EndpointFinalCommonProbe
import Candidate.Uneven.EndpointContract
import Candidate.Target830.Source.RecordPrincipal
import Candidate.Target830.Source.RecordEndpoint

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
noncomputable section
variable [config : Configuration]
open scoped Classical
open Filter HeckeFamily
open Physical Physical.FinalAssembly
open ProbePhysical CenteredMomentDetectorDictionary

def commonSourceMesh (ε t : ℝ) : ℝ :=
  min (UnevenEndpoint.sourceMesh t) (MainAssembly.sourceMesh ε)

theorem common_source_mesh_pos {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    0 < commonSourceMesh ε t :=
  lt_min (UnevenEndpoint.source_mesh_pos ht) (MainAssembly.source_mesh_pos hε)

/-- The explicit incumbent will be discharged first by PR63, then by the warmup. -/
theorem actual_chosen_source_input (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    Physical.FinalAssembly.ChosenSourceInput := by
  intro hβ
  let ε : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hβ hinc (commonSourceMesh ε)
    (fun _ ht => common_source_mesh_pos hε ht)
  have hmD : A.sourceMesh ≤ UnevenEndpoint.sourceMesh A.D.t := by
    rw [hA]
    exact min_le_left _ _
  have hmε : A.sourceMesh ≤ MainAssembly.sourceMesh ε := by
    rw [hA]
    exact min_le_right _ _
  have hβlo := (moment_parameter_gates hβ hinc).2.2
  have hfields := actual_stage_fields A.F hβlo baseline_beta hinc
    A.detector_fine A.sourceMesh A.sourceMesh_pos hmD A.source_fine
  obtain ⟨b,_hb,hsupport⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bΦ : ℝ := max 2 b
  have hbΦ : 2 ≤ bΦ := le_max_left _ _
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  obtain ⟨degree,control,C,hC,hsource⟩ :=
    MainAssembly.detector_label_initial_affine SourcePlane.A.mainPlane A.F η (Sum.inl true)
      hβlo baseline_beta (main_source_incumbent .A hinc) ε hε
      A.sourceMesh A.sourceMesh_pos hmε bΦ hbΦ
  refine ⟨A,hfields,bΦ,ε,hε,le_rfl,?_,degree,control,C,hC,?_⟩
  · intro x hx
    exact (show x ≤ b from hsupport hx).trans (le_max_right _ _)
  · simpa only [Physical.AffineAt, Physical.InitialAffineAt, MainInitial.InitialAffineAt,
      MainInitial.plainLower, MainInitial.plainUpper, plainLower, plainUpper,
      Sil.Uneven.MainSource.widthLo, Sil.Uneven.MainSource.widthHi, widthLower, widthUpper,
      SourcePlane.B, SourcePlane.lambda,
      Target830.Source.RecordEndpoint.principal_detector_label]
      using hsource

theorem beta_le_theta (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    HeckeZeroSupremum.beta ≤ theta :=
  Physical.FinalAssembly.beta_le_theta_of_chosen_source (actual_chosen_source_input hinc)

end
end OAI.SevenEighths.UnevenEndpoint.RecordEndpoint

namespace OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
noncomputable section

theorem beta_le_warmup : HeckeZeroSupremum.beta ≤ (4374143/5000000:ℝ) := by
  exact beta_le_theta (config := ⟨.warmup⟩)
    Target830.Source.RecordEndpoint.beta_le_rational

theorem beta_le_rational :
    HeckeZeroSupremum.beta ≤ (874828524351/1000000000000:ℝ) := by
  exact beta_le_theta (config := ⟨.final⟩) beta_le_warmup

end
end OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
#print axioms OAI.SevenEighths.UnevenEndpoint.RecordEndpoint.actual_chosen_source_input
#print axioms OAI.SevenEighths.UnevenEndpoint.RecordEndpoint.beta_le_warmup
#print axioms OAI.SevenEighths.UnevenEndpoint.RecordEndpoint.beta_le_rational
