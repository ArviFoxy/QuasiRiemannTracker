/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainDetectorParameters
import Candidate.Uneven.EndpointData

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.DetectorCount
noncomputable section
variable [config : Configuration]
open HeckeFamily HeckeInverseAmplification

abbrev CountParameters (M : Ideal HeckeFamily.O) [NeZero M]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (εm : ℝ) :=
  MainDetectorCount.CountParameters config.stage M H εm

abbrev cutoff (d p κ : ℝ) : ℝ := MainDetectorCount.cutoff config.stage d p κ

theorem fresh_count_parameters (D : DetectorData) (F : SourceData) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact MainDetectorCount.exists_count_parameters config.stage F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end
end OAI.SevenEighths.UnevenEndpoint.Physical.DetectorCount
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.DetectorCount.fresh_count_parameters
