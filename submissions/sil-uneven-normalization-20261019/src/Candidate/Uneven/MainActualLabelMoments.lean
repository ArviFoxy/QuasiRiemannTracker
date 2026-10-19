/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainAffineInput
import Candidate.Uneven.MainAssemblyInitialSupplier

set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open HeckeFamily Cycle25ProbeFinalAssembly

/-- The four genuine source contracts, with the incumbent hypothesis explicit. -/
theorem actual_label_initial_moments (plane : Sil.Uneven.MainSource.Plane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ plane.incumbent)
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t) :
    MainInitialTransport.LabelInitialMoments plane S mesh := by
  intro η bΦ hbΦ label
  exact detector_label_initial_affine plane S η label hβlo hβhi hκbeta
    D.t D.t_pos mesh hmesh0 hmesh bΦ hbΦ

end
end OAI.SevenEighths.MainAssembly
#print axioms OAI.SevenEighths.MainAssembly.actual_label_initial_moments
