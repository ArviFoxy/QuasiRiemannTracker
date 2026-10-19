/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointHelpers
import Candidate.Uneven.EndpointNormalizer
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Source
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open OAI.SevenEighths.UnevenEndpoint.Physical
open OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      UnevenEndpointPhysicalHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=> F.w) F.W F.W Z≠0 ∧
      ‖(UnevenEndpointPhysicalHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=> F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact UnevenEndpointPhysicalLowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _ y=>(F.bounded y).1) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)


end OAI.SevenEighths.UnevenEndpoint.Physical.Source
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.Source.source_normalizer_bound
