/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointTransportSourceCorrection
import Candidate.Uneven.EndpointBaselineMoments
import Candidate.Uneven.EndpointLowProbe
import Candidate.Uneven.EndpointTransportPrincipalSignal
import Candidate.Cycle25.Assembly.Continuation

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical OAI.SevenEighths.UnevenEndpoint.Physical PrincipalSignalComparison
open OAI.SevenEighths.UnevenEndpoint.Physical.Assembly

def sourceProbe (D : BaselineData) (F : BaselineSourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  UnevenEndpointPhysicalLow.normalizedProbe F.modulus ⊤ F.S F.maximal D.length 1 2
    (fun _=> F.w) F.W F.W η

theorem sourceProbe_low (D : BaselineData) (F : BaselineSourceData D)
    (loss : ℝ) (hloss : 0< loss) (η : Character) :
    sourceProbe D F η=O[atTop](fun Z : ℝ=> Z^(Assembly.signal theta+loss)) := by
  have hh := UnevenEndpointPhysicalLow.normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal
    1 2 1 loss (by norm_num) (by norm_num) hloss D.length D.slots_pos
    D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  exact hh

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|theta< s.re} ∧
    (∀s : ℂ,theta< s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact UnevenEndpointPhysical.Transport.actual_source_analytic S hS η

theorem fixed_source_contract (D : BaselineData) (F : BaselineSourceData D)
    (loss sigma : ℝ) (hloss : 0< loss)
    (herror : ∀η : Character,
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-sigma))) :
    Cycle25.PrimitiveProbeContract theta Assembly.signalShift loss sigma := by
  intro η _
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,
    sourceProbe D F η,hmask,hH,hHbound,?_,herror η⟩
  simpa only [Assembly.signal] using sourceProbe_low D F loss hloss η
end
end OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly

#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly.sourceProbe_low
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly.actual_source_analytic
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly.fixed_source_contract
