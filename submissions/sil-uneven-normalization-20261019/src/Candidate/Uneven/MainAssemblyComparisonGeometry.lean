/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Cycle63.Physical.FirstBranches.RawComparison

set_option autoImplicit false
namespace OAI.SevenEighths.MainAssemblyComparison
noncomputable section
open Sil.Uneven.MainSource
open HeckeFamily CenteredMomentEnergyReferenceState
theorem actual_comparison_powers (Z M n₁ n₂ : ℝ) (hZ : 1<Z) (hM : 0≤M)
    (hn₁ : (81/200)*M≤n₁) (hn₂ : (81/200)*M≤n₂)
    (hn₁' : n₁≤(45/100)*M) (hn₂' : n₂≤(45/100)*M) :
    CenteredMomentEnergyReferenceState.comparisonSecond Z M (Z^n₁) (Z^n₂) =
      Z^(n₁+n₂-M/4) ∧ M/2≤n₁+n₂-M/4 ∧ n₁+n₂-M/4≤(65/100)*M := by
  refine ⟨?_,by linarith,by linarith⟩
  unfold CenteredMomentEnergyReferenceState.comparisonSecond
    CenteredMomentEnergyReferenceState.comparisonFirst
  rw [←Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_sub (zero_lt_one.trans hZ)]

end
end OAI.SevenEighths.MainAssemblyComparison
#print axioms OAI.SevenEighths.MainAssemblyComparison.actual_comparison_powers
