/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual fresh-D source/class count. Predecessor attribution retained. Apache-2.0. -/
import Candidate.Uneven.EndpointPhysicalSourceCount
import Candidate.Cycle63.Assembly.Count.SourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary

namespace OAI.SevenEighths.UnevenEndpoint.Physical
variable [config : Configuration]
noncomputable section
set_option autoImplicit false
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection ProbeHighRowFamily

def canonicalFamily (D : BaselineData) (F : SourceData) (Z : ℝ) (z : ℂ) : FreeRow→Fin D.N→ℂ :=
  fun u j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val
    (fun y=>(F.w y:ℂ)) 2 (Z^(D.length j)) z

theorem physical_eq_canonical (D : BaselineData) (F : SourceData) (Z d : ℝ)
    (hZ : 0< Z) (hd : d≠0) (z : ℂ) :
    physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=> D.length j/d) (fun _=> z) (Z^d) = canonicalFamily D F Z z := by
  funext u j
  exact source_physical_amplitude F.modulus ⊤ D.length (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
end
end OAI.SevenEighths.UnevenEndpoint.Physical

#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.physical_eq_canonical
