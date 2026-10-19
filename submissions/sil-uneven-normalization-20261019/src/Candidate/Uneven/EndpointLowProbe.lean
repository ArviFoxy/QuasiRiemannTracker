/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/
import Candidate.Uneven.EndpointTransportProbeDefinition
import Candidate.Uneven.EndpointLowDetectorNormalized
import Candidate.Uneven.EndpointTransportLowNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical

set_option autoImplicit false

/-! The canonical compensated physical probe at the actual Cycle63 lengths.
Adapted from weighted upstream 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace OAI
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.UnevenEndpointPhysicalLow
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=UnevenEndpointPhysical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^((UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta)+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := UnevenEndpointPhysicalProbeLow.original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

end SevenEighths.UnevenEndpointPhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.UnevenEndpointPhysicalLow.normalizedProbe_low
