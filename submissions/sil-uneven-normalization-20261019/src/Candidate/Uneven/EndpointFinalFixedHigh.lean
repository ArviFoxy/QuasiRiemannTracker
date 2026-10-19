/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Uneven.EndpointFinalSourceProbe
import Candidate.Uneven.EndpointFinalHeight
import Candidate.Uneven.EndpointChosen
import Candidate.Uneven.EndpointTransportHighApproximation

                                         
                                    
                                      
                                                   

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics OAI.SevenEighths
open OAI.SevenEighths.UnevenEndpoint.Physical.Assembly
open HeckeFamily ProbePhysical OAI.SevenEighths.UnevenEndpoint.Physical PrincipalSignalComparison UnevenEndpointPhysicalHighTransport

/-- The finite numerator remains the honest analytic integration prerequisite. -/
def FixedFiniteNumeratorInput (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) : Prop :=
  ∀n : ℕ,0< n → ∀η : Character,
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=> F.w) F.W F.W n η

/-- The finite numerator bound for one character. -/
def FixedFiniteNumeratorInputAt (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀n : ℕ,0< n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=> F.w) F.W F.W n η

theorem sourceProbe_high_of_finite_numerator (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (hfinite : FixedFiniteNumeratorInput D F P τ) :
    ∀η : Character,
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      rcases config with ⟨stage⟩; cases stage <;> norm_num [Assembly.signal,Assembly.signalShift,theta,x,ell,h,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]
    linarith
  have hcap : h+rowPadding≤(7/8:ℝ)-1/100 := by
    rcases config with ⟨stage⟩; cases stage <;> norm_num [h,rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]) (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,UnevenEndpointPhysical.Transport.rowExtension,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]) P.floor_budget hfinite
  simpa only [sourceProbe,UnevenEndpointPhysical.Assembly.signalShift,Assembly.signalShift,UnevenEndpointPhysical.Arithmetic.x,UnevenEndpointPhysical.Arithmetic.ell] using hh
theorem sourceProbe_high_of_finite_numerator_at (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (η : Character) (hfinite : FixedFiniteNumeratorInputAt D F P τ η) :
      (fun Z=> sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      rcases config with ⟨stage⟩; cases stage <;> norm_num [Assembly.signal,Assembly.signalShift,theta,x,ell,h,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]
    linarith
  have hcap : h+rowPadding≤(7/8:ℝ)-1/100 := by
    rcases config with ⟨stage⟩; cases stage <;> norm_num [h,rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator_at F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]) (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by rcases config with ⟨stage⟩; cases stage <;> norm_num [rowPadding,UnevenEndpointPhysical.Transport.rowExtension,OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.upperPadding]) P.floor_budget η hfinite
  simpa only [sourceProbe,UnevenEndpointPhysical.Assembly.signalShift,Assembly.signalShift,UnevenEndpointPhysical.Arithmetic.x,UnevenEndpointPhysical.Arithmetic.ell] using hh
end
end OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly


#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly.sourceProbe_high_of_finite_numerator
#print axioms OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly.sourceProbe_high_of_finite_numerator_at
