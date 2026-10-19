/- Independent coarse seed and relative anchor; no extra analytic premise. -/
import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Target830.High.BalancedMass
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Target830.Parameters
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.AuxiliaryHighMainCompletePayment
import Candidate.Uneven.MixedAuxiliaryHighUniformSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.AuxiliaryHigh
private theorem mixed_high_spec_eq :
    @OAI.SevenEighths.AuxiliaryHigh.GeometryAffineMainHighSpec_mixed_anchor =
      @OAI.SevenEighths.AuxiliaryHigh.GeometryAffineMainHighSpec := by rfl

private theorem mixed_high_target_eq :
    geometryAffineHighTarget_mixed_anchor = geometryAffineHighTarget := by rfl

open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The common cutoff and the actual paid main terms are constructed from
the fixed natural source. The separate selected-fiber proof is the only
remaining high analytic premise. -/
theorem actual_affine_main_uniform_paid_of_fibers_mixed_anchor
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh<Sil.Uneven.AuxiliarySource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore)
    (hbΦ : 2≤bΦ)
    (fiberReceipt : ∀T : Finset α,
      OAI.SevenEighths.AuxiliaryHigh.GeometryAffineHighSelectedFiberReceipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ (9/4) (9/4)
        (geometryLossUnit 1 εaffine/8) 3 1 (geometryLossUnit 1 εaffine/64)) :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineMainPaidSpec  M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/10000000000000000000000000000 := by
    have hh:=min_le_left (εaffine/128)
      (min ((7/30000000:ℝ)*1/128) (min ((1:ℝ)/128) (1/128)))
    change μ≤εaffine/128 at hh
    linarith
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=
    actual_affine_high_uniform_literal_schedule_of_fibers_mixed_anchor  (α:=α) M H hH ηcoarse η₀ u₀ F₀ R₀ hu₀
      W hWs hW hβlo (by linarith) μ bΦ hμ hμcap hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,?_⟩
  intro Q hQM hQ hQt hQ72
  have hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) := by
    simpa only [OAI.SevenEighths.AuxiliaryHigh.geometryAffineHighDictionaryRate_mixed_anchor,hgμ] using hgδ
  have hmeshμ' : mesh≤g.μ/8 := by simpa only [hgμ] using hmeshμ
  have hmeshcap' : mesh≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := by
    simpa only [hgμ] using hmeshcap
  have hpaid:=actual_affine_main_uniform_paid_of_high (α:=α) M H hH A hc hs Sbad hbad
    W hW hWs hβlo hβhi (excluded F₀.character R₀) εaffine mesh hε hmesh hmesh0 g hgμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity)
    hδ hmeshμ' hmeshcap' hmarkedmesh ηcoarse u₀ F₀ R₀ hu₀ η₀ Q hQM hQ hQt hQ72 (by
      intro T
      obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,SH,hSH,dh,KH,hKH,hcost⟩:=hhigh T
      refine ⟨P,he.symm,hPτ.trans hgτ.symm,SH,dh,KH,hKH.le,?_⟩
      filter_upwards [hcost Q hQM hQ72] with Z hz
      simpa only [mixed_high_spec_eq,mixed_high_target_eq,hgμ,hgδ] using hz.2)
  simpa only [hgμ] using hpaid

/-- The fixed-source main payment has no remaining analytic branch premise. -/
theorem actual_affine_main_uniform_paid_mixed_anchor
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (ηcoarse η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow ηcoarse u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)(hεcap : εaffine≤1/10000000000000000000000000000)
    (hmesh : mesh<Sil.Uneven.AuxiliarySource.amplifierMinimum/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore)
    (hbΦ : 2≤bΦ)
    :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤Cm ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
        GeometryAffineMainPaidSpec  M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  exact actual_affine_main_uniform_paid_of_fibers_mixed_anchor (α:=α) M H hH A hc hs Sbad hbad W hW hWs
    hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ εaffine mesh bΦ hε hεcap hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ
    (fun T=>OAI.SevenEighths.AuxiliaryHigh.geometry_affine_high_selected_fiber_receipt_mixed_anchor (α:=T) ηcoarse η₀ u₀ F₀ R₀ hu₀
      (geometryLossUnit 1 εaffine) (geometry_loss_unit_pos 1 εaffine (by norm_num) hε))

end
end OAI.SevenEighths.AuxiliaryHigh
#print axioms OAI.SevenEighths.AuxiliaryHigh.actual_affine_main_uniform_paid_of_fibers_mixed_anchor

#print axioms OAI.SevenEighths.AuxiliaryHigh.actual_affine_main_uniform_paid_mixed_anchor
