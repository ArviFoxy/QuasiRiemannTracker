/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryAssemblyInitialSupplier
import Candidate.Uneven.MixedAuxiliaryHighMainUniform

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.AuxiliaryAssembly
open CanonicalQuadraticSieve
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic ConcretePrimeRowBridge
open Cycle63InitialMass Cycle63MarkedPlain AuxiliaryReconstruction AuxiliaryPhysical
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The auxiliary source before specialization to the detector dictionary.
It applies to every fixed natural seed and its actual relative-slot anchor. -/
theorem fixed_natural_initial_affine_capped_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (ε mesh bΦ : ℝ) (hε : 0<ε) (hεcap : ε ≤ 1/10000000000000000000000000000)
    (hmesh0 : 0< mesh) (hmesh : mesh ≤ chosenMesh ε) (hbΦ : 2 ≤ bΦ) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε U (excluded F₀.character R₀) η₀ Q degree Sd C := by
  let η := excluded F₀.character R₀
  obtain ⟨hm0,hmcomp,hmcommon,hmmu,hmamp,hmmarked⟩:=chosen_mesh_admission ε hε
  have hmeshlt : mesh<Sil.Uneven.AuxiliarySource.amplifierMinimum/2:=hmesh.trans_lt hmamp
  have hmeshμ : mesh ≤ geometryLossUnit 1 (ε/4)/8:=hmesh.trans hmmu
  have hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8):=
    hmesh.trans hmcommon
  have hmarkedmesh : mesh ≤ SaturatedPlain.fineRawMesh*SaturatedPlain.fineRawCore:=hmesh.trans hmmarked
  have hε4 : 0<ε/4 := by positivity
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=AuxiliaryHigh.actual_affine_main_uniform_paid_mixed_anchor (α:=α)
    M H hH 0 logAnnulus_compact logAnnulus_smooth Sbad hbad W hW hWs hβlo hβhi
    ηcoarse η₀ u₀ F₀ R₀ hu₀ (ε/4) mesh bΦ hε4 (by linarith) hmeshlt hmesh0.le
    hmeshμ hmeshcap hmarkedmesh hbΦ
  have hp:=hpaid Q hQM hQ0 hQt hQ72
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0 ≤ (Ψ x).re) →
      ∀T : Finset α,∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          AuxiliaryErrorReconstruction.GeometryAffineErrorPaidSpec M H hH Sbad W hW.continuous hWs
            Ψ η η₀ mesh (ε/4) T Se De Ce Z := by
    intro Ψ _ _
    apply AuxiliaryErrorReconstruction.actual_affine_error_uniform_paid_of_normalized (α:=α)
      M H hH 0 logAnnulus_compact logAnnulus_smooth Sbad hbad W hW.continuous hWs Ψ η η₀
      (ε/4) mesh hε4 hmeshlt (internalQ Q η₀) hQ0 hQt hQ72
    exact AuxiliaryErrorReconstruction.actual_affine_error_normalized_family (α:=α) M H hH
      Sbad hbad W hW hWs hβlo AuxiliaryLow.incumbent_kappa_bound Ψ η η₀ Q hQM hQ0 hQt hQ72
      (ε/4) mesh hε4 hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error M H hH Sbad hbad W hW.continuous hWs
    η η₀ Q bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  exact literal_geometry_initial_affine (α:=α) M H hH W hW hWs η η₀ Q bΦ mesh ε τ
    (geometryLossUnit 1 (ε/4)/64) (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hmcomp) hβlo (by linarith) hQM hQ0 hQt hQ72
    logAnnulus_compact logAnnulus_smooth hbudget

theorem fixed_natural_initial_affine_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (ε mesh bΦ : ℝ) (hε : 0<ε) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ sourceMesh ε) (hbΦ : 2 ≤ bΦ) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,
      AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) 1 1 ε U (excluded F₀.character R₀) η₀ Q degree Sd C := by
  have hs:=capped_error_bounds hε
  obtain ⟨degree,Sd,C,hC,hev⟩:=fixed_natural_initial_affine_capped_mixed_anchor (α:=α) M H hH Sbad hbad W hW hWs
    hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72 (cappedError ε) mesh bΦ
    hs.1 hs.2.2 hmesh0 hmesh hbΦ
  refine ⟨degree,Sd,C,hC,?_⟩
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hu hU
  exact initial_affine_error_mono (α:=α) M H hH W 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (cappedError ε) ε U (excluded F₀.character R₀) η₀ Q degree Sd C hC.le hU hs.2.1 hu

end
end OAI.SevenEighths.AuxiliaryAssembly
#print axioms OAI.SevenEighths.AuxiliaryAssembly.fixed_natural_initial_affine_mixed_anchor
