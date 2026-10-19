/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedAuxiliaryActualPlain
import Candidate.Cycle63.Marked.ActualMarkedPlainProfiles

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_common_profiles_marked_plain_energy_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ εm mesh : ℝ) (hbΦ : 2 ≤ bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (N : ℕ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧ ∀node : Fin (N+1),
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom (excluded F₀.character R₀))
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep (excluded F₀.character R₀) (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U) →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)(height : ℝ),
      (∀s,0 ≤ w s) → (∀s,w s ≤ mesh) →
      (∀s,(33/50:ℝ) ≤ σ s) → (∀s,σ s ≤ (33/50:ℝ)) →
      0 ≤ height → (∀s,|v s| ≤ height) →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s,w s) →
      (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td| ≤ height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val) (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  have hnode (node : Fin (N+1)) := actual_marked_plain_energy_mixed_anchor (α:=α) M H hH Sbad hbad
    (Cycle63MarkedHeight.commonProfile W node.val)
    ((Cycle63MarkedHeight.commonProfile_support W node.val).trans hWs)
    (Cycle63MarkedHeight.commonProfile_smooth W 1 2 (by norm_num) hWs hW node.val)
    bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72
  choose J C hC hb using hnode
  have hne : (Finset.univ : Finset (Fin (N+1))).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hC₀ : 0<∑node,C node := Finset.sum_pos (fun node _=>hC node) hne
  refine ⟨∑node,J node,∑node,C node,hC₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb] with U hU
  refine ⟨(hU ⟨0,by omega⟩).1,?_⟩
  intro node Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have he := (hU node).2 rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have hc : C node ≤ ∑node,C node := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
  have hj : J node ≤ ∑node,J node := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ node)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans (hU node).1).le _)
  exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hj) (by positivity) hC₀.le

end
end OAI.SevenEighths.AuxiliaryPlainTransport
#print axioms OAI.SevenEighths.AuxiliaryPlainTransport.actual_common_profiles_marked_plain_energy_mixed_anchor
