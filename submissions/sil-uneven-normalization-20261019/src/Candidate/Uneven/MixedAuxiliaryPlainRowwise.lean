/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedAuxiliaryPlainCommonProfiles
import Candidate.Cycle63.Marked.NaturalSlotHeight

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

theorem actual_rowwise_marked_plain_energy_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ εm mesh : ℝ) (hbΦ : 2 ≤ bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom (excluded F₀.character R₀))
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep (excluded F₀.character R₀) (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U) →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)(height : ℝ)(choice : Row→ℝ),
      (∀s,0 ≤ w s) → (∀s,w s ≤ mesh) →
      (∀s,(33/50:ℝ) ≤ σ s) → (∀s,σ s ≤ (33/50:ℝ)) →
      0 ≤ height → (∀s,|v s| ≤ height) → (∀u∈rows,|choice u| ≤ height) →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s,w s) →
      (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td| ≤ height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (choice u+v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  let N := Fintype.card α
  obtain ⟨J,C,hC,hfield⟩ := actual_common_profiles_marked_plain_energy_mixed_anchor (α:=α) M H hH
    Sbad hbad W hWs hW bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi
    ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72 N
  let K := Cycle63MarkedHeight.commonProfileCost N
  have hK : 0<K := zero_lt_one.trans_le (Cycle63MarkedHeight.commonProfileCost_ge_one N)
  refine ⟨J+1,4*K*C*2^J,by positivity,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height choice
    hw hwm hσlo hσhi hheight hv hchoice hwl hwu hcap j k hjk σd hσd td htd
  have hUp : 0<U := zero_lt_one.trans hU.1
  let factor := fun u=>polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
    polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td
  let E := C*(1+2*height)^J*U^(1+εm)
  have hE : 0≤E := by dsimp [E];positivity
  have hcard : (Finset.univ : Finset slots).card≤N := by
    simpa only [Finset.card_univ,Fintype.card_coe] using Finset.card_le_univ slots
  have hmoment (node : Fin (N+1)) (t : ℝ)(ht : t∈Icc (-height) height) :
      (∑u∈rows,‖factor u*(∏s : slots,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
        (CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val)
            (U^(w s)) (σ s) (t+v s) I) (U^(w s)))‖^2)≤E := by
    apply (hU.2 node) rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ
      (fun s=>t+v s) (2*height) hw hwm hσlo hσhi (by positivity)
    · intro s
      exact (abs_add_le t (v s)).trans (by linarith [abs_le.mpr ht,hv s])
    · exact hwl
    · exact hwu
    · exact hcap
    · exact hjk
    · exact hσd
    · linarith
  have he := Cycle63MarkedHeight.naturalSlot_rowwise_energy rows (Finset.univ : Finset slots)
    N hcard χ (fun s=>CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
    (fun s _ I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I) W
    (fun s=>U^(w s)) σ v
    (fun s _=>Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) factor
    (-height) height E (by linarith) hE choice
    (fun u hu=>abs_le.mp (hchoice u hu)) hmoment
  apply he.trans
  have hheight' : 1+2*(height- -height)≤4*(1+height) := by linarith
  have hpow : (1+2*height)^J≤2^J*(1+height)^J := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  change (1+2*(height- -height))*K*(C*(1+2*height)^J*U^(1+εm))≤_
  calc
    _≤(4*(1+height))*K*(C*(2^J*(1+height)^J)*U^(1+εm)) := by
      gcongr
    _=_ := by rw [pow_succ];ring

end
end OAI.SevenEighths.AuxiliaryPlainTransport
#print axioms OAI.SevenEighths.AuxiliaryPlainTransport.actual_rowwise_marked_plain_energy_mixed_anchor
