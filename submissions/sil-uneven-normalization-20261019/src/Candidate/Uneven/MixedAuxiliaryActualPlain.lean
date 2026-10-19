/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MixedAuxiliaryFixedInitialSupplier
import Candidate.Uneven.AuxiliaryPlainTransport

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

/-- The actual auxiliary two-plain moment for a fixed natural seed.
The profile constant, height degree and threshold precede all selected slots
and finite rows. The small mesh is fixed by the requested error alone. -/
theorem actual_marked_plain_energy_mixed_anchor
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
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  obtain ⟨degree,seminorms,A,hA,hinput⟩:=AuxiliaryAssembly.fixed_natural_initial_affine_mixed_anchor (α:=α)
    M H hH Sbad hbad W hW hWs hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72
    εm mesh bΦ hεm hmesh0 hmesh hbΦ
  obtain ⟨J,Cp,hCp,hprofiles⟩:=paired_control seminorms
  let C : ℝ := A*(1+diagonalControl radialMajorant)*Cp
  have hdiag : 0 ≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC : 0<C:=mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A*diagonalControl radialMajorant*Cp ≤ C := by
    dsimp [C]
    gcongr
    linarith
  refine ⟨J+degree,C,hC,?_⟩
  filter_upwards [hinput,eventually_gt_atTop (1:ℝ)] with U hinput hU
  refine ⟨hU,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have he:=finite_marked_plain_field M H hH W 2 bΦ mesh (33/50) (33/50) εm U m
    (excluded F₀.character R₀) η₀ Q degree J seminorms A Cp hinput (hprofiles false)
    hA.le hCp.le hU hrad hm hmmax slots θ w σ v height hw hwm hσlo hσhi hheight hv
    hwl hwu hcap rows row hinj χ hrow hkeep hnorm j k hjk σd td hσd htd
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC' (by positivity))
    (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end
end OAI.SevenEighths.AuxiliaryPlainTransport
#print axioms OAI.SevenEighths.AuxiliaryPlainTransport.actual_marked_plain_energy_mixed_anchor
