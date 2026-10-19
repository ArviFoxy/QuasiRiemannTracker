/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryInitialContract
import Candidate.Cycle63.Marked.NaturalMarkedPlainField

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot CenteredMomentHeckeSlots CenteredMomentHeckeTwist
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The auxiliary initial energy controls the literal finite detector sum.
The initial-energy theorem remains an explicit input to this transport. -/
theorem finite_marked_polynomials_of_initial {Row : Type*}
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi ε U : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W bslot a b bΦ
      mesh lo hi 1 1 ε U η η₀ Q degree seminorms C)
    (hU : 1<U)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0 ≤ w s) (hwm : ∀s,w s ≤ mesh)
    (hσlo : ∀s,lo ≤ σ s) (hσhi : ∀s,σ s ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀s,|v s| ≤ height)
    (p : Profiles a b) (X₁ X₂ σd td : ℝ) (V₁ V₂ : ℝ→ℂ)
    (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hl₁ : AuxiliaryInitial.plainLower ≤ length U X₁)
    (hu₁ : length U X₁ ≤ AuxiliaryInitial.plainUpper)
    (hl₂ : AuxiliaryInitial.plainLower ≤ length U X₂)
    (hu₂ : length U X₂ ≤ AuxiliaryInitial.plainUpper)
    (hwl : Sil.Uneven.AuxiliarySource.widthLo ≤ ∑s,w s)
    (hwu : (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi)
    (hcap : length U X₁+length U X₂+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s)
       ≤ Sil.Uneven.AuxiliarySource.B)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
        1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hnorm : ∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2) ≤ 
      C*diagonalControl radialMajorant*(p.control seminorms)^2*
        (1+height)^degree*U^(1+ε) := by
  let mask := CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1
  have hUp : 0<U := zero_lt_one.trans hU
  have he := finite_positive_energy (Slot:=slots) (rows.image row) η mask 1 0
    (p.profile 0) (p.profile 1) b b X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2)
    hX₁ hX₂ (fun s=>primePool M H bslot (U^(w s)))
    (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
    (fun s=>U^(w s)) (initialKeep η (internalQ Q η₀)) radialMajorant U hUp
    (fun u hu=>by obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu; exact hkeep v hv)
    radialMajorant_nonneg
    (fun u hu=>by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
      exact radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hUp.le,
        (div_le_one hUp).mpr (hnorm v hv)⟩)
  have hi := hinput slots θ w σ v 0 height hw hwm hσlo hσhi hheight hv
    1 le_rfl le_rfl radialMajorant hrad radialMajorant_nonneg p X₁ X₂ hX₁ hX₂
    (by simpa only [mul_one] using hl₁) (by simpa only [mul_one] using hu₁)
    (by simpa only [mul_one] using hl₂) (by simpa only [mul_one] using hu₂)
    (by simpa only [mul_one] using hwl) (by simpa only [mul_one] using hwu)
    (by simpa only [mul_one] using hcap)
  simp only [Real.rpow_one,abs_zero,add_zero] at hi
  have he := he.trans hi
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product η (χ u) mask 1 (row u)
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=>Real.rpow_pos_of_pos hUp _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row η (χ u) mask 1 (row u) (hrow u hu) _ _ _

/-- Polynomial profile control gives the precise two-plain moment required
by the seventh counting face, with the same selected-width interval. -/
theorem finite_marked_plain_field {Row : Type*}
    (W : ℝ→ℂ) (bslot bΦ mesh lo hi ε U m : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree J : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (A Cp : ℝ)
    (hinput : AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W bslot (1/4) (9/4)
      bΦ mesh lo hi 1 1 ε U η η₀ Q degree seminorms A)
    (hcontrol : ∀j k : ℕ,j+k ≤ 2 → ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      (detectorProfiles false j k σ t).control seminorms ^2 ≤ Cp*(1+‖t‖)^J)
    (hA : 0 ≤ A) (hCp : 0 ≤ Cp) (hU : 1<U)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hm : AuxiliaryInitial.plainLower ≤ m) (hmmax : m ≤ AuxiliaryInitial.plainUpper)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0 ≤ w s) (hwm : ∀s,w s ≤ mesh)
    (hσlo : ∀s,lo ≤ σ s) (hσhi : ∀s,σ s ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀s,|v s| ≤ height)
    (hwl : Sil.Uneven.AuxiliarySource.widthLo ≤ ∑s,w s)
    (hwu : (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi)
    (hcap : 2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
        1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hnorm : ∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U)
    (j k : ℕ) (hjk : j+k ≤ 2) (σd td : ℝ)
    (hσd : σd∈Icc (0:ℝ) 1) (htd : |td| ≤ height) :
    (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2) ≤ 
      (A*diagonalControl radialMajorant*Cp)*(1+height)^(J+degree)*U^(1+ε) := by
  have hUp : 0<U := zero_lt_one.trans hU
  have hm0 : 0 ≤ m := (by norm_num [AuxiliaryInitial.plainLower] : (0:ℝ) ≤ AuxiliaryInitial.plainLower).trans hm
  have hscale : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hlen : length U (U^m)=m := by
    rw [length,max_eq_right (Real.one_le_rpow hU.le hm0)]
    exact Real.logb_rpow hUp hU.ne'
  have hpc (n : ℕ) : (detectorSchwartz false n σd td : ℝ→ℂ)=
      twistProfile ((logProfile^[n]) positiveAnnular) σd td := by
    funext y
    simpa [HeckeDetectorCoefficientTransfer.orientedProfile,
      HeckeDetectorCoefficientTransfer.orientedFrequency] using detectorSchwartz_apply false n σd td y
  have hp₁ : ((detectorProfiles false j k σd td).profile 0 : ℝ→ℂ)=
      twistProfile ((logProfile^[j]) positiveAnnular) σd td := by
    simpa only [detectorProfiles,Fin.zero_eta,ite_true] using hpc j
  have hp₂ : ((detectorProfiles false j k σd td).profile 1 : ℝ→ℂ)=
      twistProfile ((logProfile^[k]) positiveAnnular) σd td := by
    simpa only [detectorProfiles,show ¬((1:Fin 2)=0) by decide,ite_false] using hpc k
  have hs := finite_marked_polynomials_of_initial M H hH W bslot (1/4) (9/4)
    bΦ mesh lo hi ε U η η₀ Q degree seminorms A hinput hU slots θ w σ v height
    hw hwm hσlo hσhi hheight hv (detectorProfiles false j k σd td) (U^m) (U^m) σd td
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular) hp₁ hp₂ hscale hscale
    (by simpa only [hlen] using hm) (by simpa only [hlen] using hmmax)
    (by simpa only [hlen] using hm) (by simpa only [hlen] using hmmax)
    hwl hwu (by rw [hlen]; linarith only [hcap]) rows row hinj χ hrow hkeep hnorm hrad
  have hp : (detectorProfiles false j k σd td).control seminorms ^2 ≤ Cp*(1+height)^J :=
    (hcontrol j k hjk σd hσd td).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by simpa only [Real.norm_eq_abs] using add_le_add le_rfl htd) J) hCp)
  apply hs.trans
  calc
    _ ≤ A*diagonalControl radialMajorant*(Cp*(1+height)^J)*(1+height)^degree*U^(1+ε) := by
      gcongr
      exact mul_nonneg hA (diagonalControl_nonneg _)
    _=_ := by rw [pow_add];ring

end
end OAI.SevenEighths.AuxiliaryPlainTransport
#print axioms OAI.SevenEighths.AuxiliaryPlainTransport.finite_marked_polynomials_of_initial
#print axioms OAI.SevenEighths.AuxiliaryPlainTransport.finite_marked_plain_field
