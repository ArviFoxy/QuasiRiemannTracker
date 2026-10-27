/- Copyright (c) 2026 Sil. Apache-2.0.
First-side packing of the cube-free common-divisor step (CF §3).

OAI's fixed first-step pair (`FixedPair`, Moments/FirstPhysicalSourceFixedFamily.lean) has
column coefficients `rowWeight η fixedBadMask 1 1 t I · leftCoefficient e r ρ (a) · ξ₁(a)`
with `a = primaryGenerator I`, `leftCoefficient e r ρ a = idealRowHom (e*r) (a) · ρ a` and
`ρ = ∏_P (a/P)_6^{n_P}` (denominator form in the column).  Sextic reciprocity with its
finite ray phase (`idealRowHom_primary_reciprocity`) turns every local factor
`(a/P)_6^{n_P}` into `idealRowHom (π_P^{n_P}) (a)` times the phase `(π_P,a)^{n_P}`,
where `π_P` is the primary generator of `P`.  Together with the factor `π_P` already present
in `r` the local exponent becomes `(1+n_P) mod 6` (`leftPackedExponent`); exponent-zero
primes are kept as punctures (hypothesis `IsCoprime I (firstZeroPrimes C D)`).  The phases
`∏ (π_P,a)^{n_P} = (Π,a)` form one ray character `firstPhase` (values ±1 on supported `a`,
factoring through `O/4`).  Hence on residual columns

  `heightCoeff F.left t I = heightCoeff (rayAnchor η (ξ₁ * firstPhase)) t I · idealRowHom V_C I`

with the fixed anchor `rayAnchor η k` (coefficients `rowWeight η fixedBadMask 1 1 · k(a)`,
finitely many: `k : RayCharacter`, a type of size ≤ 16) and `V_C = firstPacked C D hC E`.
`V_C` is a generator of `span e · ∏_P P^{(1+n_P) mod 6}`; it equals a unit times the primary
product, the unit being the one relating `activeConductor` to its primary prime product.
Under the cube-free hypothesis (common multiplicities in {1,2}) one has
`N(V_C)·N(D-common part) = N(e)·N(r)·N(C-common part)`, i.e. `q_C = q + c - d` (CF (3.1)),
and `span V_C ∣ (C-common part)²`.  The right side is symmetric with exponent
`(1+5n_P) mod 6`. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstIdealFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRay
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZero
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.RowClosure

set_option autoImplicit false

namespace QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators

open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ActualEisensteinCubic RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentActive CenteredMomentCompleteCommon UniqueFactorizationMonoid

local notation "O" => ActualEisensteinCubic.O

/-! ### Elementary row-symbol facts -/

theorem idealRowHom_finset_prod (I : Ideal O) (hI : Supported I) {α : Type*} (s : Finset α)
    (f : α → O) : idealRowHom (∏ i ∈ s, f i) I = ∏ i ∈ s, idealRowHom (f i) I := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact idealRowHom_one_supported I hI
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, idealRowHom_argument_mul, ih]

theorem phase_pow (c a : O) (ha : Supported (Ideal.span {a})) (k : ℕ) :
    sexticReciprocityPhase (c^k) a = sexticReciprocityPhase c a ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using sexticReciprocityPhase_one_left a ha
  | succ k ih => rw [pow_succ, sexticReciprocityPhase_mul_left, ih, pow_succ]

theorem phase_prod (a : O) (ha : Supported (Ideal.span {a})) {α : Type*} (s : Finset α)
    (f : α → O) :
    sexticReciprocityPhase (∏ i ∈ s, f i) a = ∏ i ∈ s, sexticReciprocityPhase (f i) a := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact sexticReciprocityPhase_one_left a ha
  · intro b s hb ih
    rw [Finset.prod_insert hb, Finset.prod_insert hb, sexticReciprocityPhase_mul_left, ih]

theorem supported_pow (I : Ideal O) (hI : Supported I) (n : ℕ) : Supported (I^n) := by
  induction n with
  | zero => simpa only [pow_zero] using CenteredMomentAddedZero.supported_one_ideal
  | succ n ih => rw [pow_succ]; exact (supported_mul_iff _ _).mpr ⟨ih, hI⟩

theorem supported_finset_prod {α : Type*} (s : Finset α) (f : α → Ideal O)
    (h : ∀ i ∈ s, Supported (f i)) : Supported (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using CenteredMomentAddedZero.supported_one_ideal
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (supported_mul_iff _ _).mpr
      ⟨h a (Finset.mem_insert_self a s), ih (fun i hi => h i (Finset.mem_insert_of_mem hi))⟩

theorem span_coprime_of_not_mem (P : Ideal O) [hP : P.IsMaximal] (a : O) (haP : a ∉ P) :
    IsCoprime (Ideal.span {a}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  obtain ⟨y, i, hi, h⟩ := hP.exists_inv haP
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (Ideal.mul_mem_left _ y (Ideal.mem_span_singleton_self a)))
    (Ideal.mem_sup_right hi)

theorem not_mem_of_coprime (I Z P : Ideal O) [hP : P.IsMaximal] (a : O)
    (haI : Ideal.span {a} = I) (hcop : IsCoprime I Z) (hd : P ∣ Z) : a ∉ P := by
  intro haP
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have hZP : Z ≤ P := Ideal.le_of_dvd hd
  have hIP : I ≤ P := by rw [← haI]; exact (Ideal.span_singleton_le_iff_mem P).mpr haP
  apply hP.ne_top
  apply top_unique
  rw [← hcop]
  exact sup_le hIP hZP

/-- The row symbol of the primary generator of `P` vanishes on columns divisible by `P`. -/
theorem row_zero_of_mem (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (hPs : Supported P)
    (a : O) (haP : a ∈ P) : idealRowHom (primaryGenerator P) (Ideal.span {a}) = 0 := by
  have hπ := (primaryGenerator_spec P (supported_primaryGenerator_ne_zero P hPs)).1
  have hmem : primaryGenerator P ∈ P := by
    have h := Ideal.mem_span_singleton_self (primaryGenerator P)
    rwa [hπ] at h
  have hd : primaryGenerator P ∣ a := by
    rw [← Ideal.mem_span_singleton, hπ]; exact haP
  obtain ⟨c, hc⟩ := hd
  rw [hc, ← Ideal.span_singleton_mul_span_singleton, map_mul, hπ, idealRowHom_prime _ P hg,
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem, MulChar.map_zero, zero_mul]

/-- Sextic reciprocity, one prime: the denominator-form local factor `(a/P)_6^n` is the
numerator-form twist `idealRowHom (π_P)^n` times the finite phase `(π_P,a)^n`. -/
theorem sextic_local_reciprocity (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (hPs : Supported P) (a : O) (ha : Supported (Ideal.span {a})) (hap : lambda^2 ∣ a - 1)
    (haP : a ∉ P) (n : ℕ) :
    (canonicalSextic P hg ^ n) (Ideal.Quotient.mk P a) =
      sexticReciprocityPhase (primaryGenerator P) a ^ n *
        idealRowHom (primaryGenerator P) (Ideal.span {a}) ^ n := by
  have hπ := primaryGenerator_spec P (supported_primaryGenerator_ne_zero P hPs)
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  have hunit : IsUnit (Ideal.Quotient.mk P a) :=
    isUnit_iff_ne_zero.mpr (fun h => haP (Ideal.Quotient.eq_zero_iff_mem.mp h))
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, MulChar.pow_apply_coe, hu, ← mul_pow]
  congr 1
  have h1 : canonicalSextic P hg (Ideal.Quotient.mk P a) = idealRowHom a P :=
    (idealRowHom_prime a P hg).symm
  rw [h1]
  have h2 := idealRowHom_primary_reciprocity (primaryGenerator P) a hπ.2 hap
    (by rw [hπ.1]; exact hPs) ha
  rw [hπ.1] at h2
  exact h2

theorem row_sixth_one (π a : O) (ha : Supported (Ideal.span {a}))
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {π})) :
    idealRowHom π (Ideal.span {a}) ^ 6 = 1 := by
  rw [← idealRowHom_argument_pow π 6 _ ha, idealRowHom_sixth_mask π _ ha, ite_eq_left hcop]

theorem pow_mod_six_of_sixth (h : ℂ) (h6 : h^6 = 1) (k : ℕ) : h^k = h^(k%6) := by
  conv_lhs => rw [← Nat.mod_add_div k 6, pow_add, pow_mul, h6, one_pow, mul_one]

/-- Reduced exponent of the packed left twist at an active prime of net exponent `n`. -/
def leftPackedExponent (n : ℕ) : ℕ := (1 + n) % 6

/-- Reduced exponent of the packed right twist at an active prime of net exponent `n`. -/
def rightPackedExponent (n : ℕ) : ℕ := (1 + 5*n) % 6

/-- Local left packing: `π_P`-symbol from `r` times `(a/P)_6^n`. -/
theorem left_local (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (hPs : Supported P)
    (a : O) (ha : Supported (Ideal.span {a})) (hap : lambda^2 ∣ a - 1) (n : ℕ)
    (hz : leftPackedExponent n = 0 → a ∉ P) :
    idealRowHom (primaryGenerator P) (Ideal.span {a}) *
        (canonicalSextic P hg ^ n) (Ideal.Quotient.mk P a) =
      sexticReciprocityPhase (primaryGenerator P) a ^ n *
        idealRowHom (primaryGenerator P ^ leftPackedExponent n) (Ideal.span {a}) := by
  rw [idealRowHom_argument_pow _ _ _ ha]
  by_cases haP : a ∈ P
  · have hk : leftPackedExponent n ≠ 0 := fun h => hz h haP
    rw [row_zero_of_mem P hg hPs a haP, zero_mul, zero_pow hk, mul_zero]
  · have hπ := (primaryGenerator_spec P (supported_primaryGenerator_ne_zero P hPs)).1
    rw [sextic_local_reciprocity P hg hPs a ha hap haP n]
    have h6 := row_sixth_one (primaryGenerator P) a ha
      (by rw [hπ]; exact span_coprime_of_not_mem P a haP)
    have hm := pow_mod_six_of_sixth _ h6 (1+n)
    unfold leftPackedExponent
    rw [← hm]
    ring

/-- Local right packing: `π_P`-symbol from `r` times `conj((a/P)_6^n)`. -/
theorem right_local (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (hPs : Supported P)
    (a : O) (ha : Supported (Ideal.span {a})) (hap : lambda^2 ∣ a - 1) (n : ℕ)
    (hz : rightPackedExponent n = 0 → a ∉ P) :
    idealRowHom (primaryGenerator P) (Ideal.span {a}) *
        (starRingEnd ℂ) ((canonicalSextic P hg ^ n) (Ideal.Quotient.mk P a)) =
      sexticReciprocityPhase (primaryGenerator P) a ^ n *
        idealRowHom (primaryGenerator P ^ rightPackedExponent n) (Ideal.span {a}) := by
  rw [idealRowHom_argument_pow _ _ _ ha]
  by_cases haP : a ∈ P
  · have hk : rightPackedExponent n ≠ 0 := fun h => hz h haP
    rw [row_zero_of_mem P hg hPs a haP, zero_mul, zero_pow hk, mul_zero]
  · have hπ := (primaryGenerator_spec P (supported_primaryGenerator_ne_zero P hPs)).1
    rw [sextic_local_reciprocity P hg hPs a ha hap haP n]
    set h := idealRowHom (primaryGenerator P) (Ideal.span {a}) with hh
    have h6 : h^6 = 1 := row_sixth_one (primaryGenerator P) a ha
      (by rw [hπ]; exact span_coprime_of_not_mem P a haP)
    have hnorm : ‖h‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h6 (by decide)
    have hh0 : h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
    have hconj : (starRingEnd ℂ) h = h^5 := by
      have hm := Complex.mul_conj h
      rw [Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one] at hm
      apply mul_left_cancel₀ hh0
      rw [hm, ← pow_succ', h6]
    have hφ : (starRingEnd ℂ) (sexticReciprocityPhase (primaryGenerator P) a) =
        sexticReciprocityPhase (primaryGenerator P) a := by
      unfold sexticReciprocityPhase
      exact map_intCast (starRingEnd ℂ) _
    have hm := pow_mod_six_of_sixth _ h6 (1+5*n)
    rw [map_mul, map_pow, map_pow, hφ, hconj]
    unfold rightPackedExponent
    rw [← hm]
    ring

/-! ### The finite phase character -/

/-- The quadratic reciprocity phase `(c, ·)` as a monoid homomorphism. -/
def phaseRow (c : O) (hc : Supported (Ideal.span {c})) : O →* ℂ where
  toFun a := sexticReciprocityPhase c a
  map_one' := sexticReciprocityPhase_one_right c hc
  map_mul' a b := sexticReciprocityPhase_mul_right c a b

theorem phaseRow_factors (c : O) (hc : Supported (Ideal.span {c})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(4:O)}) (phaseRow c hc) := by
  intro x y hxy
  change sexticReciprocityPhase c x = sexticReciprocityPhase c y
  unfold sexticReciprocityPhase
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y (Ideal.mem_span_singleton.mp hxy)]

/-- The phase `(c, ·)` is a ray character (modulo 4). -/
def phaseRay (c : O) (hc : Supported (Ideal.span {c})) : RayCharacter :=
  HeckeRowClosure.residueRow (Ideal.span {(4:O)}) (phaseRow c hc) (phaseRow_factors c hc)

theorem rayCharacter_phaseRay (c : O) (hc : Supported (Ideal.span {c})) (a : O)
    (ha : Supported (Ideal.span {a})) :
    rayCharacter (phaseRay c hc) a = sexticReciprocityPhase c a := by
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(4:O)}) a) := by
    have h := CenteredMomentFixedRay.supported_rayMask a ha
    unfold rayMask at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact zero_ne_one h
  unfold rayCharacter phaseRay
  rw [HeckeRowClosure.residueRow_mk, ite_eq_left hu]
  rfl

/-! ### The fixed anchors -/

theorem exists_rayAnchor (η : Character) (ξ : RayCharacter) :
    ∃ τ : Character, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I = rowWeight η fixedBadMask 1 1 t I * rayCharacter ξ (primaryGenerator I) := by
  obtain ⟨τ, -, -, hτ⟩ := CenteredMomentFirstFamily.exists_first_character η fixedBadMask 1 1
    fixedBadMask_ne_zero CenteredMomentAddedZero.supported_one_element
    CenteredMomentAddedZero.supported_one_element (dvd_mul_right _ _) (dvd_mul_left _ _) 1 ξ
  refine ⟨τ, fun I hI t => ?_⟩
  have : Subsingleton (O ⧸ Ideal.span {(1:O)}) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
  exact CenteredMomentFirstIdealFamily.ideal_height_of_primary η τ fixedBadMask
    (fun n => rayCharacter ξ n) (fun n hn hp => by
      rw [hτ n hn hp, show (1:O)*1 = 1 from mul_one 1, idealRowHom_one_supported _ hn,
        show Ideal.Quotient.mk (Ideal.span {(1:O)}) n = 1 from Subsingleton.elim _ _,
        MulChar.map_one]
      ring) I hI t

/-- The fixed anchor character with ray twist `ξ`: column coefficients
`rowWeight η fixedBadMask 1 1 t I · ξ(primaryGenerator I)`. -/
def rayAnchor (η : Character) (ξ : RayCharacter) : Character :=
  Classical.choose (exists_rayAnchor η ξ)

theorem rayAnchor_height (η : Character) (ξ : RayCharacter) (I : Ideal O) (hI : Supported I)
    (t : ℝ) :
    heightCoeff (rayAnchor η ξ) t I =
      rowWeight η fixedBadMask 1 1 t I * rayCharacter ξ (primaryGenerator I) :=
  Classical.choose_spec (exists_rayAnchor η ξ) I hI t

theorem rayAnchor_mul_height (η : Character) (ξ χ : RayCharacter) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    heightCoeff (rayAnchor η (ξ * χ)) t I =
      heightCoeff (rayAnchor η ξ) t I * rayCharacter χ (primaryGenerator I) := by
  rw [rayAnchor_height η _ I hI t, rayAnchor_height η _ I hI t]
  simp only [rayCharacter, MulChar.mul_apply]
  ring

/-! ### Active primes, the packed generators, and the zero primes -/

section Active
variable (C D : Ideal O)

theorem activePrime_dvd (i : ActiveIndex C D) : activePrime C D i ∣ C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp i.val.property).1)

theorem activePrime_supported (hC : Supported C) (i : ActiveIndex C D) :
    Supported (activePrime C D i) :=
  CenteredMomentFirstCanonicalFamily.supported_of_dvd _ _ hC (activePrime_dvd C D i)

/-- Primary generator of the active prime `P`. -/
def activePrimary (i : ActiveIndex C D) : O := primaryGenerator (activePrime C D i)

theorem activePrimary_span (hC : Supported C) (i : ActiveIndex C D) :
    Ideal.span {activePrimary C D i} = activePrime C D i :=
  (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (activePrime_supported C D hC i))).1

theorem activeConductor_associated (hC : Supported C) :
    Associated (∏ i : ActiveIndex C D, activePrimary C D i) (activeConductor C D) := by
  rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.prod_span_singleton, activeConductor,
    span_finitePrimeModulus]
  exact Finset.prod_congr rfl (fun i _ => activePrimary_span C D hC i)

/-- The unit relating `activeConductor C D` to the product of the primary active primes. -/
def activeUnit (hC : Supported C) : Oˣ := Classical.choose (activeConductor_associated C D hC)

theorem activeUnit_spec (hC : Supported C) :
    (∏ i : ActiveIndex C D, activePrimary C D i) * (activeUnit C D hC : O) = activeConductor C D :=
  Classical.choose_spec (activeConductor_associated C D hC)

/-- The phase element `Π = ∏ π_P^{n_P}`. -/
def firstPhaseElement : O := ∏ i : ActiveIndex C D, activePrimary C D i ^ activeExponent C D i

theorem firstPhaseElement_supported (hC : Supported C) :
    Supported (Ideal.span {firstPhaseElement C D}) := by
  unfold firstPhaseElement
  rw [← Ideal.prod_span_singleton]
  apply supported_finset_prod
  intro i _
  rw [← Ideal.span_singleton_pow, activePrimary_span C D hC i]
  exact supported_pow _ (activePrime_supported C D hC i) _

/-- The finite ray phase of the first-side packing. -/
def firstPhase (hC : Supported C) : RayCharacter :=
  phaseRay (firstPhaseElement C D) (firstPhaseElement_supported C D hC)

/-- `V_C`: the packed left twist generator. -/
def firstPacked (hC : Supported C) (E : Finset (CommonIndex C D)) : O :=
  primeSubsetGenerator (fun P : CommonIndex C D => P.val) E * (activeUnit C D hC : O) *
    ∏ i : ActiveIndex C D, activePrimary C D i ^ leftPackedExponent (activeExponent C D i)

/-- `V_D`: the packed right twist generator. -/
def firstPackedRight (hC : Supported C) (E : Finset (CommonIndex C D)) : O :=
  primeSubsetGenerator (fun P : CommonIndex C D => P.val) E * (activeUnit C D hC : O) *
    ∏ i : ActiveIndex C D, activePrimary C D i ^ rightPackedExponent (activeExponent C D i)

/-- Exponent-zero primes of the left packing (punctures). -/
def firstZeroPrimes : Ideal O :=
  ∏ i ∈ Finset.univ.filter (fun i : ActiveIndex C D => leftPackedExponent (activeExponent C D i) = 0),
    activePrime C D i

/-- Exponent-zero primes of the right packing (punctures). -/
def firstZeroPrimesRight : Ideal O :=
  ∏ i ∈ Finset.univ.filter (fun i : ActiveIndex C D => rightPackedExponent (activeExponent C D i) = 0),
    activePrime C D i

end Active

/-! ### The packing identities -/

theorem left_coefficient_packed (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (a : O) (ha : Supported (Ideal.span {a})) (hap : lambda^2 ∣ a - 1)
    (hZ : ∀ i : ActiveIndex C D, leftPackedExponent (activeExponent C D i) = 0 →
      a ∉ activePrime C D i) :
    leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) a =
      idealRowHom (firstPacked C D hC E) (Ideal.span {a}) *
        sexticReciprocityPhase (firstPhaseElement C D) a := by
  have hloc : ∏ i : ActiveIndex C D, (idealRowHom (activePrimary C D i) (Ideal.span {a}) *
      (canonicalSextic (activePrime C D i) (activeGood C D hC i) ^ activeExponent C D i)
        (Ideal.Quotient.mk (activePrime C D i) a)) =
      ∏ i : ActiveIndex C D, (sexticReciprocityPhase (activePrimary C D i) a ^ activeExponent C D i *
        idealRowHom (activePrimary C D i ^ leftPackedExponent (activeExponent C D i))
          (Ideal.span {a})) :=
    Finset.prod_congr rfl (fun i _ => left_local (activePrime C D i) (activeGood C D hC i)
      (activePrime_supported C D hC i) a ha hap _ (hZ i))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hloc
  unfold leftCoefficient finiteSexticRow firstPacked firstPhaseElement
  rw [← activeUnit_spec C D hC]
  simp only [idealRowHom_argument_mul, idealRowHom_finset_prod _ ha, phase_prod a ha,
    phase_pow _ a ha]
  linear_combination
    (idealRowHom (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) (Ideal.span {a}) *
      idealRowHom (activeUnit C D hC : O) (Ideal.span {a})) * hloc

theorem right_coefficient_packed (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (a : O) (ha : Supported (Ideal.span {a})) (hap : lambda^2 ∣ a - 1)
    (hZ : ∀ i : ActiveIndex C D, rightPackedExponent (activeExponent C D i) = 0 →
      a ∉ activePrime C D i) :
    rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) a =
      idealRowHom (firstPackedRight C D hC E) (Ideal.span {a}) *
        sexticReciprocityPhase (firstPhaseElement C D) a := by
  have hloc : ∏ i : ActiveIndex C D, (idealRowHom (activePrimary C D i) (Ideal.span {a}) *
      (starRingEnd ℂ) ((canonicalSextic (activePrime C D i) (activeGood C D hC i) ^
        activeExponent C D i) (Ideal.Quotient.mk (activePrime C D i) a))) =
      ∏ i : ActiveIndex C D, (sexticReciprocityPhase (activePrimary C D i) a ^ activeExponent C D i *
        idealRowHom (activePrimary C D i ^ rightPackedExponent (activeExponent C D i))
          (Ideal.span {a})) :=
    Finset.prod_congr rfl (fun i _ => right_local (activePrime C D i) (activeGood C D hC i)
      (activePrime_supported C D hC i) a ha hap _ (hZ i))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hloc
  unfold rightCoefficient
  rw [show star (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) a) =
      (starRingEnd ℂ) (finiteSexticRow (activePrime C D) (activeGood C D hC)
        (activeExponent C D) a) from rfl]
  unfold finiteSexticRow firstPackedRight firstPhaseElement
  rw [← activeUnit_spec C D hC, map_prod]
  simp only [idealRowHom_argument_mul, idealRowHom_finset_prod _ ha, phase_prod a ha,
    phase_pow _ a ha]
  linear_combination
    (idealRowHom (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) (Ideal.span {a}) *
      idealRowHom (activeUnit C D hC : O) (Ideal.span {a})) * hloc

/-- **First-side packing, left.**  On supported residual columns coprime to the exponent-zero
primes, the left fixed-pair height coefficient is the fixed anchor `rayAnchor η (ξ₁*firstPhase)`
times the numerator-form twist `idealRowHom V_C`. -/
theorem left_packed {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
    (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I (firstZeroPrimes C D)) (t : ℝ) :
    heightCoeff F.left t I =
      heightCoeff (rayAnchor η (ξ₁ * firstPhase C D hC)) t I *
        idealRowHom (firstPacked C D hC E) I := by
  have hspec := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have ha : Supported (Ideal.span {primaryGenerator I}) := by rw [hspec.1]; exact hI
  have hZ' : ∀ i : ActiveIndex C D, leftPackedExponent (activeExponent C D i) = 0 →
      primaryGenerator I ∉ activePrime C D i := fun i hi =>
    not_mem_of_coprime I _ _ _ hspec.1 hZ (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi⟩))
  rw [F.left_height I hI t, rayAnchor_mul_height η _ _ I hI t, rayAnchor_height η _ I hI t,
    left_coefficient_packed C D hC E _ ha hspec.2 hZ', firstPhase,
    rayCharacter_phaseRay _ _ _ ha, hspec.1]
  ring

/-- **First-side packing, right.** -/
theorem right_packed {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
    (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I (firstZeroPrimesRight C D)) (t : ℝ) :
    heightCoeff F.right t I =
      heightCoeff (rayAnchor η (ξ₂ * firstPhase C D hC)) t I *
        idealRowHom (firstPackedRight C D hC E) I := by
  have hspec := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have ha : Supported (Ideal.span {primaryGenerator I}) := by rw [hspec.1]; exact hI
  have hZ' : ∀ i : ActiveIndex C D, rightPackedExponent (activeExponent C D i) = 0 →
      primaryGenerator I ∉ activePrime C D i := fun i hi =>
    not_mem_of_coprime I _ _ _ hspec.1 hZ (Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi⟩))
  rw [F.right_height I hI t, rayAnchor_mul_height η _ _ I hI t, rayAnchor_height η _ I hI t,
    right_coefficient_packed C D hC E _ ha hspec.2 hZ', firstPhase,
    rayCharacter_phaseRay _ _ _ ha, hspec.1]
  ring


/-! ### Norm and divisibility of the packed twists under the cube-free hypothesis -/

/-- **Cube-free valuation hypothesis**: at every common prime of `C` and `D` both
multiplicities lie in `{1,2}`. -/
def CubeFreeCommon (C D : Ideal O) : Prop :=
  ∀ P : CommonIndex C D, (leftExponent C D P = 1 ∨ leftExponent C D P = 2) ∧
    (rightExponent C D P = 1 ∨ rightExponent C D P = 2)

theorem cubefree_left_exponents (l r : ℕ) (hl : l = 1 ∨ l = 2) (hr : r = 1 ∨ r = 2) :
    (netExponent l r ≠ 0 → leftPackedExponent (netExponent l r) + r = 1 + l ∧
        leftPackedExponent (netExponent l r) ≤ l) ∧
      (netExponent l r = 0 → r = l) := by
  rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

theorem cubefree_right_exponents (l r : ℕ) (hl : l = 1 ∨ l = 2) (hr : r = 1 ∨ r = 2) :
    (netExponent l r ≠ 0 → rightPackedExponent (netExponent l r) + l = 1 + r ∧
        rightPackedExponent (netExponent l r) ≤ r) ∧
      (netExponent l r = 0 → l = r) := by
  rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

theorem prod_split_exponents {ι : Type*} [DecidableEq ι] (s A : Finset ι) (hAs : A ⊆ s)
    (N k l r : ι → ℕ) (hA : ∀ i ∈ A, k i + r i = 1 + l i) (hB : ∀ i ∈ s \ A, r i = l i) :
    (∏ i ∈ A, N i ^ k i) * ∏ i ∈ s, N i ^ r i = (∏ i ∈ A, N i) * ∏ i ∈ s, N i ^ l i := by
  rw [← Finset.prod_sdiff hAs (f := fun i => N i ^ r i),
    ← Finset.prod_sdiff hAs (f := fun i => N i ^ l i)]
  have h1 : ∏ i ∈ s \ A, N i ^ r i = ∏ i ∈ s \ A, N i ^ l i :=
    Finset.prod_congr rfl (fun i hi => by rw [hB i hi])
  have h2 : (∏ i ∈ A, N i ^ k i) * ∏ i ∈ A, N i ^ r i = (∏ i ∈ A, N i) * ∏ i ∈ A, N i ^ l i := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i hi => by rw [← pow_add, hA i hi, pow_add, pow_one])
  rw [h1]
  calc _ = (∏ i ∈ s \ A, N i ^ l i) * ((∏ i ∈ A, N i ^ k i) * ∏ i ∈ A, N i ^ r i) := by ring
    _ = _ := by rw [h2]; ring

section Norms
variable (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))

theorem commonIndex_ne_zero (P : CommonIndex C D) : P.val ≠ 0 :=
  (prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).ne_zero

theorem commonIndex_absNorm_ne_zero (P : CommonIndex C D) : Ideal.absNorm P.val ≠ 0 :=
  Ideal.absNorm_eq_zero_iff.not.mpr (commonIndex_ne_zero C D P)

theorem primeSubsetGenerator_span_eq :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} = ∏ P ∈ E, P.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem firstPacked_span :
    Ideal.span {firstPacked C D hC E} =
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} *
        ∏ i : ActiveIndex C D, activePrime C D i ^ leftPackedExponent (activeExponent C D i) := by
  unfold firstPacked
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr (activeUnit C D hC).isUnit, Ideal.mul_top,
    ← Ideal.prod_span_singleton]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by
    rw [← Ideal.span_singleton_pow, activePrimary_span C D hC i])

theorem firstPackedRight_span :
    Ideal.span {firstPackedRight C D hC E} =
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} *
        ∏ i : ActiveIndex C D, activePrime C D i ^ rightPackedExponent (activeExponent C D i) := by
  unfold firstPackedRight
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr (activeUnit C D hC).isUnit, Ideal.mul_top,
    ← Ideal.prod_span_singleton]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by
    rw [← Ideal.span_singleton_pow, activePrimary_span C D hC i])

/-- The active support as a finset of common primes. -/
abbrev activeSet : Finset (CommonIndex C D) :=
  activeSupport (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D)

theorem active_absNorm_prod (f : ℕ → ℕ) :
    (∏ i : ActiveIndex C D, Ideal.absNorm (activePrime C D i) ^ f (activeExponent C D i)) =
      ∏ P ∈ activeSet C D, Ideal.absNorm P.val ^
        f (netExponent (leftExponent C D P) (rightExponent C D P)) :=
  Finset.prod_coe_sort (activeSet C D)
    (fun P => Ideal.absNorm P.val ^ f (netExponent (leftExponent C D P) (rightExponent C D P)))

theorem active_absNorm_prod_one :
    (∏ i : ActiveIndex C D, Ideal.absNorm (activePrime C D i)) =
      ∏ P ∈ activeSet C D, Ideal.absNorm P.val :=
  Finset.prod_coe_sort (activeSet C D) (fun P => Ideal.absNorm P.val)

theorem mem_activeSet_iff (P : CommonIndex C D) :
    P ∈ activeSet C D ↔ netExponent (leftExponent C D P) (rightExponent C D P) ≠ 0 := by
  unfold activeSet CenteredMomentActive.activeSupport
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **CF (3.1), left**: `N(V_C)·N(c_D) = N(e)·N(r)·N(c_C)`, i.e. `q_C = q + c - d`. -/
theorem firstPacked_norm (hcf : CubeFreeCommon C D) :
    Ideal.absNorm (Ideal.span {firstPacked C D hC E}) * Ideal.absNorm (commonPart D C) =
      Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) *
        Ideal.absNorm (Ideal.span {activeConductor C D}) * Ideal.absNorm (commonPart C D) := by
  rw [firstPacked_span C D hC E, commonPart_right_product C D, commonPart_left_product C D,
    activeConductor, span_finitePrimeModulus]
  simp only [map_mul, map_prod, map_pow]
  rw [active_absNorm_prod C D leftPackedExponent, active_absNorm_prod_one C D, mul_assoc,
    mul_assoc]
  congr 1
  apply prod_split_exponents Finset.univ (activeSet C D) (Finset.subset_univ _)
    (fun P => Ideal.absNorm P.val)
  · intro P hP
    exact (((cubefree_left_exponents _ _ (hcf P).1 (hcf P).2).1
      ((mem_activeSet_iff C D P).mp hP))).1
  · intro P hP
    have hn : netExponent (leftExponent C D P) (rightExponent C D P) = 0 := by
      by_contra h
      exact (Finset.mem_sdiff.mp hP).2 ((mem_activeSet_iff C D P).mpr h)
    exact (cubefree_left_exponents _ _ (hcf P).1 (hcf P).2).2 hn

/-- **CF (3.1), right**: `N(V_D)·N(c_C) = N(e)·N(r)·N(c_D)`, i.e. `q_D = q + d - c`. -/
theorem firstPackedRight_norm (hcf : CubeFreeCommon C D) :
    Ideal.absNorm (Ideal.span {firstPackedRight C D hC E}) * Ideal.absNorm (commonPart C D) =
      Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) *
        Ideal.absNorm (Ideal.span {activeConductor C D}) * Ideal.absNorm (commonPart D C) := by
  rw [firstPackedRight_span C D hC E, commonPart_right_product C D, commonPart_left_product C D,
    activeConductor, span_finitePrimeModulus]
  simp only [map_mul, map_prod, map_pow]
  rw [active_absNorm_prod C D rightPackedExponent, active_absNorm_prod_one C D, mul_assoc,
    mul_assoc]
  congr 1
  apply prod_split_exponents Finset.univ (activeSet C D) (Finset.subset_univ _)
    (fun P => Ideal.absNorm P.val)
  · intro P hP
    exact (((cubefree_right_exponents _ _ (hcf P).1 (hcf P).2).1
      ((mem_activeSet_iff C D P).mp hP))).1
  · intro P hP
    have hn : netExponent (leftExponent C D P) (rightExponent C D P) = 0 := by
      by_contra h
      exact (Finset.mem_sdiff.mp hP).2 ((mem_activeSet_iff C D P).mpr h)
    exact (cubefree_right_exponents _ _ (hcf P).1 (hcf P).2).2 hn

theorem commonPart_left_absNorm_ne_zero : Ideal.absNorm (commonPart C D) ≠ 0 := by
  rw [commonPart_left_product C D, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun P _ => by
    rw [map_pow]; exact pow_ne_zero _ (commonIndex_absNorm_ne_zero C D P))

theorem commonPart_right_absNorm_ne_zero : Ideal.absNorm (commonPart D C) ≠ 0 := by
  rw [commonPart_right_product C D, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun P _ => by
    rw [map_pow]; exact pow_ne_zero _ (commonIndex_absNorm_ne_zero C D P))

theorem subsetGenerator_absNorm_ne_zero :
    Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) ≠ 0 := by
  rw [primeSubsetGenerator_span_eq, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun P _ => commonIndex_absNorm_ne_zero C D P)

theorem activeConductor_absNorm_ne_zero :
    Ideal.absNorm (Ideal.span {activeConductor C D}) ≠ 0 := by
  rw [activeConductor, span_finitePrimeModulus, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => commonIndex_absNorm_ne_zero C D i.val)

theorem logb_of_norm_identity (Z : ℝ) (X d q c : ℕ) (hd : d ≠ 0) (hq : q ≠ 0) (hc : c ≠ 0)
    (h : X * d = q * c) :
    Real.logb Z (X : ℝ) = Real.logb Z (q : ℝ) + Real.logb Z (c : ℝ) - Real.logb Z (d : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hX : (X : ℝ) = (q : ℝ) * c / d := by
    rw [eq_div_iff hd']; exact_mod_cast h
  rw [hX, Real.logb_div (mul_ne_zero hq' hc') hd', Real.logb_mul hq' hc']

/-- **CF (3.1) in logarithmic form**: `log_Z N V_C = q + c - d` with
`q = log_Z (N e · N r)`, `c = log_Z N(c_C)`, `d = log_Z N(c_D)`. -/
theorem firstPacked_logb (Z : ℝ) (hcf : CubeFreeCommon C D) :
    Real.logb Z (Ideal.absNorm (Ideal.span {firstPacked C D hC E}) : ℝ) =
      Real.logb Z ((Ideal.absNorm (Ideal.span
          {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) *
          Ideal.absNorm (Ideal.span {activeConductor C D})) +
        Real.logb Z (Ideal.absNorm (commonPart C D) : ℝ) -
        Real.logb Z (Ideal.absNorm (commonPart D C) : ℝ) := by
  have h := logb_of_norm_identity Z _ _ _ _ (commonPart_right_absNorm_ne_zero C D)
    (mul_ne_zero (subsetGenerator_absNorm_ne_zero C D E) (activeConductor_absNorm_ne_zero C D))
    (commonPart_left_absNorm_ne_zero C D) (firstPacked_norm C D hC E hcf)
  rw [h]
  push_cast
  ring

/-- **CF (3.1) in logarithmic form, right**: `log_Z N V_D = q + d - c`. -/
theorem firstPackedRight_logb (Z : ℝ) (hcf : CubeFreeCommon C D) :
    Real.logb Z (Ideal.absNorm (Ideal.span {firstPackedRight C D hC E}) : ℝ) =
      Real.logb Z ((Ideal.absNorm (Ideal.span
          {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) *
          Ideal.absNorm (Ideal.span {activeConductor C D})) +
        Real.logb Z (Ideal.absNorm (commonPart D C) : ℝ) -
        Real.logb Z (Ideal.absNorm (commonPart C D) : ℝ) := by
  have h := logb_of_norm_identity Z _ _ _ _ (commonPart_left_absNorm_ne_zero C D)
    (mul_ne_zero (subsetGenerator_absNorm_ne_zero C D E) (activeConductor_absNorm_ne_zero C D))
    (commonPart_right_absNorm_ne_zero C D) (firstPackedRight_norm C D hC E hcf)
  rw [h]
  push_cast
  ring

theorem subsetGenerator_span_dvd_left :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} ∣ commonPart C D := by
  rw [primeSubsetGenerator_span_eq, commonPart_left_product C D]
  exact (Finset.prod_dvd_prod_of_subset E Finset.univ (fun P : CommonIndex C D => P.val)
    (Finset.subset_univ E)).trans (Finset.prod_dvd_prod_of_dvd _ _ (fun P _ =>
      dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))))

theorem subsetGenerator_span_dvd_right :
    Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E} ∣ commonPart D C := by
  rw [primeSubsetGenerator_span_eq, commonPart_right_product C D]
  exact (Finset.prod_dvd_prod_of_subset E Finset.univ (fun P : CommonIndex C D => P.val)
    (Finset.subset_univ E)).trans (Finset.prod_dvd_prod_of_dvd _ _ (fun P _ =>
      dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))))

theorem active_prod_dvd (f : ℕ → ℕ) (g : CommonIndex C D → ℕ)
    (hfg : ∀ P ∈ activeSet C D, f (netExponent (leftExponent C D P) (rightExponent C D P)) ≤ g P) :
    (∏ i : ActiveIndex C D, activePrime C D i ^ f (activeExponent C D i)) ∣
      ∏ P : CommonIndex C D, P.val ^ g P := by
  have hc : (∏ i : ActiveIndex C D, activePrime C D i ^ f (activeExponent C D i)) =
      ∏ P ∈ activeSet C D, P.val ^ f (netExponent (leftExponent C D P) (rightExponent C D P)) :=
    Finset.prod_coe_sort (activeSet C D)
      (fun P => P.val ^ f (netExponent (leftExponent C D P) (rightExponent C D P)))
  rw [hc]
  exact (Finset.prod_dvd_prod_of_dvd _ _ (fun P hP => pow_dvd_pow _ (hfg P hP))).trans
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _))

/-- `V_C ∣ C²` (at the level of the common part). -/
theorem firstPacked_dvd (hcf : CubeFreeCommon C D) :
    Ideal.span {firstPacked C D hC E} ∣ commonPart C D ^ 2 := by
  rw [firstPacked_span C D hC E, sq]
  apply mul_dvd_mul (subsetGenerator_span_dvd_left C D E)
  rw [commonPart_left_product C D]
  exact active_prod_dvd C D leftPackedExponent (leftExponent C D) (fun P hP =>
    ((cubefree_left_exponents _ _ (hcf P).1 (hcf P).2).1 ((mem_activeSet_iff C D P).mp hP)).2)

/-- `V_D ∣ D²` (at the level of the common part). -/
theorem firstPackedRight_dvd (hcf : CubeFreeCommon C D) :
    Ideal.span {firstPackedRight C D hC E} ∣ commonPart D C ^ 2 := by
  rw [firstPackedRight_span C D hC E, sq]
  apply mul_dvd_mul (subsetGenerator_span_dvd_right C D E)
  rw [commonPart_right_product C D]
  exact active_prod_dvd C D rightPackedExponent (rightExponent C D) (fun P hP =>
    ((cubefree_right_exponents _ _ (hcf P).1 (hcf P).2).1 ((mem_activeSet_iff C D P).mp hP)).2)

end Norms

end

end QRH.SilDensitySplit.CubeFree.Packet
