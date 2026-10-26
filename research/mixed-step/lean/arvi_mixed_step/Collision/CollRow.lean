/- Mixed source step, L3 (collisions): new in this submission; uses Collision/Factor.lean,
Collision/SquareGauss.lean and the baseline's lemmas by import (the vanishing of the
prime Gauss sum at frequencies divisible by `p` repeats the first branch of
`collisionFactor_norm_le`).

The collision rows at the ideal level. For a selected assignment `u` of distinct primes
with product `D` (supported) and a column `M ⊥ D`, with `δ = primaryGenerator D`:
* `coll_row_zero`: `primaryGaussRow (D²M) k = 0` unless `δ ∣ k`;
* `coll_row_zero_at_zero`: `primaryGaussRow (D²M) 0 = 0` for a nonempty pattern;
* `coll_row_twist`: `primaryGaussRow (D²M) (δH') = (δ³/M) · primaryGaussRow (D²) (δH') ·
  primaryGaussRow M H'`;
* `coll_square_norm`: `‖primaryGaussRow (D²) k‖ ≤ √N(D)`. -/
import Submissions.arvi_mixed_step.Collision.SquareGauss
import Submissions.arvi_mixed_step.Transfer.Rays

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QRH.MixedStep.Collision
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve CubicEisenstein ConcreteTraceCRT
open ProbePrimePower ProbePhysical CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentLiveDomain QRH.MixedStep.Transfer Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

/-- The prime Gauss factor vanishes at frequencies divisible by `p`. -/
theorem collisionFactor_dvd (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H' : O)
    (hH : p ∣ H') : collisionFactor p hp hsp H' = 0 := by
  letI hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  letI : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp.ne_zero
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  obtain ⟨hg, hc⟩ := supported_prime_data p hp hsp
  set χ := actualSextic (Ideal.span {p}) hg ^ 2 with hχ
  have hχ1 : χ ≠ 1 := by
    intro h
    have := (actualSextic_pow_eq_one_iff _ hg hc 2).mp h
    omega
  unfold collisionFactor
  have hz : Ideal.Quotient.mk (Ideal.span {p}) H' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hH)
  have h0 : primeGauss p hp.ne_zero χ H' = 0 := by
    unfold primeGauss
    rw [tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ1
  simp only [← hχ]
  exact h0

/-- The Gauss sum of `p²` vanishes at frequency `0`. -/
theorem prime_sq_at_zero (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) :
    sexticGauss (p^2) (pow_ne_zero _ hp.ne_zero) 0 = 0 := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  rw [sextic_sq p hp hsp 0]
  have hl := primePowerGauss_lift p hp.ne_zero
    (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) 1 0
  rw [pow_one, mul_zero] at hl
  rw [hl]
  have h0 := collisionFactor_dvd p hp hsp 0 (dvd_zero p)
  unfold collisionFactor at h0
  rw [h0, mul_zero]

/-- A nonempty product of distinct primes: the square's Gauss sum vanishes at `0`. -/
theorem square_gauss_at_zero {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (p : ι → O)
    (hp : ∀ i ∈ T, Prime (p i)) (hsp : ∀ i ∈ T, Supported (Ideal.span {p i}))
    (hcop : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsCoprime (p i) (p j)) :
    sexticGauss ((∏ i ∈ T, p i)^2)
      (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod T p hsp))) 0 = 0 := by
  induction T using Finset.induction_on with
  | empty => exact absurd hT (Finset.not_nonempty_empty)
  | insert i T hiT ih =>
    have hpi : Prime (p i) := hp i (Finset.mem_insert_self _ _)
    have hsi : Supported (Ideal.span {p i}) := hsp i (Finset.mem_insert_self _ _)
    have hsT : ∀ j ∈ T, Supported (Ideal.span {p j}) :=
      fun j hj => hsp j (Finset.mem_insert_of_mem hj)
    have hsP := supported_finset_prod T p hsT
    have hci : IsCoprime (p i) (∏ j ∈ T, p j) := by
      apply IsCoprime.prod_right
      intro j hj
      exact hcop i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hiT (h ▸ hj))
    have hprod : (∏ j ∈ insert i T, p j)^2 = (p i)^2 * (∏ j ∈ T, p j)^2 := by
      rw [Finset.prod_insert hiT, mul_pow]
    rw [sexticGauss_congr hprod _ (mul_ne_zero (supportedElement_ne_zero _ (supported_sq _ hsi))
      (supportedElement_ne_zero _ (supported_sq _ hsP))),
      sexticGauss_coprime_product ((p i)^2) ((∏ j ∈ T, p j)^2)
        (supported_sq _ hsi) (supported_sq _ hsP) (hci.pow_left.pow_right) 0]
    have hz : sexticGauss ((p i)^2) (supportedElement_ne_zero _ (supported_sq _ hsi)) 0 = 0 :=
      prime_sq_at_zero (p i) hpi hsi
    rw [hz, mul_zero, zero_mul]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The primary generators of an assignment of distinct supported primes. -/
theorem assignment_data {Q : Finset κ} (u : Q → Ideal O) (hu : ∀ j, Prime (u j))
    (hinj : Function.Injective u) (hsD : Supported (selProduct Q u)) :
    (∀ j ∈ (Finset.univ : Finset Q), Prime (primaryGenerator (u j))) ∧
    (∀ j ∈ (Finset.univ : Finset Q), Supported (Ideal.span {primaryGenerator (u j)})) ∧
    (∀ i ∈ (Finset.univ : Finset Q), ∀ j ∈ (Finset.univ : Finset Q), i ≠ j →
      IsCoprime (primaryGenerator (u i)) (primaryGenerator (u j))) ∧
    primaryGenerator (selProduct Q u) = ∏ j ∈ (Finset.univ : Finset Q), primaryGenerator (u j) := by
  have hsj : ∀ j, Supported (u j) := by
    intro j
    have hd : u j ∣ selProduct Q u := Finset.dvd_prod_of_mem u (Finset.mem_univ j)
    obtain ⟨c, hc⟩ := hd
    have h := hsD
    rw [hc] at h
    exact ((supported_mul_iff _ _).mp h).1
  have hspan : ∀ j, Ideal.span {primaryGenerator (u j)} = u j :=
    fun j => primary_span_supported (u j) (hsj j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _
    rw [← Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero _ (hsj j)), hspan j]
    exact Ideal.isPrime_of_prime (hu j)
  · intro j _
    rw [hspan j]
    exact hsj j
  · intro i _ j _ hij
    rw [← Ideal.isCoprime_span_singleton_iff, hspan i, hspan j]
    apply coprime_of_prime_not_dvd (hu i)
    intro hd
    exact hij (hinj ((prime_dvd_prime_iff_eq (hu i) (hu j)).mp hd))
  · unfold selProduct
    exact map_prod primaryGeneratorHom u Finset.univ

theorem supported_of_sq_mul (D M : Ideal O) (hs : Supported (D ^ 2 * M)) :
    Supported D ∧ Supported M := by
  have h := (supported_mul_iff _ _).mp hs
  rw [pow_two] at h
  exact ⟨((supported_mul_iff _ _).mp h.1).1, h.2⟩

theorem primaryGenerator_sq (D : Ideal O) :
    primaryGenerator (D ^ 2) = primaryGenerator D ^ 2 := by
  rw [pow_two, primaryGenerator_mul, pow_two]

theorem primaryGenerator_sq_mul (D M : Ideal O) :
    primaryGenerator (D ^ 2 * M) = primaryGenerator D ^ 2 * primaryGenerator M := by
  rw [primaryGenerator_mul, show D ^ 2 = D * D by ring, primaryGenerator_mul]
  ring

/-- **Collision rows vanish off `δ·O`.** -/
theorem coll_row_zero {Q : Finset κ} (u : Q → Ideal O) (hu : ∀ j, Prime (u j))
    (hinj : Function.Injective u) (M : Ideal O) (hcop : IsCoprime (selProduct Q u) M) (k : O)
    (hk : ¬primaryGenerator (selProduct Q u) ∣ k) :
    primaryGaussRow (selProduct Q u ^ 2 * M) k = 0 := by
  by_cases hs : Supported (selProduct Q u ^ 2 * M)
  · obtain ⟨hsD, hsM⟩ := supported_of_sq_mul _ _ hs
    obtain ⟨hp, hsp, hpc, hgen⟩ := assignment_data u hu hinj hsD
    rw [primaryGaussRow_of_supported _ hs]
    rw [gaussRow_congr' (primaryGenerator_sq_mul _ M) _
      (supported_sq_mul _ _ (MixedSelectedCommon.primary_supported _ hsD)
        (MixedSelectedCommon.primary_supported _ hsM))]
    unfold gaussRow
    have hcop' : IsCoprime (primaryGenerator (selProduct Q u) ^ 2) (primaryGenerator M) := by
      apply IsCoprime.pow_left
      rw [← Ideal.isCoprime_span_singleton_iff, primary_span_supported _ hsD,
        primary_span_supported _ hsM]
      exact hcop
    rw [sexticGauss_coprime_product _ _ (supported_sq _ (MixedSelectedCommon.primary_supported _ hsD))
      (MixedSelectedCommon.primary_supported _ hsM) hcop' k]
    have hz := (square_gauss Finset.univ (fun j => primaryGenerator (u j)) hp hsp hpc k).1
      (by rw [← hgen]; exact hk)
    have hz' : sexticGauss (primaryGenerator (selProduct Q u) ^ 2)
        (supportedElement_ne_zero _ (supported_sq _ (MixedSelectedCommon.primary_supported _ hsD)))
        k = 0 := by
      rw [sexticGauss_congr (congrArg (· ^ 2) hgen) _
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod Finset.univ
          (fun j => primaryGenerator (u j)) hsp)))]
      exact hz
    rw [hz']
    simp
  · exact primaryGaussRow_of_not_supported _ hs k

/-- **Collision rows vanish at frequency `0`** (nonempty pattern). -/
theorem coll_row_zero_at_zero {Q : Finset κ} (hQ : Q.Nonempty) (u : Q → Ideal O)
    (hu : ∀ j, Prime (u j)) (hinj : Function.Injective u) (M : Ideal O)
    (hcop : IsCoprime (selProduct Q u) M) :
    primaryGaussRow (selProduct Q u ^ 2 * M) 0 = 0 := by
  by_cases hs : Supported (selProduct Q u ^ 2 * M)
  · obtain ⟨hsD, hsM⟩ := supported_of_sq_mul _ _ hs
    obtain ⟨hp, hsp, hpc, hgen⟩ := assignment_data u hu hinj hsD
    rw [primaryGaussRow_of_supported _ hs]
    rw [gaussRow_congr' (primaryGenerator_sq_mul _ M) _
      (supported_sq_mul _ _ (MixedSelectedCommon.primary_supported _ hsD)
        (MixedSelectedCommon.primary_supported _ hsM))]
    unfold gaussRow
    have hcop' : IsCoprime (primaryGenerator (selProduct Q u) ^ 2) (primaryGenerator M) := by
      apply IsCoprime.pow_left
      rw [← Ideal.isCoprime_span_singleton_iff, primary_span_supported _ hsD,
        primary_span_supported _ hsM]
      exact hcop
    rw [sexticGauss_coprime_product _ _ (supported_sq _ (MixedSelectedCommon.primary_supported _ hsD))
      (MixedSelectedCommon.primary_supported _ hsM) hcop' 0]
    have hne : (Finset.univ : Finset Q).Nonempty := by
      obtain ⟨j, hj⟩ := hQ
      exact ⟨⟨j, hj⟩, Finset.mem_univ _⟩
    have hz := square_gauss_at_zero Finset.univ hne (fun j => primaryGenerator (u j)) hp hsp hpc
    have hz' : sexticGauss (primaryGenerator (selProduct Q u) ^ 2)
        (supportedElement_ne_zero _ (supported_sq _ (MixedSelectedCommon.primary_supported _ hsD)))
        0 = 0 := by
      rw [sexticGauss_congr (congrArg (· ^ 2) hgen) _
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod Finset.univ
          (fun j => primaryGenerator (u j)) hsp)))]
      exact hz
    rw [hz']
    simp
  · exact primaryGaussRow_of_not_supported _ hs 0

/-- **The collision twist at the ideal level.** -/
theorem coll_row_twist {Q : Finset κ} (u : Q → Ideal O) (M : Ideal O)
    (hcop : IsCoprime (selProduct Q u) M) (H' : O) :
    primaryGaussRow (selProduct Q u ^ 2 * M) (primaryGenerator (selProduct Q u) * H') =
      idealRowHom (primaryGenerator (selProduct Q u) ^ 3) M *
        primaryGaussRow (selProduct Q u ^ 2) (primaryGenerator (selProduct Q u) * H') *
        primaryGaussRow M H' := by
  by_cases hs : Supported (selProduct Q u ^ 2 * M)
  · obtain ⟨hsD, hsM⟩ := supported_of_sq_mul _ _ hs
    have hsD2 : Supported (selProduct Q u ^ 2) := ((supported_mul_iff _ _).mp hs).1
    have hpD := MixedSelectedCommon.primary_supported _ hsD
    have hpM := MixedSelectedCommon.primary_supported _ hsM
    have hprD := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ hsD)).2
    have hprM := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ hsM)).2
    have hcop' : IsCoprime (primaryGenerator (selProduct Q u)) (primaryGenerator M) := by
      rw [← Ideal.isCoprime_span_singleton_iff, primary_span_supported _ hsD,
        primary_span_supported _ hsM]
      exact hcop
    rw [primaryGaussRow_of_supported _ hs, primaryGaussRow_of_supported _ hsD2,
      primaryGaussRow_of_supported _ hsM]
    rw [gaussRow_congr' (primaryGenerator_sq_mul _ M) _ (supported_sq_mul _ _ hpD hpM),
      gaussRow_congr' (primaryGenerator_sq _) _ (supported_sq _ hpD)]
    rw [square_twist _ _ hpD hpM hprD hprM hcop' H', primary_span_supported _ hsM]
  · have hz : primaryGaussRow (selProduct Q u ^ 2 * M) (primaryGenerator (selProduct Q u) * H') = 0 :=
      primaryGaussRow_of_not_supported _ hs _
    rw [hz]
    by_cases hsM : Supported M
    · have hsD2 : ¬Supported (selProduct Q u ^ 2) := fun h => hs ((supported_mul_iff _ _).mpr ⟨h, hsM⟩)
      rw [primaryGaussRow_of_not_supported _ hsD2, mul_zero, zero_mul]
    · rw [primaryGaussRow_of_not_supported _ hsM, mul_zero]

/-- **The square factor has norm at most `√N(D)`.** -/
theorem coll_square_norm {Q : Finset κ} (u : Q → Ideal O) (hu : ∀ j, Prime (u j))
    (hinj : Function.Injective u) (k : O) :
    ‖primaryGaussRow (selProduct Q u ^ 2) k‖ ≤
      Real.sqrt (Ideal.absNorm (selProduct Q u) : ℝ) := by
  by_cases hs : Supported (selProduct Q u ^ 2)
  · have hsD : Supported (selProduct Q u) := by
      have h := hs
      rw [pow_two] at h
      exact ((supported_mul_iff _ _).mp h).1
    obtain ⟨hp, hsp, hpc, hgen⟩ := assignment_data u hu hinj hsD
    rw [primaryGaussRow_of_supported _ hs]
    have hgen2 : primaryGenerator (selProduct Q u ^ 2) =
        (∏ j ∈ (Finset.univ : Finset Q), primaryGenerator (u j)) ^ 2 := by
      rw [← hgen, primaryGenerator_sq]
    rw [gaussRow_congr' hgen2 _ (supported_sq _ (supported_finset_prod Finset.univ _ hsp))]
    have hn := (square_row Finset.univ (fun j => primaryGenerator (u j)) hp hsp hpc k).2
    calc
      _ ≤ _ := hn
      _ = _ := by rw [← hgen, primary_span_supported _ hsD]
  · rw [primaryGaussRow_of_not_supported _ hs, norm_zero]
    exact Real.sqrt_nonneg _

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.coll_row_zero
#print axioms QRH.MixedStep.Collision.coll_row_zero_at_zero
#print axioms QRH.MixedStep.Collision.coll_row_twist
#print axioms QRH.MixedStep.Collision.coll_square_norm
