/- Mixed source step, L3 (collisions): new in this submission; uses the single-prime
lemmas of Collision/Column.lean and Collision/Factor.lean and the baseline's CRT,
unit-scaling and reciprocity lemmas by import.

The square Gauss factor of a collision pattern with several colliding primes, and
the collision twist.

* `square_gauss_zero`, `square_gauss_norm`: for `δ = ∏_{i∈T} p i` (pairwise coprime
  supported primes) the sextic Gauss sum of `δ²` vanishes off `δ·O`, and has norm
  at most `N(δ)·√N(δ)` (CRT over the primes; single-prime facts from Collision/).
* `square_row_norm`: the normalized row `gaussRow (δ²)` has norm at most `√N(δ)`.
* `square_twist`: for `d, m` primary, supported and coprime,
  `gaussRow (d²·m) (d·H') = (d/m)³ · gaussRow (d²) (d·H') · gaussRow m H'`.
  The twist is the row symbol `idealRowHom (d³) (m)`: the reciprocity sign enters
  squared (`= 1`), and `(d/m)⁴·(d/m)⁻¹ = (d/m)³`. -/
import Submissions.arvi_mixed_step.Collision.Factor
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSelectedCommon

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
open ProbePrimePower ProbePhysical CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_congr {a b : O} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (H : O) :
    sexticGauss a ha H = sexticGauss b hb H := by
  subst h
  rfl

theorem gaussRow_congr' {a b : O} (h : a = b) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (H : O) : gaussRow a ha H = gaussRow b hb H := by
  subst h
  rfl

/-- Single prime: the Gauss sum of `p²` vanishes off `p·O`. -/
theorem prime_sq_zero (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H : O)
    (hH : ¬p ∣ H) : sexticGauss (p^2) (pow_ne_zero _ hp.ne_zero) H = 0 := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  rw [sextic_sq p hp hsp H]
  apply primePowerGauss_zero_off_support
  simpa using hH

/-- Single prime: the Gauss sum of `p²` has norm at most `N(p)·√N(p)`. -/
theorem prime_sq_norm (p : O) (hp : Prime p) (hsp : Supported (Ideal.span {p})) (H : O) :
    ‖sexticGauss (p^2) (pow_ne_zero _ hp.ne_zero) H‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) * Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  by_cases hH : p ∣ H
  · obtain ⟨H', rfl⟩ := hH
    letI : (Ideal.span {p}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    rw [sextic_sq p hp hsp (p*H')]
    have hl := primePowerGauss_lift p hp.ne_zero
      (actualSextic (Ideal.span {p}) (supported_prime_data p hp hsp).1 ^ 2) 1 H'
    rw [pow_one, pow_one] at hl
    rw [hl, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (collisionFactor_norm_le p hp hsp H') (Nat.cast_nonneg _)
  · rw [prime_sq_zero p hp hsp H hH, norm_zero]
    positivity

theorem supported_finset_prod {ι : Type*} (T : Finset ι) (p : ι → O)
    (hsp : ∀ i ∈ T, Supported (Ideal.span {p i})) :
    Supported (Ideal.span {∏ i ∈ T, p i}) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.span_singleton_one, ← Ideal.one_eq_top]
    exact CenteredMomentAddedZero.supported_one_ideal
  | insert i T hiT ih =>
    rw [Finset.prod_insert hiT, ← Ideal.span_singleton_mul_span_singleton, supported_mul_iff]
    exact ⟨hsp i (Finset.mem_insert_self _ _),
      ih (fun j hj => hsp j (Finset.mem_insert_of_mem hj))⟩

/-- Multi-prime: vanishing off `δ·O` and the norm bound, by CRT over the primes. -/
theorem square_gauss {ι : Type*} (T : Finset ι) (p : ι → O) (hp : ∀ i ∈ T, Prime (p i))
    (hsp : ∀ i ∈ T, Supported (Ideal.span {p i}))
    (hcop : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsCoprime (p i) (p j)) (H : O) :
    (¬(∏ i ∈ T, p i) ∣ H →
      sexticGauss ((∏ i ∈ T, p i)^2)
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod T p hsp))) H = 0) ∧
    ‖sexticGauss ((∏ i ∈ T, p i)^2)
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod T p hsp))) H‖ ≤
      ∏ i ∈ T, ((Ideal.absNorm (Ideal.span {p i}) : ℝ) *
        Real.sqrt (Ideal.absNorm (Ideal.span {p i}) : ℝ)) := by
  induction T using Finset.induction_on with
  | empty =>
    have h1 : sexticGauss ((∏ i ∈ (∅ : Finset ι), p i)^2)
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod ∅ p hsp))) H = 1 := by
      rw [sexticGauss_congr (by simp : (∏ i ∈ (∅ : Finset ι), p i)^2 = 1) _ one_ne_zero,
        sexticGauss_one]
    refine ⟨fun h => absurd (by simp) h, ?_⟩
    rw [h1, Finset.prod_empty, norm_one]
  | insert i T hiT ih =>
    have hpi : Prime (p i) := hp i (Finset.mem_insert_self _ _)
    have hsi : Supported (Ideal.span {p i}) := hsp i (Finset.mem_insert_self _ _)
    have hpT : ∀ j ∈ T, Prime (p j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hsT : ∀ j ∈ T, Supported (Ideal.span {p j}) :=
      fun j hj => hsp j (Finset.mem_insert_of_mem hj)
    have hcT : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → IsCoprime (p a) (p b) :=
      fun a ha b hb hab => hcop a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    obtain ⟨ihz, ihn⟩ := ih hpT hsT hcT
    have hsP := supported_finset_prod T p hsT
    have hci : IsCoprime (p i) (∏ j ∈ T, p j) := by
      apply IsCoprime.prod_right
      intro j hj
      exact hcop i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hiT (h ▸ hj))
    have hprod : (∏ j ∈ insert i T, p j)^2 = (p i)^2 * (∏ j ∈ T, p j)^2 := by
      rw [Finset.prod_insert hiT, mul_pow]
    have hsplit := sexticGauss_coprime_product ((p i)^2) ((∏ j ∈ T, p j)^2)
      (supported_sq _ hsi) (supported_sq _ hsP) (hci.pow_left.pow_right) H
    have he : sexticGauss ((∏ j ∈ insert i T, p j)^2)
        (supportedElement_ne_zero _ (supported_sq _ (supported_finset_prod (insert i T) p hsp))) H =
        idealRowHom ((∏ j ∈ T, p j)^2) (Ideal.span {(p i)^2}) *
          idealRowHom ((p i)^2) (Ideal.span {(∏ j ∈ T, p j)^2}) *
          sexticGauss ((p i)^2) (pow_ne_zero _ hpi.ne_zero) H *
          sexticGauss ((∏ j ∈ T, p j)^2)
            (supportedElement_ne_zero _ (supported_sq _ hsP)) H := by
      rw [sexticGauss_congr hprod _ (mul_ne_zero (supportedElement_ne_zero _ (supported_sq _ hsi))
        (supportedElement_ne_zero _ (supported_sq _ hsP)))]
      exact hsplit
    refine ⟨?_, ?_⟩
    · intro hnd
      rw [he]
      by_cases hdi : p i ∣ H
      · have hdT : ¬(∏ j ∈ T, p j) ∣ H := by
          intro hdT
          apply hnd
          rw [Finset.prod_insert hiT]
          exact hci.mul_dvd hdi hdT
        rw [ihz hdT, mul_zero]
      · rw [prime_sq_zero (p i) hpi hsi H hdi, mul_zero, zero_mul]
    · rw [he, Finset.prod_insert hiT]
      have h1 := idealRowHom_norm ((∏ j ∈ T, p j)^2) (Ideal.span {(p i)^2})
      have h2 := idealRowHom_norm ((p i)^2) (Ideal.span {(∏ j ∈ T, p j)^2})
      have h3 := prime_sq_norm (p i) hpi hsi H
      rw [norm_mul, norm_mul, norm_mul]
      calc
        _ ≤ 1 * 1 * ((Ideal.absNorm (Ideal.span {p i}) : ℝ) *
              Real.sqrt (Ideal.absNorm (Ideal.span {p i}) : ℝ)) *
            ∏ j ∈ T, ((Ideal.absNorm (Ideal.span {p j}) : ℝ) *
              Real.sqrt (Ideal.absNorm (Ideal.span {p j}) : ℝ)) := by
          gcongr
        _ = _ := by ring

/-- The product of the local norm factors is `N(δ)·√N(δ)`. -/
theorem norm_factor_prod {ι : Type*} (T : Finset ι) (p : ι → O) :
    ∏ i ∈ T, ((Ideal.absNorm (Ideal.span {p i}) : ℝ) *
        Real.sqrt (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) *
        Real.sqrt (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) := by
  have hN : (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) =
      ∏ i ∈ T, (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
    rw [← Ideal.prod_span_singleton, map_prod, Nat.cast_prod]
  rw [hN, Finset.prod_mul_distrib, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg _)]

/-- **The normalized square row**: vanishing off `δ·O` and `‖·‖ ≤ √N(δ)`. -/
theorem square_row {ι : Type*} (T : Finset ι) (p : ι → O) (hp : ∀ i ∈ T, Prime (p i))
    (hsp : ∀ i ∈ T, Supported (Ideal.span {p i}))
    (hcop : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsCoprime (p i) (p j)) (H : O) :
    (¬(∏ i ∈ T, p i) ∣ H →
      gaussRow ((∏ i ∈ T, p i)^2) (supported_sq _ (supported_finset_prod T p hsp)) H = 0) ∧
    ‖gaussRow ((∏ i ∈ T, p i)^2) (supported_sq _ (supported_finset_prod T p hsp)) H‖ ≤
      Real.sqrt (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) := by
  obtain ⟨hz, hn⟩ := square_gauss T p hp hsp hcop H
  have hN0 : (0 : ℝ) < Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (supported_finset_prod T p hsp).1)
  have hsq : Real.sqrt (Ideal.absNorm (Ideal.span {(∏ i ∈ T, p i)^2}) : ℝ) =
      (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) := by
    rw [← Ideal.span_singleton_pow, map_pow, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  refine ⟨fun h => ?_, ?_⟩
  · unfold gaussRow
    rw [hz h, zero_div]
  · unfold gaussRow
    rw [hsq, norm_div, Complex.norm_real, Real.norm_of_nonneg hN0.le,
      div_le_iff₀ hN0]
    rw [norm_factor_prod T p] at hn
    calc
      _ ≤ (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) *
          Real.sqrt (Ideal.absNorm (Ideal.span {∏ i ∈ T, p i}) : ℝ) := hn
      _ = _ := by ring

/-- The reciprocity sign squares to one. -/
theorem reciprocityPhase_sq (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) : sexticReciprocityPhase a b ^ 2 = 1 := by
  unfold sexticReciprocityPhase
  rw [← Int.cast_pow, QuadraticAllOddCRT.quadraticRaySign_sq _ _ (supported_residue_odd a ha)
    (supported_residue_odd b hb), Int.cast_one]

/-- **The collision twist.** -/
theorem square_twist (d m : O) (hd : Supported (Ideal.span {d}))
    (hm : Supported (Ideal.span {m})) (hpd : goodLambda^2 ∣ d - 1) (hpm : goodLambda^2 ∣ m - 1)
    (hcop : IsCoprime d m) (H' : O) :
    gaussRow (d^2 * m) (supported_sq_mul d m hd hm) (d * H') =
      idealRowHom (d^3) (Ideal.span {m}) * gaussRow (d^2) (supported_sq d hd) (d * H') *
        gaussRow m hm H' := by
  set r := idealRowHom d (Ideal.span {m}) with hr
  have hr6 : r ^ 6 = 1 := by
    rw [hr, ← idealRowHom_argument_pow d 6 _ hm, idealRowHom_sixth_eq_mask d m hm]
    simp [coprimalityMask, hcop]
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr6
    norm_num at hr6
  have hcross1 : idealRowHom m (Ideal.span {d^2}) = r ^ 2 * sexticReciprocityPhase d m ^ 2 := by
    rw [← Ideal.span_singleton_pow, map_pow,
      CanonicalRowCompletion.idealRowHom_primary_reciprocity d m hpd hpm hd hm]
    ring
  have hcross2 : idealRowHom (d^2) (Ideal.span {m}) = r ^ 2 :=
    idealRowHom_argument_pow d 2 _ hm
  have hcube : idealRowHom (d^3) (Ideal.span {m}) = r ^ 3 :=
    idealRowHom_argument_pow d 3 _ hm
  have hsplit := sexticGauss_coprime_product (d^2) m (supported_sq d hd) hm hcop.pow_left (d * H')
  have hunit := sexticGauss_unit_scale m hm d H' hcop
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {d^2 * m}) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {d^2}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {m}) : ℝ) : ℂ) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  unfold gaussRow
  rw [sexticGauss_congr rfl _ (mul_ne_zero (supportedElement_ne_zero _ (supported_sq d hd))
    (supportedElement_ne_zero m hm)), hsplit, hunit, hroot, hcross1, hcross2, hcube,
    reciprocityPhase_sq d m hd hm]
  have hs1 : (Real.sqrt (Ideal.absNorm (Ideal.span {d^2}) : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt (Ideal.absNorm (Ideal.span {d^2}) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (supported_sq d hd).1))
    exact_mod_cast this.ne'
  have hs2 : (Real.sqrt (Ideal.absNorm (Ideal.span {m}) : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt (Ideal.absNorm (Ideal.span {m}) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        hm.1))
    exact_mod_cast this.ne'
  rw [← hr]
  field_simp

end
end QRH.MixedStep.Collision

#print axioms QRH.MixedStep.Collision.square_row
#print axioms QRH.MixedStep.Collision.square_twist
