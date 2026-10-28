/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1, scalar inputs of the energy reduction.
The Gauss norm lemmas `prime_gauss_norm_le_one` … `prime_product_gauss_norm` are adapted from
Candidate.FourthPower.MixedSupplierPositive (PR76, Copyright (c) 2026 Sil. Apache-2.0).
Modified by Sil (2026-10-26): copied verbatim (namespace changed) so that the cube-free
second step does not import the replaced supplier lane; the injectivity lemma uses
`prime_dvd_prime_eq` of `ConcreteResidual2`.

* `‖g(∏_j P_j; k)‖ ≤ 1` for distinct primes (`prime_product_gauss_norm`), `‖ξ(a)‖ ≤ 1`.
* `ball_le_scaled`, `sublattice_energy_le`: the rows `k ↦ d·k` of a Gauss polynomial in the
  `K`-ball are dominated by its Gauss energy in the `K'`-ball, `K' ≥ 2K‖d‖²`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteResidual4
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.CorrespondencePullback
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss RayFourExpansion CenteredMomentFixedRay CenteredMomentFirstColumns
open CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentLiveDomain
open ConcretePrimeRowBridge ActualEisensteinCubic CubicEisenstein
open ProbePhysical ProbePrimePower CenteredMomentAmplification CenteredMomentAmplificationLocal
open CenteredMomentUnequal CenteredMomentSupportedCorrelation
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open QRH.DensitySplitThird.CubeFree.FP.MixedCommonRestriction
open QRH.DensitySplitThird.CubeFree.FP.MixedSelectedCommon (primary_supported idealGauss)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-! ### Gauss norms (verbatim from FP MixedSupplierPositive) -/

theorem prime_gauss_norm_le_one (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (k : O) : ‖gaussRow p hs k‖≤1 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  obtain ⟨hg,hc⟩ := supported_prime_data p hp hs
  have hχ : actualSextic (Ideal.span {p}) hg≠1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have hraw : ‖sexticGauss p (supportedElement_ne_zero p hs) k‖^2≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    by_cases hk : p∣k
    · have hz := primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero
        (actualSextic (Ideal.span {p}) hg) hχ 0 k hk
      simp only [pow_zero,one_mul] at hz
      have he := sexticGauss_prime_power p hp hg 0 k
      simp only [zero_add,pow_one] at he
      rw [he,hz,norm_zero,zero_pow (by decide : 2≠0)]
      exact Nat.cast_nonneg _
    · have hu := gauss_unit_scale_norm p hs k 1
        (hp.irreducible.coprime_iff_not_dvd.mpr hk).symm
      have he := gauss_prime_power_one p hp hg hc 0
      simp only [zero_add,pow_one,ite_true] at he
      have hnorm : ‖sexticGauss p (supportedElement_ne_zero p hs) k‖=
          ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1‖ := by
        simpa only [mul_one,he] using hu
      rw [hnorm,primeGauss_actual_norm_sq p hp hg hc]
  have hN : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have hn : ‖gaussRow p hs k‖^2≤1 := by
    rw [gaussRow,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      div_pow,Real.sq_sqrt hN.le]
    exact (div_le_one hN).mpr hraw
  nlinarith [norm_nonneg (gaussRow p hs k)]

theorem primary_prime_gauss_norm (P : Id) (hP : Prime P) (k : O) :
    ‖primaryGaussRow P k‖≤1 := by
  by_cases hs : Supported P
  · have hp : Prime (primaryGenerator P) :=
      (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P hs)).mp (by
        rw [primary_span_supported P hs]
        exact Ideal.isPrime_of_prime hP)
    rw [primaryGaussRow_supported P hs]
    exact prime_gauss_norm_le_one _ hp (primary_supported P hs) k
  · simp only [primaryGaussRow,dif_neg hs,norm_zero,zero_le_one]

theorem normalized_gauss_coprime_product (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : IsCoprime a b) (k : O) :
    gaussRow (a*b) (supported_mul_elements a b ha hb) k =
      idealRowHom b (Ideal.span {a})*idealRowHom a (Ideal.span {b})*
        gaussRow a ha k*gaussRow b hb k := by
  unfold gaussRow
  rw [sexticGauss_coprime_product a b ha hb hcop k,
    ←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _),Complex.ofReal_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem primary_gauss_coprime_bound (I J : Id) (hc : IsCoprime I J) (k : O)
    (hI : ‖primaryGaussRow I k‖≤1) (hJ : ‖primaryGaussRow J k‖≤1) :
    ‖primaryGaussRow (I*J) k‖≤1 := by
  by_cases hs : Supported (I*J)
  · obtain ⟨hsI,hsJ⟩ := (supported_mul_iff _ _).mp hs
    have hcop : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
      rw [←Ideal.isCoprime_span_singleton_iff,primary_span_supported I hsI,
        primary_span_supported J hsJ]
      exact hc
    have he : primaryGaussRow (I*J) k=
        idealRowHom (primaryGenerator J) I*idealRowHom (primaryGenerator I) J*
          primaryGaussRow I k*primaryGaussRow J k := by
      rw [primaryGaussRow_supported _ hs,primaryGaussRow_supported _ hsI,
        primaryGaussRow_supported _ hsJ]
      simpa only [idealGauss,primaryGenerator_mul,
        primary_span_supported I hsI,primary_span_supported J hsJ] using
        normalized_gauss_coprime_product (primaryGenerator I) (primaryGenerator J)
          (primary_supported I hsI) (primary_supported J hsJ) hcop k
    rw [he,norm_mul,norm_mul,norm_mul]
    exact (mul_le_mul
      (mul_le_mul ((mul_le_mul (idealRowHom_norm _ _) (idealRowHom_norm _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hI
        (norm_nonneg _) zero_le_one)
      hJ (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp only [primaryGaussRow,dif_neg hs,norm_zero,zero_le_one]

theorem prime_product_gauss_norm {ι : Type*} (P : ι→Id)
    (hP : ∀i,Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) (k : O) :
    ‖primaryGaussRow (∏i∈S,P i) k‖≤1 := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty,primaryGaussRow,
        dif_pos CenteredMomentAddedZero.supported_one_ideal,primaryGenerator_one,
        gaussRow,sexticGauss_one,Ideal.span_singleton_one,←Ideal.one_eq_top,
        map_one,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,div_one,norm_one,le_refl]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      have hc : IsCoprime (P i) (∏j∈S,P j) := by
        apply IsCoprime.prod_right
        intro j hj
        apply (prime_coprime ⟨P i,hP i⟩ (P j)).mpr
        intro hd
        have heij := hinj (prime_dvd_prime_eq (hP i) (hP j) hd)
        exact hi (by simpa only [heij] using hj)
      exact primary_gauss_coprime_bound _ _ hc k (primary_prime_gauss_norm _ (hP i) k) ih

/-! ### Ray characters -/

theorem rayCharacter_norm_le (χ : RayCharacter) (a : O) : ‖rayCharacter χ a‖ ≤ 1 := by
  unfold rayCharacter
  by_cases hx : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
  · obtain ⟨u, hu⟩ := hx
    rw [← hu]
    have hpow : (χ u)^(Fintype.card RayRingˣ) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have hn : ‖χ u‖^(Fintype.card RayRingˣ) = 1 := by rw [← norm_pow, hpow, norm_one]
    have hpos : Fintype.card RayRingˣ ≠ 0 := Fintype.card_ne_zero
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).mp hn)
  · rw [MulChar.map_nonunit χ hx, norm_zero]; exact zero_le_one

/-! ### Scaled rows -/

theorem ball_le_scaled (K K' M x : ℝ) (hK : 0 < K) (hK' : 0 < K') (hM : 0 ≤ M) (hx : 0 ≤ x)
    (h : 2 * K * M ≤ K') : (ballProfile (x / K)).re ≤ (ballProfile (M * x / K')).re := by
  by_cases hb : ballProfile (x / K) = 0
  · rw [hb, Complex.zero_re]; exact ballProfile_nonneg _
  · have hlt := CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper (x / K)
      (div_nonneg hx hK.le) hb
    have hx2 : x < 2 * K := by rwa [div_lt_iff₀ hK] at hlt
    have hMx : M * x ≤ K' := by nlinarith
    rw [ballProfile_one _ (div_nonneg (mul_nonneg hM hx) hK'.le) ((div_le_one hK').mpr hMx),
      Complex.one_re]
    exact ballProfile_le_one _

theorem emb_mul_sq (d k : O) :
    ‖ConcreteTraceCRT.eisEmbedding (d * k)‖^2 =
      ‖ConcreteTraceCRT.eisEmbedding d‖^2 * ‖ConcreteTraceCRT.eisEmbedding k‖^2 := by
  rw [map_mul, norm_mul, mul_pow]

/-- **Sublattice rows.** -/
theorem sublattice_energy_le {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (d : O) (hd : d ≠ 0)
    (K K' : ℝ) (hK : 0 < K) (hK' : 0 < K')
    (hKK : 2 * K * ‖ConcreteTraceCRT.eisEmbedding d‖^2 ≤ K') (rows : Finset O) :
    (∑ k ∈ rows, ‖gaussPolynomial S a ha c (d * k)‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re) ≤
      (gaussEnergy S a ha c ballProfile K').re := by
  have hinj : Set.InjOn (fun k : O => d * k) rows := fun x _ y _ h => mul_left_cancel₀ hd h
  calc (∑ k ∈ rows, ‖gaussPolynomial S a ha c (d * k)‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re)
      ≤ ∑ k ∈ rows, ‖gaussPolynomial S a ha c (d * k)‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding (d * k)‖^2 / K')).re := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [emb_mul_sq]
        exact ball_le_scaled K K' _ _ hK hK' (sq_nonneg _) (sq_nonneg _) hKK
    _ = ∑ z ∈ rows.image (fun k : O => d * k), ‖gaussPolynomial S a ha c z‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / K')).re :=
        (Finset.sum_image (f := fun z => ‖gaussPolynomial S a ha c z‖^2 *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / K')).re) hinj).symm
    _ ≤ _ := finite_weighted_le_gaussEnergy S a ha c ballProfile K' hK'
        (fun z => ballProfile_nonneg _) _

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
