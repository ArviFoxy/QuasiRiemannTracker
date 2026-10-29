/- Rigidity of twist-free transfers for the sextic Gauss sums `g(s, h) = sexticGauss s h` over `ℤ[ω]`.

A transfer identity `g(D n, 1) = c · g(D, 1) · g(n, D^s)`, required for every supported primary `n` coprime to
the split prime `D`, forces `6 ∣ 2 + s`: the dilation exponent of a twist-free transfer of a simple block is
`4 (mod 6)`, so Sil's `D⁴` is the cheapest one and no cheaper identity of this shape exists.

Proof: CRT (`sexticGauss_coprime_product`), sextic reciprocity (`idealRowHom_primary_reciprocity`) and the
dilation law (`sexticGauss_unit_scale`) reduce the identity to `ε(D, n) · χ_n(D)^{2+s} = c`
(`transfer_value`). At `n = 1` this gives `c = 1`; at `n = −q`, `q` a rational prime with `q ≡ 11 (mod 12)`
and `−q` a primitive root modulo `N(D)` (Dirichlet's theorem), `q` is inert, `ε = 1`, and `χ_{−q}(D)` is a
primitive sixth root of unity. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZero
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.UnitSexticWitness
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Fourier.TupleWeights
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles

set_option autoImplicit false

namespace QRH.ArviNewpowers.Rigidity
noncomputable section
open OAI OAI.SevenEighths
open ProbePhysical ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge QuadraticAllOddCRT CompletedGauss
local notation "O" => ActualEisensteinCubic.O

/-! ### Step A: the identity pins down `ε(D, n) · χ_n(D)^{2+s}` -/

theorem transfer_value (D n : O) (hD : Supported (Ideal.span {D})) (hn : Supported (Ideal.span {n}))
    (hDp : goodLambda ^ 2 ∣ D - 1) (hnp : goodLambda ^ 2 ∣ n - 1) (hcop : IsCoprime D n) (s : ℕ) (c : ℂ)
    (hid : sexticGauss (D * n) (mul_ne_zero (supportedElement_ne_zero D hD) (supportedElement_ne_zero n hn)) 1 =
      c * sexticGauss D (supportedElement_ne_zero D hD) 1 *
        sexticGauss n (supportedElement_ne_zero n hn) (D ^ s * 1))
    (hg : sexticGauss D (supportedElement_ne_zero D hD) 1 *
      sexticGauss n (supportedElement_ne_zero n hn) 1 ≠ 0) :
    sexticReciprocityPhase D n * idealRowHom D (Ideal.span {n}) ^ (2 + s) = c := by
  have hχ : idealRowHom D (Ideal.span {n}) ≠ 0 := idealRowHom_ne_zero_of_coprime n D hn hcop.symm
  rw [sexticGauss_coprime_product D n hD hn hcop, idealRowHom_primary_reciprocity D n hDp hnp hD hn,
    sexticGauss_unit_scale n hn (D ^ s) 1 hcop.symm.pow_right.symm, idealRowHom_argument_pow _ _ _ hn] at hid
  have h2 : (sexticReciprocityPhase D n * idealRowHom D (Ideal.span {n}) ^ (2 + s) - c) *
      (sexticGauss D (supportedElement_ne_zero D hD) 1 * sexticGauss n (supportedElement_ne_zero n hn) 1) = 0 := by
    have hs : idealRowHom D (Ideal.span {n}) ^ s ≠ 0 := pow_ne_zero _ hχ
    field_simp at hid
    rw [pow_add]
    linear_combination hid
  rcases mul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg

/-! ### Arithmetic of `ℤ[ω]` used for the test modulus `n = −q` -/

theorem finrank_O : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank]
  have : IsCyclotomicExtension {3} ℚ ActualEisensteinCubic.K := CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [IsCyclotomicExtension.finrank ActualEisensteinCubic.K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 3))]
  decide

theorem absNorm_natCast (m : ℕ) : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (m : O) = algebraMap ℤ O (m : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, finrank_O]
  simp

/-- A rational prime `q ≡ 2 (mod 3)` stays prime in `ℤ[ω]`. -/
theorem prime_natCast_of_mod_three {q : ℕ} (hq : q.Prime) (hmod : q % 3 = 2) : Prime (q : O) := by
  have hc := ShortDraftHeckeBridge.inert_count_of_mod_two hq hmod
  have hne : ((Ideal.span {(q : ℤ)}).primesOver O).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  obtain ⟨P, hP⟩ := hne
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hP.2
  have hn := ShortDraftHeckeBridge.absNorm_inert hq hmod P
  have hq0 : (q : O) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hmem : (q : O) ∈ P := by
    have h1 : ((q : ℤ)) ∈ P.under ℤ := by
      rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(q : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hle : Ideal.span {(q : O)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, absNorm_natCast, hn] at hnorm
  have hq2 : 0 < q ^ 2 := pow_pos hq.pos 2
  have hJ1 : Ideal.absNorm J = 1 := by
    have : q ^ 2 * 1 = q ^ 2 * Ideal.absNorm J := by rw [mul_one]; exact hnorm
    exact (Nat.eq_of_mul_eq_mul_left hq2 this).symm
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ1, Ideal.mul_top] at hJ
  have hprime : (Ideal.span {(q : O)}).IsPrime := by rw [hJ]; infer_instance
  exact (Ideal.span_singleton_prime hq0).mp hprime

/-- Divisibility of a rational integer by `x` forces `N(x) ∣ m²`. -/
theorem absNorm_dvd_sq {x : O} {m : ℕ} (h : x ∣ (m : O)) :
    Ideal.absNorm (Ideal.span {x}) ∣ m ^ 2 := by
  rw [← absNorm_natCast]
  exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_span_singleton).mpr h)

theorem supported_neg_natCast {q : ℕ} (h3 : q % 3 = 2) (h2 : q % 2 = 1) :
    Supported (Ideal.span {-(q : O)}) := by
  rw [Ideal.span_singleton_neg, supported_span_iff]
  constructor
  · intro hl
    have h := absNorm_dvd_sq hl
    rw [CubicEisenstein.absNorm_span_lambda] at h
    have : 3 ∣ q := (Nat.prime_three.dvd_mul.mp (by simpa [sq] using h)).elim id id
    omega
  · intro h2d
    have h' := absNorm_dvd_sq (x := ((2 : ℕ) : O)) (m := q) (by exact_mod_cast h2d)
    rw [absNorm_natCast] at h'
    have : 2 ∣ q := (Nat.prime_two.dvd_mul.mp
      (dvd_trans (by norm_num : 2 ∣ 2 ^ 2) (by simpa [sq] using h'))).elim id id
    omega

theorem primary_neg_natCast {q : ℕ} (h3 : q % 3 = 2) : goodLambda ^ 2 ∣ -(q : O) - 1 := by
  have h3' : (3 : ℕ) ∣ q + 1 := by omega
  obtain ⟨k, hk⟩ := h3'
  have : -(q : O) - 1 = (3 : O) * (-(k : O)) := by
    have hk' : ((q + 1 : ℕ) : O) = ((3 * k : ℕ) : O) := by rw [hk]
    push_cast at hk'
    linear_combination -hk'
  rw [this]
  exact (lambda_sq_dvd_three).trans (dvd_mul_right _ _)


/-! ### The test modulus: phases, primitive roots, Dirichlet -/

theorem residue_neg_natCast {q : ℕ} (h4 : q % 4 = 3) :
    ActualEisensteinCoordinates.residue (-(q : O)) = ((1 : ZMod 4), 0) := by
  have h : (-(q : O)) = ActualEisensteinCoordinates.eval (-(q : ℤ)) 0 := by
    simp [ActualEisensteinCoordinates.eval]
  rw [h, ActualEisensteinCoordinates.residue_eval]
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
  subst hk
  ext
  · push_cast
    have : (4 : ZMod 4) = 0 := rfl
    rw [this]; ring_nf; rfl
  · rfl

theorem phase_neg_right (D : O) (hD : Supported (Ideal.span {D})) {q : ℕ} (h4 : q % 4 = 3) :
    sexticReciprocityPhase D (-(q : O)) = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1 : ZMod 4), 0) = 1 := by decide
  simp only [sexticReciprocityPhase, residue_neg_natCast h4, ht _ (supported_residue_odd D hD), Int.cast_one]

theorem phase_neg_left (D : O) (hD : Supported (Ideal.span {D})) {q : ℕ} (h4 : q % 4 = 3) :
    sexticReciprocityPhase (-(q : O)) D = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1 : ZMod 4), 0) = 1 := by decide
  simp only [sexticReciprocityPhase, residue_neg_natCast h4]
  rw [quadraticRaySign_symm, ht _ (supported_residue_odd D hD), Int.cast_one]

theorem exists_generator_nat (p : ℕ) [hp : Fact p.Prime] :
    ∃ g : ℕ, g.Coprime p ∧ orderOf (g : ZMod p) = p - 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have ho : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  refine ⟨(u : ZMod p).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [ZMod.natCast_zmod_val, orderOf_units, ho]

/-- Dirichlet's theorem: a prime `q ≡ 11 (mod 12)` with `q ≡ −g (mod p)`, above `p`. -/
theorem exists_test_prime (p g : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g.Coprime p) :
    ∃ q : ℕ, q.Prime ∧ q % 12 = 11 ∧ p ∣ q + g ∧ p < q := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime 12 p := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> first | omega | exact absurd hp (by decide)
  let x := Nat.chineseRemainder hcop 11 (p - g % p)
  have hx12 : (x : ℕ) ≡ 11 [MOD 12] := x.2.1
  have hxp : (x : ℕ) ≡ p - g % p [MOD p] := x.2.2
  have hgz : (g : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hg.symm h)
  have hxz : ((x : ℕ) : ZMod p) = -(g : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hxp, Nat.cast_sub (Nat.mod_lt _ hp.pos).le,
      ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  have hxcop : Nat.Coprime x (12 * p) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hx12]; rfl
    · rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime]
      rw [Nat.Prime.coprime_iff_not_dvd hp, ← ZMod.natCast_eq_zero_iff, hxz, neg_eq_zero]
      exact hgz
  obtain ⟨q, hqgt, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq p (q := 12 * p) (a := x)
    (by positivity) hxcop
  refine ⟨q, hq, ?_, ?_, hqgt⟩
  · have := (Nat.ModEq.of_mul_right p hqmod).trans hx12
    exact this
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add,
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_mul_left 12 hqmod), hxz, neg_add_cancel]

/-! ### The prime modulus `D`: Gauss sum, residue field, sixth roots -/

theorem gauss_one_ne_zero (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p})) :
    sexticGauss p (supportedElement_ne_zero p hs) 1 ≠ 0 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  obtain ⟨hg, hc⟩ := supported_prime_data p hp hs
  have he := CenteredMomentAmplification.gauss_prime_power_one p hp hg hc 0
  simp only [zero_add, pow_one, ite_true] at he
  have hn := CenteredMomentAmplificationLocal.primeGauss_actual_norm_sq p hp hg hc
  have hN : (0 : ℝ) < Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  intro hz
  rw [← he, hz, norm_zero, zero_pow two_ne_zero] at hn
  linarith

theorem card_quotient (D : O) {p : ℕ} (hN : Ideal.absNorm (Ideal.span {D}) = p) :
    Nat.card (O ⧸ Ideal.span {D}) = p := by
  rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem orderOf_mk_natCast (D : O) (hD : Prime D) {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm (Ideal.span {D}) = p) (g : ℕ) :
    orderOf (Ideal.Quotient.mk (Ideal.span {D}) (g : O)) = orderOf (g : ZMod p) := by
  let : (Ideal.span {D}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hD.irreducible
  let : Field (O ⧸ Ideal.span {D}) := Ideal.Quotient.field _
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (O ⧸ Ideal.span {D}) = p := by
    rw [← Nat.card_eq_fintype_card]; exact card_quotient D hN
  have : CharP (O ⧸ Ideal.span {D}) p := charP_of_card_eq_prime hcard
  let f := ZMod.castHom (dvd_refl p) (O ⧸ Ideal.span {D})
  have hf : Function.Injective f := f.injective
  have hfg : f (g : ZMod p) = Ideal.Quotient.mk (Ideal.span {D}) (g : O) := by simp [f]
  rw [← hfg]
  exact orderOf_injective f.toMonoidHom hf _

theorem six_dvd_sub_one (D : O) (hD : Prime D) (hs : Supported (Ideal.span {D})) {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm (Ideal.span {D}) = p) : 6 ∣ p - 1 := by
  let : (Ideal.span {D}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hD.irreducible
  let : Field (O ⧸ Ideal.span {D}) := Ideal.Quotient.field _
  obtain ⟨hg, hc⟩ := supported_prime_data D hD hs
  have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {D}) hg hc
  have hcard : Fintype.card (O ⧸ Ideal.span {D}) = p := by
    rw [← Nat.card_eq_fintype_card]; exact card_quotient D hN
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hpow : (actualSextic (Ideal.span {D}) hg) ^ (p - 1) = 1 := by
    ext u
    rw [MulChar.pow_apply' _ hp1, MulChar.one_apply_coe, ← map_pow, ← hcard,
      FiniteField.pow_card_sub_one_eq_one _ u.ne_zero, map_one]
  rw [← ho]
  exact orderOf_dvd_of_pow_eq_one hpow

/-! ### The theorem -/

/-- **No cheaper twist-free transfer.** If `g(D n, 1) = c · g(D, 1) · g(n, D^s)` for every supported primary
`n` coprime to the split prime `D` (`N(D) = p` prime), then `6 ∣ 2 + s`. -/
theorem no_cheaper_transfer (D : O) (hDprime : Prime D) (hD : Supported (Ideal.span {D}))
    (hDp : goodLambda ^ 2 ∣ D - 1) {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm (Ideal.span {D}) = p)
    (s : ℕ) (c : ℂ)
    (hid : ∀ n : O, ∀ hn : Supported (Ideal.span {n}), goodLambda ^ 2 ∣ n - 1 → IsCoprime D n →
      sexticGauss (D * n) (mul_ne_zero (supportedElement_ne_zero D hD) (supportedElement_ne_zero n hn)) 1 =
        c * sexticGauss D (supportedElement_ne_zero D hD) 1 *
          sexticGauss n (supportedElement_ne_zero n hn) (D ^ s * 1)) :
    6 ∣ 2 + s := by
  let : (Ideal.span {D}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hDprime.irreducible
  obtain ⟨hgD, hcD⟩ := supported_prime_data D hDprime hD
  have hGD := gauss_one_ne_zero D hDprime hD
  have h6 := six_dvd_sub_one D hDprime hD hp hN
  have hp7 : 7 ≤ p := by
    obtain ⟨t, ht⟩ := h6
    have := hp.two_le
    rcases t with _ | t
    · omega
    · omega
  -- `n = 1` fixes `c = 1`
  have h1s : Supported (Ideal.span {(1 : O)}) := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact CenteredMomentAddedZero.supported_one_ideal
  have hG1 : sexticGauss 1 (supportedElement_ne_zero 1 h1s) 1 = 1 := sexticGauss_one 1
  have hc : c = 1 := by
    have hv := transfer_value D 1 hD h1s hDp (by simp) isCoprime_one_right s c
      (hid 1 h1s (by simp) isCoprime_one_right) (by rw [hG1, mul_one]; exact hGD)
    rw [sexticReciprocityPhase_one_right D hD, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one,
      one_pow, one_mul] at hv
    exact hv.symm
  -- the test modulus `n = −q`
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hgcop, hgord⟩ := exists_generator_nat p
  obtain ⟨q, hq, hq12, hpq, hqgt⟩ := exists_test_prime p g hp (by omega) hgcop
  have hq3 : q % 3 = 2 := by omega
  have hq4 : q % 4 = 3 := by omega
  have hq2 : q % 2 = 1 := by omega
  have hns := supported_neg_natCast hq3 hq2
  have hnp := primary_neg_natCast hq3
  have hnprime : Prime (-(q : O)) := (prime_natCast_of_mod_three hq hq3).neg
  have hndvd : ¬ D ∣ -(q : O) := by
    intro hdvd
    have h := absNorm_dvd_sq (x := D) (m := q) ((dvd_neg).mp hdvd)
    rw [hN] at h
    have hpq' : p ∣ q := hp.dvd_of_dvd_pow h
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq'
    omega
  have hcop : IsCoprime D (-(q : O)) := (hDprime.irreducible.coprime_iff_not_dvd).mpr hndvd
  have hGn := gauss_one_ne_zero (-(q : O)) hnprime hns
  have hv := transfer_value D (-(q : O)) hD hns hDp hnp hcop s c (hid _ hns hnp hcop) (mul_ne_zero hGD hGn)
  rw [phase_neg_right D hD hq4, one_mul, hc,
    idealRowHom_primary_reciprocity (-(q : O)) D hnp hDp hns hD, phase_neg_left D hD hq4, one_mul,
    idealRowHom_prime _ (Ideal.span {D}) hgD] at hv
  -- `χ_{−q}(D) = ι(ζ)`, `ζ = sexticChar (−q mod D)`, a sixth root of unity reducing to `(−q)^{(p−1)/6}`
  let : Field (O ⧸ Ideal.span {D}) := Ideal.Quotient.field _
  set x := Ideal.Quotient.mk (Ideal.span {D}) (-(q : O)) with hx
  have hx0 : x ≠ 0 := by
    rw [hx, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hndvd
  have hζ : (ActualEisensteinCubic.sexticChar (Ideal.span {D}) hgD x) ^ (2 + s) = 1 := by
    apply ConcreteTraceCRT.eisEmbedding_injective
    rw [map_pow, map_one]
    exact hv
  have hred := ActualEisensteinCubic.sexticChar_reduce_unit (Ideal.span {D}) hgD hcD (Units.mk0 x hx0)
  rw [Units.val_mk0, card_quotient D hN] at hred
  have hxpow : x ^ ((p - 1) / 6 * (2 + s)) = 1 := by
    rw [pow_mul, ← hred, ← map_pow, hζ, map_one]
  -- `−q ≡ g (mod D)`, a generator: order `p − 1`
  have hxg : x = Ideal.Quotient.mk (Ideal.span {D}) (g : O) := by
    rw [hx, Ideal.Quotient.eq]
    have hpD : (p : O) ∈ Ideal.span {D} := by
      have := Ideal.absNorm_mem (Ideal.span {D})
      rwa [hN] at this
    obtain ⟨t, ht⟩ := hpq
    have : -(q : O) - (g : O) = (p : O) * (-(t : O)) := by
      have ht' : ((q + g : ℕ) : O) = ((p * t : ℕ) : O) := by rw [ht]
      push_cast at ht'
      linear_combination -ht'
    rw [this]
    exact Ideal.mul_mem_right _ _ hpD
  have hord : orderOf x = p - 1 := by
    rw [hxg, orderOf_mk_natCast D hDprime hp hN g, hgord]
  have hdvd := orderOf_dvd_of_pow_eq_one hxpow
  rw [hord] at hdvd
  obtain ⟨t, ht⟩ := h6
  have htpos : 0 < t := by omega
  rw [ht, Nat.mul_div_cancel_left t (by norm_num : 0 < 6)] at hdvd
  rw [mul_comm 6 t] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left htpos hdvd

end
end QRH.ArviNewpowers.Rigidity

#print axioms QRH.ArviNewpowers.Rigidity.no_cheaper_transfer
