/-
Multiplicativity of the normalized Gauss phase of the sextic row over coprime
sixth-power-free supported ideals.

`SievePrimitive.modulus I` is `finitePrimeModulus` of the prime support of `I`, i.e. the
baseline `idealGenerator` (a `Classical.choose` generator) of `I.radical`.  Hence
`modulus (I*J) = modulus I * modulus J` is not derivable: the two sides generate the same
ideal `I.radical * J.radical`, so they differ by a unit `u` of `O`.  The unit enters the exact
identity through the sextic row value `idealRowHom u (I*J)` (a sixth root of unity), and when
the two generators happen to agree one gets the clean identity

  phase (I*J) = idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I * phase J.

Main statements:
* `phase_mul_unit`                : exact identity for any unit `u` with
                                     `modulus I * modulus J * u = modulus (I*J)`;
* `phase_mul`                     : the same with `u` produced existentially;
* `phase_mul_of_modulus_eq`       : the clean identity under `modulus (I*J) = modulus I * modulus J`;
* `phase_mul_of_norm_mod_thirty_six` : the clean identity whenever `N(I*J) ≡ 1 (mod 36)`;
* `phase_mul_root_of_unity`       : the identity up to a sixth root of unity `ζ`, `‖ζ‖ = 1`.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveGaussPairs

set_option autoImplicit false
namespace QRH.ArviPrimeDilation
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve
open Candidate.FourthPower Candidate.FourthPower.SexticSieve
open Candidate.FourthPower.SievePrimitive Candidate.FourthPower.SieveGaussPairs
open ConcreteBreveE
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-! ### Supports, power-freeness and moduli of a coprime product -/

theorem supported_mul_of_supported {I J : Id} (hI : Supported I) (hJ : Supported J) :
    Supported (I * J) := (supported_mul_iff I J).mpr ⟨hI, hJ⟩

theorem prime_isCoprime_of_not_dvd {P I : Id} (hP : Prime P) (h : ¬ P ∣ I) : IsCoprime P I := by
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hnle : ¬ I ≤ P := fun hle => h (Ideal.dvd_iff_le.mpr hle)
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (codisjoint_iff.mp (hmax.out.not_le_iff_codisjoint.mp hnle))

/-- A product of coprime sixth-power-free ideals is sixth-power-free. -/
theorem powerFree_mul {I J : Id} (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J)
    (hcop : IsCoprime I J) : PowerFree 6 (I * J) := by
  intro P hP hd
  by_cases h1 : P ∣ I
  · have h2 : ¬ P ∣ J := fun h2 => hP.not_isUnit (hcop.isUnit_of_dvd' h1 h2)
    apply hfI P hP
    exact ((prime_isCoprime_of_not_dvd hP h2).pow_left).dvd_of_dvd_mul_right hd
  · apply hfJ P hP
    exact ((prime_isCoprime_of_not_dvd hP h1).pow_left).dvd_of_dvd_mul_left hd

/-- The radical moduli of coprime ideals generate the radical of the product. -/
theorem span_modulus_mul {I J : Id} (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) :
    Ideal.span {modulus (I * J)} = Ideal.span {modulus I} * Ideal.span {modulus J} := by
  have hIJ := supported_mul_of_supported hI hJ
  rw [span_modulus _ hIJ.1, span_modulus I hI.1, span_modulus J hJ.1, Ideal.radical_mul]
  exact (Ideal.mul_eq_inf_of_isCoprime (SieveCoupling.radical_coprime I J hcop)).symm

/-- The moduli of coprime ideals are coprime. -/
theorem modulus_coprime {I J : Id} (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) :
    IsCoprime (Ideal.span {modulus I}) (Ideal.span {modulus J}) := by
  rw [span_modulus I hI.1, span_modulus J hJ.1]
  exact SieveCoupling.radical_coprime I J hcop

/-- The moduli `modulus (I*J)` and `modulus I * modulus J` differ by a unit of `O`. -/
theorem exists_modulus_unit {I J : Id} (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) :
    ∃ u : Oˣ, modulus I * modulus J * (u : O) = modulus (I * J) := by
  have h : Ideal.span {modulus I * modulus J} = Ideal.span {modulus (I * J)} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_modulus_mul hI hJ hcop]
  exact Ideal.span_singleton_eq_span_singleton.mp h

/-! ### The Gauss sum against the generator `modulus (I*J)` versus the product sum -/

/-- The normalized Gauss sum of the product character at the generator `c = a * b * u` equals
`idealRowHom u (I*J)` times the baseline product Gauss sum over `O ⧸ (a) * (b)`. -/
theorem phase_eq_unit_mul_product (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (u : Oˣ) (hu : modulus I * modulus J * (u : O) = modulus (I * J)) :
    phase (I * J) (supported_mul_of_supported hI hJ) =
      idealRowHom (u : O) (I * J) *
        normalizedTraceGaussProduct (modulus I) (modulus J) (modulus_ne_zero I)
          (modulus_ne_zero J) (character I hI) (character J hJ) := by
  have hIJ := supported_mul_of_supported hI hJ
  have hfIJ := powerFree_mul hfI hfJ hcop
  have ha : modulus I ≠ 0 := modulus_ne_zero I
  have hb : modulus J ≠ 0 := modulus_ne_zero J
  have hc : modulus (I * J) ≠ 0 := modulus_ne_zero (I * J)
  have hspan := span_modulus_mul hI hJ hcop
  let : Finite (O ⧸ Ideal.span {modulus (I * J)}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {modulus (I * J)}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {modulus (I * J)}) ≃+*
      (O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) := Ideal.quotEquivOfEq hspan
  have hnorm : ‖eisEmbedding (modulus (I * J))‖ = ‖eisEmbedding (modulus I * modulus J)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [eisEmbedding_norm_sq_eq_absNorm_span, eisEmbedding_norm_sq_eq_absNorm_span, hspan,
      Ideal.span_singleton_mul_span_singleton]
  rw [← trace_phase (I * J) hIJ]
  dsimp only [normalizedTraceGauss, normalizedTraceGaussProduct]
  rw [hnorm, ← mul_div_assoc]
  congr 1
  simp only [gaussSum]
  -- reindex the sum over `O ⧸ (a) * (b)` by multiplication with the unit `u`
  let ū : (O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J}))ˣ :=
    Units.map (Ideal.Quotient.mk ((Ideal.span {modulus I}) * (Ideal.span {modulus J}))).toMonoidHom u
  let σ : (O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) ≃
      (O ⧸ Ideal.span {modulus (I * J)}) := (Units.mulLeft ū).trans e.symm.toEquiv
  rw [← Equiv.sum_comp σ, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hσ : σ (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ ((u : O) * w) := by
    change e.symm ((ū : O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) *
      Ideal.Quotient.mk _ w) = _
    rw [RingEquiv.symm_apply_eq]
    have hū : (ū : O ⧸ (Ideal.span {modulus I}) * (Ideal.span {modulus J})) =
        Ideal.Quotient.mk _ (u : O) := rfl
    rw [hū, ← map_mul]
    exact (Ideal.quotEquivOfEq_mk hspan _).symm
  rw [hσ]
  rw [character_mk (I * J) hIJ hfIJ, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    character_mk I hI hfI, character_mk J hJ hfJ, idealRowHom_argument_mul]
  simp only [eisTraceModChar, eisTraceProdChar, IdealGaussCRT.traceModChar_mk,
    IdealGaussCRT.traceProdChar_mk]
  have hu0 : eisEmbedding (u : O) ≠ 0 := eisEmbedding_ne_zero u.ne_zero
  have hψ : eisEmbedding ((u : O) * w) / (eisEmbedding (modulus (I * J)) * eisLam) =
      eisEmbedding w / (eisEmbedding (modulus I * modulus J) * eisLam) := by
    rw [← hu, map_mul, map_mul, map_mul]
    have hab : eisEmbedding (modulus I) * eisEmbedding (modulus J) ≠ 0 :=
      mul_ne_zero (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
    field_simp [eisLam_ne_zero]
  rw [hψ, map_mul (idealRowHom (u : O)) I J, map_mul (idealRowHom w) I J]
  ring

/-! ### Multiplicativity of the phase -/

/-- Exact multiplicativity of the phase, with the unit discrepancy between the generator
`modulus (I*J)` of `(I*J).radical` and the generator `modulus I * modulus J` of
`I.radical * J.radical` made explicit. -/
theorem phase_mul_unit (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (h : Supported (I * J))
    (u : Oˣ) (hu : modulus I * modulus J * (u : O) = modulus (I * J)) :
    phase (I * J) h = idealRowHom (u : O) (I * J) *
      (idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I hI * phase J hJ) := by
  rw [show phase (I * J) h = phase (I * J) (supported_mul_of_supported hI hJ) from rfl,
    phase_eq_unit_mul_product I J hI hJ hfI hfJ hcop u hu,
    normalizedTraceGaussProduct_crt _ _ _ _ (modulus_coprime hI hJ hcop), trace_phase,
    trace_phase, character_mk I hI hfI, character_mk J hJ hfJ]

/-- The unit discrepancy is a sixth root of unity. -/
theorem idealRowHom_unit_pow_six (K : Id) (hK : Supported K) (u : Oˣ) :
    (idealRowHom (u : O) K) ^ 6 = 1 := by
  rw [← idealRowHom_argument_pow _ 6 K hK, CanonicalUnitEuler.unit_pow_six u]
  exact idealRowHom_one_supported K hK

theorem norm_idealRowHom_unit (K : Id) (hK : Supported K) (u : Oˣ) :
    ‖idealRowHom (u : O) K‖ = 1 := by
  have h := congrArg norm (idealRowHom_unit_pow_six K hK u)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

/-- Multiplicativity of the phase, with the unit produced existentially. -/
theorem phase_mul (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (h : Supported (I * J)) :
    ∃ u : Oˣ, modulus I * modulus J * (u : O) = modulus (I * J) ∧
      phase (I * J) h = idealRowHom (u : O) (I * J) *
        (idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I hI * phase J hJ) := by
  obtain ⟨u, hu⟩ := exists_modulus_unit hI hJ hcop
  exact ⟨u, hu, phase_mul_unit I J hI hJ hfI hfJ hcop h u hu⟩

/-- The clean identity, when the two generators of the radical agree. -/
theorem phase_mul_of_modulus_eq (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (h : Supported (I * J)) (hmod : modulus (I * J) = modulus I * modulus J) :
    phase (I * J) h =
      idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I hI * phase J hJ := by
  rw [phase_mul_unit I J hI hJ hfI hfJ hcop h 1 (by rw [hmod]; simp)]
  have h1 : idealRowHom ((1 : Oˣ) : O) (I * J) = 1 := by
    simpa using idealRowHom_one_supported (I * J) h
  rw [h1, one_mul]

/-- Explicit value of the unit discrepancy (Euler criterion for units). -/
theorem idealRowHom_unit_eq (K : Id) (hK : Supported K) (u : Oˣ) :
    idealRowHom (u : O) K = eisEmbedding ((u : O) ^ ((Ideal.absNorm K - 1) / 6)) :=
  CanonicalUnitEuler.idealRowHom_unit_norm u K hK.1 (supported_factors_good K hK)

/-- The unit discrepancy vanishes when `N(K) ≡ 1 (mod 36)`, whatever the unit is. -/
theorem idealRowHom_unit_eq_one (K : Id) (hK : Supported K) (u : Oˣ)
    (hN : Ideal.absNorm K % 36 = 1) : idealRowHom (u : O) K = 1 := by
  rw [idealRowHom_unit_eq K hK u]
  have hk : (Ideal.absNorm K - 1) / 6 = 6 * ((Ideal.absNorm K - 1) / 36) := by omega
  rw [hk, pow_mul, CanonicalUnitEuler.unit_pow_six u, one_pow, map_one]

/-- The clean identity holds for every choice of the two generators whenever
`N(I*J) ≡ 1 (mod 36)`. -/
theorem phase_mul_of_norm_mod_thirty_six (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (h : Supported (I * J)) (hN : Ideal.absNorm (I * J) % 36 = 1) :
    phase (I * J) h =
      idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I hI * phase J hJ := by
  obtain ⟨u, -, hu⟩ := phase_mul I J hI hJ hfI hfJ hcop h
  rw [hu, idealRowHom_unit_eq_one (I * J) h u hN, one_mul]

/-- Multiplicativity of the phase up to a sixth root of unity of modulus one. -/
theorem phase_mul_root_of_unity (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J)
    (h : Supported (I * J)) :
    ∃ ζ : ℂ, ζ ^ 6 = 1 ∧ ‖ζ‖ = 1 ∧
      phase (I * J) h = ζ *
        (idealRowHom (modulus J) I * idealRowHom (modulus I) J * phase I hI * phase J hJ) := by
  obtain ⟨u, -, hu⟩ := phase_mul I J hI hJ hfI hfJ hcop h
  exact ⟨_, idealRowHom_unit_pow_six (I * J) h u, norm_idealRowHom_unit (I * J) h u, hu⟩

/-! ### Why the clean identity cannot be proved without a hypothesis on the generators -/

theorem phase_one (h : Supported (1 : Id)) : phase (1 : Id) h = 1 := by
  have hemp : IsEmpty (PrimeIndex (1 : Id)) := by
    refine ⟨fun P => ?_⟩
    have hP : P.val ∈ UniqueFactorizationMonoid.normalizedFactors (1 : Id) :=
      Multiset.mem_toFinset.mp P.property
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact Multiset.notMem_zero _ hP
  let : IsEmpty (PrimeIndex (1 : Id)) := hemp
  exact canonicalNormalizedGauss_of_isEmpty (fun P : PrimeIndex (1 : Id) => P.val)
    (primeIndex_pairwise_coprime 1) (good 1 h) (exponent 1)

/-- The unit ideal is supported. -/
theorem supported_one : Supported (1 : Id) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
  exact absurd hP (Multiset.notMem_zero _)

/-- At `J = 1` the requested literal identity is equivalent to `idealRowHom (modulus 1) I = 1`,
where `modulus 1 = idealGenerator ⊤` is an unspecified unit. -/
theorem literal_identity_at_one_iff (I : Id) (hI : Supported I) (hfI : PowerFree 6 I)
    (h : Supported (I * 1)) :
    phase (I * 1) h = idealRowHom (modulus (1 : Id)) I * idealRowHom (modulus I) (1 : Id) *
        phase I hI * phase (1 : Id) supported_one ↔
      idealRowHom (modulus (1 : Id)) I = 1 := by
  have key : ∀ (K : Id) (hK : Supported K) (hKI : K = I), phase K hK = phase I hI := by
    intro K hK hKI
    subst hKI
    rfl
  rw [key (I * 1) h (mul_one I), phase_one supported_one, map_one, mul_one, mul_one]
  have hn : phase I hI ≠ 0 := by
    intro h0
    have := phase_norm I hI hfI
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  constructor
  · intro hh
    have : (idealRowHom (modulus (1 : Id)) I - 1) * phase I hI = 0 := by
      linear_combination -hh
    rcases mul_eq_zero.mp this with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hn
  · intro hh
    rw [hh, one_mul]

end
end QRH.ArviPrimeDilation

#print axioms QRH.ArviPrimeDilation.phase_mul_unit
#print axioms QRH.ArviPrimeDilation.phase_mul
#print axioms QRH.ArviPrimeDilation.phase_mul_of_modulus_eq
#print axioms QRH.ArviPrimeDilation.phase_mul_root_of_unity
#print axioms QRH.ArviPrimeDilation.phase_mul_of_norm_mod_thirty_six
#print axioms QRH.ArviPrimeDilation.literal_identity_at_one_iff
