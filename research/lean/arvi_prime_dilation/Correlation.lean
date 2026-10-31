/-
The canonical phase of a squarefree supported ideal, its exact multiplicativity, and the
correlation bound for slot convolutions.

`SievePrimitive.phase I hI` is the normalized Gauss sum of the sextic row of `I`, taken against the
generator `modulus I` of `I.radical`, which is only a `Classical.choose` generator.  For a squarefree
supported `I` the radical is `I` itself, so `modulus I` and the primary generator
`primaryGenerator I` generate the same ideal and differ by a unit `unitOf I`.  Removing that unit
from the phase,

  `phaseCan I = star (idealRowHom (unitOf I) I) * phase I`,

gives a phase of modulus one which is exactly multiplicative over coprime squarefree supported
ideals:

  `phaseCan (I*J) = idealRowHom (pg J) I * idealRowHom (pg I) J * phaseCan I * phaseCan J`.

Together with sextic reciprocity (taken from Sil's `SieveOperator.row_reciprocity`, i.e. the
baseline `idealRowHom_ideal_reciprocity`, whose sign `SieveOperator.phase (ray I) (ray R)` is the
sign `recSign` of the residue classes of the primary generators modulo `4`) and the sieve bound
`bilinear_sieve_squarefree`, this gives the correlation bound `correlation_bound` for the slot
convolutions `∑_s ∑_q α_s a_q conj (phaseCan (s q)) (k / s q)_6`.

Main statements:
* `exists_unit_modulus_eq`     : `modulus I = u * primaryGenerator I` for squarefree supported `I`;
* `unitOf`, `modulus_eq_unitOf_mul`, `phaseCan`, `phase_eq_unit_mul_phaseCan`;
* `norm_phaseCan`              : `‖phaseCan I‖ = 1`;
* `phaseCan_mul`               : exact multiplicativity over coprime squarefree supported ideals;
* `slot_term_eq`               : the coupling of two coprime slots is a sign times `conj rowValue (q^2) s`;
* `class_split_bound`          : the bilinear bound after twisting by a weight depending on a class of `q`;
* `correlation_bound`          : the correlation bound, with a constant depending on `ε` only
                                 (`phaseCan` extended by `0`, see `phaseCanAll`);
* `correlation_bound_of_eq`    : the same for an arbitrary phase function agreeing with `phaseCan`.
-/
import Submissions.arvi_prime_dilation.PhaseMul
import Submissions.arvi_prime_dilation.Bilinear

set_option autoImplicit false
namespace QRH.ArviPrimeDilation
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve
open Candidate.FourthPower Candidate.FourthPower.SexticSieve
open Candidate.FourthPower.SievePrimitive Candidate.FourthPower.SieveGaussPairs
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-! ### Squarefree supported ideals: the radical modulus is the primary generator up to a unit -/

/-- A `PowerFree n` ideal has all prime multiplicities `< n`. -/
theorem exponent_lt_of_powerFree (n : ℕ) (I : Id) (hI : Supported I) (hf : PowerFree n I)
    (P : PrimeIndex I) : exponent I P < n := by
  by_contra! hn
  apply hf P.val (UniqueFactorizationMonoid.prime_of_normalized_factor _
    (Multiset.mem_toFinset.mp P.property))
  apply (pow_dvd_pow P.val hn).trans
  dsimp [exponent]
  rw [Multiset.pow_count]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)).trans
    (dvd_of_eq (Ideal.prod_normalizedFactors_eq_self hI.1))

/-- A squarefree (`PowerFree 2`) supported ideal is its own radical. -/
theorem radical_eq_of_squarefree (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    I.radical = I := by
  have h1 := Candidate.FourthPower.SieveCoupling.normal_form I hI.1
  have h2 : Candidate.FourthPower.SieveCoupling.sharp I = 1 := by
    unfold Candidate.FourthPower.SieveCoupling.sharp
    apply Finset.prod_eq_one
    intro P _
    have h3 : exponent I P = 1 := by
      have h4 := exponent_lt_of_powerFree 2 I hI hf P
      have h5 := exponent_pos I P
      omega
    rw [h3]
    simp
  rw [h2, mul_one] at h1
  exact h1

/-- For a squarefree supported `I`, `modulus I` and the primary generator differ by a unit. -/
theorem exists_unit_modulus_eq (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    ∃ u : Oˣ, modulus I = (u : O) * primaryGenerator I := by
  have hpg : primaryGenerator I ≠ 0 := supported_primaryGenerator_ne_zero I hI
  have h : Ideal.span {primaryGenerator I} = Ideal.span {modulus I} := by
    rw [(primaryGenerator_spec I hpg).1, span_modulus I hI.1, radical_eq_of_squarefree I hI hf]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- The chosen unit with `modulus I = unitOf I * primaryGenerator I`. -/
def unitOf (I : Id) (hI : Supported I) (hf : PowerFree 2 I) : Oˣ :=
  Classical.choose (exists_unit_modulus_eq I hI hf)

theorem modulus_eq_unitOf_mul (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    modulus I = (unitOf I hI hf : O) * primaryGenerator I :=
  Classical.choose_spec (exists_unit_modulus_eq I hI hf)

/-! ### The canonical phase -/

/-- The phase with the unit discrepancy removed. -/
def phaseCan (I : Id) (hI : Supported I) (hf : PowerFree 2 I) : ℂ :=
  star (idealRowHom (unitOf I hI hf : O) I) * phase I hI

/-- The canonical phase has modulus one. -/
theorem norm_phaseCan (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    ‖phaseCan I hI hf‖ = 1 := by
  unfold phaseCan
  rw [norm_mul, norm_star, norm_idealRowHom_unit I hI _,
    phase_norm I hI (powerFree_mono (by norm_num) hf), one_mul]

/-- The raw phase is the canonical phase times the sixth root of unity `idealRowHom (unitOf I) I`. -/
theorem phase_eq_unit_mul_phaseCan (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    phase I hI = idealRowHom (unitOf I hI hf : O) I * phaseCan I hI hf := by
  unfold phaseCan
  have h : star (idealRowHom (unitOf I hI hf : O) I) * idealRowHom (unitOf I hI hf : O) I = 1 := by
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj', norm_idealRowHom_unit I hI _]
    norm_num
  linear_combination (-(phase I hI)) * h

/-- The canonical phase, extended by `0` to all other ideals. -/
def phaseCanAll (I : Id) : ℂ :=
  if h : Supported I ∧ PowerFree 2 I then phaseCan I h.1 h.2 else 0

theorem phaseCanAll_eq (I : Id) (hI : Supported I) (hf : PowerFree 2 I) :
    phaseCanAll I = phaseCan I hI hf := by
  unfold phaseCanAll
  rw [dite_eq_left ⟨hI, hf⟩]

theorem norm_phaseCanAll_le (I : Id) : ‖phaseCanAll I‖ ≤ 1 := by
  unfold phaseCanAll
  split_ifs with h
  · exact (norm_phaseCan I h.1 h.2).le
  · simp

/-! ### Exact multiplicativity -/

/-- The inverse of a unit acts as the complex conjugate on a supported row. -/
theorem idealRowHom_unit_inv (K : Id) (hK : Supported K) (u : Oˣ) :
    idealRowHom ((u⁻¹ : Oˣ) : O) K = star (idealRowHom (u : O) K) := by
  have h1 : idealRowHom (u : O) K * idealRowHom ((u⁻¹ : Oˣ) : O) K = 1 := by
    rw [← idealRowHom_argument_mul, Units.mul_inv, idealRowHom_one_supported K hK]
  have h2 : idealRowHom (u : O) K * star (idealRowHom (u : O) K) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_idealRowHom_unit K hK u]
    norm_num
  have hne : idealRowHom (u : O) K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

/-- A product of coprime `PowerFree n` ideals is `PowerFree n`. -/
theorem powerFree_mul_of_coprime (n : ℕ) {I J : Id} (hfI : PowerFree n I) (hfJ : PowerFree n J)
    (hcop : IsCoprime I J) : PowerFree n (I * J) := by
  intro P hP hd
  by_cases h1 : P ∣ I
  · have h2 : ¬ P ∣ J := fun h2 => hP.not_isUnit (hcop.isUnit_of_dvd' h1 h2)
    apply hfI P hP
    exact ((prime_isCoprime_of_not_dvd hP h2).pow_left).dvd_of_dvd_mul_right hd
  · apply hfJ P hP
    exact ((prime_isCoprime_of_not_dvd hP h1).pow_left).dvd_of_dvd_mul_left hd

/-- **Exact multiplicativity of the canonical phase.** -/
theorem phaseCan_mul (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 2 I) (hfJ : PowerFree 2 J) (hcop : IsCoprime I J) :
    phaseCan (I * J) (supported_mul_of_supported hI hJ) (powerFree_mul_of_coprime 2 hfI hfJ hcop) =
      idealRowHom (primaryGenerator J) I * idealRowHom (primaryGenerator I) J *
        phaseCan I hI hfI * phaseCan J hJ hfJ := by
  have hIJ : Supported (I * J) := supported_mul_of_supported hI hJ
  have hfIJ : PowerFree 2 (I * J) := powerFree_mul_of_coprime 2 hfI hfJ hcop
  set uI := unitOf I hI hfI with huI
  set uJ := unitOf J hJ hfJ with huJ
  set uK := unitOf (I * J) hIJ hfIJ with huK
  have hmI : modulus I = (uI : O) * primaryGenerator I := modulus_eq_unitOf_mul I hI hfI
  have hmJ : modulus J = (uJ : O) * primaryGenerator J := modulus_eq_unitOf_mul J hJ hfJ
  have hmK : modulus (I * J) = (uK : O) * (primaryGenerator I * primaryGenerator J) := by
    rw [modulus_eq_unitOf_mul (I * J) hIJ hfIJ, primaryGenerator_mul]
  have hu : modulus I * modulus J * ((uK * uI⁻¹ * uJ⁻¹ : Oˣ) : O) = modulus (I * J) := by
    have ha : (uI : O) * ((uI⁻¹ : Oˣ) : O) = 1 := Units.mul_inv uI
    have hb : (uJ : O) * ((uJ⁻¹ : Oˣ) : O) = 1 := Units.mul_inv uJ
    rw [hmI, hmJ, hmK]
    simp only [Units.val_mul]
    linear_combination ((uK : O) * primaryGenerator I * primaryGenerator J *
      (uJ : O) * ((uJ⁻¹ : Oˣ) : O)) * ha + ((uK : O) * primaryGenerator I * primaryGenerator J) * hb
  have key := phase_mul_unit I J hI hJ (powerFree_mono (by norm_num) hfI)
    (powerFree_mono (by norm_num) hfJ) hcop hIJ (uK * uI⁻¹ * uJ⁻¹) hu
  -- the unit factors
  have e1 : idealRowHom ((uK * uI⁻¹ * uJ⁻¹ : Oˣ) : O) (I * J) =
      idealRowHom (uK : O) (I * J) * (idealRowHom ((uI⁻¹ : Oˣ) : O) I *
        idealRowHom ((uI⁻¹ : Oˣ) : O) J) * (idealRowHom ((uJ⁻¹ : Oˣ) : O) I *
        idealRowHom ((uJ⁻¹ : Oˣ) : O) J) := by
    rw [Units.val_mul, Units.val_mul, idealRowHom_argument_mul, idealRowHom_argument_mul,
      map_mul (idealRowHom ((uI⁻¹ : Oˣ) : O)) I J, map_mul (idealRowHom ((uJ⁻¹ : Oˣ) : O)) I J]
  have e2 : idealRowHom (modulus J) I =
      idealRowHom (uJ : O) I * idealRowHom (primaryGenerator J) I := by
    rw [hmJ, idealRowHom_argument_mul]
  have e3 : idealRowHom (modulus I) J =
      idealRowHom (uI : O) J * idealRowHom (primaryGenerator I) J := by
    rw [hmI, idealRowHom_argument_mul]
  have e4 : idealRowHom ((uI⁻¹ : Oˣ) : O) J * idealRowHom (uI : O) J = 1 := by
    rw [mul_comm, ← idealRowHom_argument_mul, Units.mul_inv, idealRowHom_one_supported J hJ]
  have e5 : idealRowHom ((uJ⁻¹ : Oˣ) : O) I * idealRowHom (uJ : O) I = 1 := by
    rw [mul_comm, ← idealRowHom_argument_mul, Units.mul_inv, idealRowHom_one_supported I hI]
  have e6 : star (idealRowHom (uK : O) (I * J)) * idealRowHom (uK : O) (I * J) = 1 := by
    rw [mul_comm, ← starRingEnd_apply, Complex.mul_conj', norm_idealRowHom_unit (I * J) hIJ uK]
    norm_num
  have e7 := idealRowHom_unit_inv I hI uI
  have e8 := idealRowHom_unit_inv J hJ uJ
  change star (idealRowHom (uK : O) (I * J)) * phase (I * J) hIJ =
    idealRowHom (primaryGenerator J) I * idealRowHom (primaryGenerator I) J *
      (star (idealRowHom (uI : O) I) * phase I hI) * (star (idealRowHom (uJ : O) J) * phase J hJ)
  rw [key, e1, e2, e3, ← e7, ← e8]
  set aI := idealRowHom ((uI⁻¹ : Oˣ) : O) I with haI
  set aJ := idealRowHom ((uI⁻¹ : Oˣ) : O) J with haJ
  set bI := idealRowHom ((uJ⁻¹ : Oˣ) : O) I with hbI
  set bJ := idealRowHom ((uJ⁻¹ : Oˣ) : O) J with hbJ
  set cI := idealRowHom (uJ : O) I with hcI
  set cJ := idealRowHom (uI : O) J with hcJ
  linear_combination
    (aI * aJ * bI * bJ * cI * cJ * (idealRowHom (primaryGenerator J) I *
      idealRowHom (primaryGenerator I) J * phase I hI * phase J hJ)) * e6 +
    (aI * bJ * (idealRowHom (primaryGenerator J) I * idealRowHom (primaryGenerator I) J *
      phase I hI * phase J hJ) * (bI * cI)) * e4 +
    (aI * bJ * (idealRowHom (primaryGenerator J) I * idealRowHom (primaryGenerator I) J *
      phase I hI * phase J hJ)) * e5

/-! ### Reciprocity: the coupling of two coprime slots -/

/-- The reciprocity sign (a `±1` or `0`) is real. -/
theorem star_rayPhase (r t : EisensteinEPrimaryPhase.Coord) :
    star (SieveOperator.phase r t) = SieveOperator.phase r t := by
  unfold SieveOperator.phase
  exact star_intCast _

/-- The row value of a square is the square of the row value. -/
theorem rowValue_sq (q s : Id) : rowValue (q ^ 2) s = rowValue q s ^ 2 := by
  rw [pow_two, Candidate.FourthPower.SieveCoupling.row_mul, pow_two]

/-- **The coupling of two coprime slots.** For coprime squarefree supported `s`, `q`, the summand
`α a conj(phaseCan (s q)) (k / s q)_6` is the product of the per-slot factors with the
reciprocity sign `ε(ray q, ray s)` and `conj (q^2 / s)_6`. -/
theorem slot_term_eq (s q : Id) (hs : Supported s) (hq : Supported q)
    (hfs : PowerFree 2 s) (hfq : PowerFree 2 q) (hcop : IsCoprime s q) (α a : ℂ) (k : O) :
    α * a * star (phaseCanAll (s * q)) * idealRowHom k (s * q) =
      SieveOperator.phase (SieveOperator.ray q) (SieveOperator.ray s) *
        ((α * star (phaseCanAll s) * idealRowHom k s) *
          (a * star (phaseCanAll q) * idealRowHom k q) * star (rowValue (q ^ 2) s)) := by
  rw [phaseCanAll_eq (s * q) (supported_mul_of_supported hs hq)
      (powerFree_mul_of_coprime 2 hfs hfq hcop),
    phaseCan_mul s q hs hq hfs hfq hcop, phaseCanAll_eq s hs hfs, phaseCanAll_eq q hq hfq,
    map_mul (idealRowHom k) s q, rowValue_sq]
  have hrec : idealRowHom (primaryGenerator s) q =
      SieveOperator.phase (SieveOperator.ray q) (SieveOperator.ray s) *
        idealRowHom (primaryGenerator q) s := SieveOperator.row_reciprocity s q hs hq
  rw [hrec]
  simp only [star_mul', star_pow, star_rayPhase]
  unfold rowValue
  ring

/-! ### Splitting the `q`-sum along finitely many classes -/

/-- **Class splitting.** Let `w r s` be a weight of absolute value `≤ 1` depending on the class `r`
of `q`.  If the bilinear form restricted to each class `{q : c q = r}` (with arbitrary
coefficients on the `s` side) is bounded by `M * ‖v|_r‖² * ‖u‖²`, then the form twisted by
`w (c q) s` is bounded by `|γ| * M * ‖v‖² * ‖u‖²`.  There is no arithmetic input. -/
theorem class_split_bound {γ : Type*} [Fintype γ] [DecidableEq γ]
    (Ss Qs : Finset Id) (c : Id → γ) (w : γ → Id → ℂ) (hw : ∀ r s, ‖w r s‖ ≤ 1)
    (u v : Id → ℂ) (K : Id → Id → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hblock : ∀ (r : γ) (u' : Id → ℂ),
      ‖∑ s ∈ Ss, ∑ q ∈ Qs with c q = r, u' s * v q * K s q‖ ^ 2 ≤
        M * (∑ q ∈ Qs with c q = r, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u' s‖ ^ 2) :
    ‖∑ s ∈ Ss, ∑ q ∈ Qs, w (c q) s * (u s * v q * K s q)‖ ^ 2 ≤
      (Fintype.card γ : ℝ) * M * (∑ q ∈ Qs, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u s‖ ^ 2 := by
  set B : γ → ℂ := fun r => ∑ s ∈ Ss, ∑ q ∈ Qs with c q = r, (w r s * u s) * v q * K s q
    with hB
  have hsplit : ∑ s ∈ Ss, ∑ q ∈ Qs, w (c q) s * (u s * v q * K s q) = ∑ r, B r := by
    calc ∑ s ∈ Ss, ∑ q ∈ Qs, w (c q) s * (u s * v q * K s q)
        = ∑ s ∈ Ss, ∑ r, ∑ q ∈ Qs with c q = r, w (c q) s * (u s * v q * K s q) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          exact (Finset.sum_fiberwise Qs c _).symm
      _ = ∑ s ∈ Ss, ∑ r, ∑ q ∈ Qs with c q = r, (w r s * u s) * v q * K s q := by
          refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun r _ =>
            Finset.sum_congr rfl (fun q hq => ?_)))
          rw [(Finset.mem_filter.mp hq).2]
          ring
      _ = ∑ r, ∑ s ∈ Ss, ∑ q ∈ Qs with c q = r, (w r s * u s) * v q * K s q :=
          Finset.sum_comm
  have h1 : ‖∑ r, B r‖ ≤ ∑ r, ‖B r‖ := norm_sum_le _ _
  have h2 : (∑ r, ‖B r‖) ^ 2 ≤ (Fintype.card γ : ℝ) * ∑ r, ‖B r‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset γ)) (f := fun r => ‖B r‖)
    simpa using h
  have h3 : ∀ r, ‖B r‖ ^ 2 ≤
      M * (∑ q ∈ Qs with c q = r, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u s‖ ^ 2 := by
    intro r
    refine (hblock r (fun s => w r s * u s)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hM (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    refine Finset.sum_le_sum (fun s _ => ?_)
    rw [norm_mul]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (hw r s)) 2
  calc ‖∑ s ∈ Ss, ∑ q ∈ Qs, w (c q) s * (u s * v q * K s q)‖ ^ 2 = ‖∑ r, B r‖ ^ 2 := by
        rw [hsplit]
    _ ≤ (∑ r, ‖B r‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Fintype.card γ : ℝ) * ∑ r, ‖B r‖ ^ 2 := h2
    _ ≤ (Fintype.card γ : ℝ) * ∑ r, (M * (∑ q ∈ Qs with c q = r, ‖v q‖ ^ 2) *
          ∑ s ∈ Ss, ‖u s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => h3 r)) (Nat.cast_nonneg _)
    _ = (Fintype.card γ : ℝ) * M * (∑ q ∈ Qs, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u s‖ ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_fiberwise Qs c (fun q => ‖v q‖ ^ 2)]
        ring

/-! ### The correlation bound -/

theorem majorant_nonneg_of_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ majorant A B := by
  unfold majorant
  positivity

/-- **Correlation bound for slot convolutions.**  For squarefree supported `s ∈ Ss` (with
`N(s) ≤ X`) and squarefree supported `q ∈ Qs` (with `N(q)^2 ≤ P2`), every `s` coprime to every `q`,
arbitrary coefficients `α`, `a` and an arbitrary row `k`,

  `‖∑_s ∑_q α_s a_q conj(phaseCan (s q)) (k / s q)_6‖² ≤
      C (P2 X)^ε majorant(P2, X) ‖α‖² ‖a‖²`,

with `C` depending only on `ε`.  Here `phaseCanAll` is `phaseCan` extended by `0`; on the ideals
of the statement it is `phaseCan`, see `phaseCanAll_eq`. -/
theorem correlation_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P2 X : ℝ) (Ss Qs : Finset Id) (α a : Id → ℂ) (k : O),
      (∀ s ∈ Ss, Supported s ∧ PowerFree 2 s ∧ (Ideal.absNorm s : ℝ) ≤ X) →
      (∀ q ∈ Qs, Supported q ∧ PowerFree 2 q ∧ (Ideal.absNorm q : ℝ) ^ 2 ≤ P2) →
      (∀ s ∈ Ss, ∀ q ∈ Qs, IsCoprime s q) →
      ‖∑ s ∈ Ss, ∑ q ∈ Qs, α s * a q * star (phaseCanAll (s * q)) * idealRowHom k (s * q)‖ ^ 2 ≤
        C * (P2 * X) ^ ε * majorant P2 X * (∑ s ∈ Ss, ‖α s‖ ^ 2) * ∑ q ∈ Qs, ‖a q‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hb⟩ := bilinear_sieve_squarefree ε hε
  refine ⟨16 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro P2 X Ss Qs α a k hS hQ hcop
  by_cases hSe : Ss = ∅
  · subst hSe
    simp
  by_cases hQe : Qs = ∅
  · subst hQe
    simp
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hQe
  obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have hnorm_pos : ∀ I : Id, I ≠ 0 → (1 : ℝ) ≤ Ideal.absNorm I := fun I hI =>
    Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  have hP2 : 1 ≤ P2 := by
    obtain ⟨hs, -, hn⟩ := hQ q₀ hq₀
    have h1 := hnorm_pos _ hs.1
    nlinarith
  have hX : 1 ≤ X := by
    obtain ⟨hs, -, hn⟩ := hS s₀ hs₀
    exact (hnorm_pos _ hs.1).trans hn
  set M : ℝ := C₀ * (P2 * X) ^ ε * majorant P2 X with hMdef
  have hM : 0 ≤ M :=
    mul_nonneg (mul_nonneg hC₀.le (Real.rpow_nonneg (by nlinarith) ε))
      (majorant_nonneg_of_nonneg (by linarith) (by linarith))
  -- the per-slot coefficient vectors
  set u : Id → ℂ := fun s => α s * star (phaseCanAll s) * idealRowHom k s with hu
  set v : Id → ℂ := fun q => a q * star (phaseCanAll q) * idealRowHom k q with hv
  have hu_norm : ∀ s, ‖u s‖ ≤ ‖α s‖ := by
    intro s
    simp only [hu, norm_mul, norm_star]
    calc ‖α s‖ * ‖phaseCanAll s‖ * ‖idealRowHom k s‖ ≤ ‖α s‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_phaseCanAll_le s) (norm_nonneg _))
            (idealRowHom_norm k s) (norm_nonneg _) (by positivity)
      _ = ‖α s‖ := by ring
  have hv_norm : ∀ q, ‖v q‖ ≤ ‖a q‖ := by
    intro q
    simp only [hv, norm_mul, norm_star]
    calc ‖a q‖ * ‖phaseCanAll q‖ * ‖idealRowHom k q‖ ≤ ‖a q‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_phaseCanAll_le q) (norm_nonneg _))
            (idealRowHom_norm k q) (norm_nonneg _) (by positivity)
      _ = ‖a q‖ := by ring
  -- reciprocity turns the coupling into a sign depending on the classes, times `conj rowValue (q^2) s`
  have hterm : ∑ s ∈ Ss, ∑ q ∈ Qs, α s * a q * star (phaseCanAll (s * q)) * idealRowHom k (s * q) =
      ∑ s ∈ Ss, ∑ q ∈ Qs, SieveOperator.phase (SieveOperator.ray q) (SieveOperator.ray s) *
        (u s * v q * star (rowValue (q ^ 2) s)) := by
    refine Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun q hq => ?_))
    obtain ⟨h1, h2, -⟩ := hS s hs
    obtain ⟨h3, h4, -⟩ := hQ q hq
    exact slot_term_eq s q h1 h3 h2 h4 (hcop s hs q hq) (α s) (a q) k
  -- the sieve bound on each class of `q`
  have hblock : ∀ (r : EisensteinEPrimaryPhase.Coord) (u' : Id → ℂ),
      ‖∑ s ∈ Ss, ∑ q ∈ Qs with SieveOperator.ray q = r,
          u' s * v q * star (rowValue (q ^ 2) s)‖ ^ 2 ≤
        M * (∑ q ∈ Qs with SieveOperator.ray q = r, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u' s‖ ^ 2 := by
    intro r u'
    refine hb P2 X Ss (Qs.filter (fun q => SieveOperator.ray q = r)) u' v ?_ ?_
    · intro q hq
      exact hQ q (Finset.mem_filter.mp hq).1
    · intro s hs
      obtain ⟨h1, h2, h3⟩ := hS s hs
      exact ⟨h1, powerFree_mono (by norm_num) h2, h3⟩
  have hsplit := class_split_bound Ss Qs SieveOperator.ray
    (fun r s => SieveOperator.phase r (SieveOperator.ray s))
    (fun r s => SieveOperator.phase_norm_le _ _) u v
    (fun s q => star (rowValue (q ^ 2) s)) M hM hblock
  have hcard : (Fintype.card EisensteinEPrimaryPhase.Coord : ℝ) = 16 := by
    simp [EisensteinEPrimaryPhase.Coord, Fintype.card_prod, ZMod.card]
  rw [hcard] at hsplit
  have hV : ∑ q ∈ Qs, ‖v q‖ ^ 2 ≤ ∑ q ∈ Qs, ‖a q‖ ^ 2 :=
    Finset.sum_le_sum (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hv_norm q) 2)
  have hU : ∑ s ∈ Ss, ‖u s‖ ^ 2 ≤ ∑ s ∈ Ss, ‖α s‖ ^ 2 :=
    Finset.sum_le_sum (fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hu_norm s) 2)
  rw [hterm]
  refine hsplit.trans ?_
  calc 16 * M * (∑ q ∈ Qs, ‖v q‖ ^ 2) * ∑ s ∈ Ss, ‖u s‖ ^ 2
      ≤ 16 * M * (∑ q ∈ Qs, ‖a q‖ ^ 2) * ∑ s ∈ Ss, ‖α s‖ ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hV (mul_nonneg (by norm_num) hM)
        · exact hU
        · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        · exact mul_nonneg (mul_nonneg (by norm_num) hM) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = 16 * C₀ * (P2 * X) ^ ε * majorant P2 X * (∑ s ∈ Ss, ‖α s‖ ^ 2) * ∑ q ∈ Qs, ‖a q‖ ^ 2 := by
        rw [hMdef]
        ring

/-- The correlation bound for an arbitrary phase function `ph` agreeing with `phaseCan` on the
products `s * q` of the statement (for every choice of the proofs of the hypotheses of `phaseCan`). -/
theorem correlation_bound_of_eq (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P2 X : ℝ) (Ss Qs : Finset Id) (α a : Id → ℂ) (k : O) (ph : Id → ℂ),
      (∀ s ∈ Ss, Supported s ∧ PowerFree 2 s ∧ (Ideal.absNorm s : ℝ) ≤ X) →
      (∀ q ∈ Qs, Supported q ∧ PowerFree 2 q ∧ (Ideal.absNorm q : ℝ) ^ 2 ≤ P2) →
      (∀ s ∈ Ss, ∀ q ∈ Qs, IsCoprime s q) →
      (∀ s ∈ Ss, ∀ q ∈ Qs, ∀ (h : Supported (s * q)) (h' : PowerFree 2 (s * q)),
        ph (s * q) = phaseCan (s * q) h h') →
      ‖∑ s ∈ Ss, ∑ q ∈ Qs, α s * a q * star (ph (s * q)) * idealRowHom k (s * q)‖ ^ 2 ≤
        C * (P2 * X) ^ ε * majorant P2 X * (∑ s ∈ Ss, ‖α s‖ ^ 2) * ∑ q ∈ Qs, ‖a q‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := correlation_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro P2 X Ss Qs α a k ph hS hQ hcop hph
  have h := hb P2 X Ss Qs α a k hS hQ hcop
  have hcongr : ∑ s ∈ Ss, ∑ q ∈ Qs, α s * a q * star (ph (s * q)) * idealRowHom k (s * q) =
      ∑ s ∈ Ss, ∑ q ∈ Qs, α s * a q * star (phaseCanAll (s * q)) * idealRowHom k (s * q) := by
    refine Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun q hq => ?_))
    obtain ⟨h1, h2, -⟩ := hS s hs
    obtain ⟨h3, h4, -⟩ := hQ q hq
    have hsq : Supported (s * q) := supported_mul_of_supported h1 h3
    have hfsq : PowerFree 2 (s * q) := powerFree_mul_of_coprime 2 h2 h4 (hcop s hs q hq)
    rw [hph s hs q hq hsq hfsq, phaseCanAll_eq (s * q) hsq hfsq]
  rw [hcongr]
  exact h

end
end QRH.ArviPrimeDilation

#print axioms QRH.ArviPrimeDilation.exists_unit_modulus_eq
#print axioms QRH.ArviPrimeDilation.norm_phaseCan
#print axioms QRH.ArviPrimeDilation.phase_eq_unit_mul_phaseCan
#print axioms QRH.ArviPrimeDilation.phaseCan_mul
#print axioms QRH.ArviPrimeDilation.slot_term_eq
#print axioms QRH.ArviPrimeDilation.class_split_bound
#print axioms QRH.ArviPrimeDilation.correlation_bound
#print axioms QRH.ArviPrimeDilation.correlation_bound_of_eq
