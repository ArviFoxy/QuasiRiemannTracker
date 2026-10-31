import Submissions.arvi_rip.FourthMoment
import Submissions.arvi_rip.WideFeatures

/-!
# RIP by positive measure for a random dictionary of multiplicative atoms

Research file (QRH, RIP program (4); the fresh look's design D1, counting form).

**Model.** `P` is a finite set of "primes", a source is a finite set of primes `n : Finset P` (a
squarefree number), `Src` is a finite set of sources and `Z` a finite set of rows. An assignment is
`v : Z → P → ZMod 6`, and all `6^{|Z||P|}` assignments are equally likely (counting measure, no
measure theory). With `ζ` a primitive sixth root of unity, the atom of row `z` is
`u_v z n = ∏_{p ∈ n} ζ^{v z p}`, i.e. a random completely multiplicative function on the sources,
and `G_v(z, z') = ∑_{n ∈ Src} u_v z n · conj (u_v z' n)` is the Gram entry.

**Results.**
* `sum_psi_mul_conj`, `sum_psi_four`: single-row character orthogonality on `(ZMod 6)^P`,
  `∑_w ψ_n(w) conj ψ_{n'}(w) = 6^{|P|} [n = n']`, and the row-visited-twice version
  `∑_w conj ψ_{n₁} ψ_{n₂} conj ψ_{n₃} ψ_{n₄} = 6^{|P|} [n₁ n₃ = n₂ n₄ as multisets of primes]`.
* `sum_norm_gram_sq`: for `z ≠ z'`, `∑_v |G_v(z, z')|² = (#assignments) · |Src|`.
* `sum_fourth_moment`: over a support `S`, `∑_v ∑_{z₁,z₃∈S} |(O_v²)(z₁, z₃)|² = (#assignments) ·
  walkCount S Src`, where `O_v` is the off-diagonal Gram and `walkCount` counts the row-balanced
  closed non-backtracking 4-walks (each row's arriving and departing sources agree as multisets).
  Each of the eight atom factors of a walk is a character of `(ZMod 6)^P` (`prod_regroup`), and a
  row's factors average to `6^{|P|}` or `0` (`sum_prod_atomE`).
* `walkCount_eq`: `walkCount S Src = s(s-1)(s-2)(s-3) m + 2 s(s-1)(s-2) m² + s(s-1) E`, with
  `s = |S|`, `m = |Src|` and `E(Src)` the multiplicative energy
  `#{(n₁,n₂,n₃,n₄) ∈ Src⁴ : n₁ n₃ = n₂ n₄ as multisets of primes}` (`energy`): four distinct rows
  force `n₁ = n₂ = n₃ = n₄`, each of the two backtracking patterns (`z₁ = z₃` or `z₂ = z₄`) leaves
  two free sources, and the doubly backtracking pattern is the energy equation.
  `walkCount_le`: the simple bound `≤ s⁴ m + 2 s³ m² + s² E`.
* `half_good`: Markov in counting form.
* `rip_positive_measure`: at least half of all assignments satisfy, for every coefficient vector `c`,
  `|‖∑_{z∈S} c_z u_v z‖² − |Src| ∑|c_z|²| ≤ (2B)^{1/4} ∑|c_z|²`, `B = |S|⁴|Src| + 2|S|³|Src|² +
  |S|² E(Src)` (note `‖u_v z‖² = |Src|` exactly). The certificate is `fourth_moment_rip`.
  `exists_rip_assignment` is the existence form and `rip_positive_measure_normalized` the form for
  the unit-norm atoms `u_v z / √|Src|`, with constant `(2B)^{1/4} / |Src|`.

For sources with only the trivial multiplicative relations (`E = 2m² − m`, e.g. single primes) one
has `B ≈ 2 s³ m²` and the relative constant is `≈ (4 s³ / m²)^{1/4}`: RIP up to `|S| ≪ m^{2/3}`,
beyond the `√m` of coherence (`coherence_order_barrier`). The arithmetic input (M₄) on the actual
sextic rows is not touched here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace QRH.ArviRIP

open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace

section Characters

variable {ζ : ℂ}

/-- The character `t ↦ ζ ^ t.val` of `ZMod 6`. -/
def chi (ζ : ℂ) (t : ZMod 6) : ℂ := ζ ^ t.val

theorem zeta_ne_zero (hζ : IsPrimitiveRoot ζ 6) : ζ ≠ 0 := hζ.ne_zero (by norm_num)

theorem norm_zeta (hζ : IsPrimitiveRoot ζ 6) : ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by norm_num)

theorem conj_zeta (hζ : IsPrimitiveRoot ζ 6) : conj ζ = ζ⁻¹ := by
  have h : conj ζ * ζ = 1 := by rw [Complex.conj_mul', norm_zeta hζ]; simp
  exact eq_inv_of_mul_eq_one_left h

theorem chi_ne_zero (hζ : IsPrimitiveRoot ζ 6) (t : ZMod 6) : chi ζ t ≠ 0 :=
  pow_ne_zero _ (zeta_ne_zero hζ)

theorem conj_chi (hζ : IsPrimitiveRoot ζ 6) (t : ZMod 6) : conj (chi ζ t) = (chi ζ t)⁻¹ := by
  simp only [chi, map_pow, conj_zeta hζ, inv_pow]

theorem norm_chi (hζ : IsPrimitiveRoot ζ 6) (t : ZMod 6) : ‖chi ζ t‖ = 1 := by
  simp only [chi, norm_pow, norm_zeta hζ, one_pow]

/-- Sum of a character power over `ZMod 6`: `∑_t χ(t)^k = 6` if `k = 0`, and `0` for `0 < |k| < 6`. -/
theorem sum_chi_zpow (hζ : IsPrimitiveRoot ζ 6) (k : ℤ) (hk : |k| < 6) :
    ∑ t : ZMod 6, chi ζ t ^ k = if k = 0 then 6 else 0 := by
  have h1 : ∀ t : ZMod 6, chi ζ t ^ k = (ζ ^ k) ^ t.val := by
    intro t
    simp only [chi]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have h2 : ∑ t : ZMod 6, (ζ ^ k) ^ t.val = ∑ i ∈ Finset.range 6, (ζ ^ k) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  simp_rw [h1]
  rw [h2]
  by_cases h0 : k = 0
  · subst h0
    simp
  · simp only [h0, ↓reduceIte]
    have hne : ζ ^ k ≠ 1 := by
      intro h
      rw [hζ.zpow_eq_one_iff_dvd] at h
      exact h0 (Int.eq_zero_of_abs_lt_dvd h (by simpa using hk))
    have h6 : (ζ ^ k) ^ 6 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    have hg := geom_sum_mul (ζ ^ k) 6
    rw [h6, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

end Characters

section Atoms

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {ζ : ℂ}

/-- Character of `(ZMod 6)^P` with integer exponent vector `e`: `w ↦ ∏_p χ(w p)^{e p}`. -/
noncomputable def atomE (ζ : ℂ) (e : P → ℤ) (w : P → ZMod 6) : ℂ := ∏ p, chi ζ (w p) ^ e p

omit [DecidableEq P] in
theorem atomE_zero (w : P → ZMod 6) : atomE ζ (0 : P → ℤ) w = 1 := by
  simp [atomE]

omit [DecidableEq P] in
theorem atomE_add (hζ : IsPrimitiveRoot ζ 6) (e e' : P → ℤ) (w : P → ZMod 6) :
    atomE ζ (e + e') w = atomE ζ e w * atomE ζ e' w := by
  simp only [atomE, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => zpow_add₀ (chi_ne_zero hζ _) _ _

omit [DecidableEq P] in
theorem conj_atomE (hζ : IsPrimitiveRoot ζ 6) (e : P → ℤ) (w : P → ZMod 6) :
    conj (atomE ζ e w) = atomE ζ (-e) w := by
  simp only [atomE, map_prod, map_zpow₀, Pi.neg_apply]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [conj_chi hζ, inv_zpow']

omit [DecidableEq P] in
theorem atomE_sum (hζ : IsPrimitiveRoot ζ 6) {J : Type*} (s : Finset J) (a : J → P → ℤ)
    (w : P → ZMod 6) : atomE ζ (∑ j ∈ s, a j) w = ∏ j ∈ s, atomE ζ (a j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [atomE_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, atomE_add hζ, ih]

/-- Orthogonality of the characters of `(ZMod 6)^P`, in counting form, for exponents `|e p| < 6`. -/
theorem sum_atomE (hζ : IsPrimitiveRoot ζ 6) (e : P → ℤ) (he : ∀ p, |e p| < 6) :
    ∑ w : P → ZMod 6, atomE ζ e w = if e = 0 then (6 : ℂ) ^ Fintype.card P else 0 := by
  have h := Fintype.prod_sum (fun (p : P) (t : ZMod 6) => chi ζ t ^ e p)
  unfold atomE
  rw [← h]
  simp_rw [fun p => sum_chi_zpow hζ (e p) (he p)]
  by_cases h0 : e = 0
  · subst h0
    simp [Finset.prod_const, Finset.card_univ]
  · obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      obtain ⟨p, hp⟩ := Function.ne_iff.mp h0
      exact ⟨p, by simpa using hp⟩
    simp only [h0, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp])

/-- Regrouping a product of row factors by rows. -/
theorem prod_regroup (hζ : IsPrimitiveRoot ζ 6) {J : Type*} [Fintype J] (r : J → Z)
    (a : J → P → ℤ) (v : Z → P → ZMod 6) :
    ∏ j, atomE ζ (a j) (v (r j)) =
      ∏ z, atomE ζ (∑ j ∈ univ.filter (fun j => r j = z), a j) (v z) := by
  simp_rw [atomE_sum hζ]
  calc ∏ j, atomE ζ (a j) (v (r j))
      = ∏ z, ∏ j ∈ univ.filter (fun j => r j = z), atomE ζ (a j) (v (r j)) :=
        (Finset.prod_fiberwise univ r _).symm
    _ = _ := by
        refine Finset.prod_congr rfl fun z _ => Finset.prod_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.mp hj).2]

/-- **Average of a product of row factors.** Over all assignments `v : Z → P → ZMod 6`
(counting measure), a product of characters `atomE (a j)` evaluated at the rows `r j` has
average zero unless it is balanced at every row. -/
theorem sum_prod_atomE (hζ : IsPrimitiveRoot ζ 6) {J : Type*} [Fintype J] (r : J → Z)
    (a : J → P → ℤ) (hb : ∀ z p, |∑ j ∈ univ.filter (fun j => r j = z), a j p| < 6) :
    ∑ v : Z → P → ZMod 6, ∏ j, atomE ζ (a j) (v (r j)) =
      if (∀ z, ∑ j ∈ univ.filter (fun j => r j = z), a j = 0)
      then ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z else 0 := by
  simp_rw [prod_regroup hζ r a]
  rw [← Fintype.prod_sum (fun (z : Z) (w : P → ZMod 6) =>
    atomE ζ (∑ j ∈ univ.filter (fun j => r j = z), a j) w)]
  have hsum : ∀ z, ∑ w : P → ZMod 6, atomE ζ (∑ j ∈ univ.filter (fun j => r j = z), a j) w =
      if ∑ j ∈ univ.filter (fun j => r j = z), a j = 0 then (6 : ℂ) ^ Fintype.card P else 0 :=
    fun z => sum_atomE hζ _ (fun p => by simpa [Finset.sum_apply] using hb z p)
  simp_rw [hsum]
  by_cases h : ∀ z, ∑ j ∈ univ.filter (fun j => r j = z), a j = 0
  · simp [h, Finset.prod_const, Finset.card_univ]
  · obtain ⟨z, hz⟩ := not_forall.mp h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ z) (by simp [hz])

omit [DecidableEq Z] in
/-- Bound on the exponent sums that occur: at most `k < 6` exponents of size `≤ 1`. -/
theorem abs_sum_filter_lt [DecidableEq Z] {J : Type*} [Fintype J] (hJ : Fintype.card J < 6) (r : J → Z)
    (a : J → P → ℤ) (ha : ∀ j p, |a j p| ≤ 1) (z : Z) (p : P) :
    |∑ j ∈ univ.filter (fun j => r j = z), a j p| < 6 := by
  calc |∑ j ∈ univ.filter (fun j => r j = z), a j p|
      ≤ ∑ j ∈ univ.filter (fun j => r j = z), |a j p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ univ.filter (fun j => r j = z), (1 : ℤ) := Finset.sum_le_sum fun j _ => ha j p
    _ = ((univ.filter (fun j => r j = z)).card : ℤ) := by simp
    _ ≤ (Fintype.card J : ℤ) := by exact_mod_cast Finset.card_filter_le _ _
    _ < 6 := by exact_mod_cast hJ

end Atoms

section Model

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {ζ : ℂ}

/-- The atom of one row, with exponents `w : P → ZMod 6`, at the source `n` (a finite set of
primes, i.e. a squarefree number): `ψ_n(w) = ∏_{p ∈ n} ζ ^ (w p).val`. -/
noncomputable def psi (ζ : ℂ) (n : Finset P) (w : P → ZMod 6) : ℂ := ∏ p ∈ n, chi ζ (w p)

/-- The atom of row `z` at the source `n`: `u_v z n = ∏_{p ∈ n} ζ ^ (v z p).val`. -/
noncomputable def atom (ζ : ℂ) (v : Z → P → ZMod 6) (z : Z) (n : Finset P) : ℂ :=
  psi ζ n (v z)

/-- The indicator of a source, as an integer exponent vector. -/
def ind (n : Finset P) : P → ℤ := fun p => if p ∈ n then 1 else 0

theorem ind_injective : Function.Injective (ind : Finset P → P → ℤ) := by
  intro n n' h
  ext p
  have := congrFun h p
  simp only [ind] at this
  by_cases hp : p ∈ n <;> by_cases hp' : p ∈ n' <;> simp_all

theorem abs_ind_sub_le (n n' : Finset P) (p : P) : |ind n p - ind n' p| ≤ 1 := by
  simp only [ind]
  split_ifs <;> simp

theorem psi_eq (n : Finset P) (w : P → ZMod 6) : psi ζ n w = atomE ζ (ind n) w := by
  have : ∀ p, chi ζ (w p) ^ (ind n p) = if p ∈ n then chi ζ (w p) else 1 := by
    intro p
    simp only [ind]
    split_ifs <;> simp
  simp only [psi, atomE, this]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem atom_eq (v : Z → P → ZMod 6) (z : Z) (n : Finset P) :
    atom ζ v z n = atomE ζ (ind n) (v z) := psi_eq n (v z)

theorem conj_psi (hζ : IsPrimitiveRoot ζ 6) (n : Finset P) (w : P → ZMod 6) :
    conj (psi ζ n w) = atomE ζ (-ind n) w := by
  rw [psi_eq, conj_atomE hζ]

theorem conj_atom (hζ : IsPrimitiveRoot ζ 6) (v : Z → P → ZMod 6) (z : Z) (n : Finset P) :
    conj (atom ζ v z n) = atomE ζ (-ind n) (v z) := conj_psi hζ n (v z)

theorem norm_atom (hζ : IsPrimitiveRoot ζ 6) (v : Z → P → ZMod 6) (z : Z) (n : Finset P) :
    ‖atom ζ v z n‖ = 1 := by
  simp only [atom, psi, norm_prod, norm_chi hζ, Finset.prod_const_one]

/-- The Gram entry `G_v(z, z') = ∑_{n ∈ Src} u_v z n · conj (u_v z' n)`. -/
noncomputable def gram (ζ : ℂ) (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z z' : Z) : ℂ :=
  ∑ n ∈ Src, atom ζ v z n * conj (atom ζ v z' n)

/-! ### The single-row lemmas -/

/-- **Single-row orthogonality.** Over all exponent vectors `w : P → ZMod 6`,
`∑_w ψ_n(w) · conj ψ_{n'}(w) = 6^{|P|} · [n = n']`: character orthogonality on `(ZMod 6)^P`
with exponents `ind n − ind n' ∈ {−1, 0, 1}`. -/
theorem sum_psi_mul_conj (hζ : IsPrimitiveRoot ζ 6) (n n' : Finset P) :
    ∑ w : P → ZMod 6, psi ζ n w * conj (psi ζ n' w) =
      if n = n' then (6 : ℂ) ^ Fintype.card P else 0 := by
  have h1 : ∀ w : P → ZMod 6, psi ζ n w * conj (psi ζ n' w) = atomE ζ (ind n - ind n') w := by
    intro w
    rw [conj_psi hζ, psi_eq, sub_eq_add_neg, atomE_add hζ]
  simp_rw [h1]
  have hb : ∀ p, |(ind n - ind n') p| < 6 :=
    fun p => lt_of_le_of_lt (abs_ind_sub_le n n' p) (by norm_num)
  rw [sum_atomE hζ (ind n - ind n') hb]
  by_cases h : n = n'
  · subst h
    simp
  · have : ind n - ind n' ≠ 0 := fun h0 => h (ind_injective (sub_eq_zero.mp h0))
    simp [h, this]

theorem ind_four_eq_zero_iff (n₁ n₂ n₃ n₄ : Finset P) :
    (-ind n₁ + ind n₂ - ind n₃ + ind n₄ = 0) ↔ n₁.val + n₃.val = n₂.val + n₄.val := by
  have key : ∀ p : P, (-ind n₁ + ind n₂ - ind n₃ + ind n₄) p = 0 ↔
      (n₁.val + n₃.val).count p = (n₂.val + n₄.val).count p := by
    intro p
    rw [Multiset.count_add, Multiset.count_add, Multiset.count_eq_of_nodup n₁.nodup,
      Multiset.count_eq_of_nodup n₃.nodup, Multiset.count_eq_of_nodup n₂.nodup,
      Multiset.count_eq_of_nodup n₄.nodup]
    simp only [ind, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.mem_val]
    split_ifs <;> omega
  constructor
  · intro h
    exact Multiset.ext.mpr fun p => (key p).mp (congrFun h p)
  · intro h
    funext p
    exact (key p).mpr (by rw [h])

/-- **Row visited twice.** `∑_w conj ψ_{n₁} ψ_{n₂} conj ψ_{n₃} ψ_{n₄} = 6^{|P|}` if
`n₁ n₃ = n₂ n₄` as multisets of primes, and `0` otherwise (exponents in `{−2, …, 2}`, all
`< 6` in absolute value). -/
theorem sum_psi_four (hζ : IsPrimitiveRoot ζ 6) (n₁ n₂ n₃ n₄ : Finset P) :
    ∑ w : P → ZMod 6, conj (psi ζ n₁ w) * psi ζ n₂ w * conj (psi ζ n₃ w) * psi ζ n₄ w =
      if n₁.val + n₃.val = n₂.val + n₄.val then (6 : ℂ) ^ Fintype.card P else 0 := by
  have h1 : ∀ w : P → ZMod 6, conj (psi ζ n₁ w) * psi ζ n₂ w * conj (psi ζ n₃ w) * psi ζ n₄ w =
      atomE ζ (-ind n₁ + ind n₂ - ind n₃ + ind n₄) w := by
    intro w
    simp only [psi_eq, conj_atomE hζ, sub_eq_add_neg, atomE_add hζ]
  simp_rw [h1]
  have hb : ∀ p, |(-ind n₁ + ind n₂ - ind n₃ + ind n₄) p| < 6 := by
    intro p
    simp only [ind, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    split_ifs <;> norm_num
  rw [sum_atomE hζ _ hb]
  simp only [ind_four_eq_zero_iff]

/-! ### Step 1: orthogonality of two different rows -/

theorem term2 (hζ : IsPrimitiveRoot ζ 6) (v : Z → P → ZMod 6) (z z' : Z) (n n' : Finset P) :
    atom ζ v z n * conj (atom ζ v z' n) * (conj (atom ζ v z n') * atom ζ v z' n') =
      ∏ j : Fin 2, atomE ζ (![ind n - ind n', ind n' - ind n] j) (v (![z, z'] j)) := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg, atomE_add hζ, atom_eq,
    conj_atomE hζ]
  ring

theorem bal2_iff {z z' : Z} (hzz : z ≠ z') (n n' : Finset P) :
    (∀ r, ∑ j ∈ univ.filter (fun j : Fin 2 => (![z, z'] : Fin 2 → Z) j = r),
        (![ind n - ind n', ind n' - ind n] : Fin 2 → P → ℤ) j = 0) ↔ n = n' := by
  constructor
  · intro h
    have h0 := h z
    rw [Finset.sum_filter, Fin.sum_univ_two] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ite_true, hzz.symm, ite_false,
      add_zero] at h0
    exact ind_injective (sub_eq_zero.mp h0)
  · rintro rfl r
    refine Finset.sum_eq_zero fun j _ => ?_
    fin_cases j <;> simp

/-- **Orthogonality of two different rows** (complex form). -/
theorem sum_gram_mul_conj (hζ : IsPrimitiveRoot ζ 6) (Src : Finset (Finset P)) {z z' : Z}
    (hzz : z ≠ z') :
    ∑ v : Z → P → ZMod 6, gram ζ Src v z z' * conj (gram ζ Src v z z') =
      ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z * Src.card := by
  have hexp : ∀ v : Z → P → ZMod 6, gram ζ Src v z z' * conj (gram ζ Src v z z') =
      ∑ n ∈ Src, ∑ n' ∈ Src,
        ∏ j : Fin 2, atomE ζ (![ind n - ind n', ind n' - ind n] j) (v (![z, z'] j)) := by
    intro v
    simp only [gram, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => term2 hζ v z z' n n'
  have hb : ∀ n n' : Finset P, ∀ r p,
      |∑ j ∈ univ.filter (fun j : Fin 2 => (![z, z'] : Fin 2 → Z) j = r),
        (![ind n - ind n', ind n' - ind n] : Fin 2 → P → ℤ) j p| < 6 := by
    intro n n' r p
    refine abs_sum_filter_lt (by simp) _ _ (fun j q => ?_) r p
    fin_cases j
    · simpa using abs_ind_sub_le n n' q
    · simpa using abs_ind_sub_le n' n q
  simp_rw [hexp]
  calc ∑ v : Z → P → ZMod 6, ∑ n ∈ Src, ∑ n' ∈ Src,
        ∏ j : Fin 2, atomE ζ (![ind n - ind n', ind n' - ind n] j) (v (![z, z'] j))
      = ∑ n ∈ Src, ∑ n' ∈ Src, ∑ v : Z → P → ZMod 6,
        ∏ j : Fin 2, atomE ζ (![ind n - ind n', ind n' - ind n] j) (v (![z, z'] j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ n ∈ Src, ∑ n' ∈ Src,
        (if n = n' then ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z else 0) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
        rw [sum_prod_atomE hζ (![z, z']) (![ind n - ind n', ind n' - ind n]) (hb n n')]
        simp only [bal2_iff hzz]
    _ = ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z * Src.card := by
        have : ∀ n ∈ Src, ∑ n' ∈ Src,
            (if n = n' then ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z else 0) =
            ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z := by
          intro n hn
          simp [hn]
        rw [Finset.sum_congr rfl this]
        simp [mul_comm]

theorem card_assign : Fintype.card (Z → P → ZMod 6) = (6 ^ Fintype.card P) ^ Fintype.card Z := by
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card]

/-- **Orthogonality of two different rows**, real form: `∑_v |G_v(z, z')|² =
(#assignments) · |Src|` for `z ≠ z'`. -/
theorem sum_norm_gram_sq (hζ : IsPrimitiveRoot ζ 6) (Src : Finset (Finset P)) {z z' : Z}
    (hzz : z ≠ z') :
    ∑ v : Z → P → ZMod 6, ‖gram ζ Src v z z'‖ ^ 2 =
      (Fintype.card (Z → P → ZMod 6) : ℝ) * Src.card := by
  have h := sum_gram_mul_conj hζ Src hzz
  have h2 : ∀ v : Z → P → ZMod 6, gram ζ Src v z z' * conj (gram ζ Src v z z') =
      ((‖gram ζ Src v z z'‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [Complex.mul_conj']
    push_cast
    rfl
  simp_rw [h2] at h
  rw [← Complex.ofReal_sum] at h
  have h3 : ((Fintype.card (Z → P → ZMod 6) : ℝ) * Src.card : ℝ) =
      (((6 : ℝ) ^ Fintype.card P) ^ Fintype.card Z * Src.card : ℝ) := by
    rw [card_assign]; push_cast; ring
  rw [h3]
  exact_mod_cast h

/-! ### Step 2: the centered fourth moment as a closed-walk count -/

/-- The atom of row `z` as a vector of `ℂ^{Src}`. -/
noncomputable def atomVec (ζ : ℂ) (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z : Z) :
    EuclideanSpace ℂ Src :=
  WithLp.toLp 2 (fun n : Src => atom ζ v z n.1)

theorem inner_atomVec (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z z' : Z) :
    ⟪atomVec ζ Src v z, atomVec ζ Src v z'⟫_ℂ =
      ∑ n ∈ Src, conj (atom ζ v z n) * atom ζ v z' n := by
  rw [atomVec, atomVec, PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  rw [Finset.sum_coe_sort Src (fun n => atom ζ v z' n * conj (atom ζ v z n))]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

theorem norm_atomVec_sq (hζ : IsPrimitiveRoot ζ 6) (Src : Finset (Finset P))
    (v : Z → P → ZMod 6) (z : Z) : ‖atomVec ζ Src v z‖ ^ 2 = Src.card := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [atomVec, norm_atom hζ]

end Model

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι]

/-- The fourth-moment sum as a closed 4-walk sum. -/
theorem sum_norm_offG2_sq (S : Finset ι) (u : ι → E) :
    (((∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S u z₁ z₃‖ ^ 2 : ℝ)) : ℂ) =
      ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
        offG u z₁ z₂ * offG u z₂ z₃ * offG u z₃ z₄ * offG u z₄ z₁ := by
  have key : ∀ z₁ z₃ : ι, (((‖offG2 S u z₁ z₃‖ : ℝ) : ℂ)) ^ 2 =
      ∑ z₂ ∈ S, ∑ z₄ ∈ S, offG u z₁ z₂ * offG u z₂ z₃ * offG u z₃ z₄ * offG u z₄ z₁ := by
    intro z₁ z₃
    rw [← Complex.conj_mul']
    simp only [offG2, map_sum, map_mul, offG_conj]
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z₂ _ => Finset.sum_congr rfl fun z₄ _ => ?_
    ring
  push_cast
  simp_rw [key]
  refine Finset.sum_congr rfl fun z₁ _ => ?_
  rw [Finset.sum_comm]

end Expansion

section Walks

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {ζ : ℂ}

/-- **Row balance** of a closed 4-walk `z₁ →(n₁) z₂ →(n₂) z₃ →(n₃) z₄ →(n₄) z₁`, in exponent form:
at every row `r`, the sources arriving at `r` and the sources departing from `r` agree as
multisets of primes. The row `z₁` receives `n₄` and sends `n₁`, and so on. -/
def Bal (z₁ z₂ z₃ z₄ : Z) (n₁ n₂ n₃ n₄ : Finset P) : Prop :=
  ∀ r : Z, (if z₁ = r then ind n₄ - ind n₁ else 0) + (if z₂ = r then ind n₁ - ind n₂ else 0) +
    (if z₃ = r then ind n₂ - ind n₃ else 0) + (if z₄ = r then ind n₃ - ind n₄ else 0) = 0

instance (z₁ z₂ z₃ z₄ : Z) (n₁ n₂ n₃ n₄ : Finset P) : Decidable (Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄) := by
  unfold Bal
  infer_instance

/-- The source 4-tuples that balance the closed walk `z₁ z₂ z₃ z₄`. -/
def balSet (Src : Finset (Finset P)) (z₁ z₂ z₃ z₄ : Z) :
    Finset (Finset P × Finset P × Finset P × Finset P) :=
  (Src ×ˢ Src ×ˢ Src ×ˢ Src).filter (fun x => Bal z₁ z₂ z₃ z₄ x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- The number of row-balanced closed non-backtracking 4-walks on the support `S` with
sources in `Src`. -/
def walkCount (S : Finset Z) (Src : Finset (Finset P)) : ℕ :=
  ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
    if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then (balSet Src z₁ z₂ z₃ z₄).card else 0

theorem term4 (hζ : IsPrimitiveRoot ζ 6) (v : Z → P → ZMod 6) (z₁ z₂ z₃ z₄ : Z)
    (n₁ n₂ n₃ n₄ : Finset P) :
    conj (atom ζ v z₁ n₁) * atom ζ v z₂ n₁ * (conj (atom ζ v z₂ n₂) * atom ζ v z₃ n₂) *
      (conj (atom ζ v z₃ n₃) * atom ζ v z₄ n₃) * (conj (atom ζ v z₄ n₄) * atom ζ v z₁ n₄) =
    ∏ j : Fin 4, atomE ζ (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] j)
      (v (![z₁, z₂, z₃, z₄] j)) := by
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, sub_eq_add_neg, atomE_add hζ, atom_eq, conj_atomE hζ]
  ring

theorem bal4_iff (z₁ z₂ z₃ z₄ : Z) (n₁ n₂ n₃ n₄ : Finset P) :
    (∀ r, ∑ j ∈ univ.filter (fun j : Fin 4 => (![z₁, z₂, z₃, z₄] : Fin 4 → Z) j = r),
      (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] : Fin 4 → P → ℤ) j = 0)
      ↔ Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄ := by
  unfold Bal
  refine forall_congr' fun r => ?_
  rw [Finset.sum_filter, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  exact Iff.rfl

theorem card_balSet_eq (Src : Finset (Finset P)) (z₁ z₂ z₃ z₄ : Z) :
    ((balSet Src z₁ z₂ z₃ z₄).card : ℂ) =
      ∑ n₁ ∈ Src, ∑ n₂ ∈ Src, ∑ n₃ ∈ Src, ∑ n₄ ∈ Src,
        if Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄ then (1 : ℂ) else 0 := by
  rw [balSet, Finset.card_filter]
  push_cast
  simp only [Finset.sum_product]

theorem prod_inner_eq (hζ : IsPrimitiveRoot ζ 6) (Src : Finset (Finset P)) (v : Z → P → ZMod 6)
    (z₁ z₂ z₃ z₄ : Z) :
    (∑ n ∈ Src, conj (atom ζ v z₁ n) * atom ζ v z₂ n) *
      (∑ n ∈ Src, conj (atom ζ v z₂ n) * atom ζ v z₃ n) *
      (∑ n ∈ Src, conj (atom ζ v z₃ n) * atom ζ v z₄ n) *
      (∑ n ∈ Src, conj (atom ζ v z₄ n) * atom ζ v z₁ n) =
    ∑ n₁ ∈ Src, ∑ n₂ ∈ Src, ∑ n₃ ∈ Src, ∑ n₄ ∈ Src,
      ∏ j : Fin 4, atomE ζ
        (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] j)
        (v (![z₁, z₂, z₃, z₄] j)) := by
  have e : ∀ A B C D : ℂ, A * B * C * D = (A * B) * (C * D) := by intros; ring
  rw [e, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ =>
    Finset.sum_congr rfl fun n₃ _ => Finset.sum_congr rfl fun n₄ _ => ?_
  rw [← term4 hζ v z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄]
  ring

/-- The Gram entry in the orientation of the inner product: `⟪u z, u z'⟫`. -/
noncomputable def ipG (ζ : ℂ) (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z z' : Z) : ℂ :=
  ∑ n ∈ Src, conj (atom ζ v z n) * atom ζ v z' n

/-- **The walk average.** For a fixed closed walk `z₁ z₂ z₃ z₄` of rows, the average over all
assignments of the product of the four Gram entries equals the number of balancing source
tuples: `∑_v ∏ ⟪u z_i, u z_{i+1}⟫ = (#assignments) · #{balanced (n₁, n₂, n₃, n₄) ∈ Src⁴}`. -/
theorem sum_walk (hζ : IsPrimitiveRoot ζ 6) (Src : Finset (Finset P)) (z₁ z₂ z₃ z₄ : Z) :
    ∑ v : Z → P → ZMod 6,
      (ipG ζ Src v z₁ z₂ * ipG ζ Src v z₂ z₃ * ipG ζ Src v z₃ z₄ * ipG ζ Src v z₄ z₁) =
      ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z * ((balSet Src z₁ z₂ z₃ z₄).card : ℂ) := by
  have hb : ∀ n₁ n₂ n₃ n₄ : Finset P, ∀ r p,
      |∑ j ∈ univ.filter (fun j : Fin 4 => (![z₁, z₂, z₃, z₄] : Fin 4 → Z) j = r),
        (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] :
          Fin 4 → P → ℤ) j p| < 6 := by
    intro n₁ n₂ n₃ n₄ r p
    refine abs_sum_filter_lt (by simp) _ _ (fun j q => ?_) r p
    fin_cases j
    · simpa using abs_ind_sub_le n₄ n₁ q
    · simpa using abs_ind_sub_le n₁ n₂ q
    · simpa using abs_ind_sub_le n₂ n₃ q
    · simpa using abs_ind_sub_le n₃ n₄ q
  simp only [ipG]
  simp_rw [prod_inner_eq hζ]
  calc ∑ v : Z → P → ZMod 6, ∑ n₁ ∈ Src, ∑ n₂ ∈ Src, ∑ n₃ ∈ Src, ∑ n₄ ∈ Src,
        ∏ j : Fin 4, atomE ζ
          (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] j)
          (v (![z₁, z₂, z₃, z₄] j))
      = ∑ n₁ ∈ Src, ∑ n₂ ∈ Src, ∑ n₃ ∈ Src, ∑ n₄ ∈ Src, ∑ v : Z → P → ZMod 6,
        ∏ j : Fin 4, atomE ζ
          (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄] j)
          (v (![z₁, z₂, z₃, z₄] j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n₃ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ n₁ ∈ Src, ∑ n₂ ∈ Src, ∑ n₃ ∈ Src, ∑ n₄ ∈ Src,
        (if Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄ then ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z
          else 0) := by
        refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ =>
          Finset.sum_congr rfl fun n₃ _ => Finset.sum_congr rfl fun n₄ _ => ?_
        rw [sum_prod_atomE hζ (![z₁, z₂, z₃, z₄])
          (![ind n₄ - ind n₁, ind n₁ - ind n₂, ind n₂ - ind n₃, ind n₃ - ind n₄])
          (hb n₁ n₂ n₃ n₄)]
        simp only [bal4_iff]
    _ = ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z * ((balSet Src z₁ z₂ z₃ z₄).card : ℂ) := by
        rw [card_balSet_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₃ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n₄ _ => ?_
        split_ifs <;> simp

theorem offG_atomVec (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z z' : Z) :
    offG (atomVec ζ Src v) z z' = if z = z' then 0 else ipG ζ Src v z z' := by
  unfold offG
  split_ifs
  · rfl
  · rw [inner_atomVec]
    rfl

theorem offG_prod_atomVec (Src : Finset (Finset P)) (v : Z → P → ZMod 6) (z₁ z₂ z₃ z₄ : Z) :
    offG (atomVec ζ Src v) z₁ z₂ * offG (atomVec ζ Src v) z₂ z₃ * offG (atomVec ζ Src v) z₃ z₄ *
        offG (atomVec ζ Src v) z₄ z₁ =
      if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then
        ipG ζ Src v z₁ z₂ * ipG ζ Src v z₂ z₃ * ipG ζ Src v z₃ z₄ * ipG ζ Src v z₄ z₁ else 0 := by
  simp only [offG_atomVec]
  by_cases h12 : z₁ = z₂
  · simp [h12]
  by_cases h23 : z₂ = z₃
  · simp [h23]
  by_cases h34 : z₃ = z₄
  · simp [h34]
  by_cases h41 : z₄ = z₁
  · simp [h41]
  · simp [h12, h23, h34, h41]

/-- **The fourth moment is a closed-walk count.** Summed over all assignments, the Frobenius norm
of the square of the off-diagonal Gram on `S` is `(#assignments) ×` the number of row-balanced
closed non-backtracking 4-walks. -/
theorem sum_fourth_moment (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    ∑ v : Z → P → ZMod 6, ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 =
      (Fintype.card (Z → P → ZMod 6) : ℝ) * (walkCount S Src : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [sum_norm_offG2_sq, offG_prod_atomVec]
  calc ∑ v : Z → P → ZMod 6, ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
        (if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then
          ipG ζ Src v z₁ z₂ * ipG ζ Src v z₂ z₃ * ipG ζ Src v z₃ z₄ * ipG ζ Src v z₄ z₁ else 0)
      = ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S, ∑ v : Z → P → ZMod 6,
        (if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then
          ipG ζ Src v z₁ z₂ * ipG ζ Src v z₂ z₃ * ipG ζ Src v z₃ z₄ * ipG ζ Src v z₄ z₁
         else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z₃ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
        (if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then
          ((6 : ℂ) ^ Fintype.card P) ^ Fintype.card Z * ((balSet Src z₁ z₂ z₃ z₄).card : ℂ)
         else 0) := by
        refine Finset.sum_congr rfl fun z₁ _ => Finset.sum_congr rfl fun z₂ _ =>
          Finset.sum_congr rfl fun z₃ _ => Finset.sum_congr rfl fun z₄ _ => ?_
        split_ifs with h
        · exact sum_walk hζ Src z₁ z₂ z₃ z₄
        · simp
    _ = ((Fintype.card (Z → P → ZMod 6) : ℝ) * (walkCount S Src : ℝ) : ℝ) := by
        rw [walkCount, card_assign]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z₃ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z₄ _ => ?_
        split_ifs <;> simp

end Walks

section Bounds

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- **Multiplicative energy** of the source set: the number of `(n₁, n₂, n₃, n₄) ∈ Src⁴` with
`n₁ n₃ = n₂ n₄`, where a source is a squarefree number, i.e. a set of primes, and the product is
the sum of multisets of primes. -/
def energy (Src : Finset (Finset P)) : ℕ :=
  ((Src ×ˢ Src ×ˢ Src ×ˢ Src).filter
    (fun x => x.1.val + x.2.2.1.val = x.2.1.val + x.2.2.2.val)).card

section Patterns

variable {z₁ z₂ z₃ z₄ : Z} {n₁ n₂ n₃ n₄ : Finset P}

/-- Four distinct rows: every row is visited once, so all four sources coincide. -/
theorem bal_distinct (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁)
    (h13 : z₁ ≠ z₃) (h24 : z₂ ≠ z₄) (hb : Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄) :
    n₄ = n₁ ∧ n₁ = n₂ ∧ n₂ = n₃ := by
  have e1 := hb z₁
  have e2 := hb z₂
  have e3 := hb z₃
  simp [h12, h12.symm, h13, h13.symm, h41, h41.symm] at e1
  simp [h12, h12.symm, h23, h23.symm, h24, h24.symm] at e2
  simp [h13, h13.symm, h23, h23.symm, h34, h34.symm] at e3
  exact ⟨ind_injective (sub_eq_zero.mp e1), ind_injective (sub_eq_zero.mp e2),
    ind_injective (sub_eq_zero.mp e3)⟩

/-- Rows `z₁ = z₃` visited twice, `z₂`, `z₄` once each. -/
theorem bal_13 (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁)
    (h13 : z₁ = z₃) (h24 : z₂ ≠ z₄) (hb : Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄) :
    n₁ = n₂ ∧ n₃ = n₄ := by
  subst h13
  have e2 := hb z₂
  have e4 := hb z₄
  simp [h12, h12.symm, h24, h24.symm] at e2
  simp [h41, h41.symm, h24, h24.symm, h34] at e4
  exact ⟨ind_injective (sub_eq_zero.mp e2), ind_injective (sub_eq_zero.mp e4)⟩

/-- Rows `z₂ = z₄` visited twice, `z₁`, `z₃` once each. -/
theorem bal_24 (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁)
    (h13 : z₁ ≠ z₃) (h24 : z₂ = z₄) (hb : Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄) :
    n₄ = n₁ ∧ n₂ = n₃ := by
  subst h24
  have e1 := hb z₁
  have e3 := hb z₃
  simp [h12, h12.symm, h13, h13.symm] at e1
  simp [h13, h13.symm, h23, h23.symm] at e3
  exact ⟨ind_injective (sub_eq_zero.mp e1), ind_injective (sub_eq_zero.mp e3)⟩

/-- Both rows visited twice: the balance condition is the energy equation `n₁ n₃ = n₂ n₄`. -/
theorem bal_both (h12 : z₁ ≠ z₂) (h41 : z₄ ≠ z₁) (h13 : z₁ = z₃) (h24 : z₂ = z₄)
    (hb : Bal z₁ z₂ z₃ z₄ n₁ n₂ n₃ n₄) : n₁.val + n₃.val = n₂.val + n₄.val := by
  subst h13
  subst h24
  have e1 := hb z₁
  simp [h12.symm] at e1
  refine (ind_four_eq_zero_iff n₁ n₂ n₃ n₄).mp ?_
  calc -ind n₁ + ind n₂ - ind n₃ + ind n₄ = (ind n₄ - ind n₁) + (ind n₂ - ind n₃) := by abel
    _ = 0 := e1

end Patterns

/-! #### Counting the balancing source tuples -/

theorem card_balSet_le_distinct (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ ≠ z₃) (h24 : z₂ ≠ z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card ≤ Src.card := by
  have hsub : balSet Src z₁ z₂ z₃ z₄ ⊆ Src.image (fun a => (a, a, a, a)) := by
    intro x hx
    rw [balSet, Finset.mem_filter] at hx
    obtain ⟨hmem, hb⟩ := hx
    obtain ⟨n₁, n₂, n₃, n₄⟩ := x
    dsimp only at hb
    simp only [Finset.mem_product] at hmem
    obtain ⟨e4, e1, e2⟩ := bal_distinct h12 h23 h34 h41 h13 h24 hb
    subst e4 e1 e2
    exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem card_balSet_le_13 (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ = z₃) (h24 : z₂ ≠ z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card ≤ Src.card ^ 2 := by
  have hsub : balSet Src z₁ z₂ z₃ z₄ ⊆ (Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2)) := by
    intro x hx
    rw [balSet, Finset.mem_filter] at hx
    obtain ⟨hmem, hb⟩ := hx
    obtain ⟨n₁, n₂, n₃, n₄⟩ := x
    dsimp only at hb
    simp only [Finset.mem_product] at hmem
    obtain ⟨e1, e3⟩ := bal_13 h12 h23 h34 h41 h13 h24 hb
    subst e1 e3
    exact Finset.mem_image.mpr ⟨(_, _), Finset.mem_product.mpr ⟨hmem.1, hmem.2.2.1⟩, rfl⟩
  calc (balSet Src z₁ z₂ z₃ z₄).card ≤ ((Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2))).card :=
        Finset.card_le_card hsub
    _ ≤ (Src ×ˢ Src).card := Finset.card_image_le
    _ = Src.card ^ 2 := by rw [Finset.card_product, sq]

theorem card_balSet_le_24 (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ ≠ z₃) (h24 : z₂ = z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card ≤ Src.card ^ 2 := by
  have hsub : balSet Src z₁ z₂ z₃ z₄ ⊆ (Src ×ˢ Src).image (fun a => (a.1, a.2, a.2, a.1)) := by
    intro x hx
    rw [balSet, Finset.mem_filter] at hx
    obtain ⟨hmem, hb⟩ := hx
    obtain ⟨n₁, n₂, n₃, n₄⟩ := x
    dsimp only at hb
    simp only [Finset.mem_product] at hmem
    obtain ⟨e4, e2⟩ := bal_24 h12 h23 h34 h41 h13 h24 hb
    subst e4 e2
    exact Finset.mem_image.mpr ⟨(_, _), Finset.mem_product.mpr ⟨hmem.1, hmem.2.1⟩, rfl⟩
  calc (balSet Src z₁ z₂ z₃ z₄).card ≤ ((Src ×ˢ Src).image (fun a => (a.1, a.2, a.2, a.1))).card :=
        Finset.card_le_card hsub
    _ ≤ (Src ×ˢ Src).card := Finset.card_image_le
    _ = Src.card ^ 2 := by rw [Finset.card_product, sq]

theorem card_balSet_le_both (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h41 : z₄ ≠ z₁) (h13 : z₁ = z₃) (h24 : z₂ = z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card ≤ energy Src := by
  unfold energy
  refine Finset.card_le_card ?_
  intro x hx
  rw [balSet, Finset.mem_filter] at hx
  obtain ⟨hmem, hb⟩ := hx
  rw [Finset.mem_filter]
  exact ⟨hmem, bal_both h12 h41 h13 h24 hb⟩

end Bounds

section ExactCounts

variable {Z : Type*} [DecidableEq Z]

/-- `∑_{x ∈ S, x ∉ T} c = (|S| - |T|) c`. -/
theorem sum_notin_const (S T : Finset Z) (hT : T ⊆ S) (c : ℕ) :
    ∑ x ∈ S, (if x ∈ T then 0 else c) = (S.card - T.card) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
    Finset.filter_not, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hT,
    Finset.card_sdiff_of_subset hT]

/-- Pairs of distinct elements, as a nested count. -/
theorem sum_ne_const (S : Finset Z) {a : Z} (ha : a ∈ S) (c : ℕ) :
    ∑ x ∈ S, (if a = x then 0 else c) = (S.card - 1) * c := by
  have := sum_notin_const S {a} (by simpa using ha) c
  simpa [eq_comm] using this

theorem sum_notin_pair_const (S : Finset Z) {a b : Z} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (c : ℕ) : ∑ x ∈ S, (if x ∈ ({a, b} : Finset Z) then 0 else c) = (S.card - 2) * c := by
  have hT : ({a, b} : Finset Z) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  rw [sum_notin_const S _ hT, Finset.card_pair hab]

theorem sum_notin_triple_const (S : Finset Z) {a b d : Z} (ha : a ∈ S) (hb : b ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (c : ℕ) :
    ∑ x ∈ S, (if x ∈ ({a, b, d} : Finset Z) then 0 else c) = (S.card - 3) * c := by
  have hT : ({a, b, d} : Finset Z) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  rw [sum_notin_const S _ hT, Finset.card_insert_of_notMem (by simp [hab, had]),
    Finset.card_pair hbd]


/-- The valid closed non-backtracking walks that backtrack twice: `s (s - 1)` of them. -/
theorem count_both (S : Finset Z) :
    ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ = z₄) then 1 else 0) =
      S.card * (S.card - 1) := by
  have hpt : ∀ z₁ z₂ z₃ z₄ : Z,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ = z₄) then 1 else 0) =
      (if z₁ = z₃ then (if z₂ = z₄ then (if z₁ = z₂ then 0 else 1) else 0) else 0) := by
    intro z₁ z₂ z₃ z₄
    by_cases h13 : z₁ = z₃
    · subst h13
      by_cases h24 : z₂ = z₄
      · subst h24
        by_cases h12 : z₁ = z₂ <;> simp [h12, Ne.symm]
      · simp [h24]
    · simp [h13]
  simp_rw [hpt]
  have h1 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
      (if z₁ = z₃ then (if z₂ = z₄ then (if z₁ = z₂ then 0 else 1) else 0) else 0) =
      (if z₁ = z₂ then 0 else 1) := by
    intro z₁ hz₁ z₂ hz₂
    simp [Finset.sum_ite_eq, hz₁, hz₂]
  rw [Finset.sum_congr rfl fun z₁ hz₁ => Finset.sum_congr rfl (h1 z₁ hz₁)]
  have h2 : ∀ z₁ ∈ S, ∑ z₂ ∈ S, (if z₁ = z₂ then 0 else 1) = S.card - 1 := by
    intro z₁ hz₁
    simpa using sum_ne_const S hz₁ 1
  rw [Finset.sum_congr rfl h2]
  simp [Finset.sum_const]


/-- The valid walks with `z₁ = z₃` and `z₂ ≠ z₄`: `s (s - 1) (s - 2)` of them. -/
theorem count_13 (S : Finset Z) :
    ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ ≠ z₄) then 1 else 0) =
      S.card * (S.card - 1) * (S.card - 2) := by
  have hpt : ∀ z₁ z₂ z₃ z₄ : Z,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ ≠ z₄) then 1 else 0) =
      (if z₁ = z₃ then (if z₁ = z₂ then 0 else (if z₄ ∈ ({z₁, z₂} : Finset Z) then 0 else 1))
        else 0) := by
    intro z₁ z₂ z₃ z₄
    by_cases h13 : z₁ = z₃
    · subst h13
      by_cases h12 : z₁ = z₂
      · simp [h12]
      · by_cases h14 : z₄ = z₁
        · simp [h14]
        · by_cases h24 : z₄ = z₂
          · simp [h24, h12]
          · simp [h12, h14, h24, Ne.symm h12, Ne.symm h14, Ne.symm h24]
    · simp [h13]
  simp_rw [hpt]
  have h1 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∀ z₃ ∈ S, ∑ z₄ ∈ S,
      (if z₁ = z₃ then (if z₁ = z₂ then 0 else (if z₄ ∈ ({z₁, z₂} : Finset Z) then 0 else 1))
        else 0) = (if z₁ = z₃ then (if z₁ = z₂ then 0 else S.card - 2) else 0) := by
    intro z₁ hz₁ z₂ hz₂ z₃ hz₃
    by_cases h13 : z₁ = z₃
    · subst h13
      by_cases h12 : z₁ = z₂
      · simp [h12]
      · simp only [h12, ↓reduceIte]
        have := sum_notin_pair_const S hz₁ hz₂ h12 1
        simpa using this
    · simp [h13]
  have h2 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∑ z₃ ∈ S, (if z₁ = z₃ then (if z₁ = z₂ then 0 else S.card - 2)
      else 0) = (if z₁ = z₂ then 0 else S.card - 2) := by
    intro z₁ hz₁ z₂ hz₂
    simp [Finset.sum_ite_eq, hz₁]
  rw [Finset.sum_congr rfl fun z₁ hz₁ => Finset.sum_congr rfl fun z₂ hz₂ =>
    (Finset.sum_congr rfl (h1 z₁ hz₁ z₂ hz₂)).trans (h2 z₁ hz₁ z₂ hz₂)]
  have h3 : ∀ z₁ ∈ S, ∑ z₂ ∈ S, (if z₁ = z₂ then 0 else S.card - 2) = (S.card - 1) * (S.card - 2) :=
    fun z₁ hz₁ => sum_ne_const S hz₁ _
  rw [Finset.sum_congr rfl h3]
  simp [Finset.sum_const, mul_assoc]


/-- The valid walks with `z₁ ≠ z₃` and `z₂ = z₄`: `s (s - 1) (s - 2)` of them. -/
theorem count_24 (S : Finset Z) :
    ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ = z₄) then 1 else 0) =
      S.card * (S.card - 1) * (S.card - 2) := by
  have hpt : ∀ z₁ z₂ z₃ z₄ : Z,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ = z₄) then 1 else 0) =
      (if z₂ = z₄ then (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else 1))
        else 0) := by
    intro z₁ z₂ z₃ z₄
    by_cases h24 : z₂ = z₄
    · subst h24
      by_cases h12 : z₁ = z₂
      · simp [h12]
      · by_cases h13 : z₃ = z₁
        · simp [h13]
        · by_cases h23 : z₃ = z₂
          · simp [h23, h12]
          · simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23]
    · simp [h24]
  simp_rw [hpt]
  have h1 : ∀ z₂ ∈ S, ∀ z₁ z₃ : Z, ∑ z₄ ∈ S,
      (if z₂ = z₄ then (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else 1))
        else 0) = (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else 1)) := by
    intro z₂ hz₂ z₁ z₃
    simp [Finset.sum_ite_eq, hz₂]
  have h2 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∑ z₃ ∈ S,
      (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else 1)) =
      (if z₁ = z₂ then 0 else S.card - 2) := by
    intro z₁ hz₁ z₂ hz₂
    by_cases h12 : z₁ = z₂
    · simp [h12]
    · simp only [h12, ↓reduceIte]
      have := sum_notin_pair_const S hz₁ hz₂ h12 1
      simpa using this
  rw [Finset.sum_congr rfl fun z₁ hz₁ => Finset.sum_congr rfl fun z₂ hz₂ =>
    (Finset.sum_congr rfl fun z₃ _ => h1 z₂ hz₂ z₁ z₃).trans (h2 z₁ hz₁ z₂ hz₂)]
  have h3 : ∀ z₁ ∈ S, ∑ z₂ ∈ S, (if z₁ = z₂ then 0 else S.card - 2) = (S.card - 1) * (S.card - 2) :=
    fun z₁ hz₁ => sum_ne_const S hz₁ _
  rw [Finset.sum_congr rfl h3]
  simp [Finset.sum_const, mul_assoc]

/-- The valid walks through four distinct rows: `s (s - 1) (s - 2) (s - 3)` of them. -/
theorem count_distinct (S : Finset Z) :
    ∑ z₁ ∈ S, ∑ z₂ ∈ S, ∑ z₃ ∈ S, ∑ z₄ ∈ S,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₄) then 1 else 0) =
      S.card * (S.card - 1) * (S.card - 2) * (S.card - 3) := by
  have hpt : ∀ z₁ z₂ z₃ z₄ : Z,
      (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₄) then 1 else 0) =
      (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else
        (if z₄ ∈ ({z₁, z₂, z₃} : Finset Z) then 0 else 1))) := by
    intro z₁ z₂ z₃ z₄
    by_cases h12 : z₁ = z₂
    · simp [h12]
    · by_cases h13 : z₃ = z₁
      · simp [h13]
      · by_cases h23 : z₃ = z₂
        · simp [h23]
        · by_cases h14 : z₄ = z₁
          · simp [h14]
          · by_cases h24 : z₄ = z₂
            · simp [h24]
            · by_cases h34 : z₄ = z₃
              · simp [h34]
              · simp [h12, h13, h23, h14, h24, h34, Ne.symm h12, Ne.symm h13, Ne.symm h23,
                  Ne.symm h14, Ne.symm h24, Ne.symm h34]
  simp_rw [hpt]
  have h1 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∀ z₃ ∈ S, ∑ z₄ ∈ S,
      (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else
        (if z₄ ∈ ({z₁, z₂, z₃} : Finset Z) then 0 else 1))) =
      (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else S.card - 3)) := by
    intro z₁ hz₁ z₂ hz₂ z₃ hz₃
    by_cases h12 : z₁ = z₂
    · simp [h12]
    · by_cases h3 : z₃ ∈ ({z₁, z₂} : Finset Z)
      · simp [h12, h3]
      · have h13 : z₁ ≠ z₃ := fun h => h3 (by simp [h])
        have h23 : z₂ ≠ z₃ := fun h => h3 (by simp [h])
        simp only [h12, h3, ↓reduceIte]
        have := sum_notin_triple_const S hz₁ hz₂ hz₃ h12 h13 h23 1
        simpa using this
  have h2 : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∑ z₃ ∈ S,
      (if z₁ = z₂ then 0 else (if z₃ ∈ ({z₁, z₂} : Finset Z) then 0 else S.card - 3)) =
      (if z₁ = z₂ then 0 else (S.card - 2) * (S.card - 3)) := by
    intro z₁ hz₁ z₂ hz₂
    by_cases h12 : z₁ = z₂
    · simp [h12]
    · simp only [h12, ↓reduceIte]
      exact sum_notin_pair_const S hz₁ hz₂ h12 _
  rw [Finset.sum_congr rfl fun z₁ hz₁ => Finset.sum_congr rfl fun z₂ hz₂ =>
    (Finset.sum_congr rfl (h1 z₁ hz₁ z₂ hz₂)).trans (h2 z₁ hz₁ z₂ hz₂)]
  have h3 : ∀ z₁ ∈ S, ∑ z₂ ∈ S, (if z₁ = z₂ then 0 else (S.card - 2) * (S.card - 3)) =
      (S.card - 1) * ((S.card - 2) * (S.card - 3)) :=
    fun z₁ hz₁ => sum_ne_const S hz₁ _
  rw [Finset.sum_congr rfl h3]
  simp [Finset.sum_const, mul_assoc]

end ExactCounts

section ExactBal

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]

theorem bal_diag (z₁ z₂ z₃ z₄ : Z) (a : Finset P) : Bal z₁ z₂ z₃ z₄ a a a a := by
  intro r
  simp

theorem bal_of_13 (z₁ z₂ z₄ : Z) (a b : Finset P) : Bal z₁ z₂ z₁ z₄ a a b b := by
  intro r
  by_cases h : z₁ = r
  · simp [h]
  · simp [h]

theorem bal_of_24 (z₁ z₂ z₃ : Z) (a b : Finset P) : Bal z₁ z₂ z₃ z₂ a b b a := by
  intro r
  by_cases h : z₂ = r
  · simp [h]
  · simp [h]


theorem bal_of_both {z₁ z₂ : Z} (h12 : z₁ ≠ z₂) {n₁ n₂ n₃ n₄ : Finset P}
    (h : n₁.val + n₃.val = n₂.val + n₄.val) : Bal z₁ z₂ z₁ z₂ n₁ n₂ n₃ n₄ := by
  have hE := (ind_four_eq_zero_iff n₁ n₂ n₃ n₄).mpr h
  intro r
  by_cases h1 : z₁ = r
  · subst h1
    simp [Ne.symm h12]
    calc ind n₄ - ind n₁ + (ind n₂ - ind n₃) = -ind n₁ + ind n₂ - ind n₃ + ind n₄ := by abel
      _ = 0 := hE
  · by_cases h2 : z₂ = r
    · subst h2
      simp [h12]
      calc ind n₁ - ind n₂ + (ind n₃ - ind n₄) = -(-ind n₁ + ind n₂ - ind n₃ + ind n₄) := by abel
        _ = 0 := by rw [hE, neg_zero]
    · simp [h1, h2]

theorem card_balSet_distinct (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ ≠ z₃) (h24 : z₂ ≠ z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card = Src.card := by
  refine le_antisymm (card_balSet_le_distinct Src h12 h23 h34 h41 h13 h24) ?_
  have hsub : Src.image (fun a => (a, a, a, a)) ⊆ balSet Src z₁ z₂ z₃ z₄ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [balSet, Finset.mem_filter]
    exact ⟨by simp [ha], bal_diag z₁ z₂ z₃ z₄ a⟩
  calc Src.card = (Src.image (fun a => (a, a, a, a))).card :=
        (Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_balSet_13 (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ = z₃) (h24 : z₂ ≠ z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card = Src.card ^ 2 := by
  refine le_antisymm (card_balSet_le_13 Src h12 h23 h34 h41 h13 h24) ?_
  have hsub : (Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2)) ⊆ balSet Src z₁ z₂ z₃ z₄ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product] at ha
    rw [balSet, Finset.mem_filter]
    subst h13
    exact ⟨by simp [ha.1, ha.2], bal_of_13 z₁ z₂ z₄ a.1 a.2⟩
  calc Src.card ^ 2 = (Src ×ˢ Src).card := by rw [Finset.card_product, sq]
    _ = ((Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2))).card :=
        (Finset.card_image_of_injective _ (fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.2.1)).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_balSet_24 (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h23 : z₂ ≠ z₃) (h34 : z₃ ≠ z₄) (h41 : z₄ ≠ z₁) (h13 : z₁ ≠ z₃) (h24 : z₂ = z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card = Src.card ^ 2 := by
  refine le_antisymm (card_balSet_le_24 Src h12 h23 h34 h41 h13 h24) ?_
  have hsub : (Src ×ˢ Src).image (fun a => (a.1, a.2, a.2, a.1)) ⊆ balSet Src z₁ z₂ z₃ z₄ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product] at ha
    rw [balSet, Finset.mem_filter]
    subst h24
    exact ⟨by simp [ha.1, ha.2], bal_of_24 z₁ z₂ z₃ a.1 a.2⟩
  calc Src.card ^ 2 = (Src ×ˢ Src).card := by rw [Finset.card_product, sq]
    _ = ((Src ×ˢ Src).image (fun a => (a.1, a.2, a.2, a.1))).card :=
        (Finset.card_image_of_injective _ (fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.1)).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_balSet_both (Src : Finset (Finset P)) {z₁ z₂ z₃ z₄ : Z} (h12 : z₁ ≠ z₂)
    (h41 : z₄ ≠ z₁) (h13 : z₁ = z₃) (h24 : z₂ = z₄) :
    (balSet Src z₁ z₂ z₃ z₄).card = energy Src := by
  refine le_antisymm (card_balSet_le_both Src h12 h41 h13 h24) ?_
  unfold energy
  refine Finset.card_le_card ?_
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hmem, hE⟩ := hx
  rw [balSet, Finset.mem_filter]
  subst h13 h24
  exact ⟨hmem, bal_of_both h12 hE⟩


theorem walkTerm_eq (Src : Finset (Finset P)) (z₁ z₂ z₃ z₄ : Z) :
    (if (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) then (balSet Src z₁ z₂ z₃ z₄).card else 0) =
      Src.card * (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₄)
          then 1 else 0) +
      Src.card ^ 2 * (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ ≠ z₄)
          then 1 else 0) +
      Src.card ^ 2 * (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ ≠ z₃ ∧ z₂ = z₄)
          then 1 else 0) +
      energy Src * (if ((z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁) ∧ z₁ = z₃ ∧ z₂ = z₄)
          then 1 else 0) := by
  by_cases hv : (z₁ ≠ z₂ ∧ z₂ ≠ z₃ ∧ z₃ ≠ z₄ ∧ z₄ ≠ z₁)
  · obtain ⟨h12, h23, h34, h41⟩ := hv
    by_cases h13 : z₁ = z₃
    · by_cases h24 : z₂ = z₄
      · have hc := card_balSet_both Src h12 h41 h13 h24
        subst h13 h24
        simp [h12, h23, h34, h41, Ne.symm h12, hc]
      · have hc := card_balSet_13 Src h12 h23 h34 h41 h13 h24
        subst h13
        simp [h12, h23, h34, h41, h24, Ne.symm h12, Ne.symm h34, Ne.symm h41, hc]
    · by_cases h24 : z₂ = z₄
      · have hc := card_balSet_24 Src h12 h23 h34 h41 h13 h24
        subst h24
        simp [h12, h23, h34, h41, h13, Ne.symm h12, Ne.symm h23, Ne.symm h34, hc]
      · have hc := card_balSet_distinct Src h12 h23 h34 h41 h13 h24
        simp [h12, h23, h34, h41, h13, h24, hc]
  · simp [hv]


/-- **The exact closed-walk count.** With `s = |S|`, `m = |Src|` and `E` the multiplicative energy:
`walkCount = s(s-1)(s-2)(s-3) m + 2 s(s-1)(s-2) m² + s(s-1) E`. -/
theorem walkCount_eq (S : Finset Z) (Src : Finset (Finset P)) :
    walkCount S Src =
      S.card * (S.card - 1) * (S.card - 2) * (S.card - 3) * Src.card +
        2 * (S.card * (S.card - 1) * (S.card - 2)) * Src.card ^ 2 +
        S.card * (S.card - 1) * energy Src := by
  unfold walkCount
  simp_rw [walkTerm_eq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, count_distinct, count_13, count_24,
    count_both]
  ring


/-- The simple upper bound, from the exact count: with `s = |S|`, `m = |Src|`, `E` the energy,
`walkCount ≤ s⁴ m + 2 s³ m² + s² E`. -/
theorem walkCount_le (S : Finset Z) (Src : Finset (Finset P)) :
    walkCount S Src ≤
      S.card ^ 4 * Src.card + 2 * (S.card ^ 3 * Src.card ^ 2) + S.card ^ 2 * energy Src := by
  rw [walkCount_eq]
  have h1 : S.card - 1 ≤ S.card := Nat.sub_le _ _
  have h2 : S.card - 2 ≤ S.card := Nat.sub_le _ _
  have h3 : S.card - 3 ≤ S.card := Nat.sub_le _ _
  have e1 : S.card * (S.card - 1) * (S.card - 2) * (S.card - 3) ≤ S.card ^ 4 := by
    calc S.card * (S.card - 1) * (S.card - 2) * (S.card - 3)
        ≤ S.card * S.card * S.card * S.card :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2) h3
      _ = S.card ^ 4 := by ring
  have e2 : S.card * (S.card - 1) * (S.card - 2) ≤ S.card ^ 3 := by
    calc S.card * (S.card - 1) * (S.card - 2) ≤ S.card * S.card * S.card :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h2
      _ = S.card ^ 3 := by ring
  have e3 : S.card * (S.card - 1) ≤ S.card ^ 2 := by
    calc S.card * (S.card - 1) ≤ S.card * S.card := Nat.mul_le_mul le_rfl h1
      _ = S.card ^ 2 := by ring
  have f1 := Nat.mul_le_mul_right Src.card e1
  have f2 := Nat.mul_le_mul_right (Src.card ^ 2) e2
  have f3 := Nat.mul_le_mul_right (energy Src) e3
  calc S.card * (S.card - 1) * (S.card - 2) * (S.card - 3) * Src.card +
        2 * (S.card * (S.card - 1) * (S.card - 2)) * Src.card ^ 2 +
        S.card * (S.card - 1) * energy Src
      ≤ S.card ^ 4 * Src.card + 2 * (S.card ^ 3 * Src.card ^ 2) + S.card ^ 2 * energy Src := by
        have : 2 * (S.card * (S.card - 1) * (S.card - 2)) * Src.card ^ 2 ≤
            2 * (S.card ^ 3 * Src.card ^ 2) := by
          calc 2 * (S.card * (S.card - 1) * (S.card - 2)) * Src.card ^ 2
              = 2 * (S.card * (S.card - 1) * (S.card - 2) * Src.card ^ 2) := by ring
            _ ≤ 2 * (S.card ^ 3 * Src.card ^ 2) := Nat.mul_le_mul le_rfl f2
        omega

/-- The energy is never below `m²`: the trivial relations `n₁ = n₂`, `n₃ = n₄` already give `m²`
solutions of `n₁ n₃ = n₂ n₄`. -/
theorem sq_card_le_energy (Src : Finset (Finset P)) : Src.card ^ 2 ≤ energy Src := by
  unfold energy
  have hsub : (Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2)) ⊆
      (Src ×ˢ Src ×ˢ Src ×ˢ Src).filter
        (fun x => x.1.val + x.2.2.1.val = x.2.1.val + x.2.2.2.val) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_product] at ha
    rw [Finset.mem_filter]
    exact ⟨by simp [ha.1, ha.2], rfl⟩
  calc Src.card ^ 2 = (Src ×ˢ Src).card := by rw [Finset.card_product, sq]
    _ = ((Src ×ˢ Src).image (fun a => (a.1, a.1, a.2, a.2))).card :=
        (Finset.card_image_of_injective _ (fun a b h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.2.1)).symm
    _ ≤ _ := Finset.card_le_card hsub

end ExactBal

/-! ### Step 3: Markov in counting form -/

section Markov

/-- **Markov, counting form.** If a nonnegative function on a finite type has sum at most
`|α| · B`, then at least half of the points have `F ≤ 2B`. -/
theorem half_good {α : Type*} [Fintype α] (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) {B : ℝ} (hB : 0 ≤ B)
    (hsum : ∑ a, F a ≤ (Fintype.card α : ℝ) * B) :
    (Fintype.card α : ℝ) ≤ 2 * ((univ.filter (fun a => F a ≤ 2 * B)).card : ℝ) := by
  classical
  rcases hB.eq_or_lt with h0 | hpos
  · subst h0
    have hz : ∑ a, F a = 0 :=
      le_antisymm (by simpa using hsum) (Finset.sum_nonneg fun a _ => hF a)
    have hall : ∀ a, F a = 0 :=
      fun a => (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hF a).mp hz a (Finset.mem_univ a)
    have : univ.filter (fun a => F a ≤ 2 * 0) = (univ : Finset α) := by
      refine Finset.filter_true_of_mem fun a _ => ?_
      rw [hall a]; norm_num
    rw [this, Finset.card_univ]
    have : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
    linarith
  · have hmark := card_filter_le_sum_div F hF (t := 2 * B) (by positivity)
    have h1 : ((univ.filter (fun a => 2 * B ≤ F a)).card : ℝ) ≤ (Fintype.card α : ℝ) / 2 := by
      refine hmark.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset α))
      (fun a => F a ≤ 2 * B)
    have h3 : (univ.filter (fun a => ¬ F a ≤ 2 * B)).card ≤
        (univ.filter (fun a => 2 * B ≤ F a)).card :=
      Finset.card_le_card fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at ha ⊢
        exact ha.le
    have h4 : ((univ.filter (fun a => F a ≤ 2 * B)).card : ℝ) +
        ((univ.filter (fun a => ¬ F a ≤ 2 * B)).card : ℝ) = Fintype.card α := by
      rw [← Nat.cast_add, h2, Finset.card_univ]
    have h5 : ((univ.filter (fun a => ¬ F a ≤ 2 * B)).card : ℝ) ≤
        ((univ.filter (fun a => 2 * B ≤ F a)).card : ℝ) := by exact_mod_cast h3
    linarith

/-- The bad points (`F > 2B`) are at most half of all points. -/
theorem card_gt_le_half {α : Type*} [Fintype α] (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) {B : ℝ}
    (hB : 0 ≤ B) (hsum : ∑ a, F a ≤ (Fintype.card α : ℝ) * B) :
    2 * ((univ.filter (fun a => 2 * B < F a)).card : ℝ) ≤ Fintype.card α := by
  classical
  have h := half_good F hF hB hsum
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset α))
    (fun a => F a ≤ 2 * B)
  have h4 : ((univ.filter (fun a => F a ≤ 2 * B)).card : ℝ) +
      ((univ.filter (fun a => ¬ F a ≤ 2 * B)).card : ℝ) = Fintype.card α := by
    rw [← Nat.cast_add, h2, Finset.card_univ]
  have h5 : univ.filter (fun a => 2 * B < F a) = univ.filter (fun a => ¬ F a ≤ 2 * B) := by
    ext a
    simp
  rw [h5]
  linarith

end Markov

/-! ### Step 4: RIP by positive measure -/

section Main

variable {P : Type*} [Fintype P] [DecidableEq P] {Z : Type*} [Fintype Z] [DecidableEq Z]
variable {ζ : ℂ}

/-- The explicit bound on the average of the centered fourth moment `tr(O⁴)`, with `s = |S|`,
`m = |Src|` and `E` the multiplicative energy of `Src`: `s⁴ m + 2 s³ m² + s² E`. -/
noncomputable def fourthBound (S : Finset Z) (Src : Finset (Finset P)) : ℝ :=
  (S.card : ℝ) ^ 4 * Src.card + 2 * ((S.card : ℝ) ^ 3 * (Src.card : ℝ) ^ 2) +
    (S.card : ℝ) ^ 2 * (energy Src : ℝ)

theorem fourthBound_nonneg (S : Finset Z) (Src : Finset (Finset P)) : 0 ≤ fourthBound S Src := by
  unfold fourthBound
  positivity

/-- The RIP constant `(2 · fourthBound)^{1/4}` that holds for at least half of the assignments. -/
noncomputable def ripConst (S : Finset Z) (Src : Finset (Finset P)) : ℝ :=
  Real.sqrt (Real.sqrt (2 * fourthBound S Src))

/-- The assignment `v` is a `κ`-near-isometry on the support `S`: for every coefficient vector
`c`, `|‖∑_{z∈S} c_z u_v z‖² − |Src| ∑ |c_z|²| ≤ κ ∑ |c_z|²` (recall `‖u_v z‖² = |Src|`). -/
def RIPOn (ζ : ℂ) (Src : Finset (Finset P)) (S : Finset Z) (κ : ℝ) (v : Z → P → ZMod 6) : Prop :=
  ∀ c : Z → ℂ, |‖∑ z ∈ S, c z • atomVec ζ Src v z‖ ^ 2 - (Src.card : ℝ) * ∑ z ∈ S, ‖c z‖ ^ 2| ≤
    κ * ∑ z ∈ S, ‖c z‖ ^ 2

noncomputable instance (ζ : ℂ) (Src : Finset (Finset P)) (S : Finset Z) (κ : ℝ) :
    DecidablePred (RIPOn ζ Src S κ) := fun _ => Classical.dec _

/-- Average of the fourth moment over all assignments: `∑_v tr(O_v⁴) ≤ (#assignments) · B`. -/
theorem sum_fourth_moment_le (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    ∑ v : Z → P → ZMod 6, ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 ≤
      (Fintype.card (Z → P → ZMod 6) : ℝ) * fourthBound S Src := by
  rw [sum_fourth_moment hζ]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  unfold fourthBound
  exact_mod_cast walkCount_le S Src

/-- **The centered fourth moment, exactly.** Summed over all assignments, `‖O_v²‖_F² = tr(O_v⁴)`
equals `(#assignments)` times `s(s-1)(s-2)(s-3) m + 2 s(s-1)(s-2) m² + s(s-1) E` (natural-number
subtraction; whenever it truncates, a factor of the product is already zero). -/
theorem sum_fourth_moment_eq (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    ∑ v : Z → P → ZMod 6, ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 =
      (Fintype.card (Z → P → ZMod 6) : ℝ) *
        ((S.card * (S.card - 1) * (S.card - 2) * (S.card - 3) * Src.card +
          2 * (S.card * (S.card - 1) * (S.card - 2)) * Src.card ^ 2 +
          S.card * (S.card - 1) * energy Src : ℕ) : ℝ) := by
  rw [sum_fourth_moment hζ, walkCount_eq]

/-- A small fourth moment gives RIP (the deterministic half; `fourth_moment_rip`). -/
theorem ripOn_of_fourth_moment_le (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z)
    (Src : Finset (Finset P)) {v : Z → P → ZMod 6} {T : ℝ}
    (hT : ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 ≤ T) :
    RIPOn ζ Src S (Real.sqrt (Real.sqrt T)) v := by
  intro c
  have h := fourth_moment_rip S c (atomVec ζ Src v)
  have hn : ∀ z, ‖atomVec ζ Src v z‖ ^ 2 = Src.card := fun z => norm_atomVec_sq hζ Src v z
  simp_rw [hn] at h
  have e : ∑ z ∈ S, ‖c z‖ ^ 2 * (Src.card : ℝ) = Src.card * ∑ z ∈ S, ‖c z‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hT))
    (Finset.sum_nonneg fun z _ => by positivity))

/-- **RIP by positive measure for random multiplicative atoms on a fixed support.**
Let `Z` be a finite set of rows, `P` a finite set of primes, `Src` a finite set of sources
(squarefree numbers, i.e. sets of primes) and `S ⊆ Z` a support. Over all
`6^{|Z||P|}` assignments `v : Z → P → ZMod 6` (counting measure), at least half give atoms
`u_v z n = ∏_{p∈n} ζ^{v z p}` (`ζ` a primitive sixth root of unity) with
`|‖∑_{z∈S} c_z u_v z‖² − |Src| ∑|c_z|²| ≤ (2B)^{1/4} ∑|c_z|²` for all coefficients `c`, where
`B = |S|⁴|Src| + 2|S|³|Src|² + |S|² E(Src)` and `E(Src)` is the multiplicative energy. -/
theorem rip_positive_measure (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    (Fintype.card (Z → P → ZMod 6) : ℝ) ≤
      2 * ((univ.filter (fun v : Z → P → ZMod 6 =>
        RIPOn ζ Src S (ripConst S Src) v)).card : ℝ) := by
  have h := half_good
    (fun v : Z → P → ZMod 6 => ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2)
    (fun v => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    (fourthBound_nonneg S Src) (sum_fourth_moment_le hζ S Src)
  refine h.trans ?_
  have hsub : univ.filter (fun v : Z → P → ZMod 6 =>
      ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 ≤ 2 * fourthBound S Src) ⊆
      univ.filter (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ripOn_of_fourth_moment_le hζ S Src hv
  have := Finset.card_le_card hsub
  have : ((univ.filter (fun v : Z → P → ZMod 6 =>
      ∑ z₁ ∈ S, ∑ z₃ ∈ S, ‖offG2 S (atomVec ζ Src v) z₁ z₃‖ ^ 2 ≤
        2 * fourthBound S Src)).card : ℝ) ≤
      ((univ.filter (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v)).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- **Probability form.** For a uniformly random assignment, the near-isometry property on `S`
holds with probability at least `1/2`. -/
theorem rip_probability_half (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    (1 / 2 : ℝ) ≤ ((univ.filter (fun v : Z → P → ZMod 6 =>
        RIPOn ζ Src S (ripConst S Src) v)).card : ℝ) / Fintype.card (Z → P → ZMod 6) := by
  have hpos : (0 : ℝ) < Fintype.card (Z → P → ZMod 6) := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hpos]
  have := rip_positive_measure hζ S Src
  linarith

/-- In particular a good assignment exists. -/
theorem exists_rip_assignment (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z) (Src : Finset (Finset P)) :
    ∃ v : Z → P → ZMod 6, RIPOn ζ Src S (ripConst S Src) v := by
  have h := rip_positive_measure hζ S Src
  have hpos : (0 : ℝ) < Fintype.card (Z → P → ZMod 6) := by exact_mod_cast Fintype.card_pos
  have hcard : 0 <
      (univ.filter (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v)).card := by
    by_contra hcon
    have h0 : (univ.filter
        (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v)).card = 0 :=
      Nat.eq_zero_of_not_pos hcon
    rw [h0, Nat.cast_zero, mul_zero] at h
    linarith
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

/-- The normalized form of `RIPOn`: the atoms `u_v z / √|Src|` have unit norm, and
`|‖∑ c_z u_v z / √|Src|‖² − ∑|c_z|²| ≤ κ ∑|c_z|²`. -/
def RIPOnNorm (ζ : ℂ) (Src : Finset (Finset P)) (S : Finset Z) (κ : ℝ) (v : Z → P → ZMod 6) :
    Prop :=
  ∀ c : Z → ℂ, |(Src.card : ℝ)⁻¹ * ‖∑ z ∈ S, c z • atomVec ζ Src v z‖ ^ 2 - ∑ z ∈ S, ‖c z‖ ^ 2| ≤
    κ * ∑ z ∈ S, ‖c z‖ ^ 2

noncomputable instance (ζ : ℂ) (Src : Finset (Finset P)) (S : Finset Z) (κ : ℝ) :
    DecidablePred (RIPOnNorm ζ Src S κ) := fun _ => Classical.dec _

/-- **Normalized form.** At least half of the assignments give the unit-norm atoms
`u_v z / √|Src|` restricted-isometry constant `(2B)^{1/4} / |Src|` on `S`. -/
theorem rip_positive_measure_normalized (hζ : IsPrimitiveRoot ζ 6) (S : Finset Z)
    (Src : Finset (Finset P)) (hm : 0 < Src.card) :
    (Fintype.card (Z → P → ZMod 6) : ℝ) ≤
      2 * ((univ.filter (fun v : Z → P → ZMod 6 =>
        RIPOnNorm ζ Src S (ripConst S Src / Src.card) v)).card : ℝ) := by
  have hm' : (0 : ℝ) < Src.card := by exact_mod_cast hm
  refine (rip_positive_measure hζ S Src).trans ?_
  have hsub : univ.filter (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v) ⊆
      univ.filter (fun v : Z → P → ZMod 6 => RIPOnNorm ζ Src S (ripConst S Src / Src.card) v) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro c
    have h := hv c
    have e : (Src.card : ℝ)⁻¹ * ‖∑ z ∈ S, c z • atomVec ζ Src v z‖ ^ 2 - ∑ z ∈ S, ‖c z‖ ^ 2 =
        (Src.card : ℝ)⁻¹ * (‖∑ z ∈ S, c z • atomVec ζ Src v z‖ ^ 2 -
          (Src.card : ℝ) * ∑ z ∈ S, ‖c z‖ ^ 2) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (inv_pos.mpr hm'), div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (inv_pos.mpr hm').le
  have := Finset.card_le_card hsub
  have : ((univ.filter (fun v : Z → P → ZMod 6 => RIPOn ζ Src S (ripConst S Src) v)).card : ℝ) ≤
      ((univ.filter (fun v : Z → P → ZMod 6 =>
        RIPOnNorm ζ Src S (ripConst S Src / Src.card) v)).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- The hypothesis is satisfiable: `ζ = exp(2πi/6)`. -/
theorem rip_positive_measure_exp (S : Finset Z) (Src : Finset (Finset P)) :
    (Fintype.card (Z → P → ZMod 6) : ℝ) ≤
      2 * ((univ.filter (fun v : Z → P → ZMod 6 =>
        RIPOn (Complex.exp (2 * Real.pi * Complex.I / 6)) Src S (ripConst S Src) v)).card : ℝ) :=
  rip_positive_measure (Complex.isPrimitiveRoot_exp 6 (by norm_num)) S Src

end Main

end QRH.ArviRIP

#print axioms QRH.ArviRIP.sum_psi_mul_conj
#print axioms QRH.ArviRIP.sum_psi_four
#print axioms QRH.ArviRIP.sum_norm_gram_sq
#print axioms QRH.ArviRIP.sum_fourth_moment
#print axioms QRH.ArviRIP.walkCount_eq
#print axioms QRH.ArviRIP.sum_fourth_moment_eq
#print axioms QRH.ArviRIP.walkCount_le
#print axioms QRH.ArviRIP.card_gt_le_half
#print axioms QRH.ArviRIP.rip_positive_measure
#print axioms QRH.ArviRIP.rip_probability_half
#print axioms QRH.ArviRIP.exists_rip_assignment
#print axioms QRH.ArviRIP.rip_positive_measure_normalized
#print axioms QRH.ArviRIP.rip_positive_measure_exp
