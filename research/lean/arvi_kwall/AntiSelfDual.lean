import Mathlib

/-!
# Anti-self-dual Gram matrices are capped at twice the diagonal

Research file (QRH, K-wall; the journal entry "No anti-self-dual row class"). This documents an idea that the
numerics refuted: a row class whose off-diagonal Gram `A` is anti-self-dual under Poisson duality would have
its top eigenvalue capped at about twice the diagonal, so it would carry no excess at the balanced point.

Let `A` be an `n × n` complex matrix, `U` unitary and `Aᶜ` the entrywise complex conjugate of `A`. Say `A` is
*anti-self-dual* if `A = -U Aᶜ Uᴴ` (`AntiSelfDual`), and *self-dual with the "+" sign* if `A = U Aᶜ Uᴴ`
(`SelfDualPlus`). Write `⟨x, A x⟩ = ∑ conj (x i) (A x) i`.

* `exists_flip`: if `A = -U Aᶜ Uᴴ`, then for every `x` there is `y` with `‖y‖ = ‖x‖` and
  `Re⟨x, A x⟩ = -Re⟨y, A y⟩`, namely `y = conj (Uᴴ x)`. (`form_flip`, `sum_sq_flip`.)
* `two_d_bound`: if moreover `G = D + A` is positive semidefinite, with `D` real diagonal and
  `0 ≤ D_ii ≤ d`, then `Re⟨x, G x⟩ ≤ 2 d ‖x‖²` for all `x`. Proof: `Re⟨x, A x⟩ = -Re⟨y, A y⟩ ≤ Re⟨y, D y⟩ ≤ d ‖y‖²`
  because `Re⟨y, G y⟩ ≥ 0`, and `Re⟨x, D x⟩ ≤ d ‖x‖²`.
* `eigenvalue_le_two_d` and `eigenvalues_le_two_d`: so every eigenvalue of `G` is at most `2 d`, i.e.
  `λ_max(G) ≤ 2 d`.
* `two_d_bound_sharp`: the constant `2` cannot be improved: `σ_y` is anti-self-dual (`U = 1`) and
  `G = 1 + σ_y` has the eigenvalue `2 = 2 d`.
* `plus_sign_no_cap`: the "+" sign gives no cap. For `A = J` (all ones, real, so `A = 1 Aᶜ 1ᴴ`) on `m ≥ 2`
  indices and `D = 1` (`d = 1`), `G = 1 + J` is positive semidefinite and has the eigenvalue `m + 1 > 2 d`.

Hermiticity of `A` and the lower bound `0 ≤ D_ii` are not used in the proofs of the `2 d` bound; in the
setting of the journal `A` is Hermitian anyway (it is `G - D` for the Hermitian `G`).
-/

set_option autoImplicit false

namespace QRH.ArviKWall

open Matrix
open scoped BigOperators ComplexOrder ComplexConjugate Matrix

section AntiSelfDual

variable {n : Type*} [Fintype n]

/-- `A = -U Aᶜ Uᴴ`, where `Aᶜ` is the entrywise complex conjugate. -/
def AntiSelfDual (A U : Matrix n n ℂ) : Prop := A = -(U * A.map (starRingEnd ℂ) * Uᴴ)

/-- `A = U Aᶜ Uᴴ` (the opposite sign). -/
def SelfDualPlus (A U : Matrix n n ℂ) : Prop := A = U * A.map (starRingEnd ℂ) * Uᴴ

/-- `‖x‖² = Re ⟨x, x⟩`. -/
theorem sum_sq_eq_re (x : n → ℂ) : ∑ i, ‖x i‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h : star x ⬝ᵥ x = ∑ i, star (x i) * x i := rfl
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Conjugating the entries conjugates the form: `⟨w, Aᶜ w⟩ = conj ⟨conj w, A conj w⟩`. -/
theorem form_map_conj (B : Matrix n n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ (B.map (starRingEnd ℂ) *ᵥ w) = star (star (star w) ⬝ᵥ (B *ᵥ star w)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Matrix.map_apply,
    Complex.star_def, starRingEnd_self_apply]

/-- The form of a unitary conjugate: `⟨x, U B Uᴴ x⟩ = ⟨Uᴴ x, B Uᴴ x⟩`. -/
theorem form_unitary_conj (B U : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((U * B * Uᴴ) *ᵥ x) = star (Uᴴ *ᵥ x) ⬝ᵥ (B *ᵥ (Uᴴ *ᵥ x)) := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, ← mulVec_mulVec,
    ← dotProduct_mulVec]

/-- **The flip.** If `A = -U Aᶜ Uᴴ`, then with `y = conj (Uᴴ x)`: `Re⟨x, A x⟩ = -Re⟨y, A y⟩`.
(Neither Hermiticity of `A` nor unitarity of `U` is used here.) -/
theorem form_flip {A U : Matrix n n ℂ} (hA : AntiSelfDual A U) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      -(star (star (Uᴴ *ᵥ x)) ⬝ᵥ (A *ᵥ star (Uᴴ *ᵥ x))).re := by
  have h1 : A *ᵥ x = -((U * A.map (starRingEnd ℂ) * Uᴴ) *ᵥ x) := by
    conv_lhs => rw [hA]
    rw [neg_mulVec]
  have h2 : star x ⬝ᵥ (A *ᵥ x) =
      -(star (Uᴴ *ᵥ x) ⬝ᵥ (A.map (starRingEnd ℂ) *ᵥ (Uᴴ *ᵥ x))) := by
    rw [h1, dotProduct_neg, form_unitary_conj]
  rw [h2, form_map_conj A (Uᴴ *ᵥ x)]
  simp

variable [DecidableEq n]

/-- A unitary matrix preserves the norm: `‖conj (Uᴴ x)‖ = ‖x‖`. -/
theorem sum_sq_flip {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (x : n → ℂ) :
    ∑ i, ‖(star (Uᴴ *ᵥ x)) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h1 : ∑ i, ‖(star (Uᴴ *ᵥ x)) i‖ ^ 2 = ∑ i, ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
    simp [Pi.star_apply]
  rw [h1, sum_sq_eq_re, sum_sq_eq_re, star_mulVec, conjTranspose_conjTranspose,
    ← dotProduct_mulVec, mulVec_mulVec, hUU, one_mulVec]

/-- **Anti-self-dual forms are symmetric about zero.** If `A = -U Aᶜ Uᴴ` with `U` unitary, then for
every `x` there is `y` with `‖y‖ = ‖x‖` and `Re⟨x, A x⟩ = -Re⟨y, A y⟩` (namely `y = conj (Uᴴ x)`). -/
theorem exists_flip {A U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (hA : AntiSelfDual A U)
    (x : n → ℂ) :
    ∃ y : n → ℂ, ∑ i, ‖y i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 ∧
      (star x ⬝ᵥ (A *ᵥ x)).re = -(star y ⬝ᵥ (A *ᵥ y)).re :=
  ⟨star (Uᴴ *ᵥ x), sum_sq_flip hU x, form_flip hA x⟩

/-- The real part of the form of a real diagonal matrix. -/
theorem re_form_diagonal (D : n → ℝ) (x : n → ℂ) :
    (star x ⬝ᵥ (Matrix.diagonal (fun i => (D i : ℂ)) *ᵥ x)).re = ∑ i, D i * ‖x i‖ ^ 2 := by
  have h : star x ⬝ᵥ (Matrix.diagonal (fun i => (D i : ℂ)) *ᵥ x) =
      ∑ i, star (x i) * ((D i : ℂ) * x i) := by
    simp only [dotProduct, Pi.star_apply, mulVec_diagonal]
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (x i) * ((D i : ℂ) * x i) = ((D i * ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  rw [this, Complex.ofReal_re]

/-- **Anti-self-dual Gram matrices are capped at twice the diagonal.** Let `A = -U Aᶜ Uᴴ` with `U`
unitary and `G = D + A` positive semidefinite, with `D` real diagonal and `0 ≤ D_ii ≤ d`. Then
`Re⟨x, G x⟩ ≤ 2 d ‖x‖²` for all `x`. (The lower bound `0 ≤ D_ii` is not used.) -/
theorem two_d_bound {A U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (hA : AntiSelfDual A U)
    {D : n → ℝ} {d : ℝ} (hD : ∀ i, 0 ≤ D i ∧ D i ≤ d)
    (hG : (Matrix.diagonal (fun i => (D i : ℂ)) + A).PosSemidef) (x : n → ℂ) :
    (star x ⬝ᵥ ((Matrix.diagonal (fun i => (D i : ℂ)) + A) *ᵥ x)).re ≤ 2 * d * ∑ i, ‖x i‖ ^ 2 := by
  have hsplit : ∀ z : n → ℂ, (star z ⬝ᵥ ((Matrix.diagonal (fun i => (D i : ℂ)) + A) *ᵥ z)).re =
      ∑ i, D i * ‖z i‖ ^ 2 + (star z ⬝ᵥ (A *ᵥ z)).re := by
    intro z
    rw [add_mulVec, dotProduct_add, Complex.add_re, re_form_diagonal]
  have hdiag : ∀ z : n → ℂ, ∑ i, D i * ‖z i‖ ^ 2 ≤ d * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i).2 (sq_nonneg _)
  obtain ⟨y, hy, hxy⟩ := exists_flip hU hA x
  have hy0 : 0 ≤ ∑ i, D i * ‖y i‖ ^ 2 + (star y ⬝ᵥ (A *ᵥ y)).re := by
    rw [← hsplit y]
    simpa using hG.re_dotProduct_nonneg y
  have h1 := hdiag x
  have h2 := hdiag y
  rw [hy] at h2
  rw [hsplit x]
  linarith only [hxy, hy0, h1, h2]

/-- **Every eigenvalue is at most `2d`.** Under the hypotheses of `two_d_bound`, a real eigenvalue `μ`
of `G = D + A` satisfies `μ ≤ 2 d`; so `λ_max(G) ≤ 2 d`. -/
theorem eigenvalue_le_two_d {A U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hA : AntiSelfDual A U) {D : n → ℝ} {d : ℝ} (hD : ∀ i, 0 ≤ D i ∧ D i ≤ d)
    (hG : (Matrix.diagonal (fun i => (D i : ℂ)) + A).PosSemidef) {μ : ℝ} {v : n → ℂ} (hv : v ≠ 0)
    (hGv : (Matrix.diagonal (fun i => (D i : ℂ)) + A) *ᵥ v = μ • v) : μ ≤ 2 * d := by
  have hpos : 0 < ∑ i, ‖v i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hform : (star v ⬝ᵥ ((Matrix.diagonal (fun i => (D i : ℂ)) + A) *ᵥ v)).re =
      μ * ∑ i, ‖v i‖ ^ 2 := by
    rw [hGv, dotProduct_smul, sum_sq_eq_re, Complex.real_smul, Complex.re_ofReal_mul]
  have hb := two_d_bound hU hA hD hG v
  rw [hform] at hb
  by_contra hcon
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hcon) hpos
  linarith only [hlt, hb]

/-- **`λ_max(G) ≤ 2d`, in terms of the spectral decomposition.** Every eigenvalue of the Hermitian
matrix `G = D + A` is at most `2 d`. -/
theorem eigenvalues_le_two_d {A U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hA : AntiSelfDual A U) {D : n → ℝ} {d : ℝ} (hD : ∀ i, 0 ≤ D i ∧ D i ≤ d)
    (hG : (Matrix.diagonal (fun i => (D i : ℂ)) + A).PosSemidef) (i : n) :
    hG.isHermitian.eigenvalues i ≤ 2 * d := by
  refine eigenvalue_le_two_d hU hA hD hG ?_ (hG.isHermitian.mulVec_eigenvectorBasis i)
  intro h
  refine (hG.isHermitian.eigenvectorBasis.orthonormal.ne_zero i) ?_
  ext j
  simpa using congrFun h j

/-! ### The cap is attained: `σ_y` -/

/-- The Pauli matrix `σ_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

theorem sigmaY_antiSelfDual : AntiSelfDual sigmaY 1 := by
  unfold AntiSelfDual
  rw [conjTranspose_one, one_mul, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaY]

theorem sigmaY_posSemidef :
    (Matrix.diagonal (fun _ : Fin 2 => (((1 : ℝ)) : ℂ)) + sigmaY).PosSemidef := by
  have h : Matrix.diagonal (fun _ : Fin 2 => (((1 : ℝ)) : ℂ)) + sigmaY =
      Matrix.vecMulVec ![1, Complex.I] (star ![1, Complex.I]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaY, Matrix.vecMulVec]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem sigmaY_eigen :
    (Matrix.diagonal (fun _ : Fin 2 => (((1 : ℝ)) : ℂ)) + sigmaY) *ᵥ ![1, Complex.I] =
      (2 * (1 : ℝ)) • ![1, Complex.I] := by
  ext i
  fin_cases i <;> simp [sigmaY, mulVec, dotProduct, Fin.sum_univ_two] <;> ring_nf

/-- **The cap `2 d` is attained.** `σ_y` is anti-self-dual (with `U = 1`), `G = 1 + σ_y` is positive
semidefinite with `D = 1` (`d = 1`), and `G` has the eigenvalue `2 = 2 d`. -/
theorem two_d_bound_sharp :
    AntiSelfDual sigmaY 1 ∧
    (Matrix.diagonal (fun _ : Fin 2 => (((1 : ℝ)) : ℂ)) + sigmaY).PosSemidef ∧
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (Matrix.diagonal (fun _ : Fin 2 => (((1 : ℝ)) : ℂ)) + sigmaY) *ᵥ v = (2 * (1 : ℝ)) • v := by
  refine ⟨sigmaY_antiSelfDual, sigmaY_posSemidef, ![1, Complex.I], ?_, sigmaY_eigen⟩
  intro h
  have := congrFun h 0
  simp at this

/-! ### The opposite sign gives no cap -/

/-- The all-ones matrix. It is real, so `J = 1 · Jᶜ · 1ᴴ`: the "+" sign of the duality. -/
def onesMat (n : Type*) [Fintype n] : Matrix n n ℂ := Matrix.of fun _ _ => 1

theorem onesMat_selfDualPlus : SelfDualPlus (onesMat n) 1 := by
  unfold SelfDualPlus
  rw [conjTranspose_one, one_mul, mul_one]
  ext i j
  simp [onesMat]

omit [DecidableEq n] in
theorem onesMat_isHermitian : (onesMat n).IsHermitian := by
  ext i j
  simp [onesMat]

theorem onesMat_posSemidef :
    (Matrix.diagonal (fun _ : n => (((1 : ℝ)) : ℂ)) + onesMat n).PosSemidef := by
  have h1 : Matrix.diagonal (fun _ : n => (((1 : ℝ)) : ℂ)) = 1 := by
    rw [← Matrix.diagonal_one]; simp
  have h2 : onesMat n = Matrix.vecMulVec (fun _ => (1 : ℂ)) (star fun _ => (1 : ℂ)) := by
    ext i j; simp [onesMat, Matrix.vecMulVec]
  rw [h1, h2]
  exact Matrix.PosSemidef.one.add (Matrix.posSemidef_vecMulVec_self_star _)

theorem onesMat_eigen :
    (Matrix.diagonal (fun _ : n => (((1 : ℝ)) : ℂ)) + onesMat n) *ᵥ (fun _ => (1 : ℂ)) =
      ((Fintype.card n : ℝ) + 1) • (fun _ => (1 : ℂ)) := by
  ext i
  have h1 : (Matrix.diagonal (fun _ : n => (((1 : ℝ)) : ℂ)) *ᵥ (fun _ => (1 : ℂ))) i = 1 := by
    simp
  have h2 : (onesMat n *ᵥ (fun _ => (1 : ℂ))) i = (Fintype.card n : ℂ) := by
    simp [onesMat, mulVec, dotProduct]
  rw [add_mulVec, Pi.add_apply, h1, h2]
  simp [add_comm]

/-- **The "+" sign gives no cap.** For `A = J` (the all-ones matrix on `m ≥ 2` indices), `U = 1`,
`D = 1` (so `d = 1`): `A` is Hermitian, `A = U Aᶜ Uᴴ` holds (`1` is unitary), `G = D + A` is positive
semidefinite, `0 ≤ D_ii ≤ 1`, and yet `G` has the eigenvalue `m + 1 > 2 = 2 d`; the eigenvalue is
unbounded in `m`. -/
theorem plus_sign_no_cap (m : ℕ) (hm : 2 ≤ m) :
    (onesMat (Fin m)).IsHermitian ∧ SelfDualPlus (onesMat (Fin m)) 1 ∧
    (Matrix.diagonal (fun _ : Fin m => (((1 : ℝ)) : ℂ)) + onesMat (Fin m)).PosSemidef ∧
    ∃ v : Fin m → ℂ, v ≠ 0 ∧
      (Matrix.diagonal (fun _ : Fin m => (((1 : ℝ)) : ℂ)) + onesMat (Fin m)) *ᵥ v =
        ((m : ℝ) + 1) • v ∧ 2 * (1 : ℝ) < (m : ℝ) + 1 := by
  refine ⟨onesMat_isHermitian, onesMat_selfDualPlus, onesMat_posSemidef, fun _ => 1, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  · simpa using onesMat_eigen (n := Fin m)
  · have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [this]

end AntiSelfDual

end QRH.ArviKWall

#print axioms QRH.ArviKWall.exists_flip
#print axioms QRH.ArviKWall.two_d_bound
#print axioms QRH.ArviKWall.eigenvalue_le_two_d
#print axioms QRH.ArviKWall.eigenvalues_le_two_d
#print axioms QRH.ArviKWall.two_d_bound_sharp
#print axioms QRH.ArviKWall.plus_sign_no_cap
