import Mathlib

/-!
# The quadratic Davenport–Hasse relation (research file, D1: a face proved outside Sil's packing)

For a finite field `F` of odd characteristic, a nontrivial multiplicative character `χ` and the quadratic
character `η`:
* `chi_four_mul_jacobiSum_self`: `χ(4) · J(χ, χ) = J(χ, η)`;
* `gaussSum_duplication`: `χ(4) · g(χ) g(χη) = g(χ²) g(η)` (values in a field, `ψ` primitive);
* `sextic_duplication`: for `χ` of order 6 (so `η = χ³`), `χ(4) · g(χ) g(χ⁴) = g(χ²) g(χ³)`.

The last identity turns the sextic Gauss sum at a prime into a conjugate cubic Gauss sum times a
Hecke-character factor, which is the reduction behind direction D1 (fresh look 2).
Proof of the first: `J(χ, χ) = Σ_b χ(b) #{x : x(1 − x) = b}` and `#{x : x(1 − x) = b} = 1 + η(1 − 4b)`, by
`x ↦ 2x − 1`; then reindex `c = 4b`.
-/

namespace QRH.ArviPrimeFace

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of `F` with values in a commutative ring `R`. -/
noncomputable def eta (F R : Type*) [Field F] [Fintype F] [DecidableEq F] [CommRing R] : MulChar F R :=
  (quadraticChar F).ringHomComp (Int.castRingHom R)

theorem eta_apply (R : Type*) [CommRing R] (a : F) : eta F R a = ((quadraticChar F a : ℤ) : R) := rfl

/-- `#{x : x(1 − x) = b} = η(1 − 4b) + 1`. -/
theorem card_quad_fiber (hF : ringChar F ≠ 2) (b : F) :
    ((univ.filter (fun x : F => x * (1 - x) = b)).card : ℤ) = quadraticChar F (1 - 4 * b) + 1 := by
  rw [← quadraticChar_card_sqrts hF (1 - 4 * b)]
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  congr 1
  apply Finset.card_nbij' (fun x => 2 * x - 1) (fun y => (y + 1) / 2)
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simp only [Set.coe_toFinset, Set.mem_ofPred_eq]
    rw [← hx]; ring
  · intro y hy
    simp only [Set.coe_toFinset, Set.mem_ofPred_eq] at hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have : (y + 1) / 2 * (1 - (y + 1) / 2) = (1 - y ^ 2) / 4 := by field_simp; ring
    rw [this, hy]
    field_simp; ring
  · intro x _; field_simp; ring
  · intro y _; field_simp; ring

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `J(χ, χ) = Σ_b χ(b) η(1 − 4b)` for nontrivial `χ`. -/
theorem jacobiSum_self_eq (hF : ringChar F ≠ 2) {χ : MulChar F R} (hχ : χ ≠ 1) :
    jacobiSum χ χ = ∑ b : F, χ b * eta F R (1 - 4 * b) := by
  have h1 : jacobiSum χ χ = ∑ x : F, χ (x * (1 - x)) := by
    unfold jacobiSum
    exact Finset.sum_congr rfl (fun x _ => (map_mul χ x (1 - x)).symm)
  have h2 : ∑ x : F, χ (x * (1 - x)) =
      ∑ b : F, ((univ.filter (fun x : F => x * (1 - x) = b)).card : R) * χ b := by
    rw [← Finset.sum_fiberwise univ (fun x : F => x * (1 - x)) (fun x => χ (x * (1 - x)))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), Finset.sum_const,
      nsmul_eq_mul]
  have h3 : ∀ b : F, ((univ.filter (fun x : F => x * (1 - x) = b)).card : R) =
      eta F R (1 - 4 * b) + 1 := by
    intro b
    have := congrArg (fun z : ℤ => (z : R)) (card_quad_fiber hF b)
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_one] at this
    rw [this, eta_apply]
  rw [h1, h2]
  simp_rw [h3, add_mul, one_mul, Finset.sum_add_distrib, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

/-- **Quadratic Davenport–Hasse for Jacobi sums:** `χ(4) · J(χ, χ) = J(χ, η)`. -/
theorem chi_four_mul_jacobiSum_self (hF : ringChar F ≠ 2) {χ : MulChar F R} (hχ : χ ≠ 1) :
    χ 4 * jacobiSum χ χ = jacobiSum χ (eta F R) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hR : jacobiSum χ (eta F R) = ∑ b : F, χ (4 * b) * eta F R (1 - 4 * b) := by
    unfold jacobiSum
    exact (Equiv.sum_comp (Equiv.mulLeft₀ (4 : F) h4) (fun c => χ c * eta F R (1 - c))).symm
  rw [hR, jacobiSum_self_eq hF hχ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul]; ring

/-- **Quadratic Davenport–Hasse for Gauss sums (duplication):** `χ(4) g(χ) g(χη) = g(χ²) g(η)`. -/
theorem gaussSum_duplication {F' : Type*} [Field F'] (hF : ringChar F ≠ 2)
    (hcard : (Fintype.card F : F') ≠ 0) {χ : MulChar F F'} (hχ : χ ≠ 1) (hχ2 : χ * χ ≠ 1)
    (hχη : χ * eta F F' ≠ 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    χ 4 * (gaussSum χ ψ * gaussSum (χ * eta F F') ψ) = gaussSum (χ * χ) ψ * gaussSum (eta F F') ψ := by
  have e1 := jacobiSum_mul_nontrivial hχ2 ψ
  have e2 := jacobiSum_mul_nontrivial hχη ψ
  have e3 := chi_four_mul_jacobiSum_self hF hχ (R := F')
  have hg : gaussSum χ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hχ hψ
  have hJ : jacobiSum χ χ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hg (by simpa using e1.symm)
  apply mul_left_cancel₀ hJ
  calc jacobiSum χ χ * (χ 4 * (gaussSum χ ψ * gaussSum (χ * eta F F') ψ))
      = gaussSum χ ψ * (gaussSum (χ * eta F F') ψ * (χ 4 * jacobiSum χ χ)) := by ring
    _ = gaussSum χ ψ * (gaussSum χ ψ * gaussSum (eta F F') ψ) := by rw [e3, e2]
    _ = (gaussSum (χ * χ) ψ * jacobiSum χ χ) * gaussSum (eta F F') ψ := by rw [e1]; ring
    _ = jacobiSum χ χ * (gaussSum (χ * χ) ψ * gaussSum (eta F F') ψ) := by ring

/-- **Sextic case.** If `χ³ = η` (e.g. `χ` of order 6), then `χ(4) g(χ) g(χ⁴) = g(χ²) g(χ³)`. -/
theorem sextic_duplication {F' : Type*} [Field F'] (hF : ringChar F ≠ 2)
    (hcard : (Fintype.card F : F') ≠ 0) {χ : MulChar F F'} (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (hχ4 : χ ^ 4 ≠ 1) (hη : χ ^ 3 = eta F F') {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    χ 4 * (gaussSum χ ψ * gaussSum (χ ^ 4) ψ) = gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ := by
  have h4 : χ ^ 4 = χ * eta F F' := by rw [← hη]; exact pow_succ' χ 3
  have h2 : χ ^ 2 = χ * χ := sq χ
  rw [h4] at hχ4 ⊢
  rw [h2] at hχ2 ⊢
  rw [hη]
  exact gaussSum_duplication hF hcard hχ hχ2 hχ4 hψ

end QRH.ArviPrimeFace

#print axioms QRH.ArviPrimeFace.chi_four_mul_jacobiSum_self
#print axioms QRH.ArviPrimeFace.gaussSum_duplication
#print axioms QRH.ArviPrimeFace.sextic_duplication
