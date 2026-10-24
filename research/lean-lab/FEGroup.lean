/-
The functional-equation group of the inverse-moment mean value (research/LOG.md, round-4 spectral
report). Coordinates are centered at (1/2, 1/2, 1/2): `x₁ = s₁ − 1/2`, `x₂ = s₂ − 1/2` are the two
column variables and `y = w − 1/2` is the row variable of
`Z(s₁, s₂, w) = Σ_rows N(row)^{-w} · [column sum at s₁] · [column sum at s₂]`.
* `A`: Poisson summation in the row, `(x₁, x₂, y) ↦ (x₁ + y, x₂ + y, −y)`;
* `B₁`, `B₂`: theta reflection in one column, `(x₁, x₂, y) ↦ (−x₁, x₂, y + 2x₁)` and symmetrically.
Proved here:
* all three are involutions, with `(A B₁)⁴ = (A B₂)⁴ = (B₁ B₂)² = 1`: Coxeter labels (4, 4, 2), and
  1/4 + 1/4 + 1/2 = 1, so the group is the affine group of type C̃₂ (infinite);
* `A B₁ B₂` has infinite order: `T = (A B₁ B₂)²` satisfies `(T − 1)² = 0` and `T ≠ 1`, so `Tᵏ = 1 + k(T − 1)`;
* the linear form `x₁ + x₂ + y` (i.e. `s₁ + s₂ + w`) is invariant under all three generators.
So no combination of row Poisson steps and column reflections changes `s₁ + s₂ + w`. That is the
formal content of "Poisson twice is the identity". Only the Hecke operations of the method
(cube completion on the cubic theta, sixth-power copies on the sextic family) move it, which is
why the exchange rates 3 and 6 cap every amplifier.
Status: proved (exact integer matrix computations).
-/
import Mathlib

namespace FEGroup

open Matrix

/-- Poisson summation in the row variable. -/
def A : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 1; 0, 1, 1; 0, 0, -1]
/-- Theta reflection in the first column variable. -/
def B₁ : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, 1, 0; 2, 0, 1]
/-- Theta reflection in the second column variable. -/
def B₂ : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, -1, 0; 0, 2, 1]

theorem A_sq : A * A = 1 := by decide
theorem B₁_sq : B₁ * B₁ = 1 := by decide
theorem B₂_sq : B₂ * B₂ = 1 := by decide

theorem AB₁_order4 : (A * B₁) ^ 4 = 1 := by decide
theorem AB₂_order4 : (A * B₂) ^ 4 = 1 := by decide
theorem B₁B₂_order2 : (B₁ * B₂) ^ 2 = 1 := by decide
theorem AB₁_ne_one : (A * B₁) ^ 2 ≠ 1 := by decide
theorem AB₂_ne_one : (A * B₂) ^ 2 ≠ 1 := by decide

/-- The square of the Coxeter element is a nontrivial unipotent matrix. -/
def T : Matrix (Fin 3) (Fin 3) ℤ := (A * B₁ * B₂) ^ 2

theorem T_unipotent : (T - 1) * (T - 1) = 0 := by decide
theorem T_ne_one : T ≠ 1 := by decide

/-- Powers of `T` grow linearly, so `A B₁ B₂` has infinite order. -/
theorem T_pow (k : ℕ) : T ^ k = 1 + (k : ℤ) • (T - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h : (T - 1) * (T - 1) = 0 := T_unipotent
    have hT : T = 1 + (T - 1) := by abel
    calc (1 + (k : ℤ) • (T - 1)) * T
        = (1 + (k : ℤ) • (T - 1)) * (1 + (T - 1)) := by rw [← hT]
      _ = 1 + ((k : ℤ) + 1) • (T - 1) + (k : ℤ) • ((T - 1) * (T - 1)) := by
          simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, add_smul, one_smul]
          abel
      _ = 1 + ((k + 1 : ℕ) : ℤ) • (T - 1) := by rw [h, smul_zero, add_zero]; push_cast; rfl

/-- The invariant linear form `s₁ + s₂ + w`, as a row vector. -/
def ell : Fin 3 → ℤ := ![1, 1, 1]

theorem ell_A : Matrix.vecMul ell A = ell := by decide
theorem ell_B₁ : Matrix.vecMul ell B₁ = ell := by decide
theorem ell_B₂ : Matrix.vecMul ell B₂ = ell := by decide

end FEGroup
