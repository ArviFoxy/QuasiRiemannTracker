import Mathlib

/-!
# Why the marked inverse moment has slot cost 2: the two branches of its binding child

Collet, foundations Theorem 7.3 (MI): `Σ_{q_u ≪ Z^m} |M_u(Z^r) Q_u|² ≪ Z^m` when `r + 2z ≤ m - c₁` and
`2r + 8z ≤ 3m - c₂`. Its proof Poissons the row sum; the child is the canonical marked energy
(Proposition 7.2) with, in the binding configuration (no assigned primes `G = 0`, `P₁ = 0`, trivial
labels `V = 0`, no puncture `Q = 0`):

  columns `F_c = D₀ = r + z`,   rows `M_c = 2 D₀ - m`,   marks `z`.

The child's reflected energy (MF2.36–MF2.38) has reflected length `T_d = 2 M_c + 2 z - F_c` (the slot
primes enter the conductor squared) and two branches:

* column branch (dual length `v` up to `T_d`): exponent `T_d`;
* row branch (`v ≤ H = M_c`): exponent `H + z - u_h - (T_d - v)/2`, `u_h = min(v, z, (v+z)/3)`.

This file proves:

* `column_iff` : `T_d ≤ F_c ↔ r + 2 z ≤ m`, i.e. the column branch alone is the slot-cost-2 condition;
* `row_at_zero` : at `v = 0` the row branch has exponent exactly `F_c / 2`;
* `row_at_top`  : at `v = H` (with `u_h = z`) the row branch has exponent `(3 D₀ - m - 2 z)/2`, which is
  `F_c - (3/2) z` when `r + 2 z = m`.

So at the binding point the row branch has slack and only the column branch binds. Any improvement of
the row branch (for instance the coupled hybrid norm of `CoupledHybrid.lean`, which replaces `u_h` by
`u'_h = min(z, (v+z)/3) ≥ u_h`, proved in `coupled_u_ge`) cannot relax the slot cost. Only a bound for
the column branch, i.e. cancellation in the reflected Gauss-sum column sum of length `T_d`, can.
-/

namespace Lab.MIBranches

noncomputable section

/-- The child's column budget. -/
def Fc (r z : ℝ) : ℝ := r + z
/-- The child's row length (dual frequencies of the first Poisson). -/
def Mc (r z m : ℝ) : ℝ := 2 * (r + z) - m
/-- The reflected length of the child's reflected energy. -/
def Td (r z m : ℝ) : ℝ := 2 * Mc r z m + 2 * z - Fc r z

theorem column_iff (r z m : ℝ) : Td r z m ≤ Fc r z ↔ r + 2 * z ≤ m := by
  unfold Td Mc Fc; constructor <;> intro h <;> linarith

/-- Row branch exponent at dual length `v`, given the slot saving `u`. -/
def rowExp (H z u Td v : ℝ) : ℝ := H + z - u - (Td - v) / 2

theorem row_at_zero (r z m : ℝ) :
    rowExp (Mc r z m) z 0 (Td r z m) 0 = Fc r z / 2 := by
  unfold rowExp Td Mc Fc; ring

theorem row_at_top (r z m : ℝ) :
    rowExp (Mc r z m) z z (Td r z m) (Mc r z m) = (3 * (r + z) - m - 2 * z) / 2 := by
  unfold rowExp Td Mc Fc; ring

theorem row_at_top_binding (r z : ℝ) :
    rowExp (Mc r z (r + 2 * z)) z z (Td r z (r + 2 * z)) (Mc r z (r + 2 * z)) =
      Fc r z - 3 / 2 * z := by
  unfold rowExp Td Mc Fc; ring

/-- The slot saving of the hybrid norm (MF2.29): `max{v, z, 2(v+z)/3} = v + z - u_h`. -/
def uh (v z : ℝ) : ℝ := min v (min z ((v + z) / 3))
/-- The slot saving once the `L` term is removed (coupled hybrid norm): `max{v, 2(v+z)/3}`. -/
def uh' (v z : ℝ) : ℝ := min z ((v + z) / 3)

theorem coupled_u_ge (v z : ℝ) : uh v z ≤ uh' v z := by
  unfold uh uh'; exact min_le_right _ _

theorem uh_identity (v z : ℝ) (hv : 0 ≤ v) (hz : 0 ≤ z) :
    max v (max z (2 * (v + z) / 3)) = v + z - uh v z := by
  unfold uh
  rcases le_total v z with h1 | h1 <;> rcases le_total v ((v + z) / 3) with h2 | h2 <;>
    rcases le_total z ((v + z) / 3) with h3 | h3 <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith

end

end Lab.MIBranches
