/- Copyright (c) 2026 Sil. Apache-2.0.
Enclosed forward ordinary mass of the cube-free kernel `H₃`.

With anisotropic weights `x ↦ N(P)^(-2/3)`, `y ↦ N(P)^(-1/3)` the monomial `x^i y^j`
of `H₃` has prime exponent `(2i+j)/3 ≥ 1`, with equality at `y³`
(`FP.KernelForwardMass.ordinaryWeight_nonconstant`). Hence the local mass is
`≤ 1 + 7 N(P)⁻¹`, and the FP constant bound `ordinary_global_mass` (exponent `5/3 > 1`)
has no cube-free analogue. It is replaced here by the enclosed bound: over prime ideals
of norm `≤ X` the truncated Euler product is `≤ e^(42 log 768) (log X)^42`
(`Analysis.PrimeHarmonic`), hence `≤ C·X^δ` for every `δ > 0`, uniformly in the prime set.
Every downstream mass statement must therefore carry the enclosure `N(P) ≤ X`.
-/
import Submissions.density_split_fourth.CubeFree.FP.KernelForwardMass
import Submissions.density_split_fourth.Analysis.PrimeHarmonic

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.KernelForwardMass3
noncomputable section
open scoped Classical BigOperators
open Filter
open QRH.DensitySplitThird.CubeFree.FP.KernelForwardMass
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

/-- The local forward mass at a nonzero ideal, in the form consumed by the Mertens bound. -/
theorem ordinary_local_mass_div (P : Id) (hP : P ≠ ⊥) :
    (∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) ≤
      1 + 7 / (Ideal.absNorm P : ℝ) + 0 := by
  have hN : Ideal.absNorm P ≠ 0 := fun h => hP (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : (1 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have h := ordinary_local_mass _ h1
  rw [div_eq_mul_inv, add_zero]
  exact h

theorem prime_data {P : Id} (hP : Prime P) : P.IsPrime ∧ P ≠ ⊥ :=
  ⟨Ideal.isPrime_of_prime hP, by rw [← Ideal.zero_eq_bot]; exact hP.ne_zero⟩

/-- Explicit truncated Euler product over prime ideals of norm at most `X`. -/
theorem ordinary_mass_explicit (X : ℝ) (hX : 3 ≤ X) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P ∧ (Ideal.absNorm P : ℝ) ≤ X) :
    (∏ P ∈ S, ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) ≤
      Real.exp (42 * Real.log 768) * Real.log X ^ (42 : ℝ) := by
  have h := PrimeHarmonic.euler_product_bound 7 0 (by norm_num) X hX S
    (fun P hP => prime_data (hS P hP).1) (fun P hP => (hS P hP).2)
    (fun P => ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) (fun _ => 0)
    (fun P _ => Finset.sum_nonneg fun i _ => ordinaryWeight_nonneg _ (Nat.cast_nonneg _) i)
    (fun P hP => ordinary_local_mass_div P (prime_data (hS P hP).1).2) (by simp)
  have e1 : (7 : ℝ) * (6 * Real.log 768) + 0 = 42 * Real.log 768 := by ring
  have e2 : (7 : ℝ) * 6 = 42 := by norm_num
  rw [e1, e2] at h
  exact h

/-- Subpower form, valid for every `X ≥ 1` with one constant. -/
theorem ordinary_mass_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset Id,
      (∀ P ∈ S, Prime P ∧ (Ideal.absNorm P : ℝ) ≤ X) →
      (∏ P ∈ S, ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) ≤ C * X ^ δ := by
  obtain ⟨X0, hX0, h⟩ := PrimeHarmonic.euler_product_subpower 7 0 δ (by norm_num) hδ
  have hX00 : 0 < X0 := by linarith
  refine ⟨X0 ^ δ, Real.rpow_pos_of_pos hX00 _, ?_⟩
  intro X hX S hS
  have hb := h (max X X0) (le_max_right _ _) S (fun P hP => prime_data (hS P hP).1)
    (fun P hP => (hS P hP).2.trans (le_max_left _ _))
    (fun P => ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) (fun _ => 0)
    (fun P _ => Finset.sum_nonneg fun i _ => ordinaryWeight_nonneg _ (Nat.cast_nonneg _) i)
    (fun P hP => ordinary_local_mass_div P (prime_data (hS P hP).1).2) (by simp)
  have hmax : max X X0 ≤ X0 * X := max_le (by nlinarith) (by nlinarith)
  calc
    _ ≤ (max X X0) ^ δ := hb
    _ ≤ (X0 * X) ^ δ :=
        Real.rpow_le_rpow (le_trans (by linarith) (le_max_left X X0)) hmax hδ.le
    _ = X0 ^ δ * X ^ δ := Real.mul_rpow hX00.le (by linarith)

/-- Design form (L1): the product over primes of norm `≤ Z^Lcap` is `≤ C·Z^δ`.
Primality of the pool is required (a set of arbitrary supported ideals has no such bound);
it holds for every `Z ≥ 1`, in particular eventually. -/
theorem ordinary_mass_enclosed (Lcap δ : ℝ) (hL : 0 < Lcap) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ S : Finset Id,
      (∀ P ∈ S, Prime P ∧ (Ideal.absNorm P : ℝ) ≤ Z ^ Lcap) →
      (∏ P ∈ S, ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i) ≤ C * Z ^ δ := by
  obtain ⟨C, hC, h⟩ := ordinary_mass_subpower (δ / Lcap) (div_pos hδ hL)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ S hS
  have hZ0 : 0 ≤ Z := by linarith
  have hb := h (Z ^ Lcap) (Real.one_le_rpow hZ hL.le) S hS
  have he : Lcap * (δ / Lcap) = δ := by field_simp
  rwa [← Real.rpow_mul hZ0, he] at hb

/-- Configuration form (FP `ordinary_configuration_mass`, enclosed). -/
theorem ordinary_configuration_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset Id,
      (∀ P ∈ S, Prime P ∧ (Ideal.absNorm P : ℝ) ≤ X) →
      (∑ a ∈ Fintype.piFinset (fun _P : S => (Finset.univ : Finset (Fin 8))),
        ∏ P : S, ordinaryWeight (Ideal.absNorm P.val : ℝ) (a P)) ≤ C * X ^ δ := by
  obtain ⟨C, hC, h⟩ := ordinary_mass_subpower δ hδ
  refine ⟨C, hC, fun X hX S hS => ?_⟩
  rw [← Finset.prod_univ_sum (fun _P : S => (Finset.univ : Finset (Fin 8)))
    (fun P : S => fun i : Fin 8 => ordinaryWeight (Ideal.absNorm P.val : ℝ) i)]
  have he : (∏ P : S, ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P.val : ℝ) i) =
      ∏ P ∈ S, ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i :=
    (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
      (fun P : Id => ∑ i : Fin 8, ordinaryWeight (Ideal.absNorm P : ℝ) i)).symm
  rw [he]
  exact h X hX S hS

end
end QRH.DensitySplitThird.CubeFree.KernelForwardMass3
