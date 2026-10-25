/-
Why fourth powers (research/combined/BARRIER_REVISITED.md §1, §5.1).

For a sextic character χ_a and D coprime to a, the Gauss sum satisfies
G_a(D^e k) = χ_a(D)^{-e} G_a(k). Write χ_a(D) = ζ^x with ζ a primitive sixth root of unity and
x ∈ ZMod 6. A slot's own twist on the row a is the cubic character χ_a(D)² = ζ^{2x}. The dilation
by D^e transfers the twisted row family to the polynomial at D^e·k exactly when its phase −e·x
equals the twist 2x for every x, i.e. e ≡ 4 (mod 6). So 4 is the least usable exponent: squares
and cubes give the wrong phase, sixth powers give no phase (exact invariance, Collet's pool).

Second part: the whole-column identity as pure algebra, and the energy transfer through an
injective dilation.
-/
import Mathlib

namespace FourthPowerExponent

/-- The dilation phase `−e·x` matches the cubic twist `2·x` for all `x` iff `e ≡ 4 (mod 6)`. -/
theorem phase_matches_iff (e : ZMod 6) : (∀ x : ZMod 6, -e * x = 2 * x) ↔ e = 4 := by
  constructor
  · intro h
    have h1 := h 1
    simp only [mul_one] at h1
    have : e = -2 := by rw [← neg_neg e, h1]
    rw [this]; decide
  · rintro rfl x
    have : (-(4 : ZMod 6)) = 2 := by decide
    rw [this]

/-- The least positive exponent with the matching phase is 4. -/
theorem least_exponent :
    (∀ e : ℕ, 0 < e → e < 4 → ((e : ZMod 6) ≠ 4)) ∧ ((4 : ℕ) : ZMod 6) = 4 := by
  refine ⟨?_, by decide⟩
  intro e he he4
  interval_cases e <;> decide

/-- Sixth powers carry no phase at all (exact invariance): `−6·x = 0`. -/
theorem sixth_power_invariant (x : ZMod 6) : -(6 : ZMod 6) * x = 0 := by
  have : (6 : ZMod 6) = 0 := by decide
  rw [this]; simp

/-- Whole-column identity (Sil's `whole_column`, as algebra): if every row satisfies
`G i (D⁴k) = c i ^ 2 * G i k`, then the row family twisted by `c i ^ 2` is the polynomial at `D⁴k`. -/
theorem whole_column {ι K R : Type*} [Fintype ι] [CommRing R] (b c : ι → R)
    (G : ι → K → R) (dil : K → K) (hG : ∀ i k, G i (dil k) = c i ^ 2 * G i k) (k : K) :
    ∑ i, b i * c i ^ 2 * G i k = ∑ i, b i * G i (dil k) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hG]; ring

/-- Energy transfer: through an injective dilation, the twisted family's energy over a finite
frequency set equals the polynomial's energy on the dilated set, hence is at most its energy on any
superset. -/
theorem energy_transfer {K : Type*} [DecidableEq K] (P : K → ℝ) (dil : K → K)
    (hinj : Function.Injective dil) (S T : Finset K) (hST : S.image dil ⊆ T) :
    ∑ k ∈ S, P (dil k) ^ 2 ≤ ∑ r ∈ T, P r ^ 2 := by
  rw [← Finset.sum_image (f := fun r => P r ^ 2) (fun x _ y _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => sq_nonneg _)

end FourthPowerExponent
