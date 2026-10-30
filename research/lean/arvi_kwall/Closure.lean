/-
The amplify–reflect closure of the selected norm below slope 1/2 (research, 2026-10-30).

Work in log scale: `x = log_B (source length)` and `n x = log_B (selected norm)` for rows of norm `≈ B`
selected at slope `δ` (PR 93's `SelectedAllSourceNormBound`). PR 93's iteration uses three rules:
* initial bound: here the optimal general sextic sieve `Θ₆ = A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6}`
  (de Faveri; Sil's `SieveOptimal`), which is stronger than the `L + B²` that PR 93 starts from;
* amplification by a selected slot block: `n x ≤ n y − δ (y − x)` for `x ≤ y`;
* reflection (Poisson at conductor `B²`): `n x ≤ max x (x − 1 + n (2 − x))` for `1 ≤ x ≤ 2`.

`nstar_rules` exhibits, for `1/3 ≤ δ < 1/2`, a function obeying all three rules with `n 1 = 7/6`. So no argument
built from these rules alone proves a selected norm below `B^{7/6}` at the balanced point `L = B`, while the
fixed point PR 93 reaches for `δ > 1/2` is `B^1`. The loss `1/6` is exactly the excess of `Θ₆` at the balanced
point: below slope `1/2` the selection buys nothing there. Moving the faces' wall `K ≥ 1/2` therefore needs a
direct estimate for the selected rows at `L = B` (a Guth–Maynard-type bound for the sextic family).
-/
import Mathlib

set_option autoImplicit false
namespace QRH.ArviKWall

noncomputable section

/-- Exponent of the optimal general sextic large sieve with `B` moduli and length `B^x` (in `log_B`). -/
def theta6 (x : ℝ) : ℝ := max (max 1 x) (max (5/6 + x/3) (1/3 + 5*x/6))

/-- The three rules of the selected-norm iteration, on sources of length `B^x`, `x ≥ 0`. -/
structure Rules (δ : ℝ) (n : ℝ → ℝ) : Prop where
  init : ∀ x, 0 ≤ x → n x ≤ theta6 x
  amp : ∀ x y, 0 ≤ x → x ≤ y → n x ≤ n y - δ * (y - x)
  refl : ∀ x, 1 ≤ x → x ≤ 2 → n x ≤ max x (x - 1 + n (2 - x))

/-- The row term of the closure: slope `δ` below the balanced point, `1 − δ` above it, value `7/6` there. -/
def frow (δ x : ℝ) : ℝ := 7/6 + δ * (x - 1) + (1 - 2*δ) * max (x - 1) 0

/-- The closure. -/
def nstar (δ x : ℝ) : ℝ := max x (frow δ x)

theorem frow_left {δ x : ℝ} (hx : x ≤ 1) : frow δ x = 7/6 + δ * (x - 1) := by
  unfold frow; rw [max_eq_right (by linarith : x - 1 ≤ 0)]; ring

theorem frow_right {δ x : ℝ} (hx : 1 ≤ x) : frow δ x = 7/6 + (1 - δ) * (x - 1) := by
  unfold frow; rw [max_eq_left (by linarith : (0:ℝ) ≤ x - 1)]; ring

theorem nstar_one (δ : ℝ) : nstar δ 1 = 7/6 := by
  unfold nstar; rw [frow_left le_rfl]; norm_num

theorem nstar_init {δ : ℝ} (hδ : 1/3 ≤ δ) (x : ℝ) (_hx : 0 ≤ x) : nstar δ x ≤ theta6 x := by
  unfold nstar theta6
  apply max_le (le_max_of_le_left (le_max_right _ _))
  rcases le_total x 1 with h | h
  · rw [frow_left h]
    apply le_max_of_le_right; apply le_max_of_le_left
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ δ - 1/3) (by linarith : (0:ℝ) ≤ 1 - x)]
  · rw [frow_right h]
    apply le_max_of_le_right; apply le_max_of_le_right
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ δ - 1/6) (by linarith : (0:ℝ) ≤ x - 1)]

/-- Amplification: `nstar + δ·(y − x)` never exceeds `nstar` at `y`. -/
theorem nstar_amp {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ2 : δ < 1/2) (x y : ℝ) (hxy : x ≤ y) :
    nstar δ x ≤ nstar δ y - δ * (y - x) := by
  have hf : frow δ x + δ * (y - x) ≤ frow δ y := by
    unfold frow
    have hm : max (x - 1) 0 ≤ max (y - 1) 0 := max_le_max (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : (0:ℝ) ≤ 1 - 2*δ)]
  unfold nstar
  rw [le_sub_iff_add_le, ← max_add_add_right]
  apply max_le
  · exact le_max_of_le_left
      (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - δ) (by linarith : (0:ℝ) ≤ y - x)])
  · exact le_max_of_le_right hf

theorem nstar_refl (δ x : ℝ) (h1 : 1 ≤ x) (_h2 : x ≤ 2) :
    nstar δ x ≤ max x (x - 1 + nstar δ (2 - x)) := by
  unfold nstar
  apply max_le_max le_rfl
  rw [frow_right h1]
  have hl : frow δ (2 - x) = 7/6 + δ * (2 - x - 1) := frow_left (by linarith)
  nlinarith [le_max_right (2 - x) (frow δ (2 - x))]

/-- **The closure barrier.** For `1/3 ≤ δ < 1/2`, `nstar δ` obeys the three rules. -/
theorem nstar_rules {δ : ℝ} (hδ : 1/3 ≤ δ) (hδ2 : δ < 1/2) : Rules δ (nstar δ) :=
  ⟨nstar_init hδ, fun x y _ hxy => nstar_amp (by linarith) hδ2 x y hxy,
    fun x h1 h2 => nstar_refl δ x h1 h2⟩

/-- So the rules cannot certify any balanced-point exponent below `7/6` when `1/3 ≤ δ < 1/2`. -/
theorem no_balanced_bound_below {δ c : ℝ} (hδ : 1/3 ≤ δ) (hδ2 : δ < 1/2)
    (h : ∀ n : ℝ → ℝ, Rules δ n → n 1 ≤ c) : 7/6 ≤ c := by
  have := h (nstar δ) (nstar_rules hδ hδ2)
  rwa [nstar_one] at this

/-- In particular the slope-`δ` fixed point `max x (1 − δ + δ x)`, which equals `1` at `x = 1`, is not a
consequence of the rules below slope `1/2`. -/
theorem fixed_point_not_derivable {δ : ℝ} (hδ : 1/3 ≤ δ) (hδ2 : δ < 1/2) :
    ¬ (∀ n : ℝ → ℝ, Rules δ n → ∀ x, 0 ≤ x → x ≤ 1 → n x ≤ max x (1 - δ + δ * x)) := by
  intro h
  have := h (nstar δ) (nstar_rules hδ hδ2) 1 (by norm_num) le_rfl
  rw [nstar_one] at this
  have h1 : max (1:ℝ) (1 - δ + δ * 1) = 1 := by
    rw [show (1:ℝ) - δ + δ * 1 = 1 by ring, max_self]
  rw [h1] at this
  norm_num at this

end

end QRH.ArviKWall

#print axioms QRH.ArviKWall.no_balanced_bound_below
#print axioms QRH.ArviKWall.fixed_point_not_derivable
