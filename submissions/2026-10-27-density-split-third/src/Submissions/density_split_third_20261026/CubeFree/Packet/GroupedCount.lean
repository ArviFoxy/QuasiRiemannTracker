/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar lemmas for the grouped side bound (Seam B, WP-H): dyadic indices of ordinary lengths,
the count of dyadic classes (`O(log² Z) = Z^{o(1)}`), vanishing logarithmic constants
`log_Z c → 0`, and ordinary-length (`length Z X = log_Z max(1,X)`) comparisons. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace QRH.DensitySplitThird.CubeFree.Packet.Grouped
noncomputable section
open Filter Asymptotics
open OAI.SevenEighths.CenteredMomentEnergyBands (length)

/-! ### Dyadic indices -/

/-- The dyadic index of a positive length. -/
def dyadicIndex (X : ℝ) : ℤ := ⌈Real.logb 2 X⌉

/-- The dyadic centre `2^k ≥ X`. -/
def dyadicTop (X : ℝ) : ℝ := (2 : ℝ) ^ (dyadicIndex X)

theorem dyadicTop_pos (X : ℝ) : 0 < dyadicTop X := zpow_pos (by norm_num) _

theorem dyadicTop_spec (X : ℝ) (hX : 0 < X) : dyadicTop X / 2 ≤ X ∧ X ≤ dyadicTop X := by
  unfold dyadicTop dyadicIndex
  have h2 : (1 : ℝ) < 2 := by norm_num
  set k := ⌈Real.logb 2 X⌉ with hk
  have hk1 : Real.logb 2 X ≤ k := Int.le_ceil _
  have hk2 : (k : ℝ) - 1 < Real.logb 2 X := by
    have := Int.ceil_lt_add_one (Real.logb 2 X); linarith
  have hpow : ∀ r : ℤ, (2 : ℝ) ^ r = (2 : ℝ) ^ (r : ℝ) := fun r => (Real.rpow_intCast 2 r).symm
  constructor
  · rw [hpow, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (2 : ℝ) ^ ((k : ℝ) - 1) ≤ X := by
      rw [← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hX]
      exact Real.rpow_le_rpow_of_exponent_le h2.le hk2.le
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, div_le_iff₀ (by norm_num)] at this
    linarith
  · rw [hpow, ← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hX]
    exact Real.rpow_le_rpow_of_exponent_le h2.le hk1

theorem dyadicIndex_upper (X Z L : ℝ) (hX : 0 < X) (hZ : 0 < Z) (hXZ : X ≤ Z ^ L) :
    dyadicIndex X ≤ ⌈L * Real.logb 2 Z⌉ := by
  unfold dyadicIndex
  apply Int.ceil_mono
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hX hXZ
  rwa [Real.logb_rpow_eq_mul_logb_of_pos hZ] at h

theorem dyadicIndex_lower (X b : ℝ) (hb : 0 < b) (hX : 1 / b ≤ X) :
    ⌈- Real.logb 2 b⌉ ≤ dyadicIndex X := by
  unfold dyadicIndex
  apply Int.ceil_mono
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hX
  rwa [one_div, Real.logb_inv] at h

theorem card_Icc_int_le (k₁ k₂ : ℤ) : ((Finset.Icc k₁ k₂).card : ℝ) ≤ max 0 ((k₂ : ℝ) - k₁ + 1) := by
  rw [Int.card_Icc]
  rcases le_or_gt 0 (k₂ + 1 - k₁) with h | h
  · have e : (((k₂ + 1 - k₁).toNat : ℕ) : ℝ) = ((k₂ + 1 - k₁ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [e]
    push_cast
    exact le_max_of_le_right (by linarith)
  · rw [Int.toNat_eq_zero.mpr h.le]
    simp

/-- The number of dyadic indices between the two bounds above. -/
theorem card_dyadic_le (L b Z : ℝ) (hL : 0 ≤ L) (hb : 1 ≤ b) (hZ : 1 ≤ Z) :
    ((Finset.Icc ⌈- Real.logb 2 b⌉ ⌈L * Real.logb 2 Z⌉).card : ℝ) ≤
      L * Real.logb 2 Z + Real.logb 2 b + 2 := by
  refine (card_Icc_int_le _ _).trans (max_le ?_ ?_)
  · have h1 : 0 ≤ Real.logb 2 Z := Real.logb_nonneg (by norm_num) hZ
    have h2 : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) hb
    nlinarith
  · have h1 := Int.ceil_lt_add_one (L * Real.logb 2 Z)
    have h2 := Int.le_ceil (- Real.logb 2 b)
    linarith

/-! ### Asymptotics -/

/-- `log x ≤ x^r / r`. -/
theorem log_le_rpow_div' (x r : ℝ) (hx : 0 < x) (hr : 0 < r) : Real.log x ≤ x ^ r / r := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx r)
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hr]
  linarith

/-- `M (A log Z + B)² ≤ Z^δ` eventually. -/
theorem eventually_logSq_le (M A B δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, M * (A * Real.log Z + B) ^ 2 ≤ Z ^ δ := by
  set c : ℝ := 4 / δ with hc
  have hc0 : 0 < c := by positivity
  have ht := (tendsto_rpow_atTop (by positivity : (0:ℝ) < δ / 4)).eventually_ge_atTop
    (|B| + 1)
  have ht2 := (tendsto_rpow_atTop (by positivity : (0:ℝ) < δ / 2)).eventually_ge_atTop
    (|M| * (|A| * c + 1) ^ 2)
  filter_upwards [ht, ht2, eventually_ge_atTop (1:ℝ)] with Z h1 h2 hZ
  set u := Z ^ (δ / 4) with hu
  have hl : Real.log Z ≤ c * u := by
    have := log_le_rpow_div' Z (δ / 4) (by linarith) (by positivity)
    rw [hc, hu]; rw [div_eq_mul_inv] at this ⊢
    calc Real.log Z ≤ Z ^ (δ / 4) * (δ / 4)⁻¹ := this
      _ = 4 * δ⁻¹ * Z ^ (δ / 4) := by field_simp
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
  have hlog0 : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hsq : u ^ 2 = Z ^ (δ / 2) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf
  have hZδ : Z ^ δ = Z ^ (δ / 2) * Z ^ (δ / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hAB : |A * Real.log Z + B| ≤ (|A| * c + 1) * u := by
    calc |A * Real.log Z + B| ≤ |A| * Real.log Z + |B| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hlog0]
      _ ≤ |A| * (c * u) + u := by
          have := mul_le_mul_of_nonneg_left hl (abs_nonneg A)
          linarith
      _ = (|A| * c + 1) * u := by ring
  have hsq2 : (A * Real.log Z + B) ^ 2 ≤ (|A| * c + 1) ^ 2 * Z ^ (δ / 2) := by
    rw [← hsq, ← sq_abs]
    calc |A * Real.log Z + B| ^ 2 ≤ ((|A| * c + 1) * u) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hAB 2
      _ = (|A| * c + 1) ^ 2 * u ^ 2 := by ring
  have hZ2 : 0 ≤ Z ^ (δ / 2) := Real.rpow_nonneg (by linarith) _
  calc M * (A * Real.log Z + B) ^ 2 ≤ |M| * (A * Real.log Z + B) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _)
    _ ≤ |M| * ((|A| * c + 1) ^ 2 * Z ^ (δ / 2)) :=
        mul_le_mul_of_nonneg_left hsq2 (abs_nonneg M)
    _ = (|M| * (|A| * c + 1) ^ 2) * Z ^ (δ / 2) := by ring
    _ ≤ Z ^ (δ / 2) * Z ^ (δ / 2) := mul_le_mul_of_nonneg_right h2 hZ2
    _ = Z ^ δ := hZδ.symm

/-- `log_Z c ≤ δ` eventually. -/
theorem eventually_logb_le (c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, Real.logb Z c ≤ δ := by
  have h := Real.tendsto_log_atTop.eventually_ge_atTop ((|Real.log c| + 1) / δ)
  filter_upwards [h] with Z hZ
  have hpos : 0 < Real.log Z := lt_of_lt_of_le (by positivity) hZ
  unfold Real.logb
  rw [div_le_iff₀ hpos]
  have : |Real.log c| + 1 ≤ δ * Real.log Z := by
    rw [div_le_iff₀ hδ] at hZ; linarith
  linarith [le_abs_self (Real.log c)]

/-- The dyadic class count is subpower. -/
theorem eventually_dyadic_count (M L b δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, M * (L * Real.logb 2 Z + Real.logb 2 b + 2) ^ 2 ≤ Z ^ δ := by
  have h := eventually_logSq_le M (L / Real.log 2) (Real.logb 2 b + 2) δ hδ
  filter_upwards [h] with Z hZ
  have : L * Real.logb 2 Z = L / Real.log 2 * Real.log Z := by
    unfold Real.logb; ring
  rw [this, add_assoc]; exact hZ

/-! ### Ordinary lengths -/

theorem length_mono (Z X Y : ℝ) (hZ : 1 < Z) (h : X ≤ Y) :
    length Z X ≤ length Z Y := by
  unfold length
  exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (max_le_max le_rfl h)

theorem length_mul_le (Z c X : ℝ) (hZ : 1 < Z) (hc : 1 ≤ c) :
    length Z (c * X) ≤ length Z X + Real.logb Z c := by
  unfold length
  have h1 : max 1 (c * X) ≤ c * max 1 X := by
    apply max_le
    · nlinarith [le_max_left 1 X]
    · exact mul_le_mul_of_nonneg_left (le_max_right 1 X) (by linarith)
  have hpos : 0 < max 1 (c * X) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc Real.logb Z (max 1 (c * X)) ≤ Real.logb Z (c * max 1 X) :=
        Real.logb_le_logb_of_le hZ hpos h1
    _ = Real.logb Z (max 1 X) + Real.logb Z c := by
        rw [Real.logb_mul (by linarith) (by positivity)]; ring

theorem length_le_of_le_rpow (Z X L : ℝ) (hZ : 1 < Z) (hL : 0 ≤ L) (hX : X ≤ Z ^ L) :
    length Z X ≤ L := by
  unfold length
  have h1 : max 1 X ≤ Z ^ L := max_le (Real.one_le_rpow hZ.le hL) hX
  calc Real.logb Z (max 1 X) ≤ Real.logb Z (Z ^ L) :=
        Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) h1
    _ = L := by rw [Real.logb_rpow (by linarith) hZ.ne']

end
end QRH.DensitySplitThird.CubeFree.Packet.Grouped
