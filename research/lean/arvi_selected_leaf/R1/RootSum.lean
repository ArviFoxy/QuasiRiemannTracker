/-
The sum over sixth roots.

`∑_r N(r)^{-σ}` converges for `σ > 1` (`rootZeta`). Hence the number of roots of norm at most `X` is at most
`ζ(1+η) X^{1+η}`, and a sum of minima of a direct bound `a` and a reflected bound `b N(r)^{-5}` is at most
`ζ(5θ) a^{1-θ} b^θ` for `θ > 1/5` (interpolation `min a b ≤ a^{1-θ} b^θ`).
-/
import Submissions.arvi_selected_leaf.R1.RootSplit
import Candidate.Local.Qrh.JointDetector.FineDetectorCount

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

/-- The norm of a root ideal. -/
def rootNorm (r : HeckeInverseAmplification.NonzeroIdeal) : ℝ := (r.val.absNorm : ℝ)

theorem rootNorm_pos (r : HeckeInverseAmplification.NonzeroIdeal) : 0 < rootNorm r := by
  unfold rootNorm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr r.property)

theorem rootNorm_ge_one (r : HeckeInverseAmplification.NonzeroIdeal) : 1 ≤ rootNorm r := by
  unfold rootNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr r.property)

/-- **The root zeta series converges** for `σ > 1`. -/
theorem rootZeta_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun r : HeckeInverseAmplification.NonzeroIdeal => rootNorm r ^ (-σ)) := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((σ : ℝ) : ℂ) (by simpa using hσ)).subtype
    (fun I : Ideal O => I ≠ 0)
  apply h.congr
  intro v
  change ‖CubicEisenstein.fullIdealWeight ((σ : ℝ) : ℂ) v.val‖ = _
  have hv : v.val ≠ 0 := v.property
  simp only [CubicEisenstein.fullIdealWeight, hv, ite_false]
  have hN := rootNorm_pos v
  unfold rootNorm at hN ⊢
  rw [show ((Ideal.absNorm v.val : ℕ) : ℂ) = (((Ideal.absNorm v.val : ℕ) : ℝ) : ℂ) by norm_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

/-- The value of the root zeta series. -/
def rootZeta (σ : ℝ) : ℝ := ∑' r : HeckeInverseAmplification.NonzeroIdeal, rootNorm r ^ (-σ)

theorem rootZeta_nonneg (σ : ℝ) : 0 ≤ rootZeta σ :=
  tsum_nonneg (fun r => Real.rpow_nonneg (rootNorm_pos r).le _)

theorem finite_rootZeta_le (σ : ℝ) (hσ : 1 < σ) (R : Finset HeckeInverseAmplification.NonzeroIdeal) :
    ∑ r ∈ R, rootNorm r ^ (-σ) ≤ rootZeta σ :=
  (rootZeta_summable σ hσ).sum_le_tsum R (fun r _ => Real.rpow_nonneg (rootNorm_pos r).le _)

/-- **Root count**: at most `ζ(1+η) X^{1+η}` roots of norm at most `X`. -/
theorem root_count (η X : ℝ) (hη : 0 < η) (hX0 : 0 ≤ X)
    (R : Finset HeckeInverseAmplification.NonzeroIdeal) (hR : ∀ r ∈ R, rootNorm r ≤ X) :
    (R.card : ℝ) ≤ rootZeta (1+η) * X^(1+η) := by
  have hterm : ∀ r ∈ R, (1:ℝ) ≤ X^(1+η) * rootNorm r ^ (-(1+η)) := by
    intro r hr
    have hN := rootNorm_pos r
    have hX : rootNorm r ≤ X := hR r hr
    rw [Real.rpow_neg hN.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hN _)]
    exact Real.rpow_le_rpow hN.le hX (by linarith)
  calc (R.card : ℝ) = ∑ _r ∈ R, (1:ℝ) := by simp
    _ ≤ ∑ r ∈ R, X^(1+η) * rootNorm r ^ (-(1+η)) := Finset.sum_le_sum hterm
    _ = X^(1+η) * ∑ r ∈ R, rootNorm r ^ (-(1+η)) := by rw [Finset.mul_sum]
    _ ≤ X^(1+η) * rootZeta (1+η) :=
        mul_le_mul_of_nonneg_left (finite_rootZeta_le (1+η) (by linarith) R) (Real.rpow_nonneg hX0 _)
    _ = _ := by ring

/-- **Interpolation of a minimum.** -/
theorem min_le_rpow (a b θ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min a b ≤ a^(1-θ) * b^θ := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    calc a = a^(1-θ) * a^θ := by
          by_cases ha0 : a = 0
          · subst ha0
            rcases eq_or_lt_of_le hθ0 with h | h
            · subst h; simp
            · rw [Real.zero_rpow h.ne']; simp
          · rw [← Real.rpow_add (lt_of_le_of_ne ha (Ne.symm ha0))]; simp
      _ ≤ a^(1-θ) * b^θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab hθ0) (Real.rpow_nonneg ha _)
  · rw [min_eq_right hab]
    calc b = b^(1-θ) * b^θ := by
          by_cases hb0 : b = 0
          · subst hb0
            rcases eq_or_lt_of_le hθ0 with h | h
            · subst h; simp
            · rw [Real.zero_rpow h.ne']; simp
          · rw [← Real.rpow_add (lt_of_le_of_ne hb (Ne.symm hb0))]; simp
      _ ≤ a^(1-θ) * b^θ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb hab (by linarith)) (Real.rpow_nonneg hb _)

/-- **The sum of minima** of a direct bound `a` and a reflected bound `b N(r)^{-5}`. -/
theorem root_min_sum (a b η : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) (hη4 : η ≤ 4)
    (R : Finset HeckeInverseAmplification.NonzeroIdeal) :
    ∑ r ∈ R, min a (b * rootNorm r ^ (-(5:ℝ))) ≤
      rootZeta (1+η) * (a^(1-(1+η)/5) * b^((1+η)/5)) := by
  set θ := (1+η)/5 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hterm : ∀ r ∈ R, min a (b * rootNorm r ^ (-(5:ℝ))) ≤
      (a^(1-θ) * b^θ) * rootNorm r ^ (-(1+η)) := by
    intro r _
    have hN := rootNorm_pos r
    have h5 : 0 ≤ rootNorm r ^ (-(5:ℝ)) := Real.rpow_nonneg hN.le _
    refine (min_le_rpow a _ θ ha (mul_nonneg hb h5) hθ0 hθ1).trans (le_of_eq ?_)
    rw [Real.mul_rpow hb h5, ← Real.rpow_mul hN.le]
    have : -(5:ℝ) * θ = -(1+η) := by rw [hθ]; ring
    rw [this]
    ring
  calc ∑ r ∈ R, min a (b * rootNorm r ^ (-(5:ℝ)))
      ≤ ∑ r ∈ R, (a^(1-θ) * b^θ) * rootNorm r ^ (-(1+η)) := Finset.sum_le_sum hterm
    _ = (a^(1-θ) * b^θ) * ∑ r ∈ R, rootNorm r ^ (-(1+η)) := by rw [Finset.mul_sum]
    _ ≤ (a^(1-θ) * b^θ) * rootZeta (1+η) :=
        mul_le_mul_of_nonneg_left (finite_rootZeta_le (1+η) (by linarith) R)
          (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
    _ = _ := by ring

/-- **The sixth-power sum over roots** (PR 93's `uniform_sixth_root_sum` at exponent one). -/
theorem root_sixth_sum : ∃ C : ℝ, 0 < C ∧ ∀ (R : Finset HeckeInverseAmplification.NonzeroIdeal) (B : ℝ),
    0 ≤ B → ∑ r ∈ R, B * rootNorm r ^ (-(6:ℝ)) ≤ C * B := by
  obtain ⟨C, hC, h⟩ := Qrh.JointDetector.FineDetectorCount.uniform_sixth_root_sum
  refine ⟨C, hC, ?_⟩
  intro R B hB
  have h1 := h R B 1 hB (by norm_num)
  simp only [Real.rpow_one] at h1
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun r _ => ?_))) h1
  have hN := rootNorm_pos r
  unfold rootNorm at hN ⊢
  rw [Real.rpow_neg hN.le, div_eq_mul_inv]
  norm_cast

end
end QRH.ArviSelectedLeaf.R1
