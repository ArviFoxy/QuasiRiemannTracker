/- New amplifier research: facts about the marked detector count used by the marked HIGH leaf.

`countingR κ ν p` (Collet, `Cycle61/Arithmetic/Bernstein/Feedback.lean`) is the exponent of the
amplitude-class row count; `unmarkedDensity ν` (Collet, `LocalMoment/UnmarkedDensity.lean`) is the
exponent ρ(ν) of the unmarked count used by Sil's density leaf. At amplitude `p = 0` the two agree,
and the marked exponent decreases in `p`. -/
import Submissions.hailey_collet_1252270103.Cycle61.Arithmetic.Bernstein.Feedback
import Submissions.hailey_collet_1252270103.LocalMoment.UnmarkedDensity

set_option autoImplicit false
namespace QRH.ArviNewPowers
open Cycle61.Arithmetic.Bernstein

/-- **The marked count at amplitude zero is the unmarked count.** -/
theorem countingR_zero (κ ν : ℝ) (hκ : 0 < κ) (hν : ν < 5/2) :
    countingR κ ν 0 = OAI.SevenEighths.LocalMoment.unmarkedDensity ν := by
  have hκ' : κ ≠ 0 := hκ.ne'
  have h1 : (5:ℝ) - 2*ν ≠ 0 := by intro h; linarith
  have h2 : (5:ℝ)/6 - ν + ν*(2/3) ≠ 0 := by intro h; linarith
  have hc : countingCoefficient κ 0 = 2/3 := by
    unfold countingCoefficient countingDen
    field_simp
    ring
  unfold countingR rowDen OAI.SevenEighths.LocalMoment.unmarkedDensity
  rw [hc]
  have e1 : (5:ℝ)/6 - ν + ν*(2/3) = (5 - 2*ν)/6 := by ring
  rw [e1]
  have h4 : (5:ℝ) - ν*2 ≠ 0 := by intro h; apply h1; linarith
  have key : ν * (2/3) * (5/6 - ν) / (2 * ((5 - 2*ν)/6)) - ν = - (10*ν / (3*(5 - 2*ν))) := by
    field_simp
    ring
  linarith

/-- `countingR` is increasing in the counting coefficient. -/
theorem countingR_mono_coeff {ν c₁ c₂ : ℝ} (hν0 : 0 ≤ ν) (hν : ν < 5/6) (hc₁ : 0 ≤ c₁)
    (hc : c₁ ≤ c₂) :
    1-ν+ν*c₁*(5/6-ν)/(2*((5/6-ν)+ν*c₁)) ≤ 1-ν+ν*c₂*(5/6-ν)/(2*((5/6-ν)+ν*c₂)) := by
  have hV : 0 < 5/6 - ν := by linarith
  have hc₂ : 0 ≤ c₂ := hc₁.trans hc
  have hd₁ : 0 < 2*((5/6-ν)+ν*c₁) := by positivity
  have hd₂ : 0 < 2*((5/6-ν)+ν*c₂) := by positivity
  have key : ν*c₁*(5/6-ν)/(2*((5/6-ν)+ν*c₁)) ≤ ν*c₂*(5/6-ν)/(2*((5/6-ν)+ν*c₂)) := by
    rw [div_le_div_iff₀ hd₁ hd₂]
    have : 0 ≤ ν*(5/6-ν)*(c₂-c₁)*(2*(5/6-ν)) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hν0 hV.le) (sub_nonneg.mpr hc)) (by linarith : (0:ℝ) ≤ 2*(5/6-ν))
      exact this
    nlinarith [this]
  linarith

/-- The counting coefficient decreases in the amplitude on `[0, 1/2]`. -/
theorem countingCoefficient_anti {κ p₁ p₂ : ℝ} (hk : 7/10 ≤ κ) (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p₂)
    (hp₂ : p₂ ≤ 1/2) :
    countingCoefficient κ p₂ ≤ countingCoefficient κ p₁ := by
  have hD₁ := countingDen_lower hk ⟨hp₁, hp.trans hp₂⟩
  have hD₂ := countingDen_lower hk ⟨hp₁.trans hp, hp₂⟩
  unfold countingCoefficient
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  unfold countingDen
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by linarith : (0:ℝ) ≤ κ - 1/3),
    mul_nonneg (sub_nonneg.mpr hp) hp₁, mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp₂),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) hp₁) (by linarith : (0:ℝ) ≤ κ),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hp₂)) (by linarith : (0:ℝ) ≤ κ),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) hp₁) (sub_nonneg.mpr hp₂)]

/-- **Marking never hurts:** the marked count exponent is antitone in the amplitude. -/
theorem countingR_anti {κ ν p₁ p₂ : ℝ} (hk : 7/10 ≤ κ) (hν0 : 0 ≤ ν) (hν : ν < 5/6)
    (hp₁ : 0 ≤ p₁) (hp : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1/2) :
    countingR κ ν p₂ ≤ countingR κ ν p₁ := by
  have hc := countingCoefficient_anti hk hp₁ hp hp₂
  have hc0 := (countingCoefficient_pos hk ⟨hp₁.trans hp, hp₂⟩).le
  unfold countingR rowDen
  exact countingR_mono_coeff hν0 hν hc0 hc

/-- Together: every marked class is counted at most as the unmarked rows. -/
theorem countingR_le_unmarked {κ ν p : ℝ} (hk : 7/10 ≤ κ) (hν0 : 0 ≤ ν) (hν : ν < 5/6)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    countingR κ ν p ≤ OAI.SevenEighths.LocalMoment.unmarkedDensity ν := by
  rw [← countingR_zero κ ν (by linarith) (by linarith)]
  exact countingR_anti hk hν0 hν le_rfl hp0 hp

end QRH.ArviNewPowers

#print axioms QRH.ArviNewPowers.countingR_zero
#print axioms QRH.ArviNewPowers.countingR_anti
#print axioms QRH.ArviNewPowers.countingR_le_unmarked
