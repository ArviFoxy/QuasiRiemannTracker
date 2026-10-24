/- Repeated marks: Collet-shaped HIGH gaps and gain payments for the repeated-mark gain.
The definitions keep the shape of Collet's `selectedGain`, `ActualGaps` (Core/PhysicalReserve.lean)
and `gainAt` (HighScalar/GainPayment.lean, Apache-2.0), so that the mechanically forked
downstream modules use them unchanged. For a HIGH parent the selected gain is the repeated-mark
gain on the cell; off the cell condition of Lemma C it is `0`, which only weakens the gap. The
payments drop Collet's `-(c+d+forced)/12` slack, which no later step uses. -/
import Submissions.repeated_marks_20261024.Source.GainPaymentK
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.SingletonLoss
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.Record1252270103Source.PhysicalScalar
noncomputable section
open Record1252270103Finite

/-- Collet's `selectedGain` with the repeated-mark gain for a HIGH parent. -/
def selectedGain_rm (n low : Source) (high : Option Source) (b ν : ℝ) : ℝ :=
  match high with
  | none => Record12518109Gain.gain ν (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ))
  | some h =>
    if 0≤b-2*(n.allowance:ℝ) ∧ 2*(b-2*(n.allowance:ℝ))≤sourceFReal n low b-(n.allowance:ℝ) then
      QRH.RepeatedMarks.Source.gainAtK h ν (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ))
    else 0

/-- Collet's `ActualGaps` with the repeated-mark gain for a HIGH parent. -/
def ActualGaps_rm (n low : Source) (high : Option Source) (b ν reserve : ℝ) : Prop :=
  reserve≤1-sourceBase n low b ν+selectedGain_rm n low high b ν-(n.highFee:ℝ) ∧
    ∀j, reserve≤familyGap n low b ν j

theorem actualGaps_rm_of_K {n low h : Source} {b ν reserve : ℝ}
    (hg : QRH.RepeatedMarks.Source.ActualGapsK n low h b ν reserve) :
    ActualGaps_rm n low (some h) b ν reserve := by
  obtain ⟨h1,h2,hS,hcell⟩ := hg
  refine ⟨?_,h2⟩
  have hF : 0≤sourceFReal n low b-(n.allowance:ℝ) := by linarith
  simp only [selectedGain_rm, if_pos (And.intro hS hcell)]
  rw [←QRH.RepeatedMarks.Source.selectedGainK_eq n low h b ν hS hF]
  exact h1

theorem actualGaps_rm_none {n low : Source} {b ν reserve : ℝ} :
    ActualGaps_rm n low none b ν reserve ↔ ActualGaps n low none b ν reserve := Iff.rfl

end
end QRH.Record1252270103Source.PhysicalScalar

namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open Record1252270103Finite PhysicalScalar

/-- Collet's `gainAt` with the repeated-mark gain for a HIGH parent. -/
def gainAt_rm (high : Option Source) (ν S F : ℝ) : ℝ :=
  match high with
  | none => Record12518109Gain.gain ν S F
  | some h => QRH.RepeatedMarks.Source.gainAtK h ν S F

lemma gainParametersK_of {high : Option Source} (hp : GainParameters high) {h : Source}
    (hh : h∈high) : QRH.RepeatedMarks.Source.GainParametersK h :=
  hp h hh

lemma gainAtK_nonneg {h : Source} (hp : QRH.RepeatedMarks.Source.GainParametersK h) {ν : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (S F : ℝ) : 0≤QRH.RepeatedMarks.Source.gainAtK h ν S F :=
  QRH.RepeatedMarks.gainK_nonneg (QRH.RepeatedMarks.Source.parentParams_of hp hν0 hν1)
    (le_max_right S 0) (le_max_right F 0)

/-- The gain payment of Collet's `actual_gap_gain_payment`, without the `1/12` slack. -/
lemma actual_gap_gain_payment_rm (n low : Source) (high : Option Source)
    (hp : GainParameters high) (b ν reserve D live frequency c d forced : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD : 0≤D)
    (hc : 0≤c) (hd : 0≤d) (hforced : 0≤forced)
    (hg : ActualGaps_rm n low high b ν reserve)
    (hslots : D*(b-2*(n.allowance:ℝ))≤live+c+d+forced)
    (hrows : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*c+2*d) :
    D*(sourceBase n low b ν-1)-ν*(c+d+forced)-gainAt_rm high ν live frequency≤
      -D*((n.highFee:ℝ)+reserve) := by
  cases high with
  | none =>
    have hh := actual_gap_gain_payment n low none hp b ν reserve D live frequency c d forced
      hν0 hν1 hD hc hd hforced hg hslots hrows
    have hcd : 0≤(c+d+forced)/12 := by positivity
    change D*(sourceBase n low b ν-1)-ν*(c+d+forced)-Record12518109Gain.gain ν live frequency≤_
    change D*(sourceBase n low b ν-1)-ν*(c+d+forced)-Record12518109Gain.gain ν live frequency≤_
      at hh
    linarith
  | some h =>
    have hK := gainParametersK_of hp (show h∈some h by simp)
    by_cases hcell : 0≤b-2*(n.allowance:ℝ) ∧
        2*(b-2*(n.allowance:ℝ))≤sourceFReal n low b-(n.allowance:ℝ)
    · have hF : 0≤sourceFReal n low b-(n.allowance:ℝ) := by linarith [hcell.1, hcell.2]
      have hgK : QRH.RepeatedMarks.Source.ActualGapsK n low h b ν reserve := by
        refine ⟨?_,hg.2,hcell.1,hcell.2⟩
        have h1 := hg.1
        simp only [selectedGain_rm, if_pos hcell] at h1
        rw [QRH.RepeatedMarks.Source.selectedGainK_eq n low h b ν hcell.1 hF]
        exact h1
      exact QRH.RepeatedMarks.Source.actual_gap_gain_payment_K n low h hK b ν reserve D live
        frequency c d forced hν0 hν1 hD hc hd hforced hgK hslots hrows
    · have h1 := hg.1
      simp only [selectedGain_rm, if_neg hcell] at h1
      have hgain := gainAtK_nonneg hK hν0 hν1 live frequency
      have hν : 0≤ν*(c+d+forced) := by
        have : 0≤c+d+forced := by linarith
        positivity
      have hm := mul_le_mul_of_nonneg_left h1 hD
      change D*(sourceBase n low b ν-1)-ν*(c+d+forced)-QRH.RepeatedMarks.Source.gainAtK h ν live
        frequency≤_
      nlinarith

/-- Width monotonicity (Collet's `gainAt_weighted_width_mono`) for the repeated-mark gain. -/
lemma gainAt_weighted_width_mono_rm (high : Option Source) (hp : GainParameters high)
    {ν small full Q : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hwidth : small≤full) :
    ν*small-gainAt_rm high ν small Q≤ν*full-gainAt_rm high ν full Q := by
  cases high with
  | none => exact gainAt_weighted_width_mono none hp hν0 hν1 hwidth
  | some h =>
    have hK := gainParametersK_of hp (show h∈some h by simp)
    have hm := QRH.RepeatedMarks.gainK_width_mono (QRH.RepeatedMarks.Source.parentParams_of hK hν0 hν1)
      (le_max_right small 0) (max_le_max hwidth le_rfl) (le_max_right Q 0)
    change ν*small-QRH.RepeatedMarks.gainK ν 8 (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (max small 0) (max Q 0)≤
      ν*full-QRH.RepeatedMarks.gainK ν 8 (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (max full 0) (max Q 0)
    have hs : small-max small 0≤full-max full 0 := by
      rcases le_total small 0 with h0 | h0
      · rw [max_eq_right h0]
        rcases le_total full 0 with h1 | h1
        · rw [max_eq_right h1]; linarith
        · rw [max_eq_left h1]; linarith
      · rw [max_eq_left h0, max_eq_left (h0.trans hwidth)]; linarith
    have hν : 0≤ν := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hs hν]

end
end QRH.Record1252270103Source.HighScalar
