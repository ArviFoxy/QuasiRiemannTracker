/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainLowMain
import Candidate.Uneven.MainParameters
import Candidate.Cycle63.Moment.LowBranch.Payment

set_option autoImplicit false
namespace OAI.SevenEighths.MainLow
noncomputable section
variable (P : Sil.Uneven.MainSource.Plane)
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch

/-- Joint width and capacity deletion retain the exact new source reserve. -/
theorem low_paid_excess_bound {b M nominal width delta total padding : ℝ}
    (hb : Sil.Uneven.MainSource.widthLo≤b ∧ b≤Sil.Uneven.MainSource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤delta) (hdelta : 0≤delta) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.MainSource.gap P b+6*(M*Sil.Uneven.MainSource.amp P b)+padding) :
    width+(P.q/(6*(incumbentKappa P)))*max (total-width) 0≤
      nominal+delta+M*Sil.Uneven.MainSource.amp P b-M*Sil.Uneven.MainSource.lowReserve+(P.q/(6*(incumbentKappa P)))*padding := by
  have hprice : 0≤P.q/(6*(incumbentKappa P)) := by cases P <;> norm_num [Sil.Uneven.MainSource.Plane.q,incumbentKappa,Sil.Uneven.MainSource.Plane.incumbent]
  have hpriceHi : P.q/(6*(incumbentKappa P))≤1 := by cases P <;> norm_num [Sil.Uneven.MainSource.Plane.q,incumbentKappa,Sil.Uneven.MainSource.Plane.incumbent]
  have heq := Sil.Uneven.MainSource.low_identity P b
  change Sil.Uneven.MainSource.amp P b-P.q/(6*(incumbentKappa P))*(Sil.Uneven.MainSource.gap P b+6*Sil.Uneven.MainSource.amp P b)=Sil.Uneven.MainSource.lowReserve at heq
  have hmul := congrArg (fun x : ℝ=>M*x) heq
  have hguard := Sil.Uneven.MainSource.scheduling_guards P hb
  have ha0 : 0≤Sil.Uneven.MainSource.amp P b := by
    have hamin := hguard.2.1
    have hamp := hguard.2.2.1
    linarith
  have ha : Sil.Uneven.MainSource.lowReserve≤Sil.Uneven.MainSource.amp P b := by
    have hp := mul_nonneg hprice (show 0≤Sil.Uneven.MainSource.gap P b+6*Sil.Uneven.MainSource.amp P b by linarith [hguard.1])
    linarith
  by_cases hm : total≤width
  · rw [max_eq_right (by linarith : total-width≤0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0≤total-width)]
    nlinarith [mul_le_mul_of_nonneg_left htotal hprice,
      mul_nonneg (sub_nonneg.mpr hpriceHi) (sub_nonneg.mpr hwidth)]

theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : Sil.Uneven.MainSource.widthLo≤b ∧ b≤Sil.Uneven.MainSource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤δ) (hdelta : 0≤δ) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.MainSource.gap P b+6*(M*Sil.Uneven.MainSource.amp P b)+padding) :
    width+εold+buffer+(P.q/(6*(incumbentKappa P)))*max (total-width) 0+P.q*mesh≤
      nominal+δ+M*Sil.Uneven.MainSource.amp P b-M*Sil.Uneven.MainSource.lowReserve+εold+buffer+
        (P.q/(6*(incumbentKappa P)))*padding+P.q*mesh := by
  linarith [low_paid_excess_bound P hb hM hwidth hdelta hpad htotal]

end
end OAI.SevenEighths.MainLow
#print axioms OAI.SevenEighths.MainLow.low_paid_excess_bound
#print axioms OAI.SevenEighths.MainLow.paid_low_exponent_shifted
