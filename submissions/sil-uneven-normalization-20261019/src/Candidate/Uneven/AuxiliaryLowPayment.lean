/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryLowMain
import Candidate.Uneven.AuxiliarySchedule
import Candidate.Cycle63.Moment.LowBranch.Payment

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryLow
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch

/-- Joint width and capacity deletion retain the exact new source reserve. -/
theorem low_paid_excess_bound {b M nominal width delta total padding : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤Sil.Uneven.AuxiliarySource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤delta) (hdelta : 0≤delta) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.AuxiliarySource.gap b+6*(M*Sil.Uneven.AuxiliarySource.amp b)+padding) :
    width+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0≤
      nominal+delta+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding := by
  have hprice : 0≤Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa) := by norm_num [Sil.Uneven.AuxiliarySource.q,incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]
  have hpriceHi : Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa)≤1 := by norm_num [Sil.Uneven.AuxiliarySource.q,incumbentKappa,Sil.Uneven.AuxiliarySource.kappa]
  have heq := Sil.Uneven.AuxiliarySource.low_identity b
  change Sil.Uneven.AuxiliarySource.amp b-Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa)*(Sil.Uneven.AuxiliarySource.gap b+6*Sil.Uneven.AuxiliarySource.amp b)=Sil.Uneven.AuxiliarySource.lowReserve at heq
  have hmul := congrArg (fun x : ℝ=>M*x) heq
  have hguard := Sil.Uneven.AuxiliarySource.source_guards hb
  have ha0 : 0≤Sil.Uneven.AuxiliarySource.amp b := by
    have hamin := hguard.2.1
    have hamp := hguard.2.2.1
    linarith
  have ha : Sil.Uneven.AuxiliarySource.lowReserve≤Sil.Uneven.AuxiliarySource.amp b := by
    have hp := mul_nonneg hprice (show 0≤Sil.Uneven.AuxiliarySource.gap b+6*Sil.Uneven.AuxiliarySource.amp b by linarith [hguard.1])
    linarith
  by_cases hm : total≤width
  · rw [max_eq_right (by linarith : total-width≤0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0≤total-width)]
    nlinarith [mul_le_mul_of_nonneg_left htotal hprice,
      mul_nonneg (sub_nonneg.mpr hpriceHi) (sub_nonneg.mpr hwidth)]

theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤b ∧ b≤Sil.Uneven.AuxiliarySource.widthHi) (hM : 0≤M)
    (hwidth : width-nominal≤δ) (hdelta : 0≤δ) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Sil.Uneven.AuxiliarySource.gap b+6*(M*Sil.Uneven.AuxiliarySource.amp b)+padding) :
    width+εold+buffer+(Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*max (total-width) 0+Sil.Uneven.AuxiliarySource.q*mesh≤
      nominal+δ+M*Sil.Uneven.AuxiliarySource.amp b-M*Sil.Uneven.AuxiliarySource.lowReserve+εold+buffer+
        (Sil.Uneven.AuxiliarySource.q/(6*incumbentKappa))*padding+Sil.Uneven.AuxiliarySource.q*mesh := by
  linarith [low_paid_excess_bound hb hM hwidth hdelta hpad htotal]

end
end OAI.SevenEighths.AuxiliaryLow
#print axioms OAI.SevenEighths.AuxiliaryLow.low_paid_excess_bound
#print axioms OAI.SevenEighths.AuxiliaryLow.paid_low_exponent_shifted
