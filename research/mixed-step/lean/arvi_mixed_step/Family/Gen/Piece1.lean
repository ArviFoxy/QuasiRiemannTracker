import Submissions.arvi_mixed_step.Family.Gen.Data3
import Submissions.arvi_mixed_step.Family.Gen.Scalar1
import Submissions.arvi_mixed_step.Family.Gen.High1_0_00
import Submissions.arvi_mixed_step.Family.Gen.High1_0_01
import Submissions.arvi_mixed_step.Family.Gen.High1_0_02
import Submissions.arvi_mixed_step.Family.Gen.High1_0_10
import Submissions.arvi_mixed_step.Family.Gen.High1_0_11
import Submissions.arvi_mixed_step.Family.Gen.High1_0_12
import Submissions.arvi_mixed_step.Family.Gen.High1_1_00
import Submissions.arvi_mixed_step.Family.Gen.High1_1_01
import Submissions.arvi_mixed_step.Family.Gen.High1_1_02
import Submissions.arvi_mixed_step.Family.Gen.High1_1_10
import Submissions.arvi_mixed_step.Family.Gen.High1_1_11
import Submissions.arvi_mixed_step.Family.Gen.High1_1_12

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.MixedStep.Family
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless

theorem mpiece1_certs : mpiece1.Certs3 where
  sig0 := by norm_num [mpiece1]
  H0 := by norm_num [mpiece1]
  Dy0 := by norm_num [mpiece1]
  capS := by norm_num [mpiece1, capM]
  field i := by
    fin_cases i
    exacts [⟨_, m1_field_0⟩, ⟨_, m1_field_1⟩, ⟨_, m1_field_2⟩, ⟨_, m1_field_3⟩, ⟨_, m1_field_4⟩, ⟨_, m1_field_5⟩, ⟨_, m1_field_6⟩, ⟨_, m1_field_7⟩, ⟨_, m1_field_8⟩]
  scal e jj := by
    fin_cases e <;> fin_cases jj
    exacts [⟨_, m1_scal_0_0⟩, ⟨_, m1_scal_0_1⟩, ⟨_, m1_scal_0_2⟩, ⟨_, m1_scal_0_3⟩, ⟨_, m1_scal_0_4⟩, ⟨_, m1_scal_0_5⟩, ⟨_, m1_scal_0_6⟩, ⟨_, m1_scal_0_7⟩, ⟨_, m1_scal_0_8⟩, ⟨_, m1_scal_0_9⟩, ⟨_, m1_scal_0_10⟩, ⟨_, m1_scal_0_11⟩, ⟨_, m1_scal_0_12⟩, ⟨_, m1_scal_0_13⟩, ⟨_, m1_scal_0_14⟩, ⟨_, m1_scal_0_15⟩, ⟨_, m1_scal_0_16⟩, ⟨_, m1_scal_0_17⟩, ⟨_, m1_scal_1_0⟩, ⟨_, m1_scal_1_1⟩, ⟨_, m1_scal_1_2⟩, ⟨_, m1_scal_1_3⟩, ⟨_, m1_scal_1_4⟩, ⟨_, m1_scal_1_5⟩, ⟨_, m1_scal_1_6⟩, ⟨_, m1_scal_1_7⟩, ⟨_, m1_scal_1_8⟩, ⟨_, m1_scal_1_9⟩, ⟨_, m1_scal_1_10⟩, ⟨_, m1_scal_1_11⟩, ⟨_, m1_scal_1_12⟩, ⟨_, m1_scal_1_13⟩, ⟨_, m1_scal_1_14⟩, ⟨_, m1_scal_1_15⟩, ⟨_, m1_scal_1_16⟩, ⟨_, m1_scal_1_17⟩]
  weak e := by
    fin_cases e
    exacts [⟨_, m1_weak_0⟩, ⟨_, m1_weak_1⟩]
  sec e s i := by
    fin_cases e <;> fin_cases s <;> fin_cases i
    exacts [m1_sec_0_0_0, m1_sec_0_0_1, m1_sec_0_0_2, m1_sec_0_0_3, m1_sec_0_1_0, m1_sec_0_1_1, m1_sec_0_1_2, m1_sec_0_1_3, m1_sec_0_2_0, m1_sec_0_2_1, m1_sec_0_2_2, m1_sec_0_2_3, m1_sec_1_0_0, m1_sec_1_0_1, m1_sec_1_0_2, m1_sec_1_0_3, m1_sec_1_1_0, m1_sec_1_1_1, m1_sec_1_1_2, m1_sec_1_1_3, m1_sec_1_2_0, m1_sec_1_2_1, m1_sec_1_2_2, m1_sec_1_2_3]
  cell e := by
    fin_cases e
    exacts [⟨_, m1_cell_0⟩, ⟨_, m1_cell_1⟩]
  high e k := by
    rcases k with ⟨i, jj⟩
    fin_cases e <;> fin_cases i <;> fin_cases jj
    exacts [m1_high_0_00_pos, m1_high_0_01_pos, m1_high_0_02_pos, m1_high_0_10_pos, m1_high_0_11_pos, m1_high_0_12_pos, m1_high_1_00_pos, m1_high_1_01_pos, m1_high_1_02_pos, m1_high_1_10_pos, m1_high_1_11_pos, m1_high_1_12_pos]

end QRH.MixedStep.Family
