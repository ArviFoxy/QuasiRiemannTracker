import Submissions.arvi_mixed_step.Family.Gen.Data3
import Submissions.arvi_mixed_step.Family.Gen.Scalar5
import Submissions.arvi_mixed_step.Family.Gen.High5_0_00
import Submissions.arvi_mixed_step.Family.Gen.High5_0_01
import Submissions.arvi_mixed_step.Family.Gen.High5_0_02
import Submissions.arvi_mixed_step.Family.Gen.High5_0_10
import Submissions.arvi_mixed_step.Family.Gen.High5_0_11
import Submissions.arvi_mixed_step.Family.Gen.High5_0_12
import Submissions.arvi_mixed_step.Family.Gen.High5_1_00
import Submissions.arvi_mixed_step.Family.Gen.High5_1_01
import Submissions.arvi_mixed_step.Family.Gen.High5_1_02
import Submissions.arvi_mixed_step.Family.Gen.High5_1_10
import Submissions.arvi_mixed_step.Family.Gen.High5_1_11
import Submissions.arvi_mixed_step.Family.Gen.High5_1_12

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.MixedStep.Family
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless

theorem mpiece5_certs : mpiece5.Certs3 where
  sig0 := by norm_num [mpiece5]
  H0 := by norm_num [mpiece5]
  Dy0 := by norm_num [mpiece5]
  capS := by norm_num [mpiece5, capM]
  field i := by
    fin_cases i
    exacts [⟨_, m5_field_0⟩, ⟨_, m5_field_1⟩, ⟨_, m5_field_2⟩, ⟨_, m5_field_3⟩, ⟨_, m5_field_4⟩, ⟨_, m5_field_5⟩, ⟨_, m5_field_6⟩, ⟨_, m5_field_7⟩, ⟨_, m5_field_8⟩]
  scal e jj := by
    fin_cases e <;> fin_cases jj
    exacts [⟨_, m5_scal_0_0⟩, ⟨_, m5_scal_0_1⟩, ⟨_, m5_scal_0_2⟩, ⟨_, m5_scal_0_3⟩, ⟨_, m5_scal_0_4⟩, ⟨_, m5_scal_0_5⟩, ⟨_, m5_scal_0_6⟩, ⟨_, m5_scal_0_7⟩, ⟨_, m5_scal_0_8⟩, ⟨_, m5_scal_0_9⟩, ⟨_, m5_scal_0_10⟩, ⟨_, m5_scal_0_11⟩, ⟨_, m5_scal_0_12⟩, ⟨_, m5_scal_0_13⟩, ⟨_, m5_scal_0_14⟩, ⟨_, m5_scal_0_15⟩, ⟨_, m5_scal_0_16⟩, ⟨_, m5_scal_0_17⟩, ⟨_, m5_scal_1_0⟩, ⟨_, m5_scal_1_1⟩, ⟨_, m5_scal_1_2⟩, ⟨_, m5_scal_1_3⟩, ⟨_, m5_scal_1_4⟩, ⟨_, m5_scal_1_5⟩, ⟨_, m5_scal_1_6⟩, ⟨_, m5_scal_1_7⟩, ⟨_, m5_scal_1_8⟩, ⟨_, m5_scal_1_9⟩, ⟨_, m5_scal_1_10⟩, ⟨_, m5_scal_1_11⟩, ⟨_, m5_scal_1_12⟩, ⟨_, m5_scal_1_13⟩, ⟨_, m5_scal_1_14⟩, ⟨_, m5_scal_1_15⟩, ⟨_, m5_scal_1_16⟩, ⟨_, m5_scal_1_17⟩]
  weak e := by
    fin_cases e
    exacts [⟨_, m5_weak_0⟩, ⟨_, m5_weak_1⟩]
  sec e s i := by
    fin_cases e <;> fin_cases s <;> fin_cases i
    exacts [m5_sec_0_0_0, m5_sec_0_0_1, m5_sec_0_0_2, m5_sec_0_0_3, m5_sec_0_1_0, m5_sec_0_1_1, m5_sec_0_1_2, m5_sec_0_1_3, m5_sec_0_2_0, m5_sec_0_2_1, m5_sec_0_2_2, m5_sec_0_2_3, m5_sec_1_0_0, m5_sec_1_0_1, m5_sec_1_0_2, m5_sec_1_0_3, m5_sec_1_1_0, m5_sec_1_1_1, m5_sec_1_1_2, m5_sec_1_1_3, m5_sec_1_2_0, m5_sec_1_2_1, m5_sec_1_2_2, m5_sec_1_2_3]
  cell e := by
    fin_cases e
    exacts [⟨_, m5_cell_0⟩, ⟨_, m5_cell_1⟩]
  high e k := by
    rcases k with ⟨i, jj⟩
    fin_cases e <;> fin_cases i <;> fin_cases jj
    exacts [m5_high_0_00_pos, m5_high_0_01_pos, m5_high_0_02_pos, m5_high_0_10_pos, m5_high_0_11_pos, m5_high_0_12_pos, m5_high_1_00_pos, m5_high_1_01_pos, m5_high_1_02_pos, m5_high_1_10_pos, m5_high_1_11_pos, m5_high_1_12_pos]

end QRH.MixedStep.Family
