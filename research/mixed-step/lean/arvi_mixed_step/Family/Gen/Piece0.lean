import Submissions.arvi_mixed_step.Family.Gen.Data3
import Submissions.arvi_mixed_step.Family.Gen.Scalar0
import Submissions.arvi_mixed_step.Family.Gen.High0_0_00
import Submissions.arvi_mixed_step.Family.Gen.High0_0_01
import Submissions.arvi_mixed_step.Family.Gen.High0_0_02
import Submissions.arvi_mixed_step.Family.Gen.High0_0_10
import Submissions.arvi_mixed_step.Family.Gen.High0_0_11
import Submissions.arvi_mixed_step.Family.Gen.High0_0_12
import Submissions.arvi_mixed_step.Family.Gen.High0_1_00
import Submissions.arvi_mixed_step.Family.Gen.High0_1_01
import Submissions.arvi_mixed_step.Family.Gen.High0_1_02
import Submissions.arvi_mixed_step.Family.Gen.High0_1_10
import Submissions.arvi_mixed_step.Family.Gen.High0_1_11
import Submissions.arvi_mixed_step.Family.Gen.High0_1_12

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.MixedStep.Family
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite QRH.MixedStep.Finite QRH.RepeatedMarks.Faceless

theorem mpiece0_certs : mpiece0.Certs3 where
  sig0 := by norm_num [mpiece0]
  H0 := by norm_num [mpiece0]
  Dy0 := by norm_num [mpiece0]
  capS := by norm_num [mpiece0, capM]
  field i := by
    fin_cases i
    exacts [⟨_, m0_field_0⟩, ⟨_, m0_field_1⟩, ⟨_, m0_field_2⟩, ⟨_, m0_field_3⟩, ⟨_, m0_field_4⟩, ⟨_, m0_field_5⟩, ⟨_, m0_field_6⟩, ⟨_, m0_field_7⟩, ⟨_, m0_field_8⟩]
  scal e jj := by
    fin_cases e <;> fin_cases jj
    exacts [⟨_, m0_scal_0_0⟩, ⟨_, m0_scal_0_1⟩, ⟨_, m0_scal_0_2⟩, ⟨_, m0_scal_0_3⟩, ⟨_, m0_scal_0_4⟩, ⟨_, m0_scal_0_5⟩, ⟨_, m0_scal_0_6⟩, ⟨_, m0_scal_0_7⟩, ⟨_, m0_scal_0_8⟩, ⟨_, m0_scal_0_9⟩, ⟨_, m0_scal_0_10⟩, ⟨_, m0_scal_0_11⟩, ⟨_, m0_scal_0_12⟩, ⟨_, m0_scal_0_13⟩, ⟨_, m0_scal_0_14⟩, ⟨_, m0_scal_0_15⟩, ⟨_, m0_scal_0_16⟩, ⟨_, m0_scal_0_17⟩, ⟨_, m0_scal_1_0⟩, ⟨_, m0_scal_1_1⟩, ⟨_, m0_scal_1_2⟩, ⟨_, m0_scal_1_3⟩, ⟨_, m0_scal_1_4⟩, ⟨_, m0_scal_1_5⟩, ⟨_, m0_scal_1_6⟩, ⟨_, m0_scal_1_7⟩, ⟨_, m0_scal_1_8⟩, ⟨_, m0_scal_1_9⟩, ⟨_, m0_scal_1_10⟩, ⟨_, m0_scal_1_11⟩, ⟨_, m0_scal_1_12⟩, ⟨_, m0_scal_1_13⟩, ⟨_, m0_scal_1_14⟩, ⟨_, m0_scal_1_15⟩, ⟨_, m0_scal_1_16⟩, ⟨_, m0_scal_1_17⟩]
  weak e := by
    fin_cases e
    exacts [⟨_, m0_weak_0⟩, ⟨_, m0_weak_1⟩]
  sec e s i := by
    fin_cases e <;> fin_cases s <;> fin_cases i
    exacts [m0_sec_0_0_0, m0_sec_0_0_1, m0_sec_0_0_2, m0_sec_0_0_3, m0_sec_0_1_0, m0_sec_0_1_1, m0_sec_0_1_2, m0_sec_0_1_3, m0_sec_0_2_0, m0_sec_0_2_1, m0_sec_0_2_2, m0_sec_0_2_3, m0_sec_1_0_0, m0_sec_1_0_1, m0_sec_1_0_2, m0_sec_1_0_3, m0_sec_1_1_0, m0_sec_1_1_1, m0_sec_1_1_2, m0_sec_1_1_3, m0_sec_1_2_0, m0_sec_1_2_1, m0_sec_1_2_2, m0_sec_1_2_3]
  cell e := by
    fin_cases e
    exacts [⟨_, m0_cell_0⟩, ⟨_, m0_cell_1⟩]
  high e k := by
    rcases k with ⟨i, jj⟩
    fin_cases e <;> fin_cases i <;> fin_cases jj
    exacts [m0_high_0_00_pos, m0_high_0_01_pos, m0_high_0_02_pos, m0_high_0_10_pos, m0_high_0_11_pos, m0_high_0_12_pos, m0_high_1_00_pos, m0_high_1_01_pos, m0_high_1_02_pos, m0_high_1_10_pos, m0_high_1_11_pos, m0_high_1_12_pos]

end QRH.MixedStep.Family
