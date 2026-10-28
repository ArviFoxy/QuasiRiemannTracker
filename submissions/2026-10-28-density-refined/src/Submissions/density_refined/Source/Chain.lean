/- Fifty-nine exact density transitions after Jacob Sussman's PR86 count source.
Uses the widened API and density_step proved in tracker PR89.
AI-assisted by OpenAI Codex. Conditional on the preprint's 7/8 theorem. -/
import Submissions.density_refined.Source.Step
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_refined.Source.Wide01
import Submissions.density_refined.Source.Wide02
import Submissions.density_refined.Source.Wide03
import Submissions.density_refined.Source.Wide04
import Submissions.density_refined.Source.Wide05
import Submissions.density_refined.Source.Wide06
import Submissions.density_refined.Source.Wide07
import Submissions.density_refined.Source.Wide08
import Submissions.density_refined.Source.Wide09
import Submissions.density_refined.Source.Wide10
import Submissions.density_refined.Source.Wide11
import Submissions.density_refined.Source.Wide12
import Submissions.density_refined.Source.Wide13
import Submissions.density_refined.Source.Wide14
import Submissions.density_refined.Source.Wide15
import Submissions.density_refined.Source.Wide16
import Submissions.density_refined.Source.Wide17
import Submissions.density_refined.Source.Wide18
import Submissions.density_refined.Source.Wide19
import Submissions.density_refined.Source.Wide20
import Submissions.density_refined.Source.Wide21
import Submissions.density_refined.Source.Wide22
import Submissions.density_refined.Source.Wide23
import Submissions.density_refined.Source.Wide24
import Submissions.density_refined.Source.Wide25
import Submissions.density_refined.Source.Wide26
import Submissions.density_refined.Source.Wide27
import Submissions.density_refined.Source.Wide28
import Submissions.density_refined.Source.Wide29
import Submissions.density_refined.Source.Wide30
import Submissions.density_refined.Source.Wide31
import Submissions.density_refined.Source.Wide32
import Submissions.density_refined.Source.Wide33
import Submissions.density_refined.Source.Wide34
import Submissions.density_refined.Source.Wide35
import Submissions.density_refined.Source.Wide36
import Submissions.density_refined.Source.Wide37
import Submissions.density_refined.Source.Wide38
import Submissions.density_refined.Source.Wide39
import Submissions.density_refined.Source.Wide40
import Submissions.density_refined.Source.Wide41
import Submissions.density_refined.Source.Wide42
import Submissions.density_refined.Source.Wide43
import Submissions.density_refined.Source.Wide44
import Submissions.density_refined.Source.Wide45
import Submissions.density_refined.Source.Wide46
import Submissions.density_refined.Source.Wide47
import Submissions.density_refined.Source.Wide48
import Submissions.density_refined.Source.Wide49
import Submissions.density_refined.Source.Wide50
import Submissions.density_refined.Source.Wide51
import Submissions.density_refined.Source.Wide52
import Submissions.density_refined.Source.Wide53
import Submissions.density_refined.Source.Wide54
import Submissions.density_refined.Source.Wide55
import Submissions.density_refined.Source.Wide56
import Submissions.density_refined.Source.Wide57
import Submissions.density_refined.Source.Wide58
import Submissions.density_refined.Source.Wide59
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.DensityRefined
noncomputable section

theorem final_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (488842537 / 500000000 : ℝ) (4388001 / 2000000 : ℝ) (1 / 10 : ℝ) := by
  have s00 : QRH.Record1252270103Source.GlobalSource (9888151 / 10000000 : ℝ) (4683001 / 2000000 : ℝ) (1 / 10 : ℝ) := QRH.SilDensitySplit.K15.final_source hβ
  have s01 : QRH.Record1252270103Source.GlobalSource (988651581 / 1000000000 : ℝ) (4678001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide01
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s00
  have s02 : QRH.Record1252270103Source.GlobalSource (494243591 / 500000000 : ℝ) (4673001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide02
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s01
  have s03 : QRH.Record1252270103Source.GlobalSource (988321903 / 1000000000 : ℝ) (4668001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide03
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s02
  have s04 : QRH.Record1252270103Source.GlobalSource (494077873 / 500000000 : ℝ) (4663001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide04
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s03
  have s05 : QRH.Record1252270103Source.GlobalSource (987988711 / 1000000000 : ℝ) (4658001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide05
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s04
  have s06 : QRH.Record1252270103Source.GlobalSource (154347 / 156250 : ℝ) (4653001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide06
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s05
  have s07 : QRH.Record1252270103Source.GlobalSource (987652013 / 1000000000 : ℝ) (4648001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide07
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s06
  have s08 : QRH.Record1252270103Source.GlobalSource (987482351 / 1000000000 : ℝ) (4643001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide08
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s07
  have s09 : QRH.Record1252270103Source.GlobalSource (493655907 / 500000000 : ℝ) (4638001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide09
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s08
  have s10 : QRH.Record1252270103Source.GlobalSource (493570201 / 500000000 : ℝ) (4633001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide10
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s09
  have s11 : QRH.Record1252270103Source.GlobalSource (986968117 / 1000000000 : ℝ) (4628001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide11
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s10
  have s12 : QRH.Record1252270103Source.GlobalSource (986794959 / 1000000000 : ℝ) (4623001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide12
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s11
  have s13 : QRH.Record1252270103Source.GlobalSource (986620929 / 1000000000 : ℝ) (4618001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide13
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s12
  have s14 : QRH.Record1252270103Source.GlobalSource (246611507 / 250000000 : ℝ) (4613001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide14
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s13
  have s15 : QRH.Record1252270103Source.GlobalSource (986270257 / 1000000000 : ℝ) (4608001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide15
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s14
  have s16 : QRH.Record1252270103Source.GlobalSource (61630851 / 62500000 : ℝ) (4603001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide16
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s15
  have s17 : QRH.Record1252270103Source.GlobalSource (492958053 / 500000000 : ℝ) (4598001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide17
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s16
  have s18 : QRH.Record1252270103Source.GlobalSource (985737729 / 1000000000 : ℝ) (4593001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide18
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s17
  have s19 : QRH.Record1252270103Source.GlobalSource (197111697 / 200000000 : ℝ) (4588001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide19
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s18
  have s20 : QRH.Record1252270103Source.GlobalSource (492689187 / 500000000 : ℝ) (4583001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide20
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s19
  have s21 : QRH.Record1252270103Source.GlobalSource (492598699 / 500000000 : ℝ) (4578001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide21
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s20
  have s22 : QRH.Record1252270103Source.GlobalSource (985015557 / 1000000000 : ℝ) (4573001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide22
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s21
  have s23 : QRH.Record1252270103Source.GlobalSource (246208213 / 250000000 : ℝ) (4568001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide23
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s22
  have s24 : QRH.Record1252270103Source.GlobalSource (246162321 / 250000000 : ℝ) (4563001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide24
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s23
  have s25 : QRH.Record1252270103Source.GlobalSource (984464853 / 1000000000 : ℝ) (4558001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide25
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s24
  have s26 : QRH.Record1252270103Source.GlobalSource (24606989 / 25000000 : ℝ) (4553001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide26
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s25
  have s27 : QRH.Record1252270103Source.GlobalSource (492046703 / 500000000 : ℝ) (4548001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide27
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s26
  have s28 : QRH.Record1252270103Source.GlobalSource (122988299 / 125000000 : ℝ) (4543001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide28
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s27
  have s29 : QRH.Record1252270103Source.GlobalSource (491859259 / 500000000 : ℝ) (4538001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide29
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s28
  have s30 : QRH.Record1252270103Source.GlobalSource (196705957 / 200000000 : ℝ) (4533001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide30
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s29
  have s31 : QRH.Record1252270103Source.GlobalSource (983340193 / 1000000000 : ℝ) (4528001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide31
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s30
  have s32 : QRH.Record1252270103Source.GlobalSource (491574871 / 500000000 : ℝ) (4523001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide32
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s31
  have s33 : QRH.Record1252270103Source.GlobalSource (982958433 / 1000000000 : ℝ) (4518001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide33
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s32
  have s34 : QRH.Record1252270103Source.GlobalSource (491383133 / 500000000 : ℝ) (4513001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide34
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s33
  have s35 : QRH.Record1252270103Source.GlobalSource (491286621 / 500000000 : ℝ) (4508001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide35
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s34
  have s36 : QRH.Record1252270103Source.GlobalSource (491189681 / 500000000 : ℝ) (4503001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide36
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s35
  have s37 : QRH.Record1252270103Source.GlobalSource (982184627 / 1000000000 : ℝ) (4498001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide37
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s36
  have s38 : QRH.Record1252270103Source.GlobalSource (981989037 / 1000000000 : ℝ) (4493001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide38
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s37
  have s39 : QRH.Record1252270103Source.GlobalSource (61362037 / 62500000 : ℝ) (4488001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide39
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s38
  have s40 : QRH.Record1252270103Source.GlobalSource (490797647 / 500000000 : ℝ) (4483001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide40
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s39
  have s41 : QRH.Record1252270103Source.GlobalSource (981397143 / 1000000000 : ℝ) (4478001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide41
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s40
  have s42 : QRH.Record1252270103Source.GlobalSource (49059907 / 50000000 : ℝ) (4473001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide42
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s41
  have s43 : QRH.Record1252270103Source.GlobalSource (196199657 / 200000000 : ℝ) (4468001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide43
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s42
  have s44 : QRH.Record1252270103Source.GlobalSource (490398789 / 500000000 : ℝ) (4463001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide44
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s43
  have s45 : QRH.Record1252270103Source.GlobalSource (49029801 / 50000000 : ℝ) (4458001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide45
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s44
  have s46 : QRH.Record1252270103Source.GlobalSource (98039361 / 100000000 : ℝ) (4453001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide46
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s45
  have s47 : QRH.Record1252270103Source.GlobalSource (19603807 / 20000000 : ℝ) (4448001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide47
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s46
  have s48 : QRH.Record1252270103Source.GlobalSource (3062457 / 3125000 : ℝ) (4443001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide48
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s47
  have s49 : QRH.Record1252270103Source.GlobalSource (979781281 / 1000000000 : ℝ) (4438001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide49
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s48
  have s50 : QRH.Record1252270103Source.GlobalSource (979575473 / 1000000000 : ℝ) (4433001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide50
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s49
  have s51 : QRH.Record1252270103Source.GlobalSource (979368817 / 1000000000 : ℝ) (4428001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide51
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s50
  have s52 : QRH.Record1252270103Source.GlobalSource (979161313 / 1000000000 : ℝ) (4423001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide52
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s51
  have s53 : QRH.Record1252270103Source.GlobalSource (489476481 / 500000000 : ℝ) (4418001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide53
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s52
  have s54 : QRH.Record1252270103Source.GlobalSource (978743763 / 1000000000 : ℝ) (4413001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide54
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s53
  have s55 : QRH.Record1252270103Source.GlobalSource (978533717 / 1000000000 : ℝ) (4408001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide55
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s54
  have s56 : QRH.Record1252270103Source.GlobalSource (39132913 / 40000000 : ℝ) (4403001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide56
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s55
  have s57 : QRH.Record1252270103Source.GlobalSource (978111087 / 1000000000 : ℝ) (4398001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide57
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s56
  have s58 : QRH.Record1252270103Source.GlobalSource (977898503 / 1000000000 : ℝ) (4393001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide58
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s57
  have s59 : QRH.Record1252270103Source.GlobalSource (488842537 / 500000000 : ℝ) (4388001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityRefined.density_step hybridGates_Wide59
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s58
  exact s59

end
end QRH.DensityRefined
