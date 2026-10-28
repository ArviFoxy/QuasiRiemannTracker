/- Exact source chain with LOW reserve 1/10000.
Builds on OpenAI, Hailey Collet, Sil, ArviFoxy, Jacob Sussman and Rohan Arun.
Apache-2.0; substantially AI-assisted by OpenAI Codex.
Analytic conclusions remain conditional on the preprint's 7/8 theorem. -/
import Submissions.density_batch.Source.Step
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_batch.Source.Count001
import Submissions.density_batch.Source.Count002
import Submissions.density_batch.Source.Count003
import Submissions.density_batch.Source.Count004
import Submissions.density_batch.Source.Count005
import Submissions.density_batch.Source.Count006
import Submissions.density_batch.Source.Count007
import Submissions.density_batch.Source.Count008
import Submissions.density_batch.Source.Count009
import Submissions.density_batch.Source.Count010
import Submissions.density_batch.Source.Count011
import Submissions.density_batch.Source.Count012
import Submissions.density_batch.Source.Count013
import Submissions.density_batch.Source.Count014
import Submissions.density_batch.Source.Count015
import Submissions.density_batch.Source.Count016
import Submissions.density_batch.Source.Count017
import Submissions.density_batch.Source.Count018
import Submissions.density_batch.Source.Count019
import Submissions.density_batch.Source.Count020
import Submissions.density_batch.Source.Count021
import Submissions.density_batch.Source.Count022
import Submissions.density_batch.Source.Count023
import Submissions.density_batch.Source.Count024
import Submissions.density_batch.Source.Count025
import Submissions.density_batch.Source.Count026
import Submissions.density_batch.Source.Count027
import Submissions.density_batch.Source.Count028
import Submissions.density_batch.Source.Count029
import Submissions.density_batch.Source.Count030
import Submissions.density_batch.Source.Count031
import Submissions.density_batch.Source.Count032
import Submissions.density_batch.Source.Count033
import Submissions.density_batch.Source.Count034
import Submissions.density_batch.Source.Count035
import Submissions.density_batch.Source.Count036
import Submissions.density_batch.Source.Count037
import Submissions.density_batch.Source.Count038
import Submissions.density_batch.Source.Count039
import Submissions.density_batch.Source.Count040
import Submissions.density_batch.Source.Count041
import Submissions.density_batch.Source.Count042
import Submissions.density_batch.Source.Count043
import Submissions.density_batch.Source.Count044
import Submissions.density_batch.Source.Count045
import Submissions.density_batch.Source.Count046
import Submissions.density_batch.Source.Count047
import Submissions.density_batch.Source.Count048
import Submissions.density_batch.Source.Count049
import Submissions.density_batch.Source.Count050
import Submissions.density_batch.Source.Count051
import Submissions.density_batch.Source.Count052
import Submissions.density_batch.Source.Count053
import Submissions.density_batch.Source.Count054
import Submissions.density_batch.Source.Count055
import Submissions.density_batch.Source.Count056
import Submissions.density_batch.Source.Count057
import Submissions.density_batch.Source.Count058
import Submissions.density_batch.Source.Count059
import Submissions.density_batch.Source.Count060
import Submissions.density_batch.Source.Count061
import Submissions.density_batch.Source.Count062
import Submissions.density_batch.Source.Count063
import Submissions.density_batch.Source.Count064
import Submissions.density_batch.Source.Count065
import Submissions.density_batch.Source.Count066
import Submissions.density_batch.Source.Count067
import Submissions.density_batch.Source.Count068
import Submissions.density_batch.Source.Count069
import Submissions.density_batch.Source.Count070
import Submissions.density_batch.Source.Count071
import Submissions.density_batch.Source.Count072
import Submissions.density_batch.Source.Count073
import Submissions.density_batch.Source.Count074
import Submissions.density_batch.Source.Count075
import Submissions.density_batch.Source.Count076
import Submissions.density_batch.Source.Count077
import Submissions.density_batch.Source.Count078
import Submissions.density_batch.Source.Count079
import Submissions.density_batch.Source.Count080
import Submissions.density_batch.Source.Count081
import Submissions.density_batch.Source.Count082
import Submissions.density_batch.Source.Count083
import Submissions.density_batch.Source.Count084
import Submissions.density_batch.Source.Count085
import Submissions.density_batch.Source.Count086
import Submissions.density_batch.Source.Count087
import Submissions.density_batch.Source.Count088
import Submissions.density_batch.Source.Count089
import Submissions.density_batch.Source.Count090
import Submissions.density_batch.Source.Count091
import Submissions.density_batch.Source.Count092
import Submissions.density_batch.Source.Count093
import Submissions.density_batch.Source.Count094
import Submissions.density_batch.Source.Count095
import Submissions.density_batch.Source.Count096
import Submissions.density_batch.Source.Count097
import Submissions.density_batch.Source.Count098
import Submissions.density_batch.Source.Count099
import Submissions.density_batch.Source.Count100
import Submissions.density_batch.Source.Count101
import Submissions.density_batch.Source.Count102
import Submissions.density_batch.Source.Count103
import Submissions.density_batch.Source.Count104
import Submissions.density_batch.Source.Count105
import Submissions.density_batch.Source.Count106
import Submissions.density_batch.Source.Count107
import Submissions.density_batch.Source.Count108
import Submissions.density_batch.Source.Count109
import Submissions.density_batch.Source.Count110
import Submissions.density_batch.Source.Count111
import Submissions.density_batch.Source.Count112
import Submissions.density_batch.Source.Count113
import Submissions.density_batch.Source.Count114
import Submissions.density_batch.Source.Count115
import Submissions.density_batch.Source.Count116
import Submissions.density_batch.Source.Count117
import Submissions.density_batch.Source.Count118
import Submissions.density_batch.Source.Count119
import Submissions.density_batch.Source.Count120
import Submissions.density_batch.Source.Count121
import Submissions.density_batch.Source.Count122
import Submissions.density_batch.Source.Count123
import Submissions.density_batch.Source.Count124
import Submissions.density_batch.Source.Count125
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.DensityBatch
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.K15

theorem final_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (97697347983 / 100000000000 : ℝ) (4370501 / 2000000 : ℝ) (1 / 10 : ℝ) := by
  have s000 : QRH.Record1252270103Source.GlobalSource (9888151 / 10000000 : ℝ) (4683001 / 2000000 : ℝ) (1 / 10 : ℝ) := QRH.SilDensitySplit.K15.final_source hβ
  have s001 : QRH.Record1252270103Source.GlobalSource (98873382637 / 100000000000 : ℝ) (4680501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count001
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s000
  have s002 : QRH.Record1252270103Source.GlobalSource (98865233181 / 100000000000 : ℝ) (4678001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count002
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s001
  have s003 : QRH.Record1252270103Source.GlobalSource (98857061643 / 100000000000 : ℝ) (4675501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count003
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s002
  have s004 : QRH.Record1252270103Source.GlobalSource (98848868033 / 100000000000 : ℝ) (4673001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count004
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s003
  have s005 : QRH.Record1252270103Source.GlobalSource (49420326181 / 50000000000 : ℝ) (4670501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count005
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s004
  have s006 : QRH.Record1252270103Source.GlobalSource (1235405183 / 1250000000 : ℝ) (4668001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count006
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s005
  have s007 : QRH.Record1252270103Source.GlobalSource (49412077439 / 50000000000 : ℝ) (4665501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count007
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s006
  have s008 : QRH.Record1252270103Source.GlobalSource (19763174617 / 20000000000 : ℝ) (4663001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count008
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s007
  have s009 : QRH.Record1252270103Source.GlobalSource (98807569273 / 100000000000 : ℝ) (4660501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count009
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s008
  have s010 : QRH.Record1252270103Source.GlobalSource (24699810863 / 25000000000 : ℝ) (4658001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count010
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s009
  have s011 : QRH.Record1252270103Source.GlobalSource (49395447817 / 50000000000 : ℝ) (4655501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count011
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s010
  have s012 : QRH.Record1252270103Source.GlobalSource (98782525829 / 100000000000 : ℝ) (4653001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count012
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s011
  have s013 : QRH.Record1252270103Source.GlobalSource (3086691689 / 3125000000 : ℝ) (4650501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count013
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s012
  have s014 : QRH.Record1252270103Source.GlobalSource (49382860151 / 50000000000 : ℝ) (4648001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count014
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s013
  have s015 : QRH.Record1252270103Source.GlobalSource (49378642301 / 50000000000 : ℝ) (4645501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count015
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s014
  have s016 : QRH.Record1252270103Source.GlobalSource (98748826959 / 100000000000 : ℝ) (4643001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count016
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s015
  have s017 : QRH.Record1252270103Source.GlobalSource (98740347383 / 100000000000 : ℝ) (4640501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count017
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s016
  have s018 : QRH.Record1252270103Source.GlobalSource (19746369177 / 20000000000 : ℝ) (4638001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count018
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s017
  have s019 : QRH.Record1252270103Source.GlobalSource (24680830619 / 25000000000 : ℝ) (4635501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count019
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s018
  have s020 : QRH.Record1252270103Source.GlobalSource (49357388583 / 50000000000 : ℝ) (4633001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count020
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s019
  have s021 : QRH.Record1252270103Source.GlobalSource (19741241993 / 20000000000 : ℝ) (4630501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count021
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s020
  have s022 : QRH.Record1252270103Source.GlobalSource (24674405221 / 25000000000 : ℝ) (4628001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count022
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s021
  have s023 : QRH.Record1252270103Source.GlobalSource (98689009933 / 100000000000 : ℝ) (4625501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count023
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s022
  have s024 : QRH.Record1252270103Source.GlobalSource (49340188561 / 50000000000 : ℝ) (4623001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count024
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s023
  have s025 : QRH.Record1252270103Source.GlobalSource (98671722461 / 100000000000 : ℝ) (4620501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count025
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s024
  have s026 : QRH.Record1252270103Source.GlobalSource (98663045961 / 100000000000 : ℝ) (4618001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count026
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s025
  have s027 : QRH.Record1252270103Source.GlobalSource (9865434763 / 10000000000 : ℝ) (4615501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count027
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s026
  have s028 : QRH.Record1252270103Source.GlobalSource (49322813739 / 50000000000 : ℝ) (4613001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count028
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s027
  have s029 : QRH.Record1252270103Source.GlobalSource (12329610689 / 12500000000 : ℝ) (4610501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count029
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s028
  have s030 : QRH.Record1252270103Source.GlobalSource (49314060871 / 50000000000 : ℝ) (4608001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count030
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s029
  have s031 : QRH.Record1252270103Source.GlobalSource (6163708511 / 6250000000 : ℝ) (4605501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count031
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s030
  have s032 : QRH.Record1252270103Source.GlobalSource (12326316103 / 12500000000 : ℝ) (4603001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count032
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s031
  have s033 : QRH.Record1252270103Source.GlobalSource (19720339939 / 20000000000 : ℝ) (4600501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count033
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s032
  have s034 : QRH.Record1252270103Source.GlobalSource (98592848799 / 100000000000 : ℝ) (4598001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count034
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s033
  have s035 : QRH.Record1252270103Source.GlobalSource (49291988073 / 50000000000 : ℝ) (4595501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count035
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s034
  have s036 : QRH.Record1252270103Source.GlobalSource (19715016349 / 20000000000 : ℝ) (4593001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count036
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s035
  have s037 : QRH.Record1252270103Source.GlobalSource (49283082803 / 50000000000 : ℝ) (4590501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count037
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s036
  have s038 : QRH.Record1252270103Source.GlobalSource (49278613869 / 50000000000 : ℝ) (4588001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count038
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s037
  have s039 : QRH.Record1252270103Source.GlobalSource (98548268151 / 100000000000 : ℝ) (4585501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count039
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s038
  have s040 : QRH.Record1252270103Source.GlobalSource (49269643427 / 50000000000 : ℝ) (4583001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count040
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s039
  have s041 : QRH.Record1252270103Source.GlobalSource (19706056771 / 20000000000 : ℝ) (4580501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count041
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s040
  have s042 : QRH.Record1252270103Source.GlobalSource (24630314791 / 25000000000 : ℝ) (4578001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count042
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s041
  have s043 : QRH.Record1252270103Source.GlobalSource (98512212789 / 100000000000 : ℝ) (4575501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count043
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s042
  have s044 : QRH.Record1252270103Source.GlobalSource (4925157237 / 5000000000 : ℝ) (4573001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count044
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s043
  have s045 : QRH.Record1252270103Source.GlobalSource (3939762201 / 4000000000 : ℝ) (4570501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count045
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s044
  have s046 : QRH.Record1252270103Source.GlobalSource (49242471827 / 50000000000 : ℝ) (4568001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count046
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s045
  have s047 : QRH.Record1252270103Source.GlobalSource (24618952659 / 25000000000 : ℝ) (4565501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count047
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s046
  have s048 : QRH.Record1252270103Source.GlobalSource (98466655979 / 100000000000 : ℝ) (4563001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count048
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s047
  have s049 : QRH.Record1252270103Source.GlobalSource (24614369923 / 25000000000 : ℝ) (4560501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count049
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s048
  have s050 : QRH.Record1252270103Source.GlobalSource (98448281783 / 100000000000 : ℝ) (4558001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count050
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s049
  have s051 : QRH.Record1252270103Source.GlobalSource (98439062259 / 100000000000 : ℝ) (4555501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count051
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s050
  have s052 : QRH.Record1252270103Source.GlobalSource (98429821127 / 100000000000 : ℝ) (4553001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count052
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s051
  have s053 : QRH.Record1252270103Source.GlobalSource (49210279197 / 50000000000 : ℝ) (4550501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count053
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s052
  have s054 : QRH.Record1252270103Source.GlobalSource (98411274069 / 100000000000 : ℝ) (4548001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count054
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s053
  have s055 : QRH.Record1252270103Source.GlobalSource (98401968161 / 100000000000 : ℝ) (4545501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count055
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s054
  have s056 : QRH.Record1252270103Source.GlobalSource (49196320339 / 50000000000 : ℝ) (4543001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count056
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s055
  have s057 : QRH.Record1252270103Source.GlobalSource (24595822907 / 25000000000 : ℝ) (4540501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count057
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s056
  have s058 : QRH.Record1252270103Source.GlobalSource (4918696051 / 5000000000 : ℝ) (4538001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count058
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s057
  have s059 : QRH.Record1252270103Source.GlobalSource (98364528863 / 100000000000 : ℝ) (4535501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count059
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s058
  have s060 : QRH.Record1252270103Source.GlobalSource (24588778791 / 25000000000 : ℝ) (4533001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count060
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s059
  have s061 : QRH.Record1252270103Source.GlobalSource (24586419983 / 25000000000 : ℝ) (4530501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count061
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s060
  have s062 : QRH.Record1252270103Source.GlobalSource (12292027897 / 12500000000 : ℝ) (4528001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count062
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s061
  have s063 : QRH.Record1252270103Source.GlobalSource (98326744903 / 100000000000 : ℝ) (4525501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count063
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s062
  have s064 : QRH.Record1252270103Source.GlobalSource (98317245121 / 100000000000 : ℝ) (4523001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count064
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s063
  have s065 : QRH.Record1252270103Source.GlobalSource (49153861919 / 50000000000 : ℝ) (4520501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count065
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s064
  have s066 : QRH.Record1252270103Source.GlobalSource (4914909053 / 5000000000 : ℝ) (4518001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count066
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s065
  have s067 : QRH.Record1252270103Source.GlobalSource (98288616793 / 100000000000 : ℝ) (4515501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count067
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s066
  have s068 : QRH.Record1252270103Source.GlobalSource (49139515521 / 50000000000 : ℝ) (4513001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count068
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s067
  have s069 : QRH.Record1252270103Source.GlobalSource (19653884763 / 20000000000 : ℝ) (4510501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count069
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s068
  have s070 : QRH.Record1252270103Source.GlobalSource (49129897559 / 50000000000 : ℝ) (4508001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count070
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s069
  have s071 : QRH.Record1252270103Source.GlobalSource (307031703 / 312500000 : ℝ) (4505501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count071
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s070
  have s072 : QRH.Record1252270103Source.GlobalSource (24560118337 / 25000000000 : ℝ) (4503001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count072
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s071
  have s073 : QRH.Record1252270103Source.GlobalSource (98230780289 / 100000000000 : ℝ) (4500501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count073
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s072
  have s074 : QRH.Record1252270103Source.GlobalSource (1534704153 / 1562500000 : ℝ) (4498001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count074
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s073
  have s075 : QRH.Record1252270103Source.GlobalSource (12276416233 / 12500000000 : ℝ) (4495501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count075
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s074
  have s076 : QRH.Record1252270103Source.GlobalSource (98201572513 / 100000000000 : ℝ) (4493001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count076
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s075
  have s077 : QRH.Record1252270103Source.GlobalSource (49095896873 / 50000000000 : ℝ) (4490501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count077
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s076
  have s078 : QRH.Record1252270103Source.GlobalSource (9818199357 / 10000000000 : ℝ) (4488001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count078
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s077
  have s079 : QRH.Record1252270103Source.GlobalSource (98172171993 / 100000000000 : ℝ) (4485501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count079
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s078
  have s080 : QRH.Record1252270103Source.GlobalSource (49081164511 / 50000000000 : ℝ) (4483001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count080
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s079
  have s081 : QRH.Record1252270103Source.GlobalSource (12269058083 / 12500000000 : ℝ) (4480501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count081
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s080
  have s082 : QRH.Record1252270103Source.GlobalSource (98142578923 / 100000000000 : ℝ) (4478001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count082
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s081
  have s083 : QRH.Record1252270103Source.GlobalSource (24533167951 / 25000000000 : ℝ) (4475501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count083
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s082
  have s084 : QRH.Record1252270103Source.GlobalSource (6132671457 / 6250000000 : ℝ) (4473001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count084
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s083
  have s085 : QRH.Record1252270103Source.GlobalSource (98112793453 / 100000000000 : ℝ) (4470501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count085
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s084
  have s086 : QRH.Record1252270103Source.GlobalSource (98102822233 / 100000000000 : ℝ) (4468001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count086
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s085
  have s087 : QRH.Record1252270103Source.GlobalSource (4904641483 / 5000000000 : ℝ) (4465501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count087
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s086
  have s088 : QRH.Record1252270103Source.GlobalSource (98082815741 / 100000000000 : ℝ) (4463001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count088
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s087
  have s089 : QRH.Record1252270103Source.GlobalSource (98072780483 / 100000000000 : ℝ) (4460501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count089
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s088
  have s090 : QRH.Record1252270103Source.GlobalSource (98062723893 / 100000000000 : ℝ) (4458001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count090
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s089
  have s091 : QRH.Record1252270103Source.GlobalSource (49026322989 / 50000000000 : ℝ) (4455501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count091
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s090
  have s092 : QRH.Record1252270103Source.GlobalSource (12255318343 / 12500000000 : ℝ) (4453001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count092
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s091
  have s093 : QRH.Record1252270103Source.GlobalSource (49016213099 / 50000000000 : ℝ) (4450501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count093
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s092
  have s094 : QRH.Record1252270103Source.GlobalSource (19604456869 / 20000000000 : ℝ) (4448001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count094
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s093
  have s095 : QRH.Record1252270103Source.GlobalSource (24503030297 / 25000000000 : ℝ) (4445501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count095
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s094
  have s096 : QRH.Record1252270103Source.GlobalSource (24500484183 / 25000000000 : ℝ) (4443001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count096
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s095
  have s097 : QRH.Record1252270103Source.GlobalSource (12248966373 / 12500000000 : ℝ) (4440501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count097
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s096
  have s098 : QRH.Record1252270103Source.GlobalSource (1959630079 / 2000000000 : ℝ) (4438001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count098
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s097
  have s099 : QRH.Record1252270103Source.GlobalSource (97971255637 / 100000000000 : ℝ) (4435501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count099
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s098
  have s100 : QRH.Record1252270103Source.GlobalSource (97960986051 / 100000000000 : ℝ) (4433001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count100
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s099
  have s101 : QRH.Record1252270103Source.GlobalSource (97950695197 / 100000000000 : ℝ) (4430501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count101
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s100
  have s102 : QRH.Record1252270103Source.GlobalSource (2448509577 / 2500000000 : ℝ) (4428001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count102
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s101
  have s103 : QRH.Record1252270103Source.GlobalSource (48965024853 / 50000000000 : ℝ) (4425501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count103
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s102
  have s104 : QRH.Record1252270103Source.GlobalSource (48959847541 / 50000000000 : ℝ) (4423001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count104
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s103
  have s105 : QRH.Record1252270103Source.GlobalSource (48954659607 / 50000000000 : ℝ) (4420501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count105
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s104
  have s106 : QRH.Record1252270103Source.GlobalSource (97898922109 / 100000000000 : ℝ) (4418001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count106
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s105
  have s107 : QRH.Record1252270103Source.GlobalSource (24472125943 / 25000000000 : ℝ) (4415501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count107
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s106
  have s108 : QRH.Record1252270103Source.GlobalSource (97878064209 / 100000000000 : ℝ) (4413001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count108
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s107
  have s109 : QRH.Record1252270103Source.GlobalSource (12233450427 / 12500000000 : ℝ) (4410501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count109
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s108
  have s110 : QRH.Record1252270103Source.GlobalSource (97857121399 / 100000000000 : ℝ) (4408001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count110
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s109
  have s111 : QRH.Record1252270103Source.GlobalSource (97846618163 / 100000000000 : ℝ) (4405501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count111
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s110
  have s112 : QRH.Record1252270103Source.GlobalSource (19567218743 / 20000000000 : ℝ) (4403001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count112
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s111
  have s113 : QRH.Record1252270103Source.GlobalSource (4891277403 / 5000000000 : ℝ) (4400501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count113
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s112
  have s114 : QRH.Record1252270103Source.GlobalSource (19562996241 / 20000000000 : ℝ) (4398001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count114
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s113
  have s115 : QRH.Record1252270103Source.GlobalSource (24451098289 / 25000000000 : ℝ) (4395501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count115
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s114
  have s116 : QRH.Record1252270103Source.GlobalSource (48896891959 / 50000000000 : ℝ) (4393001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count116
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s115
  have s117 : QRH.Record1252270103Source.GlobalSource (48891576749 / 50000000000 : ℝ) (4390501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count117
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s116
  have s118 : QRH.Record1252270103Source.GlobalSource (97772501901 / 100000000000 : ℝ) (4388001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count118
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s117
  have s119 : QRH.Record1252270103Source.GlobalSource (24440457283 / 25000000000 : ℝ) (4385501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count119
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s118
  have s120 : QRH.Record1252270103Source.GlobalSource (19550227037 / 20000000000 : ℝ) (4383001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count120
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s119
  have s121 : QRH.Record1252270103Source.GlobalSource (48870210033 / 50000000000 : ℝ) (4380501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count121
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s120
  have s122 : QRH.Record1252270103Source.GlobalSource (97729683781 / 100000000000 : ℝ) (4378001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count122
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s121
  have s123 : QRH.Record1252270103Source.GlobalSource (19543785267 / 20000000000 : ℝ) (4375501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count123
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s122
  have s124 : QRH.Record1252270103Source.GlobalSource (48854073867 / 50000000000 : ℝ) (4373001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count124
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s123
  have s125 : QRH.Record1252270103Source.GlobalSource (97697347983 / 100000000000 : ℝ) (4370501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Count125
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s124
  exact s125
end
end QRH.DensityBatch
