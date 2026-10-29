/- Exact source chain with LOW reserve 1/10000.
Builds on OpenAI, Hailey Collet, Sil, ArviFoxy, Jacob Sussman and Rohan Arun.
Apache-2.0; substantially AI-assisted by OpenAI Codex.
Analytic conclusions remain conditional on the preprint's 7/8 theorem. -/
import Submissions.density_batch.Source.Step
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_batch.Source.Physical001
import Submissions.density_batch.Source.Physical002
import Submissions.density_batch.Source.Physical003
import Submissions.density_batch.Source.Physical004
import Submissions.density_batch.Source.Physical005
import Submissions.density_batch.Source.Physical006
import Submissions.density_batch.Source.Physical007
import Submissions.density_batch.Source.Physical008
import Submissions.density_batch.Source.Physical009
import Submissions.density_batch.Source.Physical010
import Submissions.density_batch.Source.Physical011
import Submissions.density_batch.Source.Physical012
import Submissions.density_batch.Source.Physical013
import Submissions.density_batch.Source.Physical014
import Submissions.density_batch.Source.Physical015
import Submissions.density_batch.Source.Physical016
import Submissions.density_batch.Source.Physical017
import Submissions.density_batch.Source.Physical018
import Submissions.density_batch.Source.Physical019
import Submissions.density_batch.Source.Physical020
import Submissions.density_batch.Source.Physical021
import Submissions.density_batch.Source.Physical022
import Submissions.density_batch.Source.Physical023
import Submissions.density_batch.Source.Physical024
import Submissions.density_batch.Source.Physical025
import Submissions.density_batch.Source.Physical026
import Submissions.density_batch.Source.Physical027
import Submissions.density_batch.Source.Physical028
import Submissions.density_batch.Source.Physical029
import Submissions.density_batch.Source.Physical030
import Submissions.density_batch.Source.Physical031
import Submissions.density_batch.Source.Physical032
import Submissions.density_batch.Source.Physical033
import Submissions.density_batch.Source.Physical034
import Submissions.density_batch.Source.Physical035
import Submissions.density_batch.Source.Physical036
import Submissions.density_batch.Source.Physical037
import Submissions.density_batch.Source.Physical038
import Submissions.density_batch.Source.Physical039
import Submissions.density_batch.Source.Physical040
import Submissions.density_batch.Source.Physical041
import Submissions.density_batch.Source.Physical042
import Submissions.density_batch.Source.Physical043
import Submissions.density_batch.Source.Physical044
import Submissions.density_batch.Source.Physical045
import Submissions.density_batch.Source.Physical046
import Submissions.density_batch.Source.Physical047
import Submissions.density_batch.Source.Physical048
import Submissions.density_batch.Source.Physical049
import Submissions.density_batch.Source.Physical050
import Submissions.density_batch.Source.Physical051
import Submissions.density_batch.Source.Physical052
import Submissions.density_batch.Source.Physical053
import Submissions.density_batch.Source.Physical054
import Submissions.density_batch.Source.Physical055
import Submissions.density_batch.Source.Physical056
import Submissions.density_batch.Source.Physical057
import Submissions.density_batch.Source.Physical058
import Submissions.density_batch.Source.Physical059
import Submissions.density_batch.Source.Physical060
import Submissions.density_batch.Source.Physical061
import Submissions.density_batch.Source.Physical062
import Submissions.density_batch.Source.Physical063
import Submissions.density_batch.Source.Physical064
import Submissions.density_batch.Source.Physical065
import Submissions.density_batch.Source.Physical066
import Submissions.density_batch.Source.Physical067
import Submissions.density_batch.Source.Physical068
import Submissions.density_batch.Source.Physical069
import Submissions.density_batch.Source.Physical070
import Submissions.density_batch.Source.Physical071
import Submissions.density_batch.Source.Physical072
import Submissions.density_batch.Source.Physical073
import Submissions.density_batch.Source.Physical074
import Submissions.density_batch.Source.Physical075
import Submissions.density_batch.Source.Physical076
import Submissions.density_batch.Source.Physical077
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.DensityBatch
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.K15

theorem physical_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (6195261783 / 6250000000 : ℝ) (2379 / 1000 : ℝ) (1 / 10 : ℝ) := by
  have s000 : QRH.Record1252270103Source.GlobalSource (99999 / 100000 : ℝ) (5143 / 2000 : ℝ) (1397 / 10000 : ℝ) := by
    simpa only [Face.Source, bootFace] using boot_source hβ
  have s001 : QRH.Record1252270103Source.GlobalSource (99991321989 / 100000000000 : ℝ) (2569 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical001
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s000
  have s002 : QRH.Record1252270103Source.GlobalSource (24995885641 / 25000000000 : ℝ) (5133 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical002
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s001
  have s003 : QRH.Record1252270103Source.GlobalSource (49987830967 / 50000000000 : ℝ) (641 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical003
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s002
  have s004 : QRH.Record1252270103Source.GlobalSource (49983840153 / 50000000000 : ℝ) (5123 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical004
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s003
  have s005 : QRH.Record1252270103Source.GlobalSource (19991919577 / 20000000000 : ℝ) (2559 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical005
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s004
  have s006 : QRH.Record1252270103Source.GlobalSource (799611319 / 800000000 : ℝ) (5113 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical006
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s005
  have s007 : QRH.Record1252270103Source.GlobalSource (49971565739 / 50000000000 : ℝ) (1277 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical007
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s006
  have s008 : QRH.Record1252270103Source.GlobalSource (19986949579 / 20000000000 : ℝ) (5103 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical008
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s007
  have s009 : QRH.Record1252270103Source.GlobalSource (24981566081 / 25000000000 : ℝ) (2549 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical009
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s008
  have s010 : QRH.Record1252270103Source.GlobalSource (49958840481 / 50000000000 : ℝ) (5093 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical010
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s009
  have s011 : QRH.Record1252270103Source.GlobalSource (19981799601 / 20000000000 : ℝ) (318 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical011
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s010
  have s012 : QRH.Record1252270103Source.GlobalSource (49950107823 / 50000000000 : ℝ) (5083 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical012
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s011
  have s013 : QRH.Record1252270103Source.GlobalSource (49945667039 / 50000000000 : ℝ) (2539 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical013
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s012
  have s014 : QRH.Record1252270103Source.GlobalSource (24970588373 / 25000000000 : ℝ) (5073 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical014
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s013
  have s015 : QRH.Record1252270103Source.GlobalSource (49936637037 / 50000000000 : ℝ) (1267 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical015
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s014
  have s016 : QRH.Record1252270103Source.GlobalSource (9986409601 / 10000000000 : ℝ) (5063 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical016
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s015
  have s017 : QRH.Record1252270103Source.GlobalSource (19970963897 / 20000000000 : ℝ) (2529 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical017
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s016
  have s018 : QRH.Record1252270103Source.GlobalSource (24961361171 / 25000000000 : ℝ) (5053 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical018
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s017
  have s019 : QRH.Record1252270103Source.GlobalSource (9983597179 / 10000000000 : ℝ) (631 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical019
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s018
  have s020 : QRH.Record1252270103Source.GlobalSource (12478300123 / 12500000000 : ℝ) (5043 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical020
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s019
  have s021 : QRH.Record1252270103Source.GlobalSource (49908366223 / 50000000000 : ℝ) (2519 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical021
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s020
  have s022 : QRH.Record1252270103Source.GlobalSource (49903483177 / 50000000000 : ℝ) (5033 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical022
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s021
  have s023 : QRH.Record1252270103Source.GlobalSource (19959420577 / 20000000000 : ℝ) (1257 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical023
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s022
  have s024 : QRH.Record1252270103Source.GlobalSource (19957428443 / 20000000000 : ℝ) (5023 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical024
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s023
  have s025 : QRH.Record1252270103Source.GlobalSource (99777084517 / 100000000000 : ℝ) (2509 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical025
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s024
  have s026 : QRH.Record1252270103Source.GlobalSource (24941732491 / 25000000000 : ℝ) (5013 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical026
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s025
  have s027 : QRH.Record1252270103Source.GlobalSource (99756678727 / 100000000000 : ℝ) (313 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical027
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s026
  have s028 : QRH.Record1252270103Source.GlobalSource (49873165481 / 50000000000 : ℝ) (5003 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical028
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s027
  have s029 : QRH.Record1252270103Source.GlobalSource (99735886829 / 100000000000 : ℝ) (2499 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical029
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s028
  have s030 : QRH.Record1252270103Source.GlobalSource (19945069299 / 20000000000 : ℝ) (4993 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical030
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s029
  have s031 : QRH.Record1252270103Source.GlobalSource (797717681 / 800000000 : ℝ) (1247 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical031
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s030
  have s032 : QRH.Record1252270103Source.GlobalSource (24925994471 / 25000000000 : ℝ) (4983 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical032
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s031
  have s033 : QRH.Record1252270103Source.GlobalSource (49846574967 / 50000000000 : ℝ) (2489 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical033
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s032
  have s034 : QRH.Record1252270103Source.GlobalSource (24920556609 / 25000000000 : ℝ) (4973 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical034
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s033
  have s035 : QRH.Record1252270103Source.GlobalSource (1993424151 / 2000000000 : ℝ) (621 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical035
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s034
  have s036 : QRH.Record1252270103Source.GlobalSource (19932018687 / 20000000000 : ℝ) (4963 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical036
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s035
  have s037 : QRH.Record1252270103Source.GlobalSource (12456110531 / 12500000000 : ℝ) (2479 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical037
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s036
  have s038 : QRH.Record1252270103Source.GlobalSource (19927516029 / 20000000000 : ℝ) (4953 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical038
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s037
  have s039 : QRH.Record1252270103Source.GlobalSource (622663633 / 625000000 : ℝ) (1237 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical039
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s038
  have s040 : QRH.Record1252270103Source.GlobalSource (99614687807 / 100000000000 : ℝ) (4943 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical040
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s039
  have s041 : QRH.Record1252270103Source.GlobalSource (99603099877 / 100000000000 : ℝ) (2469 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical041
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s040
  have s042 : QRH.Record1252270103Source.GlobalSource (99591417641 / 100000000000 : ℝ) (4933 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical042
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s041
  have s043 : QRH.Record1252270103Source.GlobalSource (3111863789 / 3125000000 : ℝ) (308 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical043
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s042
  have s044 : QRH.Record1252270103Source.GlobalSource (49783885423 / 50000000000 : ℝ) (4923 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical044
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s043
  have s045 : QRH.Record1252270103Source.GlobalSource (49777903291 / 50000000000 : ℝ) (2459 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical045
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s044
  have s046 : QRH.Record1252270103Source.GlobalSource (99543748601 / 100000000000 : ℝ) (4913 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical046
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s045
  have s047 : QRH.Record1252270103Source.GlobalSource (12441449631 / 12500000000 : ℝ) (1227 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical047
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s046
  have s048 : QRH.Record1252270103Source.GlobalSource (99519352041 / 100000000000 : ℝ) (4903 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical048
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s047
  have s049 : QRH.Record1252270103Source.GlobalSource (19901402743 / 20000000000 : ℝ) (2449 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical049
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s048
  have s050 : QRH.Record1252270103Source.GlobalSource (9949458221 / 10000000000 : ℝ) (4893 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical050
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s049
  have s051 : QRH.Record1252270103Source.GlobalSource (49741028833 / 50000000000 : ℝ) (611 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical051
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s050
  have s052 : QRH.Record1252270103Source.GlobalSource (99469440221 / 100000000000 : ℝ) (4883 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical052
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s051
  have s053 : QRH.Record1252270103Source.GlobalSource (24864182503 / 25000000000 : ℝ) (2439 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical053
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s052
  have s054 : QRH.Record1252270103Source.GlobalSource (49721963587 / 50000000000 : ℝ) (4873 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical054
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s053
  have s055 : QRH.Record1252270103Source.GlobalSource (49715515921 / 50000000000 : ℝ) (1217 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical055
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s054
  have s056 : QRH.Record1252270103Source.GlobalSource (1988360883 / 2000000000 : ℝ) (4863 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical056
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s055
  have s057 : QRH.Record1252270103Source.GlobalSource (99404964229 / 100000000000 : ℝ) (2429 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical057
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s056
  have s058 : QRH.Record1252270103Source.GlobalSource (9939179221 / 10000000000 : ℝ) (4853 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical058
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s057
  have s059 : QRH.Record1252270103Source.GlobalSource (99378528223 / 100000000000 : ℝ) (303 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical059
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s058
  have s060 : QRH.Record1252270103Source.GlobalSource (99365172397 / 100000000000 : ℝ) (4843 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical060
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s059
  have s061 : QRH.Record1252270103Source.GlobalSource (99351724859 / 100000000000 : ℝ) (2419 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical061
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s060
  have s062 : QRH.Record1252270103Source.GlobalSource (12417273217 / 12500000000 : ℝ) (4833 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical062
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s061
  have s063 : QRH.Record1252270103Source.GlobalSource (6207784697 / 6250000000 : ℝ) (1207 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical063
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s062
  have s064 : QRH.Record1252270103Source.GlobalSource (6206927077 / 6250000000 : ℝ) (4823 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical064
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s063
  have s065 : QRH.Record1252270103Source.GlobalSource (49648510049 / 50000000000 : ℝ) (2409 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical065
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s064
  have s066 : QRH.Record1252270103Source.GlobalSource (49641557929 / 50000000000 : ℝ) (4813 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical066
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s065
  have s067 : QRH.Record1252270103Source.GlobalSource (9926912061 / 10000000000 : ℝ) (601 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical067
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s066
  have s068 : QRH.Record1252270103Source.GlobalSource (3970201379 / 4000000000 : ℝ) (4803 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical068
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s067
  have s069 : QRH.Record1252270103Source.GlobalSource (99240857571 / 100000000000 : ℝ) (2399 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical069
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s068
  have s070 : QRH.Record1252270103Source.GlobalSource (19845318003 / 20000000000 : ℝ) (4793 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical070
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s069
  have s071 : QRH.Record1252270103Source.GlobalSource (24803057981 / 25000000000 : ℝ) (1197 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical071
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s070
  have s072 : QRH.Record1252270103Source.GlobalSource (99197783413 / 100000000000 : ℝ) (4783 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical072
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s071
  have s073 : QRH.Record1252270103Source.GlobalSource (99183244597 / 100000000000 : ℝ) (2389 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical073
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s072
  have s074 : QRH.Record1252270103Source.GlobalSource (99168615589 / 100000000000 : ℝ) (4773 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical074
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s073
  have s075 : QRH.Record1252270103Source.GlobalSource (99153896501 / 100000000000 : ℝ) (298 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical075
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s074
  have s076 : QRH.Record1252270103Source.GlobalSource (24784771861 / 25000000000 : ℝ) (4763 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical076
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s075
  have s077 : QRH.Record1252270103Source.GlobalSource (6195261783 / 6250000000 : ℝ) (2379 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityBatch.density_step hybridGates_Physical077
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s076
  exact s077
end
end QRH.DensityBatch
