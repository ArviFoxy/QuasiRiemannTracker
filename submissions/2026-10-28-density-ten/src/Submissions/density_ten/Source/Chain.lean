/- Exact source chain with LOW reserve 1/1000000.
Builds on OpenAI, Hailey Collet, Sil, ArviFoxy, Jacob Sussman and Rohan Arun.
Apache-2.0; substantially AI-assisted by OpenAI Codex.
Analytic conclusions remain conditional on the preprint's 7/8 theorem. -/
import Submissions.density_ten.Source.Step
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_ten.Source.Count001
import Submissions.density_ten.Source.Count002
import Submissions.density_ten.Source.Count003
import Submissions.density_ten.Source.Count004
import Submissions.density_ten.Source.Count005
import Submissions.density_ten.Source.Count006
import Submissions.density_ten.Source.Count007
import Submissions.density_ten.Source.Count008
import Submissions.density_ten.Source.Count009
import Submissions.density_ten.Source.Count010
import Submissions.density_ten.Source.Count011
import Submissions.density_ten.Source.Count012
import Submissions.density_ten.Source.Count013
import Submissions.density_ten.Source.Count014
import Submissions.density_ten.Source.Count015
import Submissions.density_ten.Source.Count016
import Submissions.density_ten.Source.Count017
import Submissions.density_ten.Source.Count018
import Submissions.density_ten.Source.Count019
import Submissions.density_ten.Source.Count020
import Submissions.density_ten.Source.Count021
import Submissions.density_ten.Source.Count022
import Submissions.density_ten.Source.Count023
import Submissions.density_ten.Source.Count024
import Submissions.density_ten.Source.Count025
import Submissions.density_ten.Source.Count026
import Submissions.density_ten.Source.Count027
import Submissions.density_ten.Source.Count028
import Submissions.density_ten.Source.Count029
import Submissions.density_ten.Source.Count030
import Submissions.density_ten.Source.Count031
import Submissions.density_ten.Source.Count032
import Submissions.density_ten.Source.Count033
import Submissions.density_ten.Source.Count034
import Submissions.density_ten.Source.Count035
import Submissions.density_ten.Source.Count036
import Submissions.density_ten.Source.Count037
import Submissions.density_ten.Source.Count038
import Submissions.density_ten.Source.Count039
import Submissions.density_ten.Source.Count040
import Submissions.density_ten.Source.Count041
import Submissions.density_ten.Source.Count042
import Submissions.density_ten.Source.Count043
import Submissions.density_ten.Source.Count044
import Submissions.density_ten.Source.Count045
import Submissions.density_ten.Source.Count046
import Submissions.density_ten.Source.Count047
import Submissions.density_ten.Source.Count048
import Submissions.density_ten.Source.Count049
import Submissions.density_ten.Source.Count050
import Submissions.density_ten.Source.Count051
import Submissions.density_ten.Source.Count052
import Submissions.density_ten.Source.Count053
import Submissions.density_ten.Source.Count054
import Submissions.density_ten.Source.Count055
import Submissions.density_ten.Source.Count056
import Submissions.density_ten.Source.Count057
import Submissions.density_ten.Source.Count058
import Submissions.density_ten.Source.Count059
import Submissions.density_ten.Source.Count060
import Submissions.density_ten.Source.Count061
import Submissions.density_ten.Source.Count062
import Submissions.density_ten.Source.Count063
import Submissions.density_ten.Source.Count064
import Submissions.density_ten.Source.Count065
import Submissions.density_ten.Source.Count066
import Submissions.density_ten.Source.Count067
import Submissions.density_ten.Source.Count068
import Submissions.density_ten.Source.Count069
import Submissions.density_ten.Source.Count070
import Submissions.density_ten.Source.Count071
import Submissions.density_ten.Source.Count072
import Submissions.density_ten.Source.Count073
import Submissions.density_ten.Source.Count074
import Submissions.density_ten.Source.Count075
import Submissions.density_ten.Source.Count076
import Submissions.density_ten.Source.Count077
import Submissions.density_ten.Source.Count078
import Submissions.density_ten.Source.Count079
import Submissions.density_ten.Source.Count080
import Submissions.density_ten.Source.Count081
import Submissions.density_ten.Source.Count082
import Submissions.density_ten.Source.Count083
import Submissions.density_ten.Source.Count084
import Submissions.density_ten.Source.Count085
import Submissions.density_ten.Source.Count086
import Submissions.density_ten.Source.Count087
import Submissions.density_ten.Source.Count088
import Submissions.density_ten.Source.Count089
import Submissions.density_ten.Source.Count090
import Submissions.density_ten.Source.Count091
import Submissions.density_ten.Source.Count092
import Submissions.density_ten.Source.Count093
import Submissions.density_ten.Source.Count094
import Submissions.density_ten.Source.Count095
import Submissions.density_ten.Source.Count096
import Submissions.density_ten.Source.Count097
import Submissions.density_ten.Source.Count098
import Submissions.density_ten.Source.Count099
import Submissions.density_ten.Source.Count100
import Submissions.density_ten.Source.Count101
import Submissions.density_ten.Source.Count102
import Submissions.density_ten.Source.Count103
import Submissions.density_ten.Source.Count104
import Submissions.density_ten.Source.Count105
import Submissions.density_ten.Source.Count106
import Submissions.density_ten.Source.Count107
import Submissions.density_ten.Source.Count108
import Submissions.density_ten.Source.Count109
import Submissions.density_ten.Source.Count110
import Submissions.density_ten.Source.Count111
import Submissions.density_ten.Source.Count112
import Submissions.density_ten.Source.Count113
import Submissions.density_ten.Source.Count114
import Submissions.density_ten.Source.Count115
import Submissions.density_ten.Source.Count116
import Submissions.density_ten.Source.Count117
import Submissions.density_ten.Source.Count118
import Submissions.density_ten.Source.Count119
import Submissions.density_ten.Source.Count120
import Submissions.density_ten.Source.Count121
import Submissions.density_ten.Source.Count122
import Submissions.density_ten.Source.Count123
import Submissions.density_ten.Source.Count124
import Submissions.density_ten.Source.Count125
import Submissions.density_ten.Source.Count126
import Submissions.density_ten.Source.Count127
import Submissions.density_ten.Source.Count128
import Submissions.density_ten.Source.Count129
import Submissions.density_ten.Source.Count130
import Submissions.density_ten.Source.Count131
import Submissions.density_ten.Source.Count132
import Submissions.density_ten.Source.Count133
import Submissions.density_ten.Source.Count134
import Submissions.density_ten.Source.Count135
import Submissions.density_ten.Source.Count136
import Submissions.density_ten.Source.Count137
import Submissions.density_ten.Source.Count138
import Submissions.density_ten.Source.Count139
import Submissions.density_ten.Source.Count140
import Submissions.density_ten.Source.Count141
import Submissions.density_ten.Source.Count142
import Submissions.density_ten.Source.Count143
import Submissions.density_ten.Source.Count144
import Submissions.density_ten.Source.Count145
import Submissions.density_ten.Source.Count146
import Submissions.density_ten.Source.Count147
import Submissions.density_ten.Source.Count148
import Submissions.density_ten.Source.Count149
import Submissions.density_ten.Source.Count150
import Submissions.density_ten.Source.Count151
import Submissions.density_ten.Source.Count152
import Submissions.density_ten.Source.Count153
import Submissions.density_ten.Source.Count154
import Submissions.density_ten.Source.Count155
import Submissions.density_ten.Source.Count156
import Submissions.density_ten.Source.Count157
import Submissions.density_ten.Source.Count158
import Submissions.density_ten.Source.Count159
import Submissions.density_ten.Source.Count160
import Submissions.density_ten.Source.Count161
import Submissions.density_ten.Source.Count162
import Submissions.density_ten.Source.Count163
import Submissions.density_ten.Source.Count164
import Submissions.density_ten.Source.Count165
import Submissions.density_ten.Source.Count166
import Submissions.density_ten.Source.Count167
import Submissions.density_ten.Source.Count168
import Submissions.density_ten.Source.Count169
import Submissions.density_ten.Source.Count170
import Submissions.density_ten.Source.Count171
import Submissions.density_ten.Source.Count172
import Submissions.density_ten.Source.Count173
import Submissions.density_ten.Source.Count174
import Submissions.density_ten.Source.Count175
import Submissions.density_ten.Source.Count176
import Submissions.density_ten.Source.Count177
import Submissions.density_ten.Source.Count178
import Submissions.density_ten.Source.Count179
import Submissions.density_ten.Source.Count180
import Submissions.density_ten.Source.Count181
import Submissions.density_ten.Source.Count182
import Submissions.density_ten.Source.Count183
import Submissions.density_ten.Source.Count184
import Submissions.density_ten.Source.Count185
import Submissions.density_ten.Source.Count186
import Submissions.density_ten.Source.Count187
import Submissions.density_ten.Source.Count188
import Submissions.density_ten.Source.Count189
import Submissions.density_ten.Source.Count190
import Submissions.density_ten.Source.Count191
import Submissions.density_ten.Source.Count192
import Submissions.density_ten.Source.Count193
import Submissions.density_ten.Source.Count194
import Submissions.density_ten.Source.Count195
import Submissions.density_ten.Source.Count196
import Submissions.density_ten.Source.Count197
import Submissions.density_ten.Source.Count198
import Submissions.density_ten.Source.Count199
import Submissions.density_ten.Source.Count200
import Submissions.density_ten.Source.Count201
import Submissions.density_ten.Source.Count202
import Submissions.density_ten.Source.Count203
import Submissions.density_ten.Source.Count204
import Submissions.density_ten.Source.Count205
import Submissions.density_ten.Source.Count206
import Submissions.density_ten.Source.Count207
import Submissions.density_ten.Source.Count208
import Submissions.density_ten.Source.Count209
import Submissions.density_ten.Source.Count210
import Submissions.density_ten.Source.Count211
import Submissions.density_ten.Source.Count212
import Submissions.density_ten.Source.Count213
import Submissions.density_ten.Source.Count214
import Submissions.density_ten.Source.Count215
import Submissions.density_ten.Source.Count216
import Submissions.density_ten.Source.Count217
import Submissions.density_ten.Source.Count218
import Submissions.density_ten.Source.Count219
import Submissions.density_ten.Source.Count220
import Submissions.density_ten.Source.Count221
import Submissions.density_ten.Source.Count222
import Submissions.density_ten.Source.Count223
import Submissions.density_ten.Source.Count224
import Submissions.density_ten.Source.Count225
import Submissions.density_ten.Source.Count226
import Submissions.density_ten.Source.Count227
import Submissions.density_ten.Source.Count228
import Submissions.density_ten.Source.Count229
import Submissions.density_ten.Source.Count230
import Submissions.density_ten.Source.Count231
import Submissions.density_ten.Source.Count232
import Submissions.density_ten.Source.Count233
import Submissions.density_ten.Source.Count234
import Submissions.density_ten.Source.Count235
import Submissions.density_ten.Source.Count236
import Submissions.density_ten.Source.Count237
import Submissions.density_ten.Source.Count238
import Submissions.density_ten.Source.Count239
import Submissions.density_ten.Source.Count240
import Submissions.density_ten.Source.Count241
import Submissions.density_ten.Source.Count242
import Submissions.density_ten.Source.Count243
import Submissions.density_ten.Source.Count244
import Submissions.density_ten.Source.Count245
import Submissions.density_ten.Source.Count246
import Submissions.density_ten.Source.Count247
import Submissions.density_ten.Source.Count248
import Submissions.density_ten.Source.Count249
import Submissions.density_ten.Source.Count250
import Submissions.density_ten.Source.Count251
import Submissions.density_ten.Source.Count252
import Submissions.density_ten.Source.Count253
import Submissions.density_ten.Source.Count254
import Submissions.density_ten.Source.Count255
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.DensityTen
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.K15

theorem final_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (9767125183289 / 10000000000000 : ℝ) (4364251 / 2000000 : ℝ) (1 / 10 : ℝ) := by
  have s000 : QRH.Record1252270103Source.GlobalSource (9888151 / 10000000 : ℝ) (4683001 / 2000000 : ℝ) (1 / 10 : ℝ) := QRH.SilDensitySplit.K15.final_source hβ
  have s001 : QRH.Record1252270103Source.GlobalSource (9887745344543 / 10000000000000 : ℝ) (4681751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count001
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s000
  have s002 : QRH.Record1252270103Source.GlobalSource (395493565447 / 400000000000 : ℝ) (4680501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count002
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s001
  have s003 : QRH.Record1252270103Source.GlobalSource (3862082959 / 3906250000 : ℝ) (4679251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count003
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s002
  have s004 : QRH.Record1252270103Source.GlobalSource (61790781633 / 62500000000 : ℝ) (4678001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count004
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s003
  have s005 : QRH.Record1252270103Source.GlobalSource (4943058597519 / 5000000000000 : ℝ) (4676751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count005
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s004
  have s006 : QRH.Record1252270103Source.GlobalSource (9885708776453 / 10000000000000 : ℝ) (4675501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count006
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s005
  have s007 : QRH.Record1252270103Source.GlobalSource (308915618927 / 312500000000 : ℝ) (4674251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count007
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s006
  have s008 : QRH.Record1252270103Source.GlobalSource (9884890282809 / 10000000000000 : ℝ) (4673001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count008
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s007
  have s009 : QRH.Record1252270103Source.GlobalSource (4942240104013 / 5000000000000 : ℝ) (4671751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count009
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s008
  have s010 : QRH.Record1252270103Source.GlobalSource (4942034790727 / 5000000000000 : ℝ) (4670501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count010
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s009
  have s011 : QRH.Record1252270103Source.GlobalSource (9883658403229 / 10000000000000 : ℝ) (4669251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count011
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s010
  have s012 : QRH.Record1252270103Source.GlobalSource (617702917093 / 625000000000 : ℝ) (4668001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count012
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s011
  have s013 : QRH.Record1252270103Source.GlobalSource (617677149523 / 625000000000 : ℝ) (4666751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count013
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s012
  have s014 : QRH.Record1252270103Source.GlobalSource (1235302695001 / 1250000000000 : ℝ) (4665501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count014
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s013
  have s015 : QRH.Record1252270103Source.GlobalSource (1976401635309 / 2000000000000 : ℝ) (4664251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count015
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s014
  have s016 : QRH.Record1252270103Source.GlobalSource (4940797121059 / 5000000000000 : ℝ) (4663001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count016
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s015
  have s017 : QRH.Record1252270103Source.GlobalSource (1976235951373 / 2000000000000 : ℝ) (4661751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count017
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s016
  have s018 : QRH.Record1252270103Source.GlobalSource (9880764720923 / 10000000000000 : ℝ) (4660501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count018
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s017
  have s019 : QRH.Record1252270103Source.GlobalSource (9880349134429 / 10000000000000 : ℝ) (4659251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count019
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s018
  have s020 : QRH.Record1252270103Source.GlobalSource (123499162469 / 125000000000 : ℝ) (4658001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count020
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s019
  have s021 : QRH.Record1252270103Source.GlobalSource (9879516310331 / 10000000000000 : ℝ) (4656751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count021
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s020
  have s022 : QRH.Record1252270103Source.GlobalSource (4939549536497 / 5000000000000 : ℝ) (4655501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count022
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s021
  have s023 : QRH.Record1252270103Source.GlobalSource (4939340642821 / 5000000000000 : ℝ) (4654251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count023
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s022
  have s024 : QRH.Record1252270103Source.GlobalSource (9878262948407 / 10000000000000 : ℝ) (4653001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count024
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s023
  have s025 : QRH.Record1252270103Source.GlobalSource (9877844061421 / 10000000000000 : ℝ) (4651751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count025
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s024
  have s026 : QRH.Record1252270103Source.GlobalSource (1975484924963 / 2000000000000 : ℝ) (4650501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count026
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s025
  have s027 : QRH.Record1252270103Source.GlobalSource (3858204937 / 3906250000 : ℝ) (4649251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count027
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s026
  have s028 : QRH.Record1252270103Source.GlobalSource (9876584103267 / 10000000000000 : ℝ) (4648001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count028
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s027
  have s029 : QRH.Record1252270103Source.GlobalSource (9876163018587 / 10000000000000 : ℝ) (4646751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count029
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s028
  have s030 : QRH.Record1252270103Source.GlobalSource (1975148276963 / 2000000000000 : ℝ) (4645501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count030
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s029
  have s031 : QRH.Record1252270103Source.GlobalSource (4937659601041 / 5000000000000 : ℝ) (4644251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count031
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s030
  have s032 : QRH.Record1252270103Source.GlobalSource (9874896470521 / 10000000000000 : ℝ) (4643001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count032
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s031
  have s033 : QRH.Record1252270103Source.GlobalSource (9874473190263 / 10000000000000 : ℝ) (4641751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count033
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s032
  have s034 : QRH.Record1252270103Source.GlobalSource (4937024680719 / 5000000000000 : ℝ) (4640501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count034
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s033
  have s035 : QRH.Record1252270103Source.GlobalSource (394944999367 / 400000000000 : ℝ) (4639251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count035
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s034
  have s036 : QRH.Record1252270103Source.GlobalSource (9873200058603 / 10000000000000 : ℝ) (4638001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count036
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s035
  have s037 : QRH.Record1252270103Source.GlobalSource (197455491697 / 200000000000 : ℝ) (4636751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count037
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s036
  have s038 : QRH.Record1252270103Source.GlobalSource (1974469712611 / 2000000000000 : ℝ) (4635501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count038
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s037
  have s039 : QRH.Record1252270103Source.GlobalSource (4935960996667 / 5000000000000 : ℝ) (4634251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count039
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s038
  have s040 : QRH.Record1252270103Source.GlobalSource (9871494875813 / 10000000000000 : ℝ) (4633001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count040
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s039
  have s041 : QRH.Record1252270103Source.GlobalSource (9871067210617 / 10000000000000 : ℝ) (4631751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count041
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s040
  have s042 : QRH.Record1252270103Source.GlobalSource (9870638997871 / 10000000000000 : ℝ) (4630501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count042
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s041
  have s043 : QRH.Record1252270103Source.GlobalSource (9870210237701 / 10000000000000 : ℝ) (4629251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count043
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s042
  have s044 : QRH.Record1252270103Source.GlobalSource (1973956186047 / 2000000000000 : ℝ) (4628001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count044
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s043
  have s045 : QRH.Record1252270103Source.GlobalSource (24673377689 / 25000000000 : ℝ) (4626751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count045
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s044
  have s046 : QRH.Record1252270103Source.GlobalSource (9868920673923 / 10000000000000 : ℝ) (4625501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count046
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s045
  have s047 : QRH.Record1252270103Source.GlobalSource (986848972533 / 1000000000000 : ℝ) (4624251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count047
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s046
  have s048 : QRH.Record1252270103Source.GlobalSource (2467014557487 / 2500000000000 : ℝ) (4623001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count048
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s047
  have s049 : QRH.Record1252270103Source.GlobalSource (4933813093951 / 5000000000000 : ℝ) (4621751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count049
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s048
  have s050 : QRH.Record1252270103Source.GlobalSource (2466798399829 / 2500000000000 : ℝ) (4620501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count050
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s049
  have s051 : QRH.Record1252270103Source.GlobalSource (9866760464311 / 10000000000000 : ℝ) (4619251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count051
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s050
  have s052 : QRH.Record1252270103Source.GlobalSource (9866326783009 / 10000000000000 : ℝ) (4618001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count052
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s051
  have s053 : QRH.Record1252270103Source.GlobalSource (986589255553 / 1000000000000 : ℝ) (4616751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count053
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s052
  have s054 : QRH.Record1252270103Source.GlobalSource (1973091556399 / 2000000000000 : ℝ) (4615501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count054
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s053
  have s055 : QRH.Record1252270103Source.GlobalSource (2466255615631 / 2500000000000 : ℝ) (4614251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count055
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s054
  have s056 : QRH.Record1252270103Source.GlobalSource (2466146649309 / 2500000000000 : ℝ) (4613001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count056
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s055
  have s057 : QRH.Record1252270103Source.GlobalSource (9864150186253 / 10000000000000 : ℝ) (4611751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count057
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s056
  have s058 : QRH.Record1252270103Source.GlobalSource (9863713229697 / 10000000000000 : ℝ) (4610501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count058
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s057
  have s059 : QRH.Record1252270103Source.GlobalSource (986327572769 / 1000000000000 : ℝ) (4609251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count059
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s058
  have s060 : QRH.Record1252270103Source.GlobalSource (4931418840177 / 5000000000000 : ℝ) (4608001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count060
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s059
  have s061 : QRH.Record1252270103Source.GlobalSource (154099985747 / 156250000000 : ℝ) (4606751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count061
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s060
  have s062 : QRH.Record1252270103Source.GlobalSource (9861959950171 / 10000000000000 : ℝ) (4605501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count062
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s061
  have s063 : QRH.Record1252270103Source.GlobalSource (2465380066891 / 2500000000000 : ℝ) (4604251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count063
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s062
  have s064 : QRH.Record1252270103Source.GlobalSource (4930540020053 / 5000000000000 : ℝ) (4603001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count064
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s063
  have s065 : QRH.Record1252270103Source.GlobalSource (9860639267917 / 10000000000000 : ℝ) (4601751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count065
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s064
  have s066 : QRH.Record1252270103Source.GlobalSource (9860197951113 / 10000000000000 : ℝ) (4600501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count066
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s065
  have s067 : QRH.Record1252270103Source.GlobalSource (985975608981 / 1000000000000 : ℝ) (4599251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count067
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s066
  have s068 : QRH.Record1252270103Source.GlobalSource (9859313684123 / 10000000000000 : ℝ) (4598001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count068
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s067
  have s069 : QRH.Record1252270103Source.GlobalSource (4929435367083 / 5000000000000 : ℝ) (4596751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count069
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s068
  have s070 : QRH.Record1252270103Source.GlobalSource (9858427240053 / 10000000000000 : ℝ) (4595501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count070
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s069
  have s071 : QRH.Record1252270103Source.GlobalSource (9857983201901 / 10000000000000 : ℝ) (4594251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count071
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s070
  have s072 : QRH.Record1252270103Source.GlobalSource (2464384654957 / 2500000000000 : ℝ) (4593001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count072
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s071
  have s073 : QRH.Record1252270103Source.GlobalSource (9857093493951 / 10000000000000 : ℝ) (4591751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count073
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s072
  have s074 : QRH.Record1252270103Source.GlobalSource (4928323912193 / 5000000000000 : ℝ) (4590501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count074
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s073
  have s075 : QRH.Record1252270103Source.GlobalSource (616012600703 / 625000000000 : ℝ) (4589251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count075
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s074
  have s076 : QRH.Record1252270103Source.GlobalSource (197115097093 / 200000000000 : ℝ) (4588001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count076
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s075
  have s077 : QRH.Record1252270103Source.GlobalSource (1971061510943 / 2000000000000 : ℝ) (4586751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count077
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s076
  have s078 : QRH.Record1252270103Source.GlobalSource (9854859711547 / 10000000000000 : ℝ) (4585501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count078
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s077
  have s079 : QRH.Record1252270103Source.GlobalSource (4927205662629 / 5000000000000 : ℝ) (4584251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count079
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s078
  have s080 : QRH.Record1252270103Source.GlobalSource (4926981197979 / 5000000000000 : ℝ) (4583001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count080
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s079
  have s081 : QRH.Record1252270103Source.GlobalSource (9853512923757 / 10000000000000 : ℝ) (4581751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count081
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s080
  have s082 : QRH.Record1252270103Source.GlobalSource (1970612581753 / 2000000000000 : ℝ) (4580501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count082
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s081
  have s083 : QRH.Record1252270103Source.GlobalSource (9852612351093 / 10000000000000 : ℝ) (4579251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count083
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s082
  have s084 : QRH.Record1252270103Source.GlobalSource (4926080625427 / 5000000000000 : ℝ) (4578001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count084
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s083
  have s085 : QRH.Record1252270103Source.GlobalSource (4925854804081 / 5000000000000 : ℝ) (4576751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count085
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s084
  have s086 : QRH.Record1252270103Source.GlobalSource (9851257423129 / 10000000000000 : ℝ) (4575501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count086
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s085
  have s087 : QRH.Record1252270103Source.GlobalSource (4925402347933 / 5000000000000 : ℝ) (4574251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count087
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s086
  have s088 : QRH.Record1252270103Source.GlobalSource (1231293928311 / 1250000000000 : ℝ) (4573001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count088
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s087
  have s089 : QRH.Record1252270103Source.GlobalSource (4924948807551 / 5000000000000 : ℝ) (4571751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count089
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s088
  have s090 : QRH.Record1252270103Source.GlobalSource (4924721630907 / 5000000000000 : ℝ) (4570501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count090
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s089
  have s091 : QRH.Record1252270103Source.GlobalSource (9848988366731 / 10000000000000 : ℝ) (4569251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count091
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s090
  have s092 : QRH.Record1252270103Source.GlobalSource (9848532929959 / 10000000000000 : ℝ) (4568001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count092
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s091
  have s093 : QRH.Record1252270103Source.GlobalSource (9848076951603 / 10000000000000 : ℝ) (4566751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count093
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s092
  have s094 : QRH.Record1252270103Source.GlobalSource (9847620431769 / 10000000000000 : ℝ) (4565501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count094
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s093
  have s095 : QRH.Record1252270103Source.GlobalSource (9847163370563 / 10000000000000 : ℝ) (4564251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count095
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s094
  have s096 : QRH.Record1252270103Source.GlobalSource (4923352884047 / 5000000000000 : ℝ) (4563001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count096
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s095
  have s097 : QRH.Record1252270103Source.GlobalSource (9846247624471 / 10000000000000 : ℝ) (4561751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count097
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s096
  have s098 : QRH.Record1252270103Source.GlobalSource (4922894469901 / 5000000000000 : ℝ) (4560501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count098
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s097
  have s099 : QRH.Record1252270103Source.GlobalSource (2461332428549 / 2500000000000 : ℝ) (4559251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count099
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s098
  have s100 : QRH.Record1252270103Source.GlobalSource (123060874347 / 125000000000 : ℝ) (4558001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count100
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s099
  have s101 : QRH.Record1252270103Source.GlobalSource (4922204820299 / 5000000000000 : ℝ) (4556751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count101
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s100
  have s102 : QRH.Record1252270103Source.GlobalSource (2460987198203 / 2500000000000 : ℝ) (4555501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count102
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s101
  have s103 : QRH.Record1252270103Source.GlobalSource (1230435925563 / 1250000000000 : ℝ) (4554251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count103
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s102
  have s104 : QRH.Record1252270103Source.GlobalSource (393721019031 / 400000000000 : ℝ) (4553001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count104
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s103
  have s105 : QRH.Record1252270103Source.GlobalSource (9842563006727 / 10000000000000 : ℝ) (4551751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count105
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s104
  have s106 : QRH.Record1252270103Source.GlobalSource (492104999873 / 500000000000 : ℝ) (4550501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count106
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s105
  have s107 : QRH.Record1252270103Source.GlobalSource (4920818224039 / 5000000000000 : ℝ) (4549251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count107
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s106
  have s108 : QRH.Record1252270103Source.GlobalSource (1968234471737 / 2000000000000 : ℝ) (4548001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count108
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s107
  have s109 : QRH.Record1252270103Source.GlobalSource (2460176932347 / 2500000000000 : ℝ) (4546751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count109
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s108
  have s110 : QRH.Record1252270103Source.GlobalSource (307507580009 / 312500000000 : ℝ) (4545501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count110
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s109
  have s111 : QRH.Record1252270103Source.GlobalSource (9839776851491 / 10000000000000 : ℝ) (4544251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count111
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s110
  have s112 : QRH.Record1252270103Source.GlobalSource (9839310603099 / 10000000000000 : ℝ) (4543001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count112
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s111
  have s113 : QRH.Record1252270103Source.GlobalSource (9838843815199 / 10000000000000 : ℝ) (4541751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count113
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s112
  have s114 : QRH.Record1252270103Source.GlobalSource (4919188243949 / 5000000000000 : ℝ) (4540501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count114
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s113
  have s115 : QRH.Record1252270103Source.GlobalSource (614869288831 / 625000000000 : ℝ) (4539251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count115
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s114
  have s116 : QRH.Record1252270103Source.GlobalSource (9837440215501 / 10000000000000 : ℝ) (4538001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count116
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s115
  have s117 : QRH.Record1252270103Source.GlobalSource (9836971270597 / 10000000000000 : ℝ) (4536751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count117
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s116
  have s118 : QRH.Record1252270103Source.GlobalSource (9836501786683 / 10000000000000 : ℝ) (4535501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count118
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s117
  have s119 : QRH.Record1252270103Source.GlobalSource (491801588193 / 500000000000 : ℝ) (4534251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count119
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s118
  have s120 : QRH.Record1252270103Source.GlobalSource (9835561202229 / 10000000000000 : ℝ) (4533001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count120
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s119
  have s121 : QRH.Record1252270103Source.GlobalSource (9835090101891 / 10000000000000 : ℝ) (4531751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count121
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s120
  have s122 : QRH.Record1252270103Source.GlobalSource (4917309231473 / 5000000000000 : ℝ) (4530501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count122
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s121
  have s123 : QRH.Record1252270103Source.GlobalSource (2458536571373 / 2500000000000 : ℝ) (4529251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count123
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s122
  have s124 : QRH.Record1252270103Source.GlobalSource (1229209196203 / 1250000000000 : ℝ) (4528001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count124
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s123
  have s125 : QRH.Record1252270103Source.GlobalSource (1966640063087 / 2000000000000 : ℝ) (4526751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count125
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s124
  have s126 : QRH.Record1252270103Source.GlobalSource (4916363261509 / 5000000000000 : ℝ) (4525501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count126
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s125
  have s127 : QRH.Record1252270103Source.GlobalSource (9832252192467 / 10000000000000 : ℝ) (4524251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count127
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s126
  have s128 : QRH.Record1252270103Source.GlobalSource (9831777323873 / 10000000000000 : ℝ) (4523001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count128
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s127
  have s129 : QRH.Record1252270103Source.GlobalSource (9831301917333 / 10000000000000 : ℝ) (4521751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count129
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s128
  have s130 : QRH.Record1252270103Source.GlobalSource (9830825972943 / 10000000000000 : ℝ) (4520501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count130
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s129
  have s131 : QRH.Record1252270103Source.GlobalSource (9830349490801 / 10000000000000 : ℝ) (4519251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count131
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s130
  have s132 : QRH.Record1252270103Source.GlobalSource (2457468117751 / 2500000000000 : ℝ) (4518001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count132
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s131
  have s133 : QRH.Record1252270103Source.GlobalSource (9829394913649 / 10000000000000 : ℝ) (4516751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count133
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s132
  have s134 : QRH.Record1252270103Source.GlobalSource (2457229204707 / 2500000000000 : ℝ) (4515501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count134
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s133
  have s135 : QRH.Record1252270103Source.GlobalSource (9828438186631 / 10000000000000 : ℝ) (4514251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count135
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s134
  have s136 : QRH.Record1252270103Source.GlobalSource (2456989754287 / 2500000000000 : ℝ) (4513001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count136
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s135
  have s137 : QRH.Record1252270103Source.GlobalSource (9827479310467 / 10000000000000 : ℝ) (4511751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count137
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s136
  have s138 : QRH.Record1252270103Source.GlobalSource (4913499533339 / 5000000000000 : ℝ) (4510501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count138
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s137
  have s139 : QRH.Record1252270103Source.GlobalSource (982651828587 / 1000000000000 : ℝ) (4509251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count139
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s138
  have s140 : QRH.Record1252270103Source.GlobalSource (9826036968137 / 10000000000000 : ℝ) (4508001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count140
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s139
  have s141 : QRH.Record1252270103Source.GlobalSource (4912777556787 / 5000000000000 : ℝ) (4506751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count141
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s140
  have s142 : QRH.Record1252270103Source.GlobalSource (4912536361137 / 5000000000000 : ℝ) (4505501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count142
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s141
  have s143 : QRH.Record1252270103Source.GlobalSource (982458979433 / 1000000000000 : ℝ) (4504251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count143
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s142
  have s144 : QRH.Record1252270103Source.GlobalSource (1228013291229 / 1250000000000 : ℝ) (4503001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count144
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s143
  have s145 : QRH.Record1252270103Source.GlobalSource (9823622328867 / 10000000000000 : ℝ) (4501751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count145
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s144
  have s146 : QRH.Record1252270103Source.GlobalSource (2455784447877 / 2500000000000 : ℝ) (4500501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count146
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s145
  have s147 : QRH.Record1252270103Source.GlobalSource (1964530543571 / 2000000000000 : ℝ) (4499251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count147
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s146
  have s148 : QRH.Record1252270103Source.GlobalSource (1964433421599 / 2000000000000 : ℝ) (4498001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count148
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s147
  have s149 : QRH.Record1252270103Source.GlobalSource (1964336192403 / 2000000000000 : ℝ) (4496751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count149
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s148
  have s150 : QRH.Record1252270103Source.GlobalSource (4910597140001 / 5000000000000 : ℝ) (4495501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count150
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s149
  have s151 : QRH.Record1252270103Source.GlobalSource (4910353531023 / 5000000000000 : ℝ) (4494251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count151
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s150
  have s152 : QRH.Record1252270103Source.GlobalSource (4910109654117 / 5000000000000 : ℝ) (4493001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count152
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s151
  have s153 : QRH.Record1252270103Source.GlobalSource (9819731018653 / 10000000000000 : ℝ) (4491751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count153
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s152
  have s154 : QRH.Record1252270103Source.GlobalSource (9819242193393 / 10000000000000 : ℝ) (4490501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count154
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s153
  have s155 : QRH.Record1252270103Source.GlobalSource (9818752832541 / 10000000000000 : ℝ) (4489251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count155
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s154
  have s156 : QRH.Record1252270103Source.GlobalSource (9818262936179 / 10000000000000 : ℝ) (4488001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count156
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s155
  have s157 : QRH.Record1252270103Source.GlobalSource (2454443126097 / 2500000000000 : ℝ) (4486751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count157
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s156
  have s158 : QRH.Record1252270103Source.GlobalSource (39269126149 / 40000000000 : ℝ) (4485501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count158
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s157
  have s159 : QRH.Record1252270103Source.GlobalSource (306774688589 / 312500000000 : ℝ) (4484251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count159
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s158
  have s160 : QRH.Record1252270103Source.GlobalSource (9816297997269 / 10000000000000 : ℝ) (4483001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count160
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s159
  have s161 : QRH.Record1252270103Source.GlobalSource (4907902712301 / 5000000000000 : ℝ) (4481751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count161
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s160
  have s162 : QRH.Record1252270103Source.GlobalSource (9815312316933 / 10000000000000 : ℝ) (4480501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count162
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s161
  have s163 : QRH.Record1252270103Source.GlobalSource (9814818674347 / 10000000000000 : ℝ) (4479251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count163
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s162
  have s164 : QRH.Record1252270103Source.GlobalSource (2453581124231 / 2500000000000 : ℝ) (4478001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count164
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s163
  have s165 : QRH.Record1252270103Source.GlobalSource (4906914892371 / 5000000000000 : ℝ) (4476751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count165
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s164
  have s166 : QRH.Record1252270103Source.GlobalSource (245333363447 / 250000000000 : ℝ) (4475501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count166
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s165
  have s167 : QRH.Record1252270103Source.GlobalSource (1962567751283 / 2000000000000 : ℝ) (4474251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count167
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s166
  have s168 : QRH.Record1252270103Source.GlobalSource (2453085610107 / 2500000000000 : ℝ) (4473001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count168
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s167
  have s169 : QRH.Record1252270103Source.GlobalSource (1962369118001 / 2000000000000 : ℝ) (4471751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count169
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s168
  have s170 : QRH.Record1252270103Source.GlobalSource (981134820523 / 1000000000000 : ℝ) (4470501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count170
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s169
  have s171 : QRH.Record1252270103Source.GlobalSource (9810850286187 / 10000000000000 : ℝ) (4469251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count171
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s170
  have s172 : QRH.Record1252270103Source.GlobalSource (9810351832959 / 10000000000000 : ℝ) (4468001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count172
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s171
  have s173 : QRH.Record1252270103Source.GlobalSource (4904926422811 / 5000000000000 : ℝ) (4466751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count173
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s172
  have s174 : QRH.Record1252270103Source.GlobalSource (9809353324251 / 10000000000000 : ℝ) (4465501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count174
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s173
  have s175 : QRH.Record1252270103Source.GlobalSource (613053329307 / 625000000000 : ℝ) (4464251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count175
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s174
  have s176 : QRH.Record1252270103Source.GlobalSource (4904176339847 / 5000000000000 : ℝ) (4463001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count176
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s175
  have s177 : QRH.Record1252270103Source.GlobalSource (392314062267 / 400000000000 : ℝ) (4461751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count177
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s176
  have s178 : QRH.Record1252270103Source.GlobalSource (9807349899933 / 10000000000000 : ℝ) (4460501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count178
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s177
  have s179 : QRH.Record1252270103Source.GlobalSource (9806847709549 / 10000000000000 : ℝ) (4459251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count179
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s178
  have s180 : QRH.Record1252270103Source.GlobalSource (4903172492801 / 5000000000000 : ℝ) (4458001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count180
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s179
  have s181 : QRH.Record1252270103Source.GlobalSource (9805841728177 / 10000000000000 : ℝ) (4456751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count181
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s180
  have s182 : QRH.Record1252270103Source.GlobalSource (4902668968671 / 5000000000000 : ℝ) (4455501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count182
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s181
  have s183 : QRH.Record1252270103Source.GlobalSource (9804833613169 / 10000000000000 : ℝ) (4454251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count183
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s182
  have s184 : QRH.Record1252270103Source.GlobalSource (9804328755729 / 10000000000000 : ℝ) (4453001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count184
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s183
  have s185 : QRH.Record1252270103Source.GlobalSource (1960764673019 / 2000000000000 : ℝ) (4451751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count185
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s184
  have s186 : QRH.Record1252270103Source.GlobalSource (4901658720673 / 5000000000000 : ℝ) (4450501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count186
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s185
  have s187 : QRH.Record1252270103Source.GlobalSource (9802810984561 / 10000000000000 : ℝ) (4449251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count187
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s186
  have s188 : QRH.Record1252270103Source.GlobalSource (9802303994819 / 10000000000000 : ℝ) (4448001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count188
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s187
  have s189 : QRH.Record1252270103Source.GlobalSource (4900898236099 / 5000000000000 : ℝ) (4446751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count189
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s188
  have s190 : QRH.Record1252270103Source.GlobalSource (19143141439 / 19531250000 : ℝ) (4445501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count190
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s189
  have s191 : QRH.Record1252270103Source.GlobalSource (4900389914299 / 5000000000000 : ℝ) (4444251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count191
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s190
  have s192 : QRH.Record1252270103Source.GlobalSource (2450067676939 / 2500000000000 : ℝ) (4443001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count192
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s191
  have s193 : QRH.Record1252270103Source.GlobalSource (9799761054311 / 10000000000000 : ℝ) (4441751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count193
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s192
  have s194 : QRH.Record1252270103Source.GlobalSource (4899625434169 / 5000000000000 : ℝ) (4440501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count194
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s193
  have s195 : QRH.Record1252270103Source.GlobalSource (4899370074957 / 5000000000000 : ℝ) (4439251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count195
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s194
  have s196 : QRH.Record1252270103Source.GlobalSource (2449557224779 / 2500000000000 : ℝ) (4438001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count196
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s195
  have s197 : QRH.Record1252270103Source.GlobalSource (489885855801 / 500000000000 : ℝ) (4436751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count197
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s196
  have s198 : QRH.Record1252270103Source.GlobalSource (9797204800693 / 10000000000000 : ℝ) (4435501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count198
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s197
  have s199 : QRH.Record1252270103Source.GlobalSource (24491729883 / 25000000000 : ℝ) (4434251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count199
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s198
  have s200 : QRH.Record1252270103Source.GlobalSource (9796178573607 / 10000000000000 : ℝ) (4433001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count200
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s199
  have s201 : QRH.Record1252270103Source.GlobalSource (489783233099 / 500000000000 : ℝ) (4431751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count201
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s200
  have s202 : QRH.Record1252270103Source.GlobalSource (1224393777299 / 1250000000000 : ℝ) (4430501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count202
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s201
  have s203 : QRH.Record1252270103Source.GlobalSource (4897317621459 / 5000000000000 : ℝ) (4429251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count203
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s202
  have s204 : QRH.Record1252270103Source.GlobalSource (9794119735627 / 10000000000000 : ℝ) (4428001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count204
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s203
  have s205 : QRH.Record1252270103Source.GlobalSource (4896801848293 / 5000000000000 : ℝ) (4426751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count205
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s204
  have s206 : QRH.Record1252270103Source.GlobalSource (4896543562933 / 5000000000000 : ℝ) (4425501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count206
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s205
  have s207 : QRH.Record1252270103Source.GlobalSource (9792570023539 / 10000000000000 : ℝ) (4424251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count207
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s206
  have s208 : QRH.Record1252270103Source.GlobalSource (9792052389667 / 10000000000000 : ℝ) (4423001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count208
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s207
  have s209 : QRH.Record1252270103Source.GlobalSource (9791534224313 / 10000000000000 : ℝ) (4421751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count209
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s208
  have s210 : QRH.Record1252270103Source.GlobalSource (1958203105509 / 2000000000000 : ℝ) (4420501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count210
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s209
  have s211 : QRH.Record1252270103Source.GlobalSource (9790496299437 / 10000000000000 : ℝ) (4419251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count211
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s210
  have s212 : QRH.Record1252270103Source.GlobalSource (489498827003 / 500000000000 : ℝ) (4418001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count212
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s211
  have s213 : QRH.Record1252270103Source.GlobalSource (9789456249477 / 10000000000000 : ℝ) (4416751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count213
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s212
  have s214 : QRH.Record1252270103Source.GlobalSource (9788935427749 / 10000000000000 : ℝ) (4415501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count214
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s213
  have s215 : QRH.Record1252270103Source.GlobalSource (1957682814987 / 2000000000000 : ℝ) (4414251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count215
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s214
  have s216 : QRH.Record1252270103Source.GlobalSource (1957578438219 / 2000000000000 : ℝ) (4413001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count216
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s215
  have s217 : QRH.Record1252270103Source.GlobalSource (9787369776299 / 10000000000000 : ℝ) (4411751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count217
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s216
  have s218 : QRH.Record1252270103Source.GlobalSource (9786846830617 / 10000000000000 : ℝ) (4410501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count218
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s217
  have s219 : QRH.Record1252270103Source.GlobalSource (244658083853 / 250000000000 : ℝ) (4409251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count219
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s218
  have s220 : QRH.Record1252270103Source.GlobalSource (9785799346871 / 10000000000000 : ℝ) (4408001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count220
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s219
  have s221 : QRH.Record1252270103Source.GlobalSource (9785274808927 / 10000000000000 : ℝ) (4406751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count221
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s220
  have s222 : QRH.Record1252270103Source.GlobalSource (1956949948069 / 2000000000000 : ℝ) (4405501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count222
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s221
  have s223 : QRH.Record1252270103Source.GlobalSource (4892112070591 / 5000000000000 : ℝ) (4404251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count223
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s222
  have s224 : QRH.Record1252270103Source.GlobalSource (1956739602301 / 2000000000000 : ℝ) (4403001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count224
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s223
  have s225 : QRH.Record1252270103Source.GlobalSource (9783171351383 / 10000000000000 : ℝ) (4401751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count225
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s224
  have s226 : QRH.Record1252270103Source.GlobalSource (9782644160879 / 10000000000000 : ℝ) (4400501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count226
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s225
  have s227 : QRH.Record1252270103Source.GlobalSource (9782116440053 / 10000000000000 : ℝ) (4399251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count227
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s226
  have s228 : QRH.Record1252270103Source.GlobalSource (2445397047241 / 2500000000000 : ℝ) (4398001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count228
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s227
  have s229 : QRH.Record1252270103Source.GlobalSource (978105940767 / 1000000000000 : ℝ) (4396751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count229
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s228
  have s230 : QRH.Record1252270103Source.GlobalSource (9780530096231 / 10000000000000 : ℝ) (4395501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count230
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s229
  have s231 : QRH.Record1252270103Source.GlobalSource (4890000127353 / 5000000000000 : ℝ) (4394251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count231
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s230
  have s232 : QRH.Record1252270103Source.GlobalSource (9779469883161 / 10000000000000 : ℝ) (4393001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count232
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s231
  have s233 : QRH.Record1252270103Source.GlobalSource (1222367372707 / 1250000000000 : ℝ) (4391751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count233
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s232
  have s234 : QRH.Record1252270103Source.GlobalSource (9778407550247 / 10000000000000 : ℝ) (4390501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count234
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s233
  have s235 : QRH.Record1252270103Source.GlobalSource (9777875588991 / 10000000000000 : ℝ) (4389251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count235
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s234
  have s236 : QRH.Record1252270103Source.GlobalSource (1955468619589 / 2000000000000 : ℝ) (4388001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count236
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s235
  have s237 : QRH.Record1252270103Source.GlobalSource (2444202519291 / 2500000000000 : ℝ) (4386751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count237
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s236
  have s238 : QRH.Record1252270103Source.GlobalSource (9776276526711 / 10000000000000 : ℝ) (4385501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count238
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s237
  have s239 : QRH.Record1252270103Source.GlobalSource (9775742446643 / 10000000000000 : ℝ) (4384251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count239
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s238
  have s240 : QRH.Record1252270103Source.GlobalSource (1955041567403 / 2000000000000 : ℝ) (4383001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count240
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s239
  have s241 : QRH.Record1252270103Source.GlobalSource (9774672697887 / 10000000000000 : ℝ) (4381751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count241
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s240
  have s242 : QRH.Record1252270103Source.GlobalSource (4887068514657 / 5000000000000 : ℝ) (4380501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count242
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s241
  have s243 : QRH.Record1252270103Source.GlobalSource (9773600831349 / 10000000000000 : ℝ) (4379251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count243
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s242
  have s244 : QRH.Record1252270103Source.GlobalSource (9773064104049 / 10000000000000 : ℝ) (4378001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count244
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s243
  have s245 : QRH.Record1252270103Source.GlobalSource (4886263423737 / 5000000000000 : ℝ) (4376751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count245
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s244
  have s246 : QRH.Record1252270103Source.GlobalSource (4885994530839 / 5000000000000 : ℝ) (4375501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count246
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s245
  have s247 : QRH.Record1252270103Source.GlobalSource (1221431343339 / 1250000000000 : ℝ) (4374251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count247
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s246
  have s248 : QRH.Record1252270103Source.GlobalSource (9770911902629 / 10000000000000 : ℝ) (4373001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count248
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s247
  have s249 : QRH.Record1252270103Source.GlobalSource (9770372529481 / 10000000000000 : ℝ) (4371751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count249
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s248
  have s250 : QRH.Record1252270103Source.GlobalSource (9769832627323 / 10000000000000 : ℝ) (4370501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count250
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s249
  have s251 : QRH.Record1252270103Source.GlobalSource (1953858439243 / 2000000000000 : ℝ) (4369251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count251
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s250
  have s252 : QRH.Record1252270103Source.GlobalSource (9768751236207 / 10000000000000 : ℝ) (4368001 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count252
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s251
  have s253 : QRH.Record1252270103Source.GlobalSource (195364194947 / 200000000000 : ℝ) (4366751 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count253
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s252
  have s254 : QRH.Record1252270103Source.GlobalSource (4883833864847 / 5000000000000 : ℝ) (4365501 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count254
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s253
  have s255 : QRH.Record1252270103Source.GlobalSource (9767125183289 / 10000000000000 : ℝ) (4364251 / 2000000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Count255
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s254
  exact s255
end
end QRH.DensityTen
