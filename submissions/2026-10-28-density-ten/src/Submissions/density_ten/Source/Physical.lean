/- Exact source chain with LOW reserve 1/1000000.
Builds on OpenAI, Hailey Collet, Sil, ArviFoxy, Jacob Sussman and Rohan Arun.
Apache-2.0; substantially AI-assisted by OpenAI Codex.
Analytic conclusions remain conditional on the preprint's 7/8 theorem. -/
import Submissions.density_ten.Source.Step
import Submissions.density_split_fine_chain.Source.ChainK15
import Submissions.density_ten.Source.Physical001
import Submissions.density_ten.Source.Physical002
import Submissions.density_ten.Source.Physical003
import Submissions.density_ten.Source.Physical004
import Submissions.density_ten.Source.Physical005
import Submissions.density_ten.Source.Physical006
import Submissions.density_ten.Source.Physical007
import Submissions.density_ten.Source.Physical008
import Submissions.density_ten.Source.Physical009
import Submissions.density_ten.Source.Physical010
import Submissions.density_ten.Source.Physical011
import Submissions.density_ten.Source.Physical012
import Submissions.density_ten.Source.Physical013
import Submissions.density_ten.Source.Physical014
import Submissions.density_ten.Source.Physical015
import Submissions.density_ten.Source.Physical016
import Submissions.density_ten.Source.Physical017
import Submissions.density_ten.Source.Physical018
import Submissions.density_ten.Source.Physical019
import Submissions.density_ten.Source.Physical020
import Submissions.density_ten.Source.Physical021
import Submissions.density_ten.Source.Physical022
import Submissions.density_ten.Source.Physical023
import Submissions.density_ten.Source.Physical024
import Submissions.density_ten.Source.Physical025
import Submissions.density_ten.Source.Physical026
import Submissions.density_ten.Source.Physical027
import Submissions.density_ten.Source.Physical028
import Submissions.density_ten.Source.Physical029
import Submissions.density_ten.Source.Physical030
import Submissions.density_ten.Source.Physical031
import Submissions.density_ten.Source.Physical032
import Submissions.density_ten.Source.Physical033
import Submissions.density_ten.Source.Physical034
import Submissions.density_ten.Source.Physical035
import Submissions.density_ten.Source.Physical036
import Submissions.density_ten.Source.Physical037
import Submissions.density_ten.Source.Physical038
import Submissions.density_ten.Source.Physical039
import Submissions.density_ten.Source.Physical040
import Submissions.density_ten.Source.Physical041
import Submissions.density_ten.Source.Physical042
import Submissions.density_ten.Source.Physical043
import Submissions.density_ten.Source.Physical044
import Submissions.density_ten.Source.Physical045
import Submissions.density_ten.Source.Physical046
import Submissions.density_ten.Source.Physical047
import Submissions.density_ten.Source.Physical048
import Submissions.density_ten.Source.Physical049
import Submissions.density_ten.Source.Physical050
import Submissions.density_ten.Source.Physical051
import Submissions.density_ten.Source.Physical052
import Submissions.density_ten.Source.Physical053
import Submissions.density_ten.Source.Physical054
import Submissions.density_ten.Source.Physical055
import Submissions.density_ten.Source.Physical056
import Submissions.density_ten.Source.Physical057
import Submissions.density_ten.Source.Physical058
import Submissions.density_ten.Source.Physical059
import Submissions.density_ten.Source.Physical060
import Submissions.density_ten.Source.Physical061
import Submissions.density_ten.Source.Physical062
import Submissions.density_ten.Source.Physical063
import Submissions.density_ten.Source.Physical064
import Submissions.density_ten.Source.Physical065
import Submissions.density_ten.Source.Physical066
import Submissions.density_ten.Source.Physical067
import Submissions.density_ten.Source.Physical068
import Submissions.density_ten.Source.Physical069
import Submissions.density_ten.Source.Physical070
import Submissions.density_ten.Source.Physical071
import Submissions.density_ten.Source.Physical072
import Submissions.density_ten.Source.Physical073
import Submissions.density_ten.Source.Physical074
import Submissions.density_ten.Source.Physical075
import Submissions.density_ten.Source.Physical076
import Submissions.density_ten.Source.Physical077
import Submissions.density_ten.Source.Physical078
import Submissions.density_ten.Source.Physical079
import Submissions.density_ten.Source.Physical080
import Submissions.density_ten.Source.Physical081
import Submissions.density_ten.Source.Physical082
import Submissions.density_ten.Source.Physical083
import Submissions.density_ten.Source.Physical084
import Submissions.density_ten.Source.Physical085
import Submissions.density_ten.Source.Physical086
import Submissions.density_ten.Source.Physical087
import Submissions.density_ten.Source.Physical088
import Submissions.density_ten.Source.Physical089
import Submissions.density_ten.Source.Physical090
import Submissions.density_ten.Source.Physical091
import Submissions.density_ten.Source.Physical092
import Submissions.density_ten.Source.Physical093
import Submissions.density_ten.Source.Physical094
import Submissions.density_ten.Source.Physical095
import Submissions.density_ten.Source.Physical096
import Submissions.density_ten.Source.Physical097
import Submissions.density_ten.Source.Physical098
import Submissions.density_ten.Source.Physical099
import Submissions.density_ten.Source.Physical100
import Submissions.density_ten.Source.Physical101
import Submissions.density_ten.Source.Physical102
import Submissions.density_ten.Source.Physical103
import Submissions.density_ten.Source.Physical104
import Submissions.density_ten.Source.Physical105
import Submissions.density_ten.Source.Physical106
import Submissions.density_ten.Source.Physical107
import Submissions.density_ten.Source.Physical108
import Submissions.density_ten.Source.Physical109
import Submissions.density_ten.Source.Physical110
import Submissions.density_ten.Source.Physical111
import Submissions.density_ten.Source.Physical112
import Submissions.density_ten.Source.Physical113
import Submissions.density_ten.Source.Physical114
import Submissions.density_ten.Source.Physical115
import Submissions.density_ten.Source.Physical116
import Submissions.density_ten.Source.Physical117
import Submissions.density_ten.Source.Physical118
import Submissions.density_ten.Source.Physical119
import Submissions.density_ten.Source.Physical120
import Submissions.density_ten.Source.Physical121
import Submissions.density_ten.Source.Physical122
import Submissions.density_ten.Source.Physical123
import Submissions.density_ten.Source.Physical124
import Submissions.density_ten.Source.Physical125
import Submissions.density_ten.Source.Physical126
import Submissions.density_ten.Source.Physical127
import Submissions.density_ten.Source.Physical128
import Submissions.density_ten.Source.Physical129
import Submissions.density_ten.Source.Physical130
import Submissions.density_ten.Source.Physical131
import Submissions.density_ten.Source.Physical132
import Submissions.density_ten.Source.Physical133
import Submissions.density_ten.Source.Physical134
import Submissions.density_ten.Source.Physical135
import Submissions.density_ten.Source.Physical136
import Submissions.density_ten.Source.Physical137
import Submissions.density_ten.Source.Physical138
import Submissions.density_ten.Source.Physical139
import Submissions.density_ten.Source.Physical140
import Submissions.density_ten.Source.Physical141
import Submissions.density_ten.Source.Physical142
import Submissions.density_ten.Source.Physical143
import Submissions.density_ten.Source.Physical144
import Submissions.density_ten.Source.Physical145
import Submissions.density_ten.Source.Physical146
import Submissions.density_ten.Source.Physical147
import Submissions.density_ten.Source.Physical148
import Submissions.density_ten.Source.Physical149
import Submissions.density_ten.Source.Physical150
import Submissions.density_ten.Source.Physical151
import Submissions.density_ten.Source.Physical152
import Submissions.density_ten.Source.Physical153
import Submissions.density_ten.Source.Physical154
import Submissions.density_ten.Source.Physical155
import Submissions.density_ten.Source.Physical156
import Submissions.density_ten.Source.Physical157
import Submissions.density_ten.Source.Physical158
import Submissions.density_ten.Source.Physical159
import Submissions.density_ten.Source.Physical160
import Submissions.density_ten.Source.Physical161
import Submissions.density_ten.Source.Physical162
import Submissions.density_ten.Source.Physical163
import Submissions.density_ten.Source.Physical164
import Submissions.density_ten.Source.Physical165
import Submissions.density_ten.Source.Physical166
import Submissions.density_ten.Source.Physical167
import Submissions.density_ten.Source.Physical168
import Submissions.density_ten.Source.Physical169
import Submissions.density_ten.Source.Physical170
import Submissions.density_ten.Source.Physical171
import Submissions.density_ten.Source.Physical172
import Submissions.density_ten.Source.Physical173
import Submissions.density_ten.Source.Physical174
import Submissions.density_ten.Source.Physical175
import Submissions.density_ten.Source.Physical176
import Submissions.density_ten.Source.Physical177
import Submissions.density_ten.Source.Physical178
import Submissions.density_ten.Source.Physical179
import Submissions.density_ten.Source.Physical180
import Submissions.density_ten.Source.Physical181
import Submissions.density_ten.Source.Physical182
import Submissions.density_ten.Source.Physical183
import Submissions.density_ten.Source.Physical184
import Submissions.density_ten.Source.Physical185
import Submissions.density_ten.Source.Physical186
import Submissions.density_ten.Source.Physical187
import Submissions.density_ten.Source.Physical188
import Submissions.density_ten.Source.Physical189
import Submissions.density_ten.Source.Physical190
import Submissions.density_ten.Source.Physical191
import Submissions.density_ten.Source.Physical192
import Submissions.density_ten.Source.Physical193
import Submissions.density_ten.Source.Physical194
import Submissions.density_ten.Source.Physical195
import Submissions.density_ten.Source.Physical196
import Submissions.density_ten.Source.Physical197
import Submissions.density_ten.Source.Physical198
import Submissions.density_ten.Source.Physical199
import Submissions.density_ten.Source.Physical200
import Submissions.density_ten.Source.Physical201
import Submissions.density_ten.Source.Physical202
import Submissions.density_ten.Source.Physical203
import Submissions.density_ten.Source.Physical204
import Submissions.density_ten.Source.Physical205
import Submissions.density_ten.Source.Physical206
import Submissions.density_ten.Source.Physical207
import Submissions.density_ten.Source.Physical208
import Submissions.density_ten.Source.Physical209
import Submissions.density_ten.Source.Physical210
import Submissions.density_ten.Source.Physical211
import Submissions.density_ten.Source.Physical212
import Submissions.density_ten.Source.Physical213
import Submissions.density_ten.Source.Physical214
import Submissions.density_ten.Source.Physical215
import Submissions.density_ten.Source.Physical216
import Submissions.density_ten.Source.Physical217
import Submissions.density_ten.Source.Physical218
import Submissions.density_ten.Source.Physical219
import Submissions.density_ten.Source.Physical220
import Submissions.density_ten.Source.Physical221
import Submissions.density_ten.Source.Physical222
import Submissions.density_ten.Source.Physical223
import Submissions.density_ten.Source.Physical224
import Submissions.density_ten.Source.Physical225
import Submissions.density_ten.Source.Physical226
import Submissions.density_ten.Source.Physical227
import Submissions.density_ten.Source.Physical228
import Submissions.density_ten.Source.Physical229
import Submissions.density_ten.Source.Physical230
import Submissions.density_ten.Source.Physical231
import Submissions.density_ten.Source.Physical232
import Submissions.density_ten.Source.Physical233
import Submissions.density_ten.Source.Physical234
import Submissions.density_ten.Source.Physical235
import Submissions.density_ten.Source.Physical236
import Submissions.density_ten.Source.Physical237
import Submissions.density_ten.Source.Physical238
import Submissions.density_ten.Source.Physical239
import Submissions.density_ten.Source.Physical240
import Submissions.density_ten.Source.Physical241
import Submissions.density_ten.Source.Physical242
import Submissions.density_ten.Source.Physical243
import Submissions.density_ten.Source.Physical244
import Submissions.density_ten.Source.Physical245
import Submissions.density_ten.Source.Physical246
import Submissions.density_ten.Source.Physical247
import Submissions.density_ten.Source.Physical248
import Submissions.density_ten.Source.Physical249
import Submissions.density_ten.Source.Physical250
import Submissions.density_ten.Source.Physical251
import Submissions.density_ten.Source.Physical252
import Submissions.density_ten.Source.Physical253
import Submissions.density_ten.Source.Physical254
import Submissions.density_ten.Source.Physical255
import Submissions.density_ten.Source.Physical256
import Submissions.density_ten.Source.Physical257
import Submissions.density_ten.Source.Physical258
import Submissions.density_ten.Source.Physical259
import Submissions.density_ten.Source.Physical260
import Submissions.density_ten.Source.Physical261
import Submissions.density_ten.Source.Physical262
import Submissions.density_ten.Source.Physical263
import Submissions.density_ten.Source.Physical264
import Submissions.density_ten.Source.Physical265
import Submissions.density_ten.Source.Physical266
import Submissions.density_ten.Source.Physical267
import Submissions.density_ten.Source.Physical268
import Submissions.density_ten.Source.Physical269
import Submissions.density_ten.Source.Physical270
import Submissions.density_ten.Source.Physical271
import Submissions.density_ten.Source.Physical272
import Submissions.density_ten.Source.Physical273
import Submissions.density_ten.Source.Physical274
import Submissions.density_ten.Source.Physical275
import Submissions.density_ten.Source.Physical276
import Submissions.density_ten.Source.Physical277
import Submissions.density_ten.Source.Physical278
import Submissions.density_ten.Source.Physical279
import Submissions.density_ten.Source.Physical280
import Submissions.density_ten.Source.Physical281
import Submissions.density_ten.Source.Physical282
import Submissions.density_ten.Source.Physical283
import Submissions.density_ten.Source.Physical284
import Submissions.density_ten.Source.Physical285
import Submissions.density_ten.Source.Physical286
import Submissions.density_ten.Source.Physical287
import Submissions.density_ten.Source.Physical288
import Submissions.density_ten.Source.Physical289
import Submissions.density_ten.Source.Physical290
import Submissions.density_ten.Source.Physical291
import Submissions.density_ten.Source.Physical292
import Submissions.density_ten.Source.Physical293
import Submissions.density_ten.Source.Physical294
import Submissions.density_ten.Source.Physical295
import Submissions.density_ten.Source.Physical296
import Submissions.density_ten.Source.Physical297
import Submissions.density_ten.Source.Physical298
import Submissions.density_ten.Source.Physical299
import Submissions.density_ten.Source.Physical300
import Submissions.density_ten.Source.Physical301
import Submissions.density_ten.Source.Physical302
import Submissions.density_ten.Source.Physical303
import Submissions.density_ten.Source.Physical304
import Submissions.density_ten.Source.Physical305
import Submissions.density_ten.Source.Physical306
import Submissions.density_ten.Source.Physical307
import Submissions.density_ten.Source.Physical308
import Submissions.density_ten.Source.Physical309
import Submissions.density_ten.Source.Physical310
import Submissions.density_ten.Source.Physical311
import Submissions.density_ten.Source.Physical312
import Submissions.density_ten.Source.Physical313
import Submissions.density_ten.Source.Physical314
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QRH.DensityTen
noncomputable section
open QRH.SilDensitySplit QRH.SilDensitySplit.K15

theorem physical_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (396418568023 / 400000000000 : ℝ) (9501 / 4000 : ℝ) (1 / 10 : ℝ) := by
  have s000 : QRH.Record1252270103Source.GlobalSource (99999 / 100000 : ℝ) (5143 / 2000 : ℝ) (1397 / 10000 : ℝ) := by
    simpa only [Face.Source, bootFace] using boot_source hβ
  have s001 : QRH.Record1252270103Source.GlobalSource (2499927530909 / 2500000000000 : ℝ) (20567 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical001
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s000
  have s002 : QRH.Record1252270103Source.GlobalSource (9999519611201 / 10000000000000 : ℝ) (10281 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical002
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s001
  have s003 : QRH.Record1252270103Source.GlobalSource (399973138521 / 400000000000 : ℝ) (20557 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical003
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s002
  have s004 : QRH.Record1252270103Source.GlobalSource (4999568339719 / 5000000000000 : ℝ) (2569 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical004
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s003
  have s005 : QRH.Record1252270103Source.GlobalSource (9998944260769 / 10000000000000 : ℝ) (20547 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical005
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s004
  have s006 : QRH.Record1252270103Source.GlobalSource (9998751207347 / 10000000000000 : ℝ) (10271 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical006
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s005
  have s007 : QRH.Record1252270103Source.GlobalSource (9998557519499 / 10000000000000 : ℝ) (20537 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical007
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s006
  have s008 : QRH.Record1252270103Source.GlobalSource (624897699847 / 625000000000 : ℝ) (5133 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical008
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s007
  have s009 : QRH.Record1252270103Source.GlobalSource (1249771030229 / 1250000000000 : ℝ) (20527 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical009
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s008
  have s010 : QRH.Record1252270103Source.GlobalSource (1999594530533 / 2000000000000 : ℝ) (10261 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical010
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s009
  have s011 : QRH.Record1252270103Source.GlobalSource (1249722053797 / 1250000000000 : ℝ) (20517 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical011
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s010
  have s012 : QRH.Record1252270103Source.GlobalSource (9997579575289 / 10000000000000 : ℝ) (641 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical012
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s011
  have s013 : QRH.Record1252270103Source.GlobalSource (624836380483 / 625000000000 : ℝ) (20507 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical013
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s012
  have s014 : QRH.Record1252270103Source.GlobalSource (4998591984007 / 5000000000000 : ℝ) (10251 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical014
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s013
  have s015 : QRH.Record1252270103Source.GlobalSource (999698521647 / 1000000000000 : ℝ) (20497 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical015
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s014
  have s016 : QRH.Record1252270103Source.GlobalSource (9996785833417 / 10000000000000 : ℝ) (5123 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical016
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s015
  have s017 : QRH.Record1252270103Source.GlobalSource (399863432767 / 400000000000 : ℝ) (20487 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical017
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s016
  have s018 : QRH.Record1252270103Source.GlobalSource (624774073379 / 625000000000 : ℝ) (10241 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical018
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s017
  have s019 : QRH.Record1252270103Source.GlobalSource (9996183898403 / 10000000000000 : ℝ) (20477 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical019
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s018
  have s020 : QRH.Record1252270103Source.GlobalSource (9995981992511 / 10000000000000 : ℝ) (2559 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical020
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s019
  have s021 : QRH.Record1252270103Source.GlobalSource (4997889728353 / 5000000000000 : ℝ) (20467 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical021
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s020
  have s022 : QRH.Record1252270103Source.GlobalSource (4997788145649 / 5000000000000 : ℝ) (10231 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical022
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s021
  have s023 : QRH.Record1252270103Source.GlobalSource (999537249661 / 1000000000000 : ℝ) (20457 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical023
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s022
  have s024 : QRH.Record1252270103Source.GlobalSource (4997584036479 / 5000000000000 : ℝ) (5113 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical024
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s023
  have s025 : QRH.Record1252270103Source.GlobalSource (9994963020657 / 10000000000000 : ℝ) (20447 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical025
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s024
  have s026 : QRH.Record1252270103Source.GlobalSource (4997378670011 / 5000000000000 : ℝ) (10221 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical026
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s025
  have s027 : QRH.Record1252270103Source.GlobalSource (4997275515683 / 5000000000000 : ℝ) (20437 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical027
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s026
  have s028 : QRH.Record1252270103Source.GlobalSource (9994344095003 / 10000000000000 : ℝ) (1277 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical028
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s027
  have s029 : QRH.Record1252270103Source.GlobalSource (9994136531251 / 10000000000000 : ℝ) (20427 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical029
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s028
  have s030 : QRH.Record1252270103Source.GlobalSource (156155130319 / 156250000000 : ℝ) (10211 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical030
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s029
  have s031 : QRH.Record1252270103Source.GlobalSource (1998743904561 / 2000000000000 : ℝ) (20417 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical031
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s030
  have s032 : QRH.Record1252270103Source.GlobalSource (4996755039367 / 5000000000000 : ℝ) (5103 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical032
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s031
  have s033 : QRH.Record1252270103Source.GlobalSource (156145312633 / 156250000000 : ℝ) (20407 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical033
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s032
  have s034 : QRH.Record1252270103Source.GlobalSource (9993089312449 / 10000000000000 : ℝ) (10201 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical034
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s033
  have s035 : QRH.Record1252270103Source.GlobalSource (4996438995427 / 5000000000000 : ℝ) (20397 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical035
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s034
  have s036 : QRH.Record1252270103Source.GlobalSource (4996333022017 / 5000000000000 : ℝ) (2549 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical036
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s035
  have s037 : QRH.Record1252270103Source.GlobalSource (9992453472297 / 10000000000000 : ℝ) (20387 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical037
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s036
  have s038 : QRH.Record1252270103Source.GlobalSource (199844805519 / 200000000000 : ℝ) (10191 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical038
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s037
  have s039 : QRH.Record1252270103Source.GlobalSource (99920264553 / 100000000000 : ℝ) (20377 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical039
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s038
  have s040 : QRH.Record1252270103Source.GlobalSource (2497953002663 / 2500000000000 : ℝ) (5093 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical040
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s039
  have s041 : QRH.Record1252270103Source.GlobalSource (1248949617789 / 1250000000000 : ℝ) (20367 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical041
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s040
  have s042 : QRH.Record1252270103Source.GlobalSource (1248922656323 / 1250000000000 : ℝ) (10181 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical042
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s041
  have s043 : QRH.Record1252270103Source.GlobalSource (2497791233943 / 2500000000000 : ℝ) (20357 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical043
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s042
  have s044 : QRH.Record1252270103Source.GlobalSource (499547399909 / 500000000000 : ℝ) (318 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical044
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s043
  have s045 : QRH.Record1252270103Source.GlobalSource (999073043811 / 1000000000000 : ℝ) (20347 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical045
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s044
  have s046 : QRH.Record1252270103Source.GlobalSource (1248814031983 / 1250000000000 : ℝ) (10171 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical046
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s045
  have s047 : QRH.Record1252270103Source.GlobalSource (9990293451743 / 10000000000000 : ℝ) (20337 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical047
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s046
  have s048 : QRH.Record1252270103Source.GlobalSource (156094906657 / 156250000000 : ℝ) (5083 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical048
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s047
  have s049 : QRH.Record1252270103Source.GlobalSource (9989853979081 / 10000000000000 : ℝ) (20327 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical049
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s048
  have s050 : QRH.Record1252270103Source.GlobalSource (9989633311139 / 10000000000000 : ℝ) (10161 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical050
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s049
  have s051 : QRH.Record1252270103Source.GlobalSource (9989412022521 / 10000000000000 : ℝ) (20317 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical051
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s050
  have s052 : QRH.Record1252270103Source.GlobalSource (2497297528381 / 2500000000000 : ℝ) (2539 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical052
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s051
  have s053 : QRH.Record1252270103Source.GlobalSource (1997793516889 / 2000000000000 : ℝ) (20307 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical053
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s052
  have s054 : QRH.Record1252270103Source.GlobalSource (9988744435581 / 10000000000000 : ℝ) (10151 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical054
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s053
  have s055 : QRH.Record1252270103Source.GlobalSource (2497130166807 / 2500000000000 : ℝ) (20297 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical055
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s054
  have s056 : QRH.Record1252270103Source.GlobalSource (9988296279681 / 10000000000000 : ℝ) (5073 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical056
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s055
  have s057 : QRH.Record1252270103Source.GlobalSource (1997614254647 / 2000000000000 : ℝ) (20287 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical057
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s056
  have s058 : QRH.Record1252270103Source.GlobalSource (1248480706023 / 1250000000000 : ℝ) (10141 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical058
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s057
  have s059 : QRH.Record1252270103Source.GlobalSource (9987619404821 / 10000000000000 : ℝ) (20277 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical059
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s058
  have s060 : QRH.Record1252270103Source.GlobalSource (9987392543439 / 10000000000000 : ℝ) (1267 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical060
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s059
  have s061 : QRH.Record1252270103Source.GlobalSource (9987165064331 / 10000000000000 : ℝ) (20267 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical061
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s060
  have s062 : QRH.Record1252270103Source.GlobalSource (9986936967787 / 10000000000000 : ℝ) (10131 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical062
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s061
  have s063 : QRH.Record1252270103Source.GlobalSource (9986708254093 / 10000000000000 : ℝ) (20257 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical063
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s062
  have s064 : QRH.Record1252270103Source.GlobalSource (4993239461773 / 5000000000000 : ℝ) (5063 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical064
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s063
  have s065 : QRH.Record1252270103Source.GlobalSource (1997249795287 / 2000000000000 : ℝ) (20247 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical065
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s064
  have s066 : QRH.Record1252270103Source.GlobalSource (199720368261 / 200000000000 : ℝ) (10121 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical066
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s065
  have s067 : QRH.Record1252270103Source.GlobalSource (9985787233679 / 10000000000000 : ℝ) (20237 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical067
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s066
  have s068 : QRH.Record1252270103Source.GlobalSource (998555543861 / 1000000000000 : ℝ) (2529 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical068
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s067
  have s069 : QRH.Record1252270103Source.GlobalSource (9985323028131 / 10000000000000 : ℝ) (20227 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical069
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s068
  have s070 : QRH.Record1252270103Source.GlobalSource (312034062579 / 312500000000 : ℝ) (10111 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical070
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s069
  have s071 : QRH.Record1252270103Source.GlobalSource (9984856362087 / 10000000000000 : ℝ) (20217 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical071
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s070
  have s072 : QRH.Record1252270103Source.GlobalSource (4992311053547 / 5000000000000 : ℝ) (5053 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical072
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s071
  have s073 : QRH.Record1252270103Source.GlobalSource (1996877447567 / 2000000000000 : ℝ) (20207 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical073
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s072
  have s074 : QRH.Record1252270103Source.GlobalSource (1996830350919 / 2000000000000 : ℝ) (10101 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical074
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s073
  have s075 : QRH.Record1252270103Source.GlobalSource (9983915657657 / 10000000000000 : ℝ) (20197 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical075
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s074
  have s076 : QRH.Record1252270103Source.GlobalSource (1996735789461 / 2000000000000 : ℝ) (631 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical076
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s075
  have s077 : QRH.Record1252270103Source.GlobalSource (9983441623823 / 10000000000000 : ℝ) (20187 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical077
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s076
  have s078 : QRH.Record1252270103Source.GlobalSource (9983203687493 / 10000000000000 : ℝ) (10091 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical078
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s077
  have s079 : QRH.Record1252270103Source.GlobalSource (2495741284649 / 2500000000000 : ℝ) (20177 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical079
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s078
  have s080 : QRH.Record1252270103Source.GlobalSource (4991362988707 / 5000000000000 : ℝ) (5043 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical080
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s079
  have s081 : QRH.Record1252270103Source.GlobalSource (399299448169 / 400000000000 : ℝ) (20167 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical081
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s080
  have s082 : QRH.Record1252270103Source.GlobalSource (998224581931 / 1000000000000 : ℝ) (10081 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical082
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s081
  have s083 : QRH.Record1252270103Source.GlobalSource (1247750602869 / 1250000000000 : ℝ) (20157 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical083
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s082
  have s084 : QRH.Record1252270103Source.GlobalSource (4990881607713 / 5000000000000 : ℝ) (2519 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical084
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s083
  have s085 : QRH.Record1252270103Source.GlobalSource (9981520997009 / 10000000000000 : ℝ) (20147 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical085
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s084
  have s086 : QRH.Record1252270103Source.GlobalSource (9981278167979 / 10000000000000 : ℝ) (10071 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical086
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s085
  have s087 : QRH.Record1252270103Source.GlobalSource (2495258682153 / 2500000000000 : ℝ) (20137 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical087
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s086
  have s088 : QRH.Record1252270103Source.GlobalSource (623799417449 / 625000000000 : ℝ) (5033 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical088
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s087
  have s089 : QRH.Record1252270103Source.GlobalSource (9980546019971 / 10000000000000 : ℝ) (20127 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical089
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s088
  have s090 : QRH.Record1252270103Source.GlobalSource (9980300751247 / 10000000000000 : ℝ) (10061 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical090
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s089
  have s091 : QRH.Record1252270103Source.GlobalSource (4990027436643 / 5000000000000 : ℝ) (20117 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical091
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s090
  have s092 : QRH.Record1252270103Source.GlobalSource (4989904193181 / 5000000000000 : ℝ) (1257 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical092
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s091
  have s093 : QRH.Record1252270103Source.GlobalSource (9979561290747 / 10000000000000 : ℝ) (20107 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical093
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s092
  have s094 : QRH.Record1252270103Source.GlobalSource (4989656793357 / 5000000000000 : ℝ) (10051 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical094
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s093
  have s095 : QRH.Record1252270103Source.GlobalSource (1995813054907 / 2000000000000 : ℝ) (20097 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical095
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s094
  have s096 : QRH.Record1252270103Source.GlobalSource (9978816354481 / 10000000000000 : ℝ) (5023 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical096
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s095
  have s097 : QRH.Record1252270103Source.GlobalSource (9978566826823 / 10000000000000 : ℝ) (20087 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical097
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s096
  have s098 : QRH.Record1252270103Source.GlobalSource (997831669183 / 1000000000000 : ℝ) (10041 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical098
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s097
  have s099 : QRH.Record1252270103Source.GlobalSource (2494516487443 / 2500000000000 : ℝ) (20077 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical099
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s098
  have s100 : QRH.Record1252270103Source.GlobalSource (4988907300459 / 5000000000000 : ℝ) (2509 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical100
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s099
  have s101 : QRH.Record1252270103Source.GlobalSource (9977562645537 / 10000000000000 : ℝ) (20067 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical101
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s100
  have s102 : QRH.Record1252270103Source.GlobalSource (9977310083897 / 10000000000000 : ℝ) (10031 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical102
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s101
  have s103 : QRH.Record1252270103Source.GlobalSource (4988528458133 / 5000000000000 : ℝ) (20057 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical103
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s102
  have s104 : QRH.Record1252270103Source.GlobalSource (9976803142911 / 10000000000000 : ℝ) (5013 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical104
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s103
  have s105 : QRH.Record1252270103Source.GlobalSource (9976548764099 / 10000000000000 : ℝ) (20047 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical105
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s104
  have s106 : QRH.Record1252270103Source.GlobalSource (77939795157 / 78125000000 : ℝ) (10021 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical106
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s105
  have s107 : QRH.Record1252270103Source.GlobalSource (9976038191167 / 10000000000000 : ℝ) (20037 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical107
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s106
  have s108 : QRH.Record1252270103Source.GlobalSource (4987890998789 / 5000000000000 : ℝ) (313 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical108
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s107
  have s109 : QRH.Record1252270103Source.GlobalSource (9975525199593 / 10000000000000 : ℝ) (20027 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical109
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s108
  have s110 : QRH.Record1252270103Source.GlobalSource (399010711899 / 400000000000 : ℝ) (10011 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical110
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s109
  have s111 : QRH.Record1252270103Source.GlobalSource (19482440999 / 19531250000 : ℝ) (20017 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical111
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s110
  have s112 : QRH.Record1252270103Source.GlobalSource (1994950236379 / 2000000000000 : ℝ) (5003 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical112
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s111
  have s113 : QRH.Record1252270103Source.GlobalSource (9974491968957 / 10000000000000 : ℝ) (20007 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical113
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s112
  have s114 : QRH.Record1252270103Source.GlobalSource (1246779019117 / 1250000000000 : ℝ) (10001 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical114
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s113
  have s115 : QRH.Record1252270103Source.GlobalSource (9973971734091 / 10000000000000 : ℝ) (19997 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical115
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s114
  have s116 : QRH.Record1252270103Source.GlobalSource (4986855356341 / 5000000000000 : ℝ) (2499 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical116
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s115
  have s117 : QRH.Record1252270103Source.GlobalSource (9973449088969 / 10000000000000 : ℝ) (19987 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical117
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s116
  have s118 : QRH.Record1252270103Source.GlobalSource (997318686321 / 1000000000000 : ℝ) (9991 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical118
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s117
  have s119 : QRH.Record1252270103Source.GlobalSource (9972924035663 / 10000000000000 : ℝ) (19977 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical119
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s118
  have s120 : QRH.Record1252270103Source.GlobalSource (4986330303293 / 5000000000000 : ℝ) (4993 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical120
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s119
  have s121 : QRH.Record1252270103Source.GlobalSource (2493099144059 / 2500000000000 : ℝ) (19967 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical121
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s120
  have s122 : QRH.Record1252270103Source.GlobalSource (9972131944869 / 10000000000000 : ℝ) (9981 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical122
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s121
  have s123 : QRH.Record1252270103Source.GlobalSource (4985933356371 / 5000000000000 : ℝ) (19957 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical123
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s122
  have s124 : QRH.Record1252270103Source.GlobalSource (9971600880109 / 10000000000000 : ℝ) (1247 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical124
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s123
  have s125 : QRH.Record1252270103Source.GlobalSource (398853377889 / 400000000000 : ℝ) (19947 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical125
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s124
  have s126 : QRH.Record1252270103Source.GlobalSource (1994213482869 / 2000000000000 : ℝ) (9971 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical126
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s125
  have s127 : QRH.Record1252270103Source.GlobalSource (4985399890861 / 5000000000000 : ℝ) (19937 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical127
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s126
  have s128 : QRH.Record1252270103Source.GlobalSource (9970531549609 / 10000000000000 : ℝ) (4983 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical128
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s127
  have s129 : QRH.Record1252270103Source.GlobalSource (9970262718259 / 10000000000000 : ℝ) (19927 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical129
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s128
  have s130 : QRH.Record1252270103Source.GlobalSource (2492498321981 / 2500000000000 : ℝ) (9961 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical130
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s129
  have s131 : QRH.Record1252270103Source.GlobalSource (1246215407357 / 1250000000000 : ℝ) (19917 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical131
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s130
  have s132 : QRH.Record1252270103Source.GlobalSource (9969452631307 / 10000000000000 : ℝ) (2489 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical132
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s131
  have s133 : QRH.Record1252270103Source.GlobalSource (1246147675691 / 1250000000000 : ℝ) (19907 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical133
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s132
  have s134 : QRH.Record1252270103Source.GlobalSource (9968909581769 / 10000000000000 : ℝ) (9951 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical134
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s133
  have s135 : QRH.Record1252270103Source.GlobalSource (9968637160281 / 10000000000000 : ℝ) (19897 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical135
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s134
  have s136 : QRH.Record1252270103Source.GlobalSource (9968364141313 / 10000000000000 : ℝ) (4973 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical136
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s135
  have s137 : QRH.Record1252270103Source.GlobalSource (4984045262557 / 5000000000000 : ℝ) (19887 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical137
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s136
  have s138 : QRH.Record1252270103Source.GlobalSource (9967816311933 / 10000000000000 : ℝ) (9941 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical138
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s137
  have s139 : QRH.Record1252270103Source.GlobalSource (9967541502017 / 10000000000000 : ℝ) (19877 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical139
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s138
  have s140 : QRH.Record1252270103Source.GlobalSource (2491816523903 / 2500000000000 : ℝ) (621 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical140
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s139
  have s141 : QRH.Record1252270103Source.GlobalSource (1993398018593 / 2000000000000 : ℝ) (19867 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical141
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s140
  have s142 : QRH.Record1252270103Source.GlobalSource (4983356747161 / 5000000000000 : ℝ) (9931 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical142
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s141
  have s143 : QRH.Record1252270103Source.GlobalSource (1245804537491 / 1250000000000 : ℝ) (19857 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical143
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s142
  have s144 : QRH.Record1252270103Source.GlobalSource (9966158510027 / 10000000000000 : ℝ) (4963 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical144
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s143
  have s145 : QRH.Record1252270103Source.GlobalSource (155716876951 / 156250000000 : ℝ) (19847 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical145
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s144
  have s146 : QRH.Record1252270103Source.GlobalSource (4982800572341 / 5000000000000 : ℝ) (9921 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical146
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s145
  have s147 : QRH.Record1252270103Source.GlobalSource (9965321569733 / 10000000000000 : ℝ) (19837 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical147
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s146
  have s148 : QRH.Record1252270103Source.GlobalSource (39860165601 / 40000000000 : ℝ) (2479 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical148
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s147
  have s149 : QRH.Record1252270103Source.GlobalSource (9964760636467 / 10000000000000 : ℝ) (19827 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical149
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s148
  have s150 : QRH.Record1252270103Source.GlobalSource (4982239639317 / 5000000000000 : ℝ) (9911 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical150
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s149
  have s151 : QRH.Record1252270103Source.GlobalSource (622762332937 / 625000000000 : ℝ) (19817 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical151
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s150
  have s152 : QRH.Record1252270103Source.GlobalSource (9963914781781 / 10000000000000 : ℝ) (4953 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical152
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s151
  have s153 : QRH.Record1252270103Source.GlobalSource (622726977703 / 625000000000 : ℝ) (19807 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical153
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s152
  have s154 : QRH.Record1252270103Source.GlobalSource (4981673955809 / 5000000000000 : ℝ) (9901 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical154
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s153
  have s155 : QRH.Record1252270103Source.GlobalSource (9963063587137 / 10000000000000 : ℝ) (19797 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical155
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s154
  have s156 : QRH.Record1252270103Source.GlobalSource (9962778670043 / 10000000000000 : ℝ) (1237 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical156
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s155
  have s157 : QRH.Record1252270103Source.GlobalSource (9962493160577 / 10000000000000 : ℝ) (19787 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical157
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s156
  have s158 : QRH.Record1252270103Source.GlobalSource (9962207058971 / 10000000000000 : ℝ) (9891 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical158
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s157
  have s159 : QRH.Record1252270103Source.GlobalSource (1245240045683 / 1250000000000 : ℝ) (19777 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical159
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s158
  have s160 : QRH.Record1252270103Source.GlobalSource (2490408270073 / 2500000000000 : ℝ) (4943 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical160
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s159
  have s161 : QRH.Record1252270103Source.GlobalSource (9961345203691 / 10000000000000 : ℝ) (19767 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical161
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s160
  have s162 : QRH.Record1252270103Source.GlobalSource (9961056735897 / 10000000000000 : ℝ) (9881 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical162
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s161
  have s163 : QRH.Record1252270103Source.GlobalSource (4980383838573 / 5000000000000 : ℝ) (19757 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical163
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s162
  have s164 : QRH.Record1252270103Source.GlobalSource (1245059753459 / 1250000000000 : ℝ) (2469 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical164
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s163
  have s165 : QRH.Record1252270103Source.GlobalSource (9960187787709 / 10000000000000 : ℝ) (19747 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical165
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s164
  have s166 : QRH.Record1252270103Source.GlobalSource (9959896957491 / 10000000000000 : ℝ) (9871 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical166
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s165
  have s167 : QRH.Record1252270103Source.GlobalSource (2489901384313 / 2500000000000 : ℝ) (19737 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical167
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s166
  have s168 : QRH.Record1252270103Source.GlobalSource (1244914190903 / 1250000000000 : ℝ) (4933 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical168
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s167
  have s169 : QRH.Record1252270103Source.GlobalSource (4979510463819 / 5000000000000 : ℝ) (19727 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical169
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s168
  have s170 : QRH.Record1252270103Source.GlobalSource (4979363869363 / 5000000000000 : ℝ) (9861 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical170
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s169
  have s171 : QRH.Record1252270103Source.GlobalSource (9958433960717 / 10000000000000 : ℝ) (19717 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical171
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s170
  have s172 : QRH.Record1252270103Source.GlobalSource (9958139593841 / 10000000000000 : ℝ) (308 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical172
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s171
  have s173 : QRH.Record1252270103Source.GlobalSource (1244730579791 / 1250000000000 : ℝ) (19707 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical173
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s172
  have s174 : QRH.Record1252270103Source.GlobalSource (4978774547203 / 5000000000000 : ℝ) (9851 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical174
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s173
  have s175 : QRH.Record1252270103Source.GlobalSource (9957252962303 / 10000000000000 : ℝ) (19697 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical175
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s174
  have s176 : QRH.Record1252270103Source.GlobalSource (9956956242247 / 10000000000000 : ℝ) (4923 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical176
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s175
  have s177 : QRH.Record1252270103Source.GlobalSource (1991331786893 / 2000000000000 : ℝ) (19687 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical177
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s176
  have s178 : QRH.Record1252270103Source.GlobalSource (622272564949 / 625000000000 : ℝ) (9841 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical178
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s177
  have s179 : QRH.Record1252270103Source.GlobalSource (995606255663 / 1000000000000 : ℝ) (19677 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical179
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s178
  have s180 : QRH.Record1252270103Source.GlobalSource (2488940871757 / 2500000000000 : ℝ) (2459 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical180
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s179
  have s181 : QRH.Record1252270103Source.GlobalSource (4977731915303 / 5000000000000 : ℝ) (19667 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical181
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s180
  have s182 : QRH.Record1252270103Source.GlobalSource (1991032717517 / 2000000000000 : ℝ) (9831 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical182
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s181
  have s183 : QRH.Record1252270103Source.GlobalSource (995486275819 / 1000000000000 : ℝ) (19657 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical183
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s182
  have s184 : QRH.Record1252270103Source.GlobalSource (1990912268529 / 2000000000000 : ℝ) (4913 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical184
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s183
  have s185 : QRH.Record1252270103Source.GlobalSource (398170373647 / 400000000000 : ℝ) (19647 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical185
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s184
  have s186 : QRH.Record1252270103Source.GlobalSource (2488489188501 / 2500000000000 : ℝ) (9821 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical186
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s185
  have s187 : QRH.Record1252270103Source.GlobalSource (4976826790677 / 5000000000000 : ℝ) (19637 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical187
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s186
  have s188 : QRH.Record1252270103Source.GlobalSource (1244168727931 / 1250000000000 : ℝ) (1227 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical188
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s187
  have s189 : QRH.Record1252270103Source.GlobalSource (2488261370127 / 2500000000000 : ℝ) (19627 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical189
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s188
  have s190 : QRH.Record1252270103Source.GlobalSource (2488185138189 / 2500000000000 : ℝ) (9811 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical190
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s189
  have s191 : QRH.Record1252270103Source.GlobalSource (9952435040413 / 10000000000000 : ℝ) (19617 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical191
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s190
  have s192 : QRH.Record1252270103Source.GlobalSource (99521289437 / 100000000000 : ℝ) (4903 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical192
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s191
  have s193 : QRH.Record1252270103Source.GlobalSource (9951822262837 / 10000000000000 : ℝ) (19607 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical193
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s192
  have s194 : QRH.Record1252270103Source.GlobalSource (9951514998043 / 10000000000000 : ℝ) (9801 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical194
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s193
  have s195 : QRH.Record1252270103Source.GlobalSource (310975223423 / 312500000000 : ℝ) (19597 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical195
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s194
  have s196 : QRH.Record1252270103Source.GlobalSource (4975449358767 / 5000000000000 : ℝ) (2449 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical196
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s195
  have s197 : QRH.Record1252270103Source.GlobalSource (4975294851127 / 5000000000000 : ℝ) (19587 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical197
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s196
  have s198 : QRH.Record1252270103Source.GlobalSource (9950280103913 / 10000000000000 : ℝ) (9791 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical198
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s197
  have s199 : QRH.Record1252270103Source.GlobalSource (9949969922727 / 10000000000000 : ℝ) (19577 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical199
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s198
  have s200 : QRH.Record1252270103Source.GlobalSource (9949659158911 / 10000000000000 : ℝ) (4893 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical200
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s199
  have s201 : QRH.Record1252270103Source.GlobalSource (9949347812681 / 10000000000000 : ℝ) (19567 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical201
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s200
  have s202 : QRH.Record1252270103Source.GlobalSource (9949035884251 / 10000000000000 : ℝ) (9781 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical202
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s201
  have s203 : QRH.Record1252270103Source.GlobalSource (1989744674767 / 2000000000000 : ℝ) (19557 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical203
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s202
  have s204 : QRH.Record1252270103Source.GlobalSource (9948410281647 / 10000000000000 : ℝ) (611 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical204
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s203
  have s205 : QRH.Record1252270103Source.GlobalSource (9948096607901 / 10000000000000 : ℝ) (19547 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical205
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s204
  have s206 : QRH.Record1252270103Source.GlobalSource (9947782352809 / 10000000000000 : ℝ) (9771 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical206
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s205
  have s207 : QRH.Record1252270103Source.GlobalSource (9947467516583 / 10000000000000 : ℝ) (19537 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical207
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s206
  have s208 : QRH.Record1252270103Source.GlobalSource (1989430419887 / 2000000000000 : ℝ) (4883 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical208
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s207
  have s209 : QRH.Record1252270103Source.GlobalSource (4973418050789 / 5000000000000 : ℝ) (19527 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical209
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s208
  have s210 : QRH.Record1252270103Source.GlobalSource (9946519523223 / 10000000000000 : ℝ) (9761 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical210
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s209
  have s211 : QRH.Record1252270103Source.GlobalSource (4973101182291 / 5000000000000 : ℝ) (19517 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical211
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s210
  have s212 : QRH.Record1252270103Source.GlobalSource (1989176925173 / 2000000000000 : ℝ) (2439 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical212
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s211
  have s213 : QRH.Record1252270103Source.GlobalSource (9945566307283 / 10000000000000 : ℝ) (19507 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical213
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s212
  have s214 : QRH.Record1252270103Source.GlobalSource (9945247409047 / 10000000000000 : ℝ) (9751 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical214
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s213
  have s215 : QRH.Record1252270103Source.GlobalSource (1988985586273 / 2000000000000 : ℝ) (19497 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical215
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s214
  have s216 : QRH.Record1252270103Source.GlobalSource (4972303937223 / 5000000000000 : ℝ) (4873 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical216
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s215
  have s217 : QRH.Record1252270103Source.GlobalSource (4972143619249 / 5000000000000 : ℝ) (19487 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical217
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s216
  have s218 : QRH.Record1252270103Source.GlobalSource (9943966023727 / 10000000000000 : ℝ) (9741 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical218
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s217
  have s219 : QRH.Record1252270103Source.GlobalSource (9943644230341 / 10000000000000 : ℝ) (19477 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical219
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s218
  have s220 : QRH.Record1252270103Source.GlobalSource (1988664371709 / 2000000000000 : ℝ) (1217 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical220
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s219
  have s221 : QRH.Record1252270103Source.GlobalSource (4971499454273 / 5000000000000 : ℝ) (19467 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical221
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s220
  have s222 : QRH.Record1252270103Source.GlobalSource (9942675380549 / 10000000000000 : ℝ) (9731 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical222
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s221
  have s223 : QRH.Record1252270103Source.GlobalSource (9942351274759 / 10000000000000 : ℝ) (19457 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical223
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s222
  have s224 : QRH.Record1252270103Source.GlobalSource (497101329569 / 500000000000 : ℝ) (4863 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical224
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s223
  have s225 : QRH.Record1252270103Source.GlobalSource (1988340266123 / 2000000000000 : ℝ) (19447 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical225
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s224
  have s226 : QRH.Record1252270103Source.GlobalSource (9941375492669 / 10000000000000 : ℝ) (9721 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical226
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s225
  have s227 : QRH.Record1252270103Source.GlobalSource (621315567359 / 625000000000 : ℝ) (19437 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical227
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s226
  have s228 : QRH.Record1252270103Source.GlobalSource (9940722086043 / 10000000000000 : ℝ) (2429 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical228
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s227
  have s229 : QRH.Record1252270103Source.GlobalSource (1242549314721 / 1250000000000 : ℝ) (19427 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical229
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s228
  have s230 : QRH.Record1252270103Source.GlobalSource (3882838427 / 3906250000 : ℝ) (9711 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical230
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s229
  have s231 : QRH.Record1252270103Source.GlobalSource (99397376523 / 100000000000 : ℝ) (19417 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical231
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s230
  have s232 : QRH.Record1252270103Source.GlobalSource (9939408355509 / 10000000000000 : ℝ) (4853 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical232
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s231
  have s233 : QRH.Record1252270103Source.GlobalSource (2484769620737 / 2500000000000 : ℝ) (19407 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical233
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s232
  have s234 : QRH.Record1252270103Source.GlobalSource (9938748034817 / 10000000000000 : ℝ) (9701 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical234
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s233
  have s235 : QRH.Record1252270103Source.GlobalSource (2484604252829 / 2500000000000 : ℝ) (19397 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical235
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s234
  have s236 : QRH.Record1252270103Source.GlobalSource (1987617082529 / 2000000000000 : ℝ) (303 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical236
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s235
  have s237 : QRH.Record1252270103Source.GlobalSource (4968876619501 / 5000000000000 : ℝ) (19387 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical237
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s236
  have s238 : QRH.Record1252270103Source.GlobalSource (4968710245293 / 5000000000000 : ℝ) (9691 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical238
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s237
  have s239 : QRH.Record1252270103Source.GlobalSource (1987417433519 / 2000000000000 : ℝ) (19377 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical239
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s238
  have s240 : QRH.Record1252270103Source.GlobalSource (9936753270227 / 10000000000000 : ℝ) (4843 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical240
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s239
  have s241 : QRH.Record1252270103Source.GlobalSource (9936418798679 / 10000000000000 : ℝ) (19367 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical241
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s240
  have s242 : QRH.Record1252270103Source.GlobalSource (9936083753147 / 10000000000000 : ℝ) (9681 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical242
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s241
  have s243 : QRH.Record1252270103Source.GlobalSource (4967874066913 / 5000000000000 : ℝ) (19357 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical243
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s242
  have s244 : QRH.Record1252270103Source.GlobalSource (993541194091 / 1000000000000 : ℝ) (2419 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical244
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s243
  have s245 : QRH.Record1252270103Source.GlobalSource (9935075174593 / 10000000000000 : ℝ) (19347 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical245
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s244
  have s246 : QRH.Record1252270103Source.GlobalSource (9934737835069 / 10000000000000 : ℝ) (9671 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical246
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s245
  have s247 : QRH.Record1252270103Source.GlobalSource (2483599980633 / 2500000000000 : ℝ) (19337 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical247
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s246
  have s248 : QRH.Record1252270103Source.GlobalSource (4967030718587 / 5000000000000 : ℝ) (4833 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical248
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s247
  have s249 : QRH.Record1252270103Source.GlobalSource (9933722379187 / 10000000000000 : ℝ) (19327 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical249
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s248
  have s250 : QRH.Record1252270103Source.GlobalSource (9933382748763 / 10000000000000 : ℝ) (9661 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical250
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s249
  have s251 : QRH.Record1252270103Source.GlobalSource (4966521273047 / 5000000000000 : ℝ) (19317 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical251
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s250
  have s252 : QRH.Record1252270103Source.GlobalSource (993270177137 / 1000000000000 : ℝ) (1207 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical252
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s251
  have s253 : QRH.Record1252270103Source.GlobalSource (9932360424783 / 10000000000000 : ℝ) (19307 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical253
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s252
  have s254 : QRH.Record1252270103Source.GlobalSource (9932018506523 / 10000000000000 : ℝ) (9651 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical254
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s253
  have s255 : QRH.Record1252270103Source.GlobalSource (4965838008391 / 5000000000000 : ℝ) (19297 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical255
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s254
  have s256 : QRH.Record1252270103Source.GlobalSource (39725331823 / 40000000000 : ℝ) (4823 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical256
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s255
  have s257 : QRH.Record1252270103Source.GlobalSource (9930989323617 / 10000000000000 : ℝ) (19287 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical257
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s256
  have s258 : QRH.Record1252270103Source.GlobalSource (9930645120573 / 10000000000000 : ℝ) (9641 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical258
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s257
  have s259 : QRH.Record1252270103Source.GlobalSource (1241287543351 / 1250000000000 : ℝ) (19277 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical259
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s258
  have s260 : QRH.Record1252270103Source.GlobalSource (992995500251 / 1000000000000 : ℝ) (2409 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical260
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s259
  have s261 : QRH.Record1252270103Source.GlobalSource (9929609087867 / 10000000000000 : ℝ) (19267 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical261
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s260
  have s262 : QRH.Record1252270103Source.GlobalSource (9929262603067 / 10000000000000 : ℝ) (9631 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical262
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s261
  have s263 : QRH.Record1252270103Source.GlobalSource (1241114443537 / 1250000000000 : ℝ) (19257 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical263
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s262
  have s264 : QRH.Record1252270103Source.GlobalSource (496428396187 / 500000000000 : ℝ) (4813 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical264
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s263
  have s265 : QRH.Record1252270103Source.GlobalSource (620513733099 / 625000000000 : ℝ) (19247 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical265
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s264
  have s266 : QRH.Record1252270103Source.GlobalSource (9927870966013 / 10000000000000 : ℝ) (9621 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical266
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s265
  have s267 : QRH.Record1252270103Source.GlobalSource (992752163321 / 1000000000000 : ℝ) (19237 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical267
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s266
  have s268 : QRH.Record1252270103Source.GlobalSource (62044823321 / 62500000000 : ℝ) (601 / 250 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical268
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s267
  have s269 : QRH.Record1252270103Source.GlobalSource (1985364252129 / 2000000000000 : ℝ) (19227 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical269
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s268
  have s270 : QRH.Record1252270103Source.GlobalSource (155101097207 / 156250000000 : ℝ) (9611 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical270
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s269
  have s271 : QRH.Record1252270103Source.GlobalSource (1240764826669 / 1250000000000 : ℝ) (19217 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical271
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s270
  have s272 : QRH.Record1252270103Source.GlobalSource (4962883218569 / 5000000000000 : ℝ) (4803 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical272
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s271
  have s273 : QRH.Record1252270103Source.GlobalSource (2481353423197 / 2500000000000 : ℝ) (19207 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical273
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s272
  have s274 : QRH.Record1252270103Source.GlobalSource (2481265095121 / 2500000000000 : ℝ) (9601 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical274
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s273
  have s275 : QRH.Record1252270103Source.GlobalSource (9924706500407 / 10000000000000 : ℝ) (19197 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical275
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s274
  have s276 : QRH.Record1252270103Source.GlobalSource (9924352052739 / 10000000000000 : ℝ) (2399 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical276
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s275
  have s277 : QRH.Record1252270103Source.GlobalSource (4961998518831 / 5000000000000 : ℝ) (19187 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical277
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s276
  have s278 : QRH.Record1252270103Source.GlobalSource (2480910363839 / 2500000000000 : ℝ) (9591 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical278
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s277
  have s279 : QRH.Record1252270103Source.GlobalSource (4961642653001 / 5000000000000 : ℝ) (19177 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical279
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s278
  have s280 : QRH.Record1252270103Source.GlobalSource (9922928589779 / 10000000000000 : ℝ) (4793 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical280
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s279
  have s281 : QRH.Record1252270103Source.GlobalSource (4961285653433 / 5000000000000 : ℝ) (19167 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical281
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s280
  have s282 : QRH.Record1252270103Source.GlobalSource (4961106728721 / 5000000000000 : ℝ) (9581 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical282
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s281
  have s283 : QRH.Record1252270103Source.GlobalSource (9921855041683 / 10000000000000 : ℝ) (19157 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical283
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s282
  have s284 : QRH.Record1252270103Source.GlobalSource (9921496059767 / 10000000000000 : ℝ) (1197 / 500 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical284
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s283
  have s285 : QRH.Record1252270103Source.GlobalSource (9921136511881 / 10000000000000 : ℝ) (19147 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical285
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s284
  have s286 : QRH.Record1252270103Source.GlobalSource (496038819909 / 500000000000 : ℝ) (9571 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical286
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s285
  have s287 : QRH.Record1252270103Source.GlobalSource (9920415718851 / 10000000000000 : ℝ) (19137 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical287
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s286
  have s288 : QRH.Record1252270103Source.GlobalSource (9920054474069 / 10000000000000 : ℝ) (4783 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical288
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s287
  have s289 : QRH.Record1252270103Source.GlobalSource (1239961583001 / 1250000000000 : ℝ) (19127 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical289
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s288
  have s290 : QRH.Record1252270103Source.GlobalSource (9919330288843 / 10000000000000 : ℝ) (9561 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical290
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s289
  have s291 : QRH.Record1252270103Source.GlobalSource (9918967348749 / 10000000000000 : ℝ) (19117 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical291
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s290
  have s292 : QRH.Record1252270103Source.GlobalSource (4959301921949 / 5000000000000 : ℝ) (2389 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical292
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s291
  have s293 : QRH.Record1252270103Source.GlobalSource (38743124119 / 39062500000 : ℝ) (19107 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical293
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s292
  have s294 : QRH.Record1252270103Source.GlobalSource (495893757031 / 500000000000 : ℝ) (9551 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical294
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s293
  have s295 : QRH.Record1252270103Source.GlobalSource (4958754971269 / 5000000000000 : ℝ) (19097 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical295
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s294
  have s296 : QRH.Record1252270103Source.GlobalSource (991714418039 / 1000000000000 : ℝ) (4773 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical296
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s295
  have s297 : QRH.Record1252270103Source.GlobalSource (9916777854349 / 10000000000000 : ℝ) (19087 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical297
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s296
  have s298 : QRH.Record1252270103Source.GlobalSource (4958205482293 / 5000000000000 : ℝ) (9541 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical298
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s297
  have s299 : QRH.Record1252270103Source.GlobalSource (4958021755637 / 5000000000000 : ℝ) (19077 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical299
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s298
  have s300 : QRH.Record1252270103Source.GlobalSource (1239459436823 / 1250000000000 : ℝ) (298 / 125 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical300
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s299
  have s301 : QRH.Record1252270103Source.GlobalSource (1983061382937 / 2000000000000 : ℝ) (19067 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical301
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s300
  have s302 : QRH.Record1252270103Source.GlobalSource (9914937771747 / 10000000000000 : ℝ) (9531 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical302
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s301
  have s303 : QRH.Record1252270103Source.GlobalSource (4957284032973 / 5000000000000 : ℝ) (19057 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical303
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s302
  have s304 : QRH.Record1252270103Source.GlobalSource (4957098898723 / 5000000000000 : ℝ) (4763 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical304
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s303
  have s305 : QRH.Record1252270103Source.GlobalSource (4956913483207 / 5000000000000 : ℝ) (19047 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical305
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s304
  have s306 : QRH.Record1252270103Source.GlobalSource (1239181946627 / 1250000000000 : ℝ) (9521 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical306
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s305
  have s307 : QRH.Record1252270103Source.GlobalSource (9913083617419 / 10000000000000 : ℝ) (19037 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical307
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s306
  have s308 : QRH.Record1252270103Source.GlobalSource (991271109979 / 1000000000000 : ℝ) (2379 / 1000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical308
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s307
  have s309 : QRH.Record1252270103Source.GlobalSource (9912338020293 / 10000000000000 : ℝ) (19027 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical309
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s308
  have s310 : QRH.Record1252270103Source.GlobalSource (4955982189547 / 5000000000000 : ℝ) (9511 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical310
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s309
  have s311 : QRH.Record1252270103Source.GlobalSource (4955795088179 / 5000000000000 : ℝ) (19017 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical311
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s310
  have s312 : QRH.Record1252270103Source.GlobalSource (9911215412249 / 10000000000000 : ℝ) (4753 / 2000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical312
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s311
  have s313 : QRH.Record1252270103Source.GlobalSource (9910840086933 / 10000000000000 : ℝ) (19007 / 8000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical313
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s312
  have s314 : QRH.Record1252270103Source.GlobalSource (396418568023 / 400000000000 : ℝ) (9501 / 4000 : ℝ) (1 / 10 : ℝ) :=
    QRH.DensityTen.density_step hybridGates_Physical314
      ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      (by norm_num) (by norm_num) (by norm_num) hβ s313
  exact s314
end
end QRH.DensityTen
