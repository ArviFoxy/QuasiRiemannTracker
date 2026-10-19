/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
    Exact rational certificates for the auxiliary source's extended width interval. -/
import Candidate.Uneven.AuxiliarySchedule

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Sil.Uneven.AuxiliarySource

theorem channel_lo_0 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 0 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2))) := by
    have he : (-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2)))=(812992457940765777712118518/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(10077208533257291828513800000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(7957997964510073183750000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (128221500000000000000+(-51288600000000000000*d)) := by
    have he : (128221500000000000000+(-51288600000000000000*d))=89755050000000000000+51288600000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 0-highReserve=(-333342179274000000+(-31386564701372643895*d)+(46685626834944897558*(d^2)))/(128221500000000000000+(-51288600000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_1 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 1 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2))) := by
    have he : (-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2)))=(136306279232478109112439766/20548089:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(621786684911240977290200000/20548089:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(502310237524819641250000000/20548089:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (2249500000000000000+(-899800000000000000*d)) := by
    have he : (2249500000000000000+(-899800000000000000*d))=1574650000000000000+899800000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 1-highReserve=(-122466854226500000+(-384020726312386735*d)+(819046084823594694*(d^2)))/(2249500000000000000+(-899800000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_2 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 2 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2))) := by
    have he : (3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2)))=(219776633802846895079922/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(250681943674219317290200000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(266112879243319641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 2-highReserve=(3766714620000000+(-1660448873904960205*d)+(2349162319256384082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_3 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 3 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2))) := by
    have he : (94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2)))=(9293078339733053958177180218556/3449795831:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(493443415398255465913512309700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(745281296606931990629382500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(335084620371480087437500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    have he : (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2)))=54325425000000000000+(3942558281200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(3869140000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 3-highReserve=(94167865500000000+(-21858903873039005125*d)+(-12592239397689313476*(d^3))+(40209093148966885740*(d^2)))/(168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_4 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 4 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2))) := by
    have he : (433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2)))=(6912497892958368551839567004/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(1881693334045481414302935993100000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(3837286007537922070048947500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(1952546420034018827312500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    have he : (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2)))=351934275000000000000+(15426874843600000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(15206620000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 4-highReserve=(433172181300000000+(-174809152226255423575*d)+(-98781721919135140428*(d^3))+(316808658103340020500*(d^2)))/(776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_lo_5 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (1/50:ℝ) d 5 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2))) := by
    have he : (696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2)))=(193504356979632978002468511426788/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(3440712548524045000636427863700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(5205148968714916005965132500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(2342209100195980076187500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    have he : (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2)))=385001925000000000000+(29626413489200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(29063540000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (1/50:ℝ) d 5-highReserve=(696842204700000000+(-153316145563467637925*d)+(-88262580294192203316*(d^3))+(281871413920179563460*(d^2)))/(1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_0 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 0 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2))) := by
    have he : (326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2)))=(1183611897047542402897718518/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(12047913084763387268513800000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(8805065575461073183750000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (128221500000000000000+(-51288600000000000000*d)) := by
    have he : (128221500000000000000+(-51288600000000000000*d))=89755050000000000000+51288600000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 0-highReserve=(326245037748000000+(-30637437061153443895*d)+(44965959876898497558*(d^2)))/(128221500000000000000+(-51288600000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_1 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 1 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2))) := by
    have he : (-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2)))=(198000759556705997299639766/6849363:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(254023638134380245763400000/2283121:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(580280059153819641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 1-highReserve=(-472628024941500000+(-912689376820360205*d)+(2366629467205184082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_2 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 2 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2))) := by
    have he : (47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2)))=(2698332645973742957479922/2283121:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(242524187606119077290200000/6849363:ℝ)*(d-70467/100000)^1*(3/4-d)^1+(249603700872319641250000000/6849363:ℝ)*(d-70467/100000)^2*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (6748500000000000000+(-2699400000000000000*d)) := by
    have he : (6748500000000000000+(-2699400000000000000*d))=4723950000000000000+2699400000000000000*(d-70467/100000)^0*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 2-highReserve=(47006252358000000+(-1624430871788160205*d)+(2215463131990784082*(d^2)))/(6748500000000000000+(-2699400000000000000*d)) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_3 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 3 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2))) := by
    have he : (1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2)))=(7874406792208992867546341818556/3449795831:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(435610466574953908044312309700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(668267387461511328629382500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(303139488357930087437500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    have he : (168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2)))=54325425000000000000+(3942558281200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(3869140000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 3-highReserve=(1175156308950000000+(-23681316254163005125*d)+(-12467522313762913476*(d^3))+(40453307240648485740*(d^2)))/(168712500000000000000+(-188958000000000000000*d)+(48589200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_4 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 4 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2))) := by
    have he : (5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2)))=(53152210807629484410255567004/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(1723536570098474338047975993100000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(3519284621096163148048947500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(1792973714283168827312500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    have he : (776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2)))=351934275000000000000+(15426874843600000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(15206620000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 4-highReserve=(5405719021170000000+(-176296267775435423575*d)+(-94491690093647140428*(d^3))+(305882817264912820500*(d^2)))/(776077500000000000000+(-674850000000000000000*d)+(145767600000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_hi_5 {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) :
    highReserve ≤ channel (7/250:ℝ) d 5 := by
  have hlo : 0 ≤ d-70467/100000 := by norm_num [q] at hd0;linarith
  have hhi : 0 ≤ 3/4-d := by linarith
  have hn : (0:ℝ) ≤ (8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2))) := by
    have he : (8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2)))=(145069225140153111938703234626788/10349387493:ℝ)*(d-70467/100000)^0*(3/4-d)^3+(2884585612392876857413787863700000/31048162479:ℝ)*(d-70467/100000)^1*(3/4-d)^2+(4532495302815940419965132500000000/31048162479:ℝ)*(d-70467/100000)^2*(3/4-d)^1+(2080362931377130076187500000000000/31048162479:ℝ)*(d-70467/100000)^3*(3/4-d)^0 := by ring
    rw [he]
    positivity
  have hden : (0:ℝ) < (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    have he : (1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2)))=385001925000000000000+(29626413489200000000000000/1511:ℝ)*(d-70467/100000)^0*(3/4-d)^2+(29063540000000000000000000/1511:ℝ)*(d-70467/100000)^1*(3/4-d)^1 := by ring
    rw [he]
    positivity
  have he : channel (7/250:ℝ) d 5-highReserve=(8696156686230000000+(-169525977417783637925*d)+(-88714894746374603316*(d^3))+(288206242475317163460*(d^2)))/(1248472500000000000000+(-1430682000000000000000*d)+(372517200000000000000*(d^2))) := by
    norm_num [channel,highBase,total,amp,gap,supplied,frequency,B,lambda,q,kappa,
      lowReserve,highReserve,widthMesh,discard,frequencyAllowance,
      Saturated.rho,Saturated.slope,Saturated.offset]
    field_simp (disch := first | positivity | linarith) <;> ring
  have hh := div_nonneg hn hden.le
  rw [←he] at hh
  linarith only [hh]

theorem channel_width_identity (b d : ℝ) (i : Fin 6) :
    ((7/250:ℝ)-1/50)*(channel b d i-highReserve)=
      ((7/250:ℝ)-b)*(channel (1/50) d i-highReserve)+
      (b-1/50)*(channel (7/250) d i-highReserve) := by
  fin_cases i <;> simp [channel,highBase,total,amp,gap,supplied,frequency] <;> ring

theorem channel_endpoints {d : ℝ} (hd0 : q ≤ d) (hd1 : d ≤ 3/4) (i : Fin 6) :
    highReserve ≤ channel (1/50) d i ∧ highReserve ≤ channel (7/250) d i := by
  fin_cases i
  · exact ⟨channel_lo_0 hd0 hd1,channel_hi_0 hd0 hd1⟩
  · exact ⟨channel_lo_1 hd0 hd1,channel_hi_1 hd0 hd1⟩
  · exact ⟨channel_lo_2 hd0 hd1,channel_hi_2 hd0 hd1⟩
  · exact ⟨channel_lo_3 hd0 hd1,channel_hi_3 hd0 hd1⟩
  · exact ⟨channel_lo_4 hd0 hd1,channel_hi_4 hd0 hd1⟩
  · exact ⟨channel_lo_5 hd0 hd1,channel_hi_5 hd0 hd1⟩

theorem all_channels {b d : ℝ} (hb : b∈Set.Icc widthLo widthHi)
    (hd0 : q ≤ d) (hd1 : d ≤ 3/4) (i : Fin 6) : highReserve ≤ channel b d i := by
  have hs := channel_endpoints hd0 hd1 i
  have hlo : 0 ≤ b-1/50 := by norm_num [widthLo] at hb;linarith [hb.1]
  have hhi : 0 ≤ (7/250:ℝ)-b := by norm_num [widthHi] at hb;linarith [hb.2]
  have hl := mul_nonneg hhi (sub_nonneg.mpr hs.1)
  have hh := mul_nonneg hlo (sub_nonneg.mpr hs.2)
  have he := channel_width_identity b d i
  nlinarith only [hl,hh,he]

end Sil.Uneven.AuxiliarySource
#print axioms Sil.Uneven.AuxiliarySource.all_channels
