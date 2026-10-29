/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.PowerRows
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def row192_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1961959464088324965001/4461751054687500:ℝ), (5398271490318298770587/4461751054687500:ℝ), (4918870429223959429211/4461751054687500:ℝ), (11859831399843084989/35694008437500:ℝ)],
![(1123227605644768731817/2230875527343750:ℝ), (2882492471816231337179/2230875527343750:ℝ), (801497272102579547009/743625175781250:ℝ), (129027507474195207133/446175105468750:ℝ)],
![(484751550380256040933/4461751054687500:ℝ), (959312405828653458131/4461751054687500:ℝ), (237330722404679958599/2230875527343750:ℝ), (0:ℝ)]]
theorem row192_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (252405628057044648349/15208789573632000000000:ℝ) row192_coefficients
      (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row192_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row192_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row192_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row192_coefficients]

def row193_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2289766456003603318387/743625175781250:ℝ), (19665030795466824748811/2230875527343750:ℝ), (18730130893712756415179/2230875527343750:ℝ), (94196186146824470183/35410722656250:ℝ)],
![(3519933817573171603321/1115437763671875:ℝ), (458173478301423511519/53116083984375:ℝ), (1738481217450790967191/223087552734375:ℝ), (41121462763723534879/17705361328125:ℝ)],
![(134197666869895351523/318696503906250:ℝ), (1868828114649082547587/2230875527343750:ℝ), (464747370620148168463/1115437763671875:ℝ), (0:ℝ)]]
theorem row193_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (1637971631423665871819/101391930490880000000000:ℝ) row193_coefficients
      (3/8:ℝ) (27/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row193_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row193_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row193_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row193_coefficients]

def row194_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25586614906652109911233/1115437763671875:ℝ), (14981148259206093326503/223087552734375:ℝ), (73059486061895740314371/1115437763671875:ℝ), (23740339803013983593089/1115437763671875:ℝ)],
![(195388553825770787434/8923502109375:ℝ), (69588909185023218312454/1115437763671875:ℝ), (21974895116571285220466/371812587890625:ℝ), (20759300686529335778194/1115437763671875:ℝ)],
![(1849175997652343425117/1115437763671875:ℝ), (3688538510476437601499/1115437763671875:ℝ), (1839387660164334801382/1115437763671875:ℝ), (0:ℝ)]]
theorem row194_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (135740441041935589807679/8516922161233920000000000:ℝ) row194_coefficients
      (3/8:ℝ) (27/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row194_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row194_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row194_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row194_coefficients]

def row195_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25569989420370791020736/1115437763671875:ℝ), (74871501608258583527104/1115437763671875:ℝ), (4869388235779048718336/74362517578125:ℝ), (23739291479294538268672/1115437763671875:ℝ)],
![(2713177769026994514832/123937529296875:ℝ), (23203005491201001191216/371812587890625:ℝ), (65979673728660669571072/1115437763671875:ℝ), (20789212469917966630912/1115437763671875:ℝ)],
![(1829649617356807427647/1115437763671875:ℝ), (3649561191906087481559/1115437763671875:ℝ), (1819936721889520678912/1115437763671875:ℝ), (0:ℝ)]]
theorem row195_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (1167609439737189439/74261667840000000000:ℝ) row195_coefficients
      (3/8:ℝ) (27/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row195_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row195_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row195_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row195_coefficients]

def row196_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12105520100449916563289/2129669788359375000:ℝ), (20170790619481044725899/2129669788359375000:ℝ), (8580478939460854308731/2129669788359375000:ℝ), (1889959518083038841/26292219609375000:ℝ)],
![(2445613041353295178309/212966978835937500:ℝ), (20233113699110898875563/1064834894179687500:ℝ), (8448154909187912705591/1064834894179687500:ℝ), (875626929410366933/13146109804687500:ℝ)],
![(12370802737743035219801/2129669788359375000:ℝ), (20344703152497486991027/2129669788359375000:ℝ), (4178209700651757135613/1064834894179687500:ℝ), (0:ℝ)]]
theorem row196_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (7862952191223708348583/294073498337280000000000:ℝ) row196_coefficients
      (27/64:ℝ) (111/256:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row196_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row196_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row196_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row196_coefficients]

def row197_coefficients : Fin 3 → Fin 4 → ℝ := ![![(316585618301641232777/2157750468750000:ℝ), (1943036643859104505489/6473251406250000:ℝ), (221041133111422418797/1294650281250000:ℝ), (109779970235731286827/6473251406250000:ℝ)],
![(299751036695857258489/1078875234375000:ℝ), (118853251377595569599/215775046875000:ℝ), (938066841130789256069/3236625703125000:ℝ), (52315665677027487551/3236625703125000:ℝ)],
![(94968312972244203767/719250156250000:ℝ), (1639593448066613618681/6473251406250000:ℝ), (393572705247982892389/3236625703125000:ℝ), (0:ℝ)]]
theorem row197_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (3797002168809399410341/193072243671040000000000:ℝ) row197_coefficients
      (27/64:ℝ) (111/256:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row197_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row197_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row197_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row197_coefficients]

def row198_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1949241464449949667739/3236625703125000:ℝ), (4295992883650012536209/3236625703125000:ℝ), (2806226597402250247201/3236625703125000:ℝ), (50933580557620819859/359625078125000:ℝ)],
![(343876849243026894127/323662570312500:ℝ), (3595913050445989825073/1618312851562500:ℝ), (233031716408890414749/179812539062500:ℝ), (24405987334495375367/179812539062500:ℝ)],
![(503373861169008173477/1078875234375000:ℝ), (2956073929529141991737/3236625703125000:ℝ), (723542867805946235653/1618312851562500:ℝ), (0:ℝ)]]
theorem row198_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (13677887091730573120933/772288974684160000000000:ℝ) row198_coefficients
      (27/64:ℝ) (111/256:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row198_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row198_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row198_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row198_coefficients]

def row199_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12724921254813471387953/4461751054687500:ℝ), (30255687839446579529171/4461751054687500:ℝ), (3214467494733983267749/637393007812500:ℝ), (198755857949174989321/178470042187500:ℝ)],
![(10171017033755420624417/2230875527343750:ℝ), (22562967575496268012979/2230875527343750:ℝ), (2111707282449195425561/318696503906250:ℝ), (477669259849094118073/446175105468750:ℝ)],
![(7817368615876413403181/4461751054687500:ℝ), (15462846264060446051147/4461751054687500:ℝ), (1274529622094782524661/743625175781250:ℝ), (0:ℝ)]]
theorem row199_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (27275651052643125668483/1703384432246784000000000:ℝ) row199_coefficients
      (27/64:ℝ) (111/256:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row199_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row199_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row199_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row199_coefficients]

def row200_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5000328643332023531831/318696503906250:ℝ), (17963547055214595363623/446175105468750:ℝ), (74788401301532397447539/2230875527343750:ℝ), (317018441490410878607/35410722656250:ℝ)],
![(8226699968462849384059/371812587890625:ℝ), (58806475557349732040867/1115437763671875:ℝ), (6248107988211109064489/159348251953125:ℝ), (152532590435516739091/17705361328125:ℝ)],
![(15126714708406665790717/2230875527343750:ℝ), (477552200953692175813/35410722656250:ℝ), (7479961996934136267751/1115437763671875:ℝ), (0:ℝ)]]
theorem row200_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (25256490778307421313283/1622270887854080000000000:ℝ) row200_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row200_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row200_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row200_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row200_coefficients]

def row201_coefficients : Fin 3 → Fin 4 → ℝ := ![![(109642979592070190099753/1115437763671875:ℝ), (299185107056521087517627/1115437763671875:ℝ), (7702819812900784077593/31869650390625:ℝ), (80056163629632695297881/1115437763671875:ℝ)],
![(136385090252473733883442/1115437763671875:ℝ), (69904577091352160519486/223087552734375:ℝ), (290213746785514141196974/1115437763671875:ℝ), (77075124513148047482986/1115437763671875:ℝ)],
![(29754332336486648690789/1115437763671875:ℝ), (8477592717389057285909/159348251953125:ℝ), (9863080568777639311858/371812587890625:ℝ), (0:ℝ)]]
theorem row201_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (2091790893041336741624983/136270754579742720000000000:ℝ) row201_coefficients
      (27/64:ℝ) (111/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row201_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row201_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row201_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row201_coefficients]

def row202_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21896232949600842745648/223087552734375:ℝ), (299013291681383284362608/1115437763671875:ℝ), (269739300161118215520256/1115437763671875:ℝ), (80206770870295294885888/1115437763671875:ℝ)],
![(45308375583297028114568/371812587890625:ℝ), (348787007003603254283096/1115437763671875:ℝ), (2763041896978189697024/10623216796875:ℝ), (77256691860918723248128/1115437763671875:ℝ)],
![(29425001118371518430359/1115437763671875:ℝ), (310506675390379033627/5901787109375:ℝ), (29261185551506284550144/1115437763671875:ℝ), (0:ℝ)]]
theorem row202_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (41958941486062931787/2772435599360000000000:ℝ) row202_coefficients
      (27/64:ℝ) (111/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row202_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row202_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row202_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row202_coefficients]

def row203_coefficients : Fin 3 → Fin 4 → ℝ := ![![(49755678917700853062521/2129669788359375000:ℝ), (82196216510176084514059/2129669788359375000:ℝ), (6848616301080038726971/425933957671875000:ℝ), (3363802058379162757/26292219609375000:ℝ)],
![(50041153979653971719033/1064834894179687500:ℝ), (82419395416949260744987/1064834894179687500:ℝ), (272476883917051174129/8518679153437500:ℝ), (537516066519476297/4382036601562500:ℝ)],
![(10069364293253418075109/425933957671875000:ℝ), (16538368139495834188343/425933957671875000:ℝ), (3391672799625114306617/212966978835937500:ℝ), (0:ℝ)]]
theorem row203_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (6235868159633224242203/235258798669824000000000:ℝ) row203_coefficients
      (111/256:ℝ) (225/512:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row203_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row203_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row203_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row203_coefficients]

def row204_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3622973290827224974091/6473251406250000:ℝ), (7170715863745755390161/6473251406250000:ℝ), (3760923713463164054549/6473251406250000:ℝ), (204114023826433638479/6473251406250000:ℝ)],
![(3533896704152477090963/3236625703125000:ℝ), (2294768406183705179851/1078875234375000:ℝ), (3459080852193517111967/3236625703125000:ℝ), (99482692472378663377/3236625703125000:ℝ)],
![(690157113791541437827/1294650281250000:ℝ), (1322985424790865345029/1294650281250000:ℝ), (317345538471536953601/647325140625000:ℝ), (0:ℝ)]]
theorem row204_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (2996778930282232800577/154457794936832000000000:ℝ) row204_coefficients
      (111/256:ℝ) (225/512:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row204_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row204_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row204_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row204_coefficients]

def row205_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2300002475024086990937/1078875234375000:ℝ), (14402858991249056640209/3236625703125000:ℝ), (1673381243116011711697/647325140625000:ℝ), (95502343449351432343/359625078125000:ℝ)],
![(6481482099656041072403/1618312851562500:ℝ), (13123180749415360973537/1618312851562500:ℝ), (471100452762921069041/107887523437500:ℝ), (46690368780360681609/179812539062500:ℝ)],
![(1216710265953305283779/647325140625000:ℝ), (2380748643973768036933/647325140625000:ℝ), (582484880496168876577/323662570312500:ℝ), (0:ℝ)]]
theorem row205_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (10770405455175625918529/617831179747328000000000:ℝ) row205_coefficients
      (111/256:ℝ) (225/512:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row205_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row205_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row205_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row205_coefficients]

def row206_coefficients : Fin 3 → Fin 4 → ℝ := ![![(40630655810249102421889/4461751054687500:ℝ), (89934929096472130632083/4461751054687500:ℝ), (19557418323501709006453/1487250351562500:ℝ), (1872236269348689761833/892350210937500:ℝ)],
![(35923358974491087979417/2230875527343750:ℝ), (75734686473600486708419/2230875527343750:ℝ), (44402708481353781357437/2230875527343750:ℝ), (916897749650501525687/446175105468750:ℝ)],
![(6283263588382423415849/892350210937500:ℝ), (12425408560648666467823/892350210937500:ℝ), (3071771023362027775987/446175105468750:ℝ), (0:ℝ)]]
theorem row206_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (107230367941223812912099/6813537728987136000000000:ℝ) row206_coefficients
      (111/256:ℝ) (225/512:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row206_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row206_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row206_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row206_coefficients]

def row207_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3927680648174244207481/89235021093750:ℝ), (3704740107182837371069/35410722656250:ℝ), (172895168087661416214479/2230875527343750:ℝ), (598177101122689555939/35410722656250:ℝ)],
![(1757449906897607565869/24787505859375:ℝ), (175957252957984504448051/1115437763671875:ℝ), (115341504240442434382637/1115437763671875:ℝ), (293111920251656077757/17705361328125:ℝ)],
![(12149458163476461990073/446175105468750:ℝ), (24161290396981274866271/446175105468750:ℝ), (6006265385366859563099/223087552734375:ℝ), (0:ℝ)]]
theorem row207_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (19846286361972323317063/1297816710283264000000000:ℝ) row207_coefficients
      (111/256:ℝ) (225/512:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row207_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row207_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row207_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row207_coefficients]

def row208_coefficients : Fin 3 → Fin 4 → ℝ := ![![(270186539255758041914233/1115437763671875:ℝ), (98697175116618277922669/159348251953125:ℝ), (63540510728307334799503/123937529296875:ℝ), (21595601415687349593011/159348251953125:ℝ)],
![(386620227352515210824738/1115437763671875:ℝ), (920087276806027889727958/1115437763671875:ℝ), (681658666363835415739402/1115437763671875:ℝ), (148188170793326799336182/1115437763671875:ℝ)],
![(23889181954568054763521/223087552734375:ℝ), (47642484322236726038167/223087552734375:ℝ), (23753651636283124399646/223087552734375:ℝ), (0:ℝ)]]
theorem row208_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (1643198872451107103869771/109016603663794176000000000:ℝ) row208_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row208_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row208_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row208_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row208_coefficients]

def row209_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89754436395315649526644/371812587890625:ℝ), (367697579057338226132/594900140625:ℝ), (571734656343407762776064/1115437763671875:ℝ), (151563304712460874858496/1115437763671875:ℝ)],
![(384376369345597802193892/1115437763671875:ℝ), (183206990810587677770164/223087552734375:ℝ), (32394059834639087017984/53116083984375:ℝ), (148613225703084303220736/1115437763671875:ℝ)],
![(23618819855227100285771/223087552734375:ℝ), (47102807929398176457667/223087552734375:ℝ), (23484337342785529296896/223087552734375:ℝ), (0:ℝ)]]
theorem row209_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (790810572556582033/53230763507712000000:ℝ) row209_coefficients
      (111/256:ℝ) (225/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row209_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row209_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row209_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row209_coefficients]

def row210_coefficients : Fin 3 → Fin 4 → ℝ := ![![(201898516323325045759889/2129669788359375000:ℝ), (332301054164686736539987/2129669788359375000:ℝ), (137200603359774625037807/2129669788359375000:ℝ), (6311487138971410589/26292219609375000:ℝ)],
![(202509851296551283072913/1064834894179687500:ℝ), (332845944725746556933443/1064834894179687500:ℝ), (136914838373014117637897/1064834894179687500:ℝ), (3086390739854552807/13146109804687500:ℝ)],
![(203141378694437520385937/2129669788359375000:ℝ), (333440101660563111292699/2129669788359375000:ℝ), (68334830954321076703381/1064834894179687500:ℝ), (0:ℝ)]]
theorem row210_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (124206132734407800586351/4705175973396480000000000:ℝ) row210_coefficients
      (225/512:ℝ) (453/1024:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row210_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row210_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row210_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row210_coefficients]

def row211_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1577324934093185233147/719250156250000:ℝ), (27638054888840821925929/6473251406250000:ℝ), (13872167931884993169389/6473251406250000:ℝ), (392782131007838341783/6473251406250000:ℝ)],
![(4676567378816375764889/1078875234375000:ℝ), (9033099566549081432371/1078875234375000:ℝ), (532036679877147920699/129465028125000:ℝ), (193816746063081015029/3236625703125000:ℝ)],
![(4623148439179855157437/2157750468750000:ℝ), (26577575061051517704497/6473251406250000:ℝ), (6372941727881951116093/3236625703125000:ℝ), (0:ℝ)]]
theorem row211_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (59542796474636817669757/3089155898736640000000000:ℝ) row211_coefficients
      (225/512:ℝ) (453/1024:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row211_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row211_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row211_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row211_coefficients]

def row212_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25995964142161419591379/3236625703125000:ℝ), (52600249348761302486057/3236625703125000:ℝ), (28284671689132696810477/3236625703125000:ℝ), (184639869232812657311/359625078125000:ℝ)],
![(25200102602382390284363/1618312851562500:ℝ), (50161374289668260908313/1618312851562500:ℝ), (2866817301796493585643/179812539062500:ℝ), (91259131672091294093/179812539062500:ℝ)],
![(8141611872710022074749/1078875234375000:ℝ), (47782739942862394208369/3236625703125000:ℝ), (11688390590429151492061/1618312851562500:ℝ), (0:ℝ)]]
theorem row212_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (213746350280417204454781/12356623594946560000000000:ℝ) row212_coefficients
      (225/512:ℝ) (453/1024:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row212_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row212_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row212_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row212_coefficients]

def row213_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5752440916416802611137/178470042187500:ℝ), (60589084928257624048159/892350210937500:ℝ), (35461618872559180384763/892350210937500:ℝ), (3629150228554319392289/892350210937500:ℝ)],
![(134796940845262123478081/2230875527343750:ℝ), (275730137300573811502187/2230875527343750:ℝ), (149938097867328894728681/2230875527343750:ℝ), (359070945850663268183/89235021093750:ℝ)],
![(125983114583283225220037/4461751054687500:ℝ), (249107448912373992317939/4461751054687500:ℝ), (20525441602213288266317/743625175781250:ℝ), (0:ℝ)]]
theorem row213_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (60756045933762990322301/3893450130849792000000000:ℝ) row213_coefficients
      (225/512:ℝ) (453/1024:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row213_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row213_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row213_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row213_coefficients]

def row214_coefficients : Fin 3 → Fin 4 → ℝ := ![![(316100311753925795169449/2230875527343750:ℝ), (702559253392815163429387/2230875527343750:ℝ), (459584060867864048627927/2230875527343750:ℝ), (1160494420387246910603/35410722656250:ℝ)],
![(93141467255968578047323/371812587890625:ℝ), (118451530289331780639199/223087552734375:ℝ), (349026360094316371124633/1115437763671875:ℝ), (574270579883934755089/17705361328125:ℝ)],
![(34788186740405629617667/318696503906250:ℝ), (161415540773986254258401/743625175781250:ℝ), (120371736390606918350767/1115437763671875:ℝ), (0:ℝ)]]
theorem row214_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (393444243978284725609451/25956334205665280000000000:ℝ) row214_coefficients
      (225/512:ℝ) (453/1024:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row214_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row214_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row214_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row214_coefficients]

def row215_coefficients : Fin 3 → Fin 4 → ℝ := ![![(771178941561530046127889/1115437763671875:ℝ), (1833035593855241373335747/1115437763671875:ℝ), (1355258940136169340565327/1115437763671875:ℝ), (293395302470168950857469/1115437763671875:ℝ)],
![(1246901067509390765876722/1115437763671875:ℝ), (2778746320543161487978918/1115437763671875:ℝ), (364454716054066067528954/223087552734375:ℝ), (290414263353684303042574/1115437763671875:ℝ)],
![(478734347623943824655933/1115437763671875:ℝ), (954716097309403800564731/1115437763671875:ℝ), (52887647611834135170422/123937529296875:ℝ), (0:ℝ)]]
theorem row215_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (32570582146551973126537951/2180332073275883520000000000:ℝ) row215_coefficients
      (225/512:ℝ) (453/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row215_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row215_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row215_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row215_coefficients]

def row216_coefficients : Fin 3 → Fin 4 → ℝ := ![![(766652769501334040519132/1115437763671875:ℝ), (1824885275778339633564476/1115437763671875:ℝ), (193216552006583812907008/159348251953125:ℝ), (294276372396792034803712/1115437763671875:ℝ)],
![(16492389298880193098212/14872503515625:ℝ), (2759756802038766018580652/1115437763671875:ℝ), (604722653964347437293568/371812587890625:ℝ), (291326293387415463165952/1115437763671875:ℝ)],
![(473257467031165089661663/1115437763671875:ℝ), (314594524195662684150397/371812587890625:ℝ), (470533184376870203414528/1115437763671875:ℝ), (0:ℝ)]]
theorem row216_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (93288820334358747317/6336995655680000000000:ℝ) row216_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row216_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row216_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row216_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row216_coefficients]

def row217_coefficients : Fin 3 → Fin 4 → ℝ := ![![(25453767354486713904712/266208723544921875:ℝ), (41863297760616460480997/266208723544921875:ℝ), (138135942333010725962039/2129669788359375000:ℝ), (2011358606815600213/8764073203125000:ℝ)],
![(10213083311688997427536/53241744708984375:ℝ), (83875134754937059551808/266208723544921875:ℝ), (34472691467159690432726/266208723544921875:ℝ), (736921270148061958/3286527451171875:ℝ)],
![(25614173257040773232968/266208723544921875:ℝ), (42017995291040190816536/266208723544921875:ℝ), (17210772240831917583568/266208723544921875:ℝ), (0:ℝ)]]
theorem row217_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1933083946764868902103/73518374584320000000000:ℝ) row217_coefficients
      (453/1024:ℝ) (57/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row217_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row217_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row217_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row217_coefficients]

def row218_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3562982542696012797661/1618312851562500:ℝ), (3465628702598121857437/809156425781250:ℝ), (2778667603099471877437/1294650281250000:ℝ), (382484853244485718333/6473251406250000:ℝ)],
![(1761459168984311171036/404578212890625:ℝ), (680082649554731206672/80915642578125:ℝ), (1667288059291570450237/404578212890625:ℝ), (23583513397675587913/404578212890625:ℝ)],
![(871086374027806595452/404578212890625:ℝ), (185407047876328977156/44953134765625:ℝ), (799968020434954198952/404578212890625:ℝ), (0:ℝ)]]
theorem row218_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (924379869084255186741/48268060917760000000000:ℝ) row218_coefficients
      (453/1024:ℝ) (57/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row218_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row218_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row218_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row218_coefficients]

def row219_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2170700461269169907983/269718808593750:ℝ), (6581681211770289027877/404578212890625:ℝ), (28247490932158220998769/3236625703125000:ℝ), (180396657455552519061/359625078125000:ℝ)],
![(1263656927548885741784/80915642578125:ℝ), (12568703836839111380768/404578212890625:ℝ), (6455729099212020428026/404578212890625:ℝ), (22284381445865306242/44953134765625:ℝ)],
![(3064808265281512002808/404578212890625:ℝ), (5994552714104719212616/404578212890625:ℝ), (977378470799669069936/134859404296875:ℝ), (0:ℝ)]]
theorem row219_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (3314418443176831746613/193072243671040000000000:ℝ) row219_coefficients
      (453/1024:ℝ) (57/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row219_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row219_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row219_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row219_coefficients]

def row220_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3992901611821609863247/123937529296875:ℝ), (75597869809814545472126/1115437763671875:ℝ), (58812226646721306389489/1487250351562500:ℝ), (3552268688458945971371/892350210937500:ℝ)],
![(2498715403029612163312/41312509765625:ℝ), (137884395425529181352128/1115437763671875:ℝ), (74825615843057377018844/1115437763671875:ℝ), (878456979602814815228/223087552734375:ℝ)],
![(3508807258466644502864/123937529296875:ℝ), (62434675353843258268592/1115437763671875:ℝ), (4408940416910122534688/159348251953125:ℝ), (0:ℝ)]]
theorem row220_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (2196562775249385345233/141948702687232000000000:ℝ) row220_coefficients
      (453/1024:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row220_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row220_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row220_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row220_coefficients]

def row221_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22508738916371029302722/159348251953125:ℝ), (23302057842034125717284/74362517578125:ℝ), (455558585720278845444851/2230875527343750:ℝ), (1136587899148492109753/35410722656250:ℝ)],
![(279215250244128083419808/1115437763671875:ℝ), (591050706136323631097728/1115437763671875:ℝ), (347275698407176311021752/1115437763671875:ℝ), (562317319264557354664/17705361328125:ℝ)],
![(40679495176669248468448/371812587890625:ℝ), (242665124916539805244768/1115437763671875:ℝ), (120633812277259459839424/1115437763671875:ℝ), (0:ℝ)]]
theorem row221_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (6094288754388113270003/405567721963520000000000:ℝ) row221_coefficients
      (453/1024:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row221_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row221_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row221_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row221_coefficients]

def row222_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28376576735597906662356/41312509765625:ℝ), (1817015770021002766247768/1115437763671875:ℝ), (89219233414540412147789/74362517578125:ℝ), (287433224237199655227679/1115437763671875:ℝ)],
![(138100307940087093689152/123937529296875:ℝ), (552943482823530329129216/223087552734375:ℝ), (1806281079178896459856496/1115437763671875:ℝ), (284452185120715007412784/1115437763671875:ℝ)],
![(53305269030635940913984/123937529296875:ℝ), (956707014718132565319872/1115437763671875:ℝ), (476966766333136497094016/1115437763671875:ℝ), (0:ℝ)]]
theorem row222_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (168141400637056111829741/11355896214978560000000000:ℝ) row222_coefficients
      (453/1024:ℝ) (57/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row222_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row222_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row222_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row222_coefficients]

def row223_coefficients : Fin 3 → Fin 4 → ℝ := ![![(152326736281840796237971/223087552734375:ℝ), (602970738573701575678589/371812587890625:ℝ), (190808832501569553999872/159348251953125:ℝ), (288376214378038891528192/1115437763671875:ℝ)],
![(410951033154907886445712/371812587890625:ℝ), (2745634774577419540393264/1115437763671875:ℝ), (359644412376534370189312/223087552734375:ℝ), (40775162195523188555776/159348251953125:ℝ)],
![(474200457172004325962176/1115437763671875:ℝ), (945634605182876480792512/1115437763671875:ℝ), (157147106967199851610112/371812587890625:ℝ), (0:ℝ)]]
theorem row223_identity (δ p : ℝ) : rowMargin .newSwitch .C δ p =
    Record12518109.Bernstein.bsum 2 3 (30335377183096665521/2079326699520000000000:ℝ) row223_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_C_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row223_coefficients, Fin.sum_univ_succ, power_newSwitch_C] <;> ring
theorem row223_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .C δ p := by
  rw [row223_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row223_coefficients]

end
end Qrh.JointDetector.FineReturn.FinalEdges
