/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission06_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission06_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission06_00_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission06_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_00_coefficients]
def admission06_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission06_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission06_01_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission06_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_01_coefficients]
def admission06_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission06_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission06_02_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission06_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_02_coefficients]
def admission06_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30508598139103759360/130347805367637:ℝ), (40345108797963947008/130347805367637:ℝ), (1096065628762243072/14483089485293:ℝ)],
![(20631476518417686784/130347805367637:ℝ), (20603216518417686784/130347805367637:ℝ), (0:ℝ)]]
theorem admission06_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (7901793553053943/8089463799785472:ℝ) admission06_03_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission06_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_03_coefficients]
def admission06_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(44606781980000316/1114083806561:ℝ), (39936:ℝ), (0:ℝ)],
![(901541104321024785/14483089485293:ℝ), (1217975746091604224/14483089485293:ℝ), (317935706749353984/14483089485293:ℝ)]]
theorem admission06_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (174647299850109/1140821817918464:ℝ) admission06_04_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission06_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_04_coefficients]
def admission06_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(372442301405460807621/9051930928308125:ℝ), (449700026971771891694/5431158556984875:ℝ), (1129838575538709173107/27155792784924375:ℝ)],
![(0:ℝ), (1952462253814927778/2468708434993125:ℝ), (81513660756121189/109942480910625:ℝ)]]
theorem admission06_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (54671209552397115870349/607464801605223710720000:ℝ) admission06_05_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission06_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_05_coefficients]
def admission06_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1684950225796687180123499797353886720/69850040385988550335877517717:ℝ), (3360893201756681049392078514463077376/69850040385988550335877517717:ℝ), (558652177317377442550912905703063552/23283346795329516778625839239:ℝ), (0:ℝ)],
![(198715715939973043717556421801708800/6350003671453504575988865247:ℝ), (4856769380304944899699900418917633792/69850040385988550335877517717:ℝ), (1054993359093842782524759957922054144/23283346795329516778625839239:ℝ), (54896658825195885271664454963036160/7761115598443172259541946413:ℝ)]]
theorem admission06_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5124779179136396661941503925465/23842147118417425181312859380736:ℝ) admission06_06_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission06_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_06_coefficients]
def admission06_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(323529753283145637748518371357444/1887838929351041900969662641:ℝ), (473131312336131558917283473173504/1887838929351041900969662641:ℝ), (16664742322116757211454094786560/209759881039004655663295849:ℝ)],
![(172195927356883011940925563551323/1887838929351041900969662641:ℝ), (171817772722422429663012891666688/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission06_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (388884672922117523631547988285/859176472735763069596859797504:ℝ) admission06_07_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission06_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_07_coefficients]
def admission06_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (12003369383654475215153664831867923973724377559961/30726545074072947606928102880859375000000000:ℝ), (28909144490567575197957442303584106087669176048269/36871854088887537128313723457031250000000000:ℝ), (72518384733175735466667899040733093080296489881579/184359270444437685641568617285156250000000000:ℝ)],
![(330117840966436791817384953097444644944077019269771/81937453530861193618474941015625000000000000:ℝ), (609509318180229561049350441100963301305294336177109/49162472118516716171084964609375000000000000:ℝ), (213054017886052669334924086617477838335919791019043/16759933676767062331051692480468750000000000:ℝ), (61591709898257870258040859635814924267380087704023/14181482341879821972428355175781250000000000:ℝ)]]
theorem admission06_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1044977175295220627640337302609288829553675903018039/55566107878826613680032701009100800000000000000000000:ℝ) admission06_08_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission06_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_08_coefficients]
def admission06_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10911022357085642526148032071198213228704/1418148234187982197242835517578125:ℝ), (369821382066368752571953915214780289532988/18435927044443768564156861728515625:ℝ), (314245721733235506515016560399978219600896/18435927044443768564156861728515625:ℝ), (1917069903584627672284580952506325843968/409687267654305968092374705078125:ℝ)],
![(54029708134880218271906152962408523620184/18435927044443768564156861728515625:ℝ), (107932352653018078191823135249329974637461/18435927044443768564156861728515625:ℝ), (53902125862269156459906753581372964689152/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission06_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (183417048271335374678133655190082569/10650948009121029788390823936000000000:ℝ) admission06_09_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission06_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_09_coefficients]
def admission06_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1013803811645170416970192259072/1272927786793330078125:ℝ), (291137206914031205526733498368/141436420754814453125:ℝ), (244435792973440465718176243712/141436420754814453125:ℝ), (53953999553850341699379724288/115720707890302734375:ℝ)],
![(285917170776134174442997218304/254585557358666015625:ℝ), (181852018615820146495339058176/66996199304912109375:ℝ), (2623311732342227212283765936128/1272927786793330078125:ℝ), (597715087641065301087309922304/1272927786793330078125:ℝ)],
![(137162532031147844594960755072/424309262264443359375:ℝ), (822143767069298413767674530432/1272927786793330078125:ℝ), (410653224650073629982792265216/1272927786793330078125:ℝ), (0:ℝ)]]
theorem admission06_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (155707419945427798496636251/37966550100326481920000000000:ℝ) admission06_10_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission06_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_10_coefficients]
def admission06_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30131212431932899561035925329948/209759881039004655663295849:ℝ), (397901190289417205112907897539584/1887838929351041900969662641:ℝ), (14120393739551191128615454097408/209759881039004655663295849:ℝ)],
![(15878928520647956360668928655805/209759881039004655663295849:ℝ), (142550173108830444035656761217280/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission06_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (955971954244584250729999395389/2577529418207289208790579392512:ℝ) admission06_11_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission06_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_11_coefficients]
def admission06_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission06_12_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission06_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_12_coefficients]
def admission06_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission06_13_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission06_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_13_coefficients]
def admission06_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission06_14_coefficients (117/256:ℝ) (471/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission06_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_14_coefficients]
theorem admission06_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (471/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission06_00_pos hδ hp
 · exact admission06_01_pos hδ hp
 · exact admission06_02_pos hδ hp
 · exact admission06_03_pos hδ hp
 · exact admission06_04_pos hδ hp
 · exact admission06_05_pos hδ hp
 · exact admission06_06_pos hδ hp
 · exact admission06_07_pos hδ hp
 · exact admission06_08_pos hδ hp
 · exact admission06_09_pos hδ hp
 · exact admission06_10_pos hδ hp
 · exact admission06_11_pos hδ hp
 · exact admission06_12_pos hδ hp
 · exact admission06_13_pos hδ hp
 · exact admission06_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
