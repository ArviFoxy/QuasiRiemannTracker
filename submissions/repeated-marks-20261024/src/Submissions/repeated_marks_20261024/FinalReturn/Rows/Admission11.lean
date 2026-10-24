/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission11_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission11_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission11_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission11_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_00_coefficients]
def admission11_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission11_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission11_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission11_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_01_coefficients]
def admission11_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission11_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission11_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission11_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_02_coefficients]
def admission11_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(25213876884704128/6860410808823:ℝ), (629597889854068864/130347805367637:ℝ), (17126025449410048/14483089485293:ℝ)],
![(24886197041265568/10026754259049:ℝ), (319740561536452384/130347805367637:ℝ), (0:ℝ)]]
theorem admission11_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (950093767118879/1011182974973184:ℝ) admission11_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission11_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_03_coefficients]
def admission11_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9460395739221220/14483089485293:ℝ), (640:ℝ), (0:ℝ)],
![(14901160944140937/14483089485293:ℝ), (19668126970034208/14483089485293:ℝ), (4967745417958656/14483089485293:ℝ)]]
theorem admission11_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (291078833083515/1853835454117504:ℝ) admission11_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission11_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_04_coefficients]
def admission11_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(554527192882460053/822902811664375:ℝ), (37591507828721269498/27155792784924375:ℝ), (77412958845797167/109942480910625:ℝ)],
![(0:ℝ), (1961529986722821508/27155792784924375:ℝ), (1781864876600224633/27155792784924375:ℝ)]]
theorem admission11_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6245834870062070787/91265745433477120000:ℝ) admission11_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission11_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_05_coefficients]
def admission11_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(267005187744559021798092976900480/5373080029691426948913655209:ℝ), (6795914571384366324767283324177280/69850040385988550335877517717:ℝ), (100805608436822963896729534074880/2116667890484501525329621749:ℝ), (0:ℝ)],
![(122904301191589309588562391220576/1887838929351041900969662641:ℝ), (9908644993123992111681475229660896/69850040385988550335877517717:ℝ), (2109330341680798594418547833965568/23283346795329516778625839239:ℝ), (107220036767960713421219638599680/7761115598443172259541946413:ℝ)]]
theorem admission11_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (655321828710891843802120619275/2980268389802178147664107422592:ℝ) admission11_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission11_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_06_coefficients]
def admission11_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(556788097520541544255716299820/209759881039004655663295849:ℝ), (7308415641776586892576499559040/1887838929351041900969662641:ℝ), (260386598783074331428970231040/209759881039004655663295849:ℝ)],
![(277347116675772892002169535787/209759881039004655663295849:ℝ), (2452934636730311495842925981728/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission11_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (44414901615342106011972786805/107397059091970383699607474688:ℝ) admission11_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission11_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_07_coefficients]
def admission11_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (2563489472082616196775798359034867751607888893/147487416355550148513254893828125000000000000:ℝ), (1745553715520449597852447550724376151832175613/15524991195321068264553146718750000000000000:ℝ), (805386000385310979861354681618410969896835117/8938631294275766576560902656250000000000000:ℝ)],
![(5892559750741996928546852924383048715290326937899/655499628246889548947799528125000000000000000:ℝ), (30283863651110243541707870775908124926535354871727/1179899330844401188106039150625000000000000000:ℝ), (36114844345509188929138062665328286980449633434171/1474874163555501485132548938281250000000000000:ℝ), (767373666779422356078332480898699314830995030319/98324944237033432342169929218750000000000000:ℝ)]]
theorem admission11_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (228082342566171102770491211037795885270891752981/10574479664440160856576735969280000000000000000000:ℝ) admission11_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission11_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_08_coefficients]
def admission11_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(106557173677093859969883175166660262209/7374370817777507425662744691406250:ℝ), (55976242357160381936601627041252129429/1474874163555501485132548938281250:ℝ), (10940663571912963399440733220133989904/335198673535341246621033849609375:ℝ), (3744277155438725922430822172863917664/409687267654305968092374705078125:ℝ)],
![(584507753036504130377366697418789505413/147487416355550148513254893828125000:ℝ), (12239374007780006262446687192374435411/1552499119532106826455314671875000:ℝ), (72209722860959764055276548923064529204/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission11_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (120563697627193431971975183871616427/14645053512541415959037382912000000000:ℝ) admission11_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission11_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_09_coefficients]
def admission11_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(255336250729727421221755648/1272927786793330078125:ℝ), (223233171741776197628075648/424309262264443359375:ℝ), (30245765762451291294904576/66996199304912109375:ℝ), (12334930576228720226208896/97917522061025390625:ℝ)],
![(339817318911594244496447296/1272927786793330078125:ℝ), (282055929403441134840717056/424309262264443359375:ℝ), (674848481923904754204960448/1272927786793330078125:ℝ), (168598418875175594179256576/1272927786793330078125:ℝ)],
![(25020673697504411192734552/424309262264443359375:ℝ), (16602068897722897483906368/141436420754814453125:ℝ), (24767961901914281258984552/424309262264443359375:ℝ), (0:ℝ)]]
theorem admission11_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (743585422300753894001259/593227345317601280000000000:ℝ) admission11_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission11_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_10_coefficients]
def admission11_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4201397430129402474740681858548/1887838929351041900969662641:ℝ), (6143210481480561282253375738496/1887838929351041900969662641:ℝ), (220631152180487361384616470272/209759881039004655663295849:ℝ)],
![(2064644149983403243416592683325/1887838929351041900969662641:ℝ), (2023858508648623682058658952480/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission11_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (108831218857785800493067780597/322191177275911151098822424064:ℝ) admission11_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission11_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_11_coefficients]
def admission11_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission11_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission11_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_12_coefficients]
def admission11_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission11_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission11_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_13_coefficients]
def admission11_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission11_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission11_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission11_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission11_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission11_14_coefficients]
theorem admission11_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission11_00_pos hδ hp
 · exact admission11_01_pos hδ hp
 · exact admission11_02_pos hδ hp
 · exact admission11_03_pos hδ hp
 · exact admission11_04_pos hδ hp
 · exact admission11_05_pos hδ hp
 · exact admission11_06_pos hδ hp
 · exact admission11_07_pos hδ hp
 · exact admission11_08_pos hδ hp
 · exact admission11_09_pos hδ hp
 · exact admission11_10_pos hδ hp
 · exact admission11_11_pos hδ hp
 · exact admission11_12_pos hδ hp
 · exact admission11_13_pos hδ hp
 · exact admission11_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
