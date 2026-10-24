/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission07_00_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission07_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]
def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission07_01_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission07_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]
def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission07_02_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission07_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]
def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30521129100929644288/130347805367637:ℝ), (3104447673829987072/10026754259049:ℝ), (1096065628762243072/14483089485293:ℝ)],
![(20644007480243571712/130347805367637:ℝ), (20615927480243571712/130347805367637:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (21805193124924071/22246025449410048:ℝ) admission07_03_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission07_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]
def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(576170933908337415/14483089485293:ℝ), (39680:ℝ), (0:ℝ)],
![(897823872489358092/14483089485293:ℝ), (1214268075183369216/14483089485293:ℝ), (317935706749353984/14483089485293:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9023443825588965/59322734531760128:ℝ) admission07_04_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission07_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]
def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(372442301405460807621/9051930928308125:ℝ), (203715397862999078696/2468708434993125:ℝ), (1122216372654273989668/27155792784924375:ℝ)],
![(0:ℝ), (13846326426094612744/27155792784924375:ℝ), (1137424665666068204/2468708434993125:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (13947134114153374573303/151866200401305927680000:ℝ) admission07_05_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission07_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]
def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1678097505680433846798859049556302080/69850040385988550335877517717:ℝ), (3347226811488706101419196894010497280/69850040385988550335877517717:ℝ), (556380924967675070022045948151398400/23283346795329516778625839239:ℝ), (0:ℝ)],
![(167616935017188472889883068617016320/5373080029691426948913655209:ℝ), (4843102990036969951727018798465053696/69850040385988550335877517717:ℝ), (1052722106744140409995893000370388992/23283346795329516778625839239:ℝ), (54896658825195885271664454963036160/7761115598443172259541946413:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20381321265994848559290554673125/95368588473669700725251437522944:ℝ) admission07_06_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission07_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]
def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(324880898310357448653024326084525/1887838929351041900969662641:ℝ), (36498422319364542951183103732480/145218379180849376997666357:ℝ), (16664742322116757211454094786560/209759881039004655663295849:ℝ)],
![(173547072384094822845431518278404/1887838929351041900969662641:ℝ), (173165950538029929111109767015424/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (97984019594151668988245308295/214794118183940767399214949376:ℝ) admission07_07_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission07_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]
def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (11556788793525492455217100968207208154981153350177/24581236059258358085542482304687500000000000:ℝ), (139034139746035787250206322921068954043275151475337/147487416355550148513254893828125000000000000:ℝ), (2787509854831422053373464553123923897882404254971/5899496654222005940530195753125000000000000:ℝ)],
![(330117840966436791817384953097444644944077019269771/81937453530861193618474941015625000000000000:ℝ), (3067087523767166928077693896531945196286488193907627/245812360592583580855424823046875000000000000:ℝ), (9491364595905144883028542579702687535243463041249197/737437081777750742566274469140625000000000000:ℝ), (652226821526126813644627234807986835363575826590851/147487416355550148513254893828125000000000000:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3057888190149553462972366816817157969663307018237721/168920967951632905587299411067666432000000000000000000:ℝ) admission07_08_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission07_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]
def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28677745497607648431027307605192071469512/3687185408888753712831372345703125:ℝ), (74581194899158938238733253318375323098567/3687185408888753712831372345703125:ℝ), (63156976124055424162341587726045897115392/3687185408888753712831372345703125:ℝ), (1917069903584627672284580952506325843968/409687267654305968092374705078125:ℝ)],
![(55575144980805107587118274062792108994592/18435927044443768564156861728515625:ℝ), (111016945082444016813535486626426300597308/18435927044443768564156861728515625:ℝ), (5040116795391888250599830164693111878656/1675993367676706233105169248046875:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5811635197699680500434460253529491923/322191177275911151098822424064000000000:ℝ) admission07_09_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission07_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]
def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(78002856909263822964807857792/97917522061025390625:ℝ), (2612224523296194969827665359488/1272927786793330078125:ℝ), (2183236321732414695190074265088/1272927786793330078125:ℝ), (585051809994930673904911056896/1272927786793330078125:ℝ)],
![(1438641402515303278279429010432/1272927786793330078125:ℝ), (266522086511570620260915540992/97917522061025390625:ℝ), (237764804013409727401047003136/115720707890302734375:ℝ), (589272902543642216299044012032/1272927786793330078125:ℝ)],
![(3592391594468518446812096512/10879724673447265625:ℝ), (21532125049979989068232579072/32639174020341796875:ℝ), (10754875679074433727796289536/32639174020341796875:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (792131825126934782245983/182531490866954240000000000:ℝ) admission07_10_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission07_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]
def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(30263102603666651632787467906683/209759881039004655663295849:ℝ), (30698855396775578913467758469888/145218379180849376997666357:ℝ), (14120393739551191128615454097408/209759881039004655663295849:ℝ)],
![(16010818692381708432420471232540/209759881039004655663295849:ℝ), (143734102977495764797829723786240/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (240932129547107377382169329543/644382354551822302197644848128:ℝ) admission07_11_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission07_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]
def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission07_12_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission07_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]
def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission07_13_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission07_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]
def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients (465/1024:ℝ) (117/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission07_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]
theorem admission07_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission07_00_pos hδ hp
 · exact admission07_01_pos hδ hp
 · exact admission07_02_pos hδ hp
 · exact admission07_03_pos hδ hp
 · exact admission07_04_pos hδ hp
 · exact admission07_05_pos hδ hp
 · exact admission07_06_pos hδ hp
 · exact admission07_07_pos hδ hp
 · exact admission07_08_pos hδ hp
 · exact admission07_09_pos hδ hp
 · exact admission07_10_pos hδ hp
 · exact admission07_11_pos hδ hp
 · exact admission07_12_pos hδ hp
 · exact admission07_13_pos hδ hp
 · exact admission07_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
