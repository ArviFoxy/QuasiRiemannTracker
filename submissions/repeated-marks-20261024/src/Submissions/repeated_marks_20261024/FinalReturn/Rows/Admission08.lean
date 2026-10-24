/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission08_00_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission08_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]
def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission08_01_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission08_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]
def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission08_02_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission08_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]
def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(121927748709111497728/130347805367637:ℝ), (161329591344552248320/130347805367637:ℝ), (4384262515048972288/14483089485293:ℝ)],
![(82444144150018977280/130347805367637:ℝ), (82387444150018977280/130347805367637:ℝ), (0:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (173538414751083835/177968203595280384:ℝ) admission08_03_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission08_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]
def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2331419460329134114/14483089485293:ℝ), (160768:ℝ), (0:ℝ)],
![(277737476158957827/1114083806561:ℝ), (4879318326182886912/14483089485293:ℝ), (1271742826997415936/14483089485293:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9139875358822371/59322734531760128:ℝ) admission08_04_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission08_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]
def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1484684885205074971733/9051930928308125:ℝ), (1797728961611499513026/5431158556984875:ℝ), (348607979328605238937/2088907137301875:ℝ)],
![(0:ℝ), (19155980519183620322/5431158556984875:ℝ), (18616985188815829697/5431158556984875:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (17319953747262366173043/194388736513671587430400:ℝ) admission08_05_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission08_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]
def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(13498265653877671912104880539662629888/69850040385988550335877517717:ℝ), (26960400680108539551374557257776118784/69850040385988550335877517717:ℝ), (345183649025895270818326069695217664/1791026676563808982971218403:ℝ), (0:ℝ)],
![(17478157956725111050548844537906393600/69850040385988550335877517717:ℝ), (2990205138083325318180480481639774720/5373080029691426948913655209:ℝ), (8449031882149551750313547493583093760/23283346795329516778625839239:ℝ), (439173270601567082173315639704289280/7761115598443172259541946413:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20616912167096324736241476730595/95368588473669700725251437522944:ℝ) admission08_06_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission08_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]
def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(429319374584938047606741440917394/629279643117013966989887547:ℝ), (1887132538082096237876746391299072/1887838929351041900969662641:ℝ), (66658969288467028845816379146240/209759881039004655663295849:ℝ)],
![(228442692438597190951758026786735/629279643117013966989887547:ℝ), (684574735258474719755857815969280/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (774717940389745894941662731675/1718352945471526139193719595008:ℝ) admission08_07_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission08_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]
def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (21065046643575191276849626459334048623233407357387/8379966838383531165525846240234375000000000:ℝ), (929097997583438552604809268778027735843013601033467/184359270444437685641568617285156250000000000:ℝ), (51739181921009598949638438993119790137209605741217/20484363382715298404618735253906250000000000:ℝ)],
![(1307472708285852188625666517134633755739799391088939/40968726765430596809237470507812500000000000:ℝ), (36111894881493095254967333469653334082434210275936263/368718540888875371283137234570312500000000000:ℝ), (18463378022088523434036679548573701569617836688154619/184359270444437685641568617285156250000000000:ℝ), (699004820982499890405516906748551721155560405981857/20484363382715298404618735253906250000000000:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (110006161437098540475262764282178410106899215436083229/5630698931721096852909980368922214400000000000000000000:ℝ) admission08_08_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission08_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]
def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1121873538590800867869721226488500229722074/18435927044443768564156861728515625:ℝ), (23467055307052987604111151986841084220388/147487416355550148513254893828125:ℝ), (2501652502769551137746601457357815628998656/18435927044443768564156861728515625:ℝ), (15336559228677021378276647620050606751744/409687267654305968092374705078125:ℝ)],
![(17022367405517698544546249315139669943331/737437081777750742566274469140625:ℝ), (170124119420641446003271270794621180047822/3687185408888753712831372345703125:ℝ), (85012074269997358898497703145995730721792/3687185408888753712831372345703125:ℝ), (0:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (8666769546339203801284935163976400971/515505883641457841758115878502400000000:ℝ) admission08_09_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission08_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]
def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(16174348493897999466691418641408/1272927786793330078125:ℝ), (4659914684321752984390682186752/141436420754814453125:ℝ), (35362082022341389549374743437312/1272927786793330078125:ℝ), (9597210142646737156550022397952/1272927786793330078125:ℝ)],
![(4542846656783633781105845083136/254585557358666015625:ℝ), (22240904130712802692498883584/514314257290234375:ℝ), (8392591935392114450821719498752/254585557358666015625:ℝ), (148168905892868146087739785216/19583504412205078125:ℝ)],
![(28914769582192035841080927488/5657456830192578125:ℝ), (57800507007961670875101854976/5657456830192578125:ℝ), (28885684712488385034020927488/5657456830192578125:ℝ), (0:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (24180978165492787270833411/6074648016052237107200000000:ℝ) admission08_10_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission08_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]
def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1079255234213166983193510585745738/1887838929351041900969662641:ℝ), (1586869041683007537402939739882496/1887838929351041900969662641:ℝ), (56481574958204764514461816389632/209759881039004655663295849:ℝ)],
![(568550118175055013155417392479475/1887838929351041900969662641:ℝ), (567832832697991134618281119731200/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (1904187344545323242661320867995/5155058836414578417581158785024:ℝ) admission08_11_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission08_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]
def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission08_12_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission08_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]
def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission08_13_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission08_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]
def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission08_14_coefficients (471/1024:ℝ) (945/2048:ℝ) (255/512:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission08_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]
theorem admission08_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (945/2048:ℝ))
 (hp : p ∈ Set.Icc (255/512:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission08_00_pos hδ hp
 · exact admission08_01_pos hδ hp
 · exact admission08_02_pos hδ hp
 · exact admission08_03_pos hδ hp
 · exact admission08_04_pos hδ hp
 · exact admission08_05_pos hδ hp
 · exact admission08_06_pos hδ hp
 · exact admission08_07_pos hδ hp
 · exact admission08_08_pos hδ hp
 · exact admission08_09_pos hδ hp
 · exact admission08_10_pos hδ hp
 · exact admission08_11_pos hδ hp
 · exact admission08_12_pos hδ hp
 · exact admission08_13_pos hδ hp
 · exact admission08_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
