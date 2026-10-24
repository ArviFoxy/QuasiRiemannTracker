/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission03_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission03_00_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission03_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_00_coefficients]
def admission03_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission03_01_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission03_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_01_coefficients]
def admission03_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission03_02_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission03_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_02_coefficients]
def admission03_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(480472531037614048/130347805367637:ℝ), (631186760082304480/130347805367637:ℝ), (17126025449410048/14483089485293:ℝ)],
![(324929431764688000/130347805367637:ℝ), (321329431764688000/130347805367637:ℝ), (0:ℝ)]]
theorem admission03_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2688018713602645/2780753181176256:ℝ) admission03_03_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission03_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_03_coefficients]
def admission03_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(473019786961061/762267867647:ℝ), (608:ℝ), (0:ℝ)],
![(14428141157179876/14483089485293:ℝ), (19204668106504832/14483089485293:ℝ), (4967745417958656/14483089485293:ℝ)]]
theorem admission03_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (58215766616703/390281148235264:ℝ) admission03_04_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission03_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_04_coefficients]
def admission03_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(554527192882460053/822902811664375:ℝ), (7324538188095470798/5431158556984875:ℝ), (18160739428102394116/27155792784924375:ℝ)],
![(0:ℝ), (7941704787831248/217246342279395:ℝ), (6572827758325748/217246342279395:ℝ)]]
theorem admission03_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4974762533796405099/59322734531760128000:ℝ) admission03_05_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission03_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_05_coefficients]
def admission03_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3359656068181376532764585671648288/69850040385988550335877517717:ℝ), (6578125142379679800226021660885024/69850040385988550335877517717:ℝ), (1073373374840953032100478663078912/23283346795329516778625839239:ℝ), (0:ℝ)],
![(4436047771590913704166185447103360/69850040385988550335877517717:ℝ), (745450428009177352856939505105280/5373080029691426948913655209:ℝ), (2073842023716699023655001622220800/23283346795329516778625839239:ℝ), (107220036767960713421219638599680/7761115598443172259541946413:ℝ)]]
theorem admission03_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2503491864292829286733021448365/11921073559208712590656429690368:ℝ) admission03_06_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission03_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_06_coefficients]
def admission03_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(575842479582235865080292832813/209759881039004655663295849:ℝ), (7476937868727524323588608977632/1887838929351041900969662641:ℝ), (260386598783074331428970231040/209759881039004655663295849:ℝ)],
![(296401498737467212826746068780/209759881039004655663295849:ℝ), (2621456863681248926855035400320/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission03_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (11866576767457814583351507925/26849264772992595924901868672:ℝ) admission03_07_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission03_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_07_coefficients]
def admission03_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (3942437086124654328983869473762240050145342038039/2949748327111002970265097876562500000000000000:ℝ), (15966356711792703048580638435579693266432747052469/5899496654222005940530195753125000000000000000:ℝ), (2684575756807080495212905215087260676005687658797/1966498884740668646843398584375000000000000000:ℝ)],
![(5892559750741996928546852924383048715290326937899/655499628246889548947799528125000000000000000:ℝ), (12246280988378247824510466222515670001761780221461/453807434940154303117707365625000000000000000:ℝ), (159762423681931687917948959027617578250535054056213/5899496654222005940530195753125000000000000000:ℝ), (17854864172310759201210056803105196559248284539437/1966498884740668646843398584375000000000000000:ℝ)]]
theorem admission03_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (41623729814978495934687156096677784024560874961363/2749364712754441822709951352012800000000000000000000:ℝ) admission03_08_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission03_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_08_coefficients]
def admission03_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2329839418089308936342864327016610623907/147487416355550148513254893828125000:ℝ), (1197737722563830359232520435656364688927/29497483271110029702650978765625000:ℝ), (625785854065238210355043111955045475596/18435927044443768564156861728515625:ℝ), (3744277155438725922430822172863917664/409687267654305968092374705078125:ℝ)],
![(3560016807199708487829852368646340387/670397347070682493242067699218750:ℝ), (77690245392110709871743737871609093289/7374370817777507425662744691406250:ℝ), (19251816094196997488215866754148112016/3687185408888753712831372345703125:ℝ), (0:ℝ)]]
theorem admission03_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (118963931193313470868769787935287877/8054779431897778777470560601600000000:ℝ) admission03_09_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission03_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_09_coefficients]
def admission03_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28490920966362340725735112/141436420754814453125:ℝ), (16790225950955219257067072/32639174020341796875:ℝ), (542222827331311384957633592/1272927786793330078125:ℝ), (143865454722568900463633792/1272927786793330078125:ℝ)],
![(2886555912202949716073152/10183422294346640625:ℝ), (58033712516343385958030848/84861852452888671875:ℝ), (44113675405103547104232896/84861852452888671875:ℝ), (30421955221354226340434944/254585557358666015625:ℝ)],
![(151971445182006493249664/2036684458869328125:ℝ), (33535506267094845166592/226298273207703125:ℝ), (149771611221847113249664/2036684458869328125:ℝ), (0:ℝ)]]
theorem admission03_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4990879522372458229939/1483068363294003200000000:ℝ) admission03_10_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission03_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_10_coefficients]
def admission03_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4352470340651015453603222801323/1887838929351041900969662641:ℝ), (6291201715063726377524996059616/1887838929351041900969662641:ℝ), (220631152180487361384616470272/209759881039004655663295849:ℝ)],
![(2215717060505016222279133626100/1887838929351041900969662641:ℝ), (2171849742231788777330279273600/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission03_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (29146945700407764822936425845/80547794318977787774705606016:ℝ) admission03_11_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission03_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_11_coefficients]
def admission03_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission03_12_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission03_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_12_coefficients]
def admission03_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission03_13_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission03_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_13_coefficients]
def admission03_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission03_14_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission03_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_14_coefficients]
theorem admission03_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission03_00_pos hδ hp
 · exact admission03_01_pos hδ hp
 · exact admission03_02_pos hδ hp
 · exact admission03_03_pos hδ hp
 · exact admission03_04_pos hδ hp
 · exact admission03_05_pos hδ hp
 · exact admission03_06_pos hδ hp
 · exact admission03_07_pos hδ hp
 · exact admission03_08_pos hδ hp
 · exact admission03_09_pos hδ hp
 · exact admission03_10_pos hδ hp
 · exact admission03_11_pos hδ hp
 · exact admission03_12_pos hδ hp
 · exact admission03_13_pos hδ hp
 · exact admission03_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
