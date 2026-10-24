/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission09_00_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission09_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]
def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission09_01_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission09_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]
def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission09_02_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission09_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]
def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(488003265614874308608/130347805367637:ℝ), (49671162781279793152/10026754259049:ℝ), (17537050060195889152/14483089485293:ℝ)],
![(330119151225807766528/130347805367637:ℝ), (330007371225807766528/130347805367637:ℝ), (0:ℝ)]]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (349786220247093869/355936407190560768:ℝ) admission09_03_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission09_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]
def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9200951624950464540/14483089485293:ℝ), (634880:ℝ), (0:ℝ)],
![(14302763177496500001/14483089485293:ℝ), (19383797152035087360/14483089485293:ℝ), (5086971307989663744/14483089485293:ℝ)]]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9023443825588965/59322734531760128:ℝ) admission09_04_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission09_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]
def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1185715891093639555761/1810386185661625:ℝ), (7127819886167356823342/5431158556984875:ℝ), (3569611333188571393559/5431158556984875:ℝ)],
![(0:ℝ), (98094398602469358886/27155792784924375:ℝ), (4883233927984270369/1429252251838125:ℝ)]]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (144977604976287782765461/1555109892109372699443200:ℝ) admission09_05_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission09_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]
def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(106968251657095116166606761326702202880/69850040385988550335877517717:ℝ), (213793335374509717789056383371770695680/69850040385988550335877517717:ℝ), (35608379197931204481410940681689497600/23283346795329516778625839239:ℝ), (0:ℝ)],
![(10669069449597699101431398526804716544/5373080029691426948913655209:ℝ), (308872957554698678152462508973427391488/69850040385988550335877517717:ℝ), (67265194718839272358351538061224968192/23283346795329516778625839239:ℝ), (3513386164812536657386525117634314240/7761115598443172259541946413:ℝ)]]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20381321265994848559290554673125/95368588473669700725251437522944:ℝ) admission09_06_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission09_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]
def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5193485304273688716159619249656500/1887838929351041900969662641:ℝ), (583974757109832687218929659719680/145218379180849376997666357:ℝ), (266635877153868115383265516584960/209759881039004655663295849:ℝ)],
![(253487884674076488041948456328961/171621720850094718269969331:ℝ), (2786833342395768859154918776431616/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1576898529869894160776224667405/3436705890943052278387439190016:ℝ) admission09_07_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission09_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]
def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (15524487068990802091943841327072576726268928016307/512109084567882460115468381347656250000000:ℝ), (111844294465135974086460683337761620215988887722053/1843592704444376856415686172851562500000000:ℝ), (279779289930321112481172496980569818090521703066739/9217963522221884282078430864257812500000000:ℝ)],
![(1040795875065171683838738905987149579672778838339839/4096872676543059680923747050781250000000000:ℝ), (16207034753483698984025627906796087019395443333284547/20484363382715298404618735253906250000000000:ℝ), (37806559640793722102902105992636376476670016886669757/46089817611109421410392154321289062500000000:ℝ), (2609935590551686161722334980900124769756584583933043/9217963522221884282078430864257812500000000:ℝ)]]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (18882021527997424980512119897664741331855923189072257/1039513648933125572844919452724101120000000000000000000:ℝ) admission09_08_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission09_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]
def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1834031614136354602186062228284142121175156/3687185408888753712831372345703125:ℝ), (4771846231250186268123707560346212998872176/3687185408888753712831372345703125:ℝ), (4042046471939547146389861614466937415385088/3687185408888753712831372345703125:ℝ), (122692473829416171026213180960404854013952/409687267654305968092374705078125:ℝ)],
![(4289165803834873468520883335974625110307/21817665141353572265274392578125:ℝ), (7246469006273045754472315889041994015212436/18435927044443768564156861728515625:ℝ), (278624757733375908820266660845847040724992/1418148234187982197242835517578125:ℝ), (0:ℝ)]]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (96145397013096313004002370264825801297/5155058836414578417581158785024000000000:ℝ) admission09_09_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission09_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]
def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(258609543757162627264055023345664/1272927786793330078125:ℝ), (666123925171065804433709749870592/1272927786793330078125:ℝ), (556477149055440313549638429704192/1272927786793330078125:ℝ), (13542073962668148761816700289024/115720707890302734375:ℝ)],
![(367977542682904095331691832455168/1272927786793330078125:ℝ), (885072648919830444693559877218304/1272927786793330078125:ℝ), (666327977705549774455076257071104/1272927786793330078125:ℝ), (149232963512467175093208212307968/1272927786793330078125:ℝ)],
![(12121853163243164936032146909696/141436420754814453125:ℝ), (24237325994837248246841533819392/141436420754814453125:ℝ), (12115467709799552060809386909696/141436420754814453125:ℝ), (0:ℝ)]]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (2743534126217038911278396859/607464801605223710720000000000:ℝ) admission09_10_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission09_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]
def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1451163537252487042463616707807684/629279643117013966989887547:ℝ), (491181686348409262615484135518208/145218379180849376997666357:ℝ), (225926299832819058057847265558528/209759881039004655663295849:ℝ)],
![(70164094306378481028422483712085/57207240283364906089989777:ℝ), (2313952806063916085911351131407360/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (3878183764585253814510743041037/10310117672829156835162317570048:ℝ) admission09_11_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission09_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]
def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission09_12_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission09_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]
def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission09_13_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission09_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]
def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission09_14_coefficients (465/1024:ℝ) (1863/4096:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission09_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]
theorem admission09_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (465/1024:ℝ) (1863/4096:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission09_00_pos hδ hp
 · exact admission09_01_pos hδ hp
 · exact admission09_02_pos hδ hp
 · exact admission09_03_pos hδ hp
 · exact admission09_04_pos hδ hp
 · exact admission09_05_pos hδ hp
 · exact admission09_06_pos hδ hp
 · exact admission09_07_pos hδ hp
 · exact admission09_08_pos hδ hp
 · exact admission09_09_pos hδ hp
 · exact admission09_10_pos hδ hp
 · exact admission09_11_pos hδ hp
 · exact admission09_12_pos hδ hp
 · exact admission09_13_pos hδ hp
 · exact admission09_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
