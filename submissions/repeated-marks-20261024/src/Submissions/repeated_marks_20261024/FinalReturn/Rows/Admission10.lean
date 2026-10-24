/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission10_00_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission10_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]
def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission10_01_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission10_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]
def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission10_02_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission10_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]
def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7627994053862997376/130347805367637:ℝ), (10079921718578044288/130347805367637:ℝ), (274016407190560768/14483089485293:ℝ)],
![(5155670908235008000/130347805367637:ℝ), (5141270908235008000/130347805367637:ℝ), (0:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2688018713602645/2780753181176256:ℝ) admission10_03_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission10_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]
def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(147208313826385931/14483089485293:ℝ), (10112:ℝ), (0:ℝ)],
![(228555636891273616/14483089485293:ℝ), (307274689704077312/14483089485293:ℝ), (79483926687338496/14483089485293:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4599045562719537/29661367265880064:ℝ) admission10_04_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission10_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]
def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93747184838640535421/9051930928308125:ℝ), (51857813895874545704/2468708434993125:ℝ), (288518515305380055856/27155792784924375:ℝ)],
![(0:ℝ), (94214227897167968/217246342279395:ℝ), (88738719779145968/217246342279395:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (80114829066920140809/949163752508162048000:ℝ) admission10_05_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission10_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]
def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(213469343197732507405172765434866304/69850040385988550335877517717:ℝ), (424660484060571095627975323237264000/69850040385988550335877517717:ℝ), (70399335252097773451080852600799232/23283346795329516778625839239:ℝ), (0:ℝ)],
![(21303926816970809005434264077178880/5373080029691426948913655209:ℝ), (47181771092695471047152556356638720/5373080029691426948913655209:ℝ), (132725889517868737513920103822131200/23283346795329516778625839239:ℝ), (6862082353149485658958056870379520/7761115598443172259541946413:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (545650200464396390124129941035/2509699696675518440138195724288:ℝ) admission10_06_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission10_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]
def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2058991350330630043339808041087/48406126393616458999222119:ℝ), (117608739176229140005272430619008/1887838929351041900969662641:ℝ), (4166185580529189302863523696640/209759881039004655663295849:ℝ)],
![(14042645439574602261341094426640/629279643117013966989887547:ℝ), (41943309818899982829680566405120/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (11866576767457814583351507925/26849264772992595924901868672:ℝ) admission10_07_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission10_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]
def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (4141881087375452132933297100453214945404076756183/147487416355550148513254893828125000000000000:ℝ), (6473020463887744813797312323146818676940726991421/113451858735038575779426841406250000000000000:ℝ), (14233868094978500769778413400631282607010811108881/491624721185167161710849646093750000000000000:ℝ)],
![(84165037171492515293028077947577191655695039700427/163874907061722387236949882031250000000000000:ℝ), (2284305353027054318791980495131391495823917415719049/1474874163555501485132548938281250000000000000:ℝ), (2297724682785493922304530714074997258126839142012569/1474874163555501485132548938281250000000000000:ℝ), (256958482743037360065732838808918256738892361199121/491624721185167161710849646093750000000000000:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (3549671532443474968631688786777192500624893846852079/175959341616284276653436886528819200000000000000000000:ℝ) admission10_08_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission10_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]
def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(34718169336293206025644019479384704329881/36871854088887537128313723457031250:ℝ), (90943505870163482643052311407644472216183/36871854088887537128313723457031250:ℝ), (38895925494894034740204225492434460956096/18435927044443768564156861728515625:ℝ), (239633737948078459035572619063290730496/409687267654305968092374705078125:ℝ)],
![(1237527221502149755538490382489206080824/3687185408888753712831372345703125:ℝ), (129984016219989338833824900598478499992/194062389941513353306914333984375:ℝ), (1232116230028607839245815472265479169024/3687185408888753712831372345703125:ℝ), (0:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (118963931193313470868769787935287877/8054779431897778777470560601600000000:ℝ) admission10_09_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission10_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]
def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21206473240172624077389036608/424309262264443359375:ℝ), (18394733877491275793846592064/141436420754814453125:ℝ), (28068981059423365365788465536/254585557358666015625:ℝ), (38412466114744466916490108928/1272927786793330078125:ℝ)],
![(17643841195636670394104424448/254585557358666015625:ℝ), (2869202137193237686869346304/16972370490577734375:ℝ), (3686878802658730761343012864/28287284150962890625:ℝ), (7788020536666681943151345664/254585557358666015625:ℝ)],
![(3498726713294823755628544/185153132624484375:ℝ), (25609583439678640767942656/678894819623109375:ℝ), (38341532472792860991913984/2036684458869328125:ℝ), (0:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4990879522372458229939/1483068363294003200000000:ℝ) admission10_10_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission10_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]
def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5176230590312524501626312262531/145218379180849376997666357:ℝ), (98883332638021640897140493100416/1887838929351041900969662641:ℝ), (3530098434887797782153863524352/209759881039004655663295849:ℝ)],
![(34925065148801530217079885787600/1887838929351041900969662641:ℝ), (34749595875708620437284468377600/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (29146945700407764822936425845/80547794318977787774705606016:ℝ) admission10_11_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission10_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]
def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission10_12_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission10_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]
def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission10_13_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission10_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]
def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission10_14_coefficients (237/512:ℝ) (15/32:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission10_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]
theorem admission10_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (237/512:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission10_00_pos hδ hp
 · exact admission10_01_pos hδ hp
 · exact admission10_02_pos hδ hp
 · exact admission10_03_pos hδ hp
 · exact admission10_04_pos hδ hp
 · exact admission10_05_pos hδ hp
 · exact admission10_06_pos hδ hp
 · exact admission10_07_pos hδ hp
 · exact admission10_08_pos hδ hp
 · exact admission10_09_pos hδ hp
 · exact admission10_10_pos hδ hp
 · exact admission10_11_pos hδ hp
 · exact admission10_12_pos hδ hp
 · exact admission10_13_pos hδ hp
 · exact admission10_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
