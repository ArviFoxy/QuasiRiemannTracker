/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission03_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission03_00_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission03_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_00_coefficients]
def admission03_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission03_01_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission03_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_01_coefficients]
def admission03_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission03_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission03_02_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission03_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_02_coefficients]
def admission03_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1915050124150456192/130347805367637:ℝ), (2524747040329217920/130347805367637:ℝ), (68504101797640192/14483089485293:ℝ)],
![(1295515467515223232/130347805367637:ℝ), (1288495467515223232/130347805367637:ℝ), (0:ℝ)]]
theorem admission03_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (21805193124924071/22246025449410048:ℝ) admission03_03_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission03_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_03_coefficients]
def admission03_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1872957300980874/762267867647:ℝ), (2432:ℝ), (0:ℝ)],
![(56393649040961667/14483089485293:ℝ), (75891754698960576/14483089485293:ℝ), (19870981671834624/14483089485293:ℝ)]]
theorem admission03_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (58215766616703/390281148235264:ℝ) admission03_04_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission03_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_04_coefficients]
def admission03_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(250064951457653703/95283483455875:ℝ), (12907490052980678198/2468708434993125:ℝ), (70388771122848598573/27155792784924375:ℝ)],
![(0:ℝ), (1365891065543861734/27155792784924375:ℝ), (1032227289601896109/27155792784924375:ℝ)]]
theorem admission03_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (174171829941879074039/1898327505016324096000:ℝ) admission03_05_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission03_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_05_coefficients]
def admission03_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(26315802670167830858584086643540096/69850040385988550335877517717:ℝ), (52073461565701591971315574557433984/69850040385988550335877517717:ℝ), (8586986998727624256803829304631296/23283346795329516778625839239:ℝ), (0:ℝ)],
![(34471311072855878212354423949301568/69850040385988550335877517717:ℝ), (76094428181159673968544094362486592/69850040385988550335877517717:ℝ), (16448782917877193906185828130787328/23283346795329516778625839239:ℝ), (857760294143685707369757108797440/7761115598443172259541946413:ℝ)]]
theorem admission03_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2503491864292829286733021448365/11921073559208712590656429690368:ℝ) admission03_06_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission03_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_06_coefficients]
def admission03_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20632081591839956252901024787178/1887838929351041900969662641:ℝ), (29907751474910097294354435910528/1887838929351041900969662641:ℝ), (1041546395132297325715880924160/209759881039004655663295849:ℝ)],
![(10918152370143094003024798254209/1887838929351041900969662641:ℝ), (10822871908626870569444360438464/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission03_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (97984019594151668988245308295/214794118183940767399214949376:ℝ) admission03_07_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission03_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_07_coefficients]
def admission03_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (2686888695900593237294087201986713270849437658797/245812360592583580855424823046875000000000000:ℝ), (32397639814417975222712931200181145608857130805877/1474874163555501485132548938281250000000000000:ℝ), (3252486000890667869292263213372830082939600970619/294974832711100297026509787656250000000000000:ℝ)],
![(4373963873888843404499441929119092899933949987663/65549962824688954894779952812500000000000000:ℝ), (202561390902428703333636124615085660696731232213909/983249442370334323421699292187500000000000000:ℝ), (312726302524090068446055616084380453542142809735381/1474874163555501485132548938281250000000000000:ℝ), (21456832099495082316488845118994353142830717227387/294974832711100297026509787656250000000000000:ℝ)]]
theorem admission03_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (20617489474278943112493576786972655439684029863553/1319695062122132074900776648966144000000000000000000:ℝ) admission03_08_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission03_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_08_coefficients]
def admission03_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(928099553555654241912052345424576679619/7374370817777507425662744691406250:ℝ), (11957442949989139165618004022869519977051/36871854088887537128313723457031250:ℝ), (5006286832521905682840344895640363804768/18435927044443768564156861728515625:ℝ), (29954217243509807379446577382911341312/409687267654305968092374705078125:ℝ)],
![(699631768091880705510621647402202659159/14748741635555014851325489382812500:ℝ), (6963754489619465169659572227247488649871/73743708177775074256627446914062500:ℝ), (78751824927998253915622346323329873104/1675993367676706233105169248046875:ℝ), (0:ℝ)]]
theorem admission03_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (5811635197699680500434460253529491923/322191177275911151098822424064000000000:ℝ) admission03_09_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission03_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_09_coefficients]
def admission03_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(4021499684718859354587528704/1272927786793330078125:ℝ), (71772595156898625221502592/8901592914638671875:ℝ), (339108060963205144383886208/50917111471733203125:ℝ), (2235892704487484557509813248/1272927786793330078125:ℝ)],
![(5743978005991826781551610368/1272927786793330078125:ℝ), (13761056680406625025111361408/1272927786793330078125:ℝ), (10318571659350900650977891712/1272927786793330078125:ℝ), (2301847275561102407418140672/1272927786793330078125:ℝ)],
![(14118720112498593982234752/10879724673447265625:ℝ), (7670186834330026245082592/2967197638212890625:ℝ), (42011233121384506749204256/32639174020341796875:ℝ), (0:ℝ)]]
theorem admission03_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (792131825126934782245983/182531490866954240000000000:ℝ) admission03_10_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission03_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_10_coefficients]
def admission03_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5771994457393570385777780418994/629279643117013966989887547:ℝ), (25164806860254905510099984238464/1887838929351041900969662641:ℝ), (882524608721949445538465881088/209759881039004655663295849:ℝ)],
![(3024732583192796024450995687765/629279643117013966989887547:ℝ), (8983381436093485299864357736640/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission03_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (240932129547107377382169329543/644382354551822302197644848128:ℝ) admission03_11_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission03_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_11_coefficients]
def admission03_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission03_12_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission03_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_12_coefficients]
def admission03_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission03_13_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission03_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_13_coefficients]
def admission03_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission03_14_coefficients (57/128:ℝ) (117/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission03_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission03_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission03_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission03_14_coefficients]
theorem admission03_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
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
