/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission01_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission01_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission01_00_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission01_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_00_coefficients]
def admission01_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission01_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission01_01_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission01_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_01_coefficients]
def admission01_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission01_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission01_02_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission01_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_02_coefficients]
def admission01_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(483290271494085280/130347805367637:ℝ), (634364500538775712/130347805367637:ℝ), (17126025449410048/14483089485293:ℝ)],
![(327747172221159232/130347805367637:ℝ), (324507172221159232/130347805367637:ℝ), (0:ℝ)]]
theorem admission01_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (5677080843308201/5561506362352512:ℝ) admission01_03_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission01_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_03_coefficients]
def admission01_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8041336378338037/14483089485293:ℝ), (544:ℝ), (0:ℝ)],
![(13482101583257754/14483089485293:ℝ), (18277750379446080/14483089485293:ℝ), (4967745417958656/14483089485293:ℝ)]]
theorem admission01_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (989668032483951/7415341816470016:ℝ) admission01_04_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission01_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_04_coefficients]
def admission01_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3879663341789895103/5431158556984875:ℝ), (36882895851646110506/27155792784924375:ℝ), (5779711986103891872/9051930928308125:ℝ)],
![(1098919343828293766/27155792784924375:ℝ), (1252918009647662516/27155792784924375:ℝ), (0:ℝ)]]
theorem admission01_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2109298844724096433/18538354541175040000:ℝ) admission01_05_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission01_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_05_coefficients]
def admission01_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3136833323185595031543339615532384/69850040385988550335877517717:ℝ), (6142546284370306751143498334300512/69850040385988550335877517717:ℝ), (1002396738912753890573386239589376/23283346795329516778625839239:ℝ), (0:ℝ)],
![(4213225026595132202944939390987456/69850040385988550335877517717:ℝ), (9255276706109932538057690239784128/69850040385988550335877517717:ℝ), (2002865387788499882127909198731264/23283346795329516778625839239:ℝ), (107220036767960713421219638599680/7761115598443172259541946413:ℝ)]]
theorem admission01_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (174453920245488700752469183915/917005658400670199281263822336:ℝ) admission01_06_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission01_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_06_coefficients]
def admission01_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3632847595891269270588437271/1241182728041447666646721:ℝ), (7813982322629399185612827814816/1887838929351041900969662641:ℝ), (260386598783074331428970231040/209759881039004655663295849:ℝ)],
![(334510262860855854475899134766/209759881039004655663295849:ℝ), (2958501317583123788879254237504/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission01_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (26784558989404781488136260745/53698529545985191849803737344:ℝ) admission01_07_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission01_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_07_coefficients]
def admission01_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (11724771679490658339080576486925325440371710558397/2949748327111002970265097876562500000000000000:ℝ), (46572449311582567451374055168188553923905787691527/5899496654222005940530195753125000000000000000:ℝ), (7699357430251704654499719585349681201262455524911/1966498884740668646843398584375000000000000000:ℝ)],
![(5892559750741996928546852924383048715290326937899/655499628246889548947799528125000000000000000:ℝ), (174766322035649229738829474919029880803355879919709/5899496654222005940530195753125000000000000000:ℝ), (190368516281721552320742375760226438908008094695271/5899496654222005940530195753125000000000000000:ℝ), (22869645845755383360496871173367617084505052405551/1966498884740668646843398584375000000000000000:ℝ)]]
theorem admission01_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (6268371310526514363406038550379491732818913333969/2749364712754441822709951352012800000000000000000000:ℝ) admission01_08_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission01_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_08_coefficients]
def admission01_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2727231307184172410233265974383421383361/147487416355550148513254893828125000:ℝ), (1354163473405075800233496225319008889621/29497483271110029702650978765625000:ℝ), (673884569285288657126648681650397537348/18435927044443768564156861728515625:ℝ), (3744277155438725922430822172863917664/409687267654305968092374705078125:ℝ)],
![(590297793339399670606484584234502822297/73743708177775074256627446914062500:ℝ), (9343734648193765609759014822981611477/589949665422200594053019575312500:ℝ), (144357795691035434212684903466092621832/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission01_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2242717261900276374371366615470855613/80547794318977787774705606016000000000:ℝ) admission01_09_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission01_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_09_coefficients]
def admission01_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(251534010401420206403654344/1272927786793330078125:ℝ), (18519917372539734057743296/38573569296767578125:ℝ), (470476887546900993011344504/1272927786793330078125:ℝ), (2016148530650181372899456/23144141578060546875:ℝ)],
![(77745424158220270607834528/254585557358666015625:ℝ), (297127073926740357420452096/424309262264443359375:ℝ), (621713438434081925970194656/1272927786793330078125:ℝ), (119132490569962206748011008/1272927786793330078125:ℝ)],
![(14197118144480839659892256/141436420754814453125:ℝ), (2163882868213000974983424/10879724673447265625:ℝ), (13929056017288173014892256/141436420754814453125:ℝ), (0:ℝ)]]
theorem admission01_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1028858004340240624654419/148306836329400320000000000:ℝ) admission01_10_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission01_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_10_coefficients]
def admission01_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(27542107465646398883599436017/11170644552373028999820489:ℝ), (6587184182230056568068236701856/1887838929351041900969662641:ℝ), (220631152180487361384616470272/209759881039004655663295849:ℝ)],
![(2517862881548242180004215511650/1887838929351041900969662641:ℝ), (2467832209398118967873519915840/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission01_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (66050455344660788444550774473/161095588637955575549411212032:ℝ) admission01_11_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission01_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_11_coefficients]
def admission01_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission01_12_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission01_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_12_coefficients]
def admission01_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission01_13_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission01_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_13_coefficients]
def admission01_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission01_14_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission01_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_14_coefficients]
theorem admission01_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission01_00_pos hδ hp
 · exact admission01_01_pos hδ hp
 · exact admission01_02_pos hδ hp
 · exact admission01_03_pos hδ hp
 · exact admission01_04_pos hδ hp
 · exact admission01_05_pos hδ hp
 · exact admission01_06_pos hδ hp
 · exact admission01_07_pos hδ hp
 · exact admission01_08_pos hδ hp
 · exact admission01_09_pos hδ hp
 · exact admission01_10_pos hδ hp
 · exact admission01_11_pos hδ hp
 · exact admission01_12_pos hδ hp
 · exact admission01_13_pos hδ hp
 · exact admission01_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
