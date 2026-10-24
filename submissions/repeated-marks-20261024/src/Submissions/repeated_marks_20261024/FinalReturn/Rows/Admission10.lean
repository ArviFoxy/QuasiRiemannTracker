/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission10_00_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission10_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]
def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission10_01_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission10_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]
def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission10_02_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission10_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]
def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(487952601767570768896/130347805367637:ℝ), (645674272309333771264/130347805367637:ℝ), (17537050060195889152/14483089485293:ℝ)],
![(17372025651500222464/6860410808823:ℝ), (29996047943500384256/11849800487967:ℝ), (0:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (174742588415495479/177968203595280384:ℝ) admission10_03_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission10_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]
def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9215791869506836257/14483089485293:ℝ), (635904:ℝ), (0:ℝ)],
![(14317603422052871718/14483089485293:ℝ), (19398627835668027392/14483089485293:ℝ), (5086971307989663744/14483089485293:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (36151991068972563/237290938127040512:ℝ) admission10_04_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission10_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]
def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1185715891093639555761/1810386185661625:ℝ), (35669571131411656031716/27155792784924375:ℝ), (1625319982821481315766/2468708434993125:ℝ)],
![(0:ℝ), (6766636798807435468/1429252251838125:ℝ), (123244589725138642642/27155792784924375:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (360665438604078997580011/3887774730273431748608000:ℝ) admission10_05_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission10_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]
def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(107077427361457258402129454789752486912/69850040385988550335877517717:ℝ), (214011531104760188403026330797300907008/69850040385988550335877517717:ℝ), (35644719235526442441872812002516140032/23283346795329516778625839239:ℝ), (0:ℝ)],
![(138807078549132230554130874311511599104/69850040385988550335877517717:ℝ), (309091153284949148766432456398957602816/69850040385988550335877517717:ℝ), (165360036256595848449172996024696832/57207240283364906089989777:ℝ), (3513386164812536657386525117634314240/7761115598443172259541946413:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (81643080514530132325637679721235/381474353894678802901005750091776:ℝ) admission10_06_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission10_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]
def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5188089625799654406910822668883211/1887838929351041900969662641:ℝ), (7586279131165394936053698074960896/1887838929351041900969662641:ℝ), (266635877153868115383265516584960/209759881039004655663295849:ℝ)],
![(22999760768105843464567243296242/15601974622735883479088121:ℝ), (252858239193939896487502843185152/171621720850094718269969331:ℝ), (0:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (71538505655245682202490519205/156213904133775103563065417728:ℝ) admission10_07_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission10_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]
def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (297548313753061863222272158494421662151880379093481/10242181691357649202309367626953125000000000:ℝ), (824522725336670084106051666329254819296532643907751/14181482341879821972428355175781250000000000:ℝ), (82506114355399960949283828439704066305486830051817/2836296468375964394485671035156250000000000:ℝ)],
![(1040795875065171683838738905987149579672778838339839/4096872676543059680923747050781250000000000:ℝ), (16181151898230190626792418570702027274648446970819229/20484363382715298404618735253906250000000000:ℝ), (150760604546038002096341027299049656535936103145274491/184359270444437685641568617285156250000000000:ℝ), (944836789918696335391394518672215697148689119467167/3351986735353412466210338496093750000000000:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (198246456466290528828235776966490179094712603075363183/10810941948904505957587162308330651648000000000000000000:ℝ) admission10_08_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission10_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]
def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(166281935028439923219631628402123211797041/335198673535341246621033849609375:ℝ), (23809952973244228843011095318696649307095956/18435927044443768564156861728515625:ℝ), (20185605817505069903202246020650666821308416/18435927044443768564156861728515625:ℝ), (122692473829416171026213180960404854013952/409687267654305968092374705078125:ℝ)],
![(719938692024578169409914967918924852234178/3687185408888753712831372345703125:ℝ), (7197190823266343256864873406007578327947512/18435927044443768564156861728515625:ℝ), (3597495308341220985916404539311991273807872/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (47546159531564585669159350764353912227/2577529418207289208790579392512000000000:ℝ) admission10_09_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission10_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]
def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(258599791904773198230722043623936/1272927786793330078125:ℝ), (17093468570776650657458255607296/32639174020341796875:ℝ), (3379082119363333999797470584832/7714713859353515625:ℝ), (149503113435584713806432721436672/1272927786793330078125:ℝ)],
![(367415398065019269978330899167232/1272927786793330078125:ℝ), (176897953501563755006266333779968/254585557358666015625:ℝ), (666847540460742382572658000297984/1272927786793330078125:ℝ), (149773263358702252519657230565376/1272927786793330078125:ℝ)],
![(36181428567897696034753789540352/424309262264443359375:ℝ), (217031703452299993352183377242112/1272927786793330078125:ℝ), (108487371503878780247922008621056/1272927786793330078125:ℝ), (0:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (676972451585116771455060979/151866200401305927680000000000:ℝ) admission10_10_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission10_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]
def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1449583936868620465486189117508519/629279643117013966989887547:ℝ), (6380626203054659130952601911460864/1887838929351041900969662641:ℝ), (225926299832819058057847265558528/209759881039004655663295849:ℝ)],
![(6365499479225592680456361409370/5200658207578627826362707:ℝ), (209928826053568618442059934648320/171621720850094718269969331:ℝ), (0:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (175928509120064025259639323557/468641712401325310689196253184:ℝ) admission10_11_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission10_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]
def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission10_12_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission10_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]
def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission10_13_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission10_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]
def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission10_14_coefficients (1863/4096:ℝ) (933/2048:ℝ) (511/1024:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission10_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission10_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]
theorem admission10_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (1863/4096:ℝ) (933/2048:ℝ))
 (hp : p ∈ Set.Icc (511/1024:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
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
