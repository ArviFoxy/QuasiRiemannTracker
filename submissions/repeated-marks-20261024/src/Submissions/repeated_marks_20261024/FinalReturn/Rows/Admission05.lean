/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission05_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission05_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission05_00_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission05_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_00_coefficients]
def admission05_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission05_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission05_01_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission05_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_01_coefficients]
def admission05_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission05_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission05_02_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission05_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_02_coefficients]
def admission05_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(7634169534775939840/130347805367637:ℝ), (10086277199490986752/130347805367637:ℝ), (274016407190560768/14483089485293:ℝ)],
![(5161846389147950464/130347805367637:ℝ), (5147626389147950464/130347805367637:ℝ), (0:ℝ)]]
theorem admission05_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (43309342833745231/44492050898820096:ℝ) admission05_03_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission05_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_03_coefficients]
def admission05_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11180378265295134/1114083806561:ℝ), (9984:ℝ), (0:ℝ)],
![(17437864654901879/1114083806561:ℝ), (305420854249959808/14483089485293:ℝ), (79483926687338496/14483089485293:ℝ)]]
theorem admission05_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (174647299850109/1140821817918464:ℝ) admission05_04_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission05_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_04_coefficients]
def admission05_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93747184838640535421/9051930928308125:ℝ), (51510183471840981542/2468708434993125:ℝ), (284703136122445259449/27155792784924375:ℝ)],
![(0:ℝ), (7952843822776790218/27155792784924375:ℝ), (7276960789458449593/27155792784924375:ℝ)]]
theorem admission05_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (6690427879869532870983/75933100200652963840000:ℝ) admission05_05_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission05_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_05_coefficients]
def admission05_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(211746378953189868670322609699822848/69850040385988550335877517717:ℝ), (421234167451137180434834949338471680/69850040385988550335877517717:ℝ), (69831522164672180318864113212882944/23283346795329516778625839239:ℝ), (0:ℝ)],
![(25020734943279807121435934297116544/6350003671453504575988865247:ℝ), (609936707595607208419842858737511040/69850040385988550335877517717:ℝ), (132158076430443144381703364434214912/23283346795329516778625839239:ℝ), (6862082353149485658958056870379520/7761115598443172259541946413:ℝ)]]
theorem admission05_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5124779179136396661941503925465/23842147118417425181312859380736:ℝ) admission05_06_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission05_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_06_coefficients]
def admission05_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2453870266130382814263940322882/57207240283364906089989777:ℝ), (118282828084032889729320868293376/1887838929351041900969662641:ℝ), (4166185580529189302863523696640/209759881039004655663295849:ℝ)],
![(14268330812710622654826933444211/629279643117013966989887547:ℝ), (42617398726703732553729004079488/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission05_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (192916633733814185655057371695/429588236367881534798429898752:ℝ) admission05_07_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission05_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_07_coefficients]
def admission05_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (3549413617537631838922177573112848889396509565807/73743708177775074256627446914062500000000000:ℝ), (71514926452942677882978755455702101088692915837953/737437081777750742566274469140625000000000000:ℝ), (12002182480698593676454110917537941721107190059961/245812360592583580855424823046875000000000000:ℝ)],
![(84165037171492515293028077947577191655695039700427/163874907061722387236949882031250000000000000:ℝ), (177990370346465571864699313506855101858292833805643/113451858735038575779426841406250000000000000:ℝ), (1178302634830419297745561582392746408751997761400001/737437081777750742566274469140625000000000000:ℝ), (133364489804728023324431323621681428787047965105081/245812360592583580855424823046875000000000000:ℝ)]]
theorem admission05_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (149871655496772610125118388769748223893536760352309/7998151891649285302428949387673600000000000000000000:ℝ) admission05_08_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission05_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_08_coefficients]
def admission05_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(17747015021118926591350799709090591053441/18435927044443768564156861728515625:ℝ), (46244469706273903484036642277244766099983/18435927044443768564156861728515625:ℝ), (39280715216654438314377070049997277450112/18435927044443768564156861728515625:ℝ), (239633737948078459035572619063290730496/409687267654305968092374705078125:ℝ)],
![(13151132920966144712442483763688538585241/36871854088887537128313723457031250:ℝ), (2385672420380208973040700387323270452933/3351986735353412466210338496093750:ℝ), (6545370871903442770401921918890212339136/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission05_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10570192445432219335185251770941007003/644382354551822302197644848128000000000:ℝ) admission05_09_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission05_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_09_coefficients]
def admission05_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(63680546964862231391080325888/1272927786793330078125:ℝ), (577581296897769565749114112/4466413286994140625:ℝ), (15365176488938186240597118464/141436420754814453125:ℝ), (37357192977566581317956870144/1272927786793330078125:ℝ)],
![(1192447208991989375002214656/16972370490577734375:ℝ), (24060606956858477840481743104/141436420754814453125:ℝ), (164995278380357621556393078272/1272927786793330078125:ℝ), (37884829546155524117223489536/1272927786793330078125:ℝ)],
![(25206953605773405315677000896/1272927786793330078125:ℝ), (16771735517729360465049667264/424309262264443359375:ℝ), (25107506952883426079472000896/1272927786793330078125:ℝ), (0:ℝ)]]
theorem admission05_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (36630650685706250605751459/9491637525081620480000000000:ℝ) admission05_10_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission05_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_10_coefficients]
def admission05_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6171458571393993344165405574458/171621720850094718269969331:ℝ), (99475297572354301278226974384896/1887838929351041900969662641:ℝ), (3530098434887797782153863524352/209759881039004655663295849:ℝ)],
![(35520111760072638481757287693735/1887838929351041900969662641:ℝ), (35341560810041280818370949662080/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission05_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (474107695150369495965660736303/1288764709103644604395289696256:ℝ) admission05_11_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission05_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_11_coefficients]
def admission05_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission05_12_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission05_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_12_coefficients]
def admission05_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission05_13_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission05_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_13_coefficients]
def admission05_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission05_14_coefficients (117/256:ℝ) (237/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission05_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_14_coefficients]
theorem admission05_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission05_00_pos hδ hp
 · exact admission05_01_pos hδ hp
 · exact admission05_02_pos hδ hp
 · exact admission05_03_pos hδ hp
 · exact admission05_04_pos hδ hp
 · exact admission05_05_pos hδ hp
 · exact admission05_06_pos hδ hp
 · exact admission05_07_pos hδ hp
 · exact admission05_08_pos hδ hp
 · exact admission05_09_pos hδ hp
 · exact admission05_10_pos hδ hp
 · exact admission05_11_pos hδ hp
 · exact admission05_12_pos hδ hp
 · exact admission05_13_pos hδ hp
 · exact admission05_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
