/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission07_00_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission07_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]
def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission07_01_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission07_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]
def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission07_02_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission07_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]
def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2345851321329067264/10026754259049:ℝ), (40332397836138062080/130347805367637:ℝ), (1096065628762243072/14483089485293:ℝ)],
![(20618945556591801856/130347805367637:ℝ), (20590505556591801856/130347805367637:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (43309342833745231/44492050898820096:ℝ) admission07_03_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission07_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]
def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(583605397571670801/14483089485293:ℝ), (40192:ℝ), (0:ℝ)],
![(47645175586983762/762267867647:ℝ), (1221683416999839232/14483089485293:ℝ), (317935706749353984/14483089485293:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (9139875358822371/59322734531760128:ℝ) admission07_04_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission07_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]
def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(372442301405460807621/9051930928308125:ℝ), (173548530248056080868/2088907137301875:ℝ), (1137460778423144356546/27155792784924375:ℝ)],
![(0:ℝ), (29107843157833798372/27155792784924375:ℝ), (27756077091197117122/27155792784924375:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (187251337930701865201/2124002802815467520000:ℝ) admission07_05_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission07_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]
def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(45724403943592986849949744463553280/1887838929351041900969662641:ℝ), (3374559592024655997364960134915657472/69850040385988550335877517717:ℝ), (43147956128236908852290758711902208/1791026676563808982971218403:ℝ), (0:ℝ)],
![(2192725595455956814217761387616381440/69850040385988550335877517717:ℝ), (4870435770572919847672782039370213888/69850040385988550335877517717:ℝ), (1057264611443545155053626915473719296/23283346795329516778625839239:ℝ), (54896658825195885271664454963036160/7761115598443172259541946413:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (20616912167096324736241476730595/95368588473669700725251437522944:ℝ) admission07_06_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission07_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]
def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(322178608255933826844012416630363/1887838929351041900969662641:ℝ), (471783134520524059469186597824768/1887838929351041900969662641:ℝ), (16664742322116757211454094786560/209759881039004655663295849:ℝ)],
![(170844782329671201036419608824242/1887838929351041900969662641:ℝ), (170469594906814930214916016317952/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (192916633733814185655057371695/429588236367881534798429898752:ℝ) admission07_07_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission07_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]
def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (38243011101608339445143813813907351014889253728803/122906180296291790427712411523437500000000000:ℝ), (18447803235700962866690643101520778931615651382163/29497483271110029702650978765625000000000000:ℝ), (231708346011478127061660123185374257407071387181257/737437081777750742566274469140625000000000000:ℝ)],
![(330117840966436791817384953097444644944077019269771/81937453530861193618474941015625000000000000:ℝ), (3028005658035128682415810514477687816766455167863463/245812360592583580855424823046875000000000000:ℝ), (9257388978067490018444777042635362238317478568426587/737437081777750742566274469140625000000000000:ℝ), (25986807618084168914157960562684445842889669324497/6094521337006204484018797265625000000000000:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (82389325891134698827022099576182952850576061802798903/4223024198790822639682485276691660800000000000000000000:ℝ) admission07_08_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission07_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]
def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1159486395009822012600928064671018071064/152363033425155112100469931640625:ℝ), (366736789636942813950241563837683963573141/18435927044443768564156861728515625:ℝ), (312706562846193892218325182169726953624832/18435927044443768564156861728515625:ℝ), (1917069903584627672284580952506325843968/409687267654305968092374705078125:ℝ)],
![(52484271288955328956694031862024938245776/18435927044443768564156861728515625:ℝ), (104847760223592139570110783872233648677614/18435927044443768564156861728515625:ℝ), (52362966975227542163215375351121698713088/18435927044443768564156861728515625:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (10570192445432219335185251770941007003/644382354551822302197644848128000000000:ℝ) admission07_09_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission07_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]
def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1013423776283220377266325142656/1272927786793330078125:ℝ), (2627952307638628944212003162752/1272927786793330078125:ℝ), (2216461765219404160427120897536/1272927786793330078125:ℝ), (9260556618304259130483736576/19583504412205078125:ℝ)],
![(1420236890872656949887428724224/1272927786793330078125:ℝ), (1148334598571757310849304427008/424309262264443359375:ℝ), (46156460480644357342737901568/22332066434970703125:ℝ), (606157272738488385875575832576/1272927786793330078125:ℝ)],
![(10320991498650760286184410624/32639174020341796875:ℝ), (61864751051664574494826463744/97917522061025390625:ℝ), (401720111246134817271552014336/1272927786793330078125:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (36630650685706250605751459/9491637525081620480000000000:ℝ) admission07_10_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission07_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]
def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29999322260199147489284382753213/209759881039004655663295849:ℝ), (396717260420751884350734934970624/1887838929351041900969662641:ℝ), (14120393739551191128615454097408/209759881039004655663295849:ℝ)],
![(15747038348914204288917386079070/209759881039004655663295849:ℝ), (141366243240165123273483798648320/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (474107695150369495965660736303/1288764709103644604395289696256:ℝ) admission07_11_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission07_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]
def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission07_12_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission07_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]
def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission07_13_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission07_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]
def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients (471/1024:ℝ) (237/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission07_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission07_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]
theorem admission07_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (471/1024:ℝ) (237/512:ℝ))
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
