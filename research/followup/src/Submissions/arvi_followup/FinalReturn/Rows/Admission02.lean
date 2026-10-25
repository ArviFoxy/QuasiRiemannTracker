/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_followup.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission02_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission02_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission02_00_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission02_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_00_coefficients]
def admission02_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission02_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission02_01_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission02_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_01_coefficients]
def admission02_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission02_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission02_02_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission02_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_02_coefficients]
def admission02_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29577055148703275751359936/8001314262374457576663:ℝ), (38842067142904001629114304/8001314262374457576663:ℝ), (1051526118102804066417152/889034918041606397407:ℝ)],
![(20027116857148475556058784/8001314262374457576663:ℝ), (19817353617939269796058784/8001314262374457576663:ℝ), (0:ℝ)]]
theorem admission02_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (678723180504449833981409/682778817055953713208576:ℝ) admission02_03_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission02_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_03_coefficients]
def admission02_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(653305346385533186872589793819/1111293647552007996758750000:ℝ), (576:ℝ), (0:ℝ)],
![(2141692361766314619931455429433/2222587295104015993517500000:ℝ), (89884920235946449910192866544/69455852972000499797421875:ℝ), (23827880814485073016680183272/69455852972000499797421875:ℝ)]]
theorem admission02_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (80419097748887121431295618543/568982347546628094340480000000:ℝ) admission02_04_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission02_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_04_coefficients]
def admission02_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2263533107297412531793232751599/3333880942656023990276250000:ℝ), (275724461029723522552106531132/208367558916001499392265625:ℝ), (44357285260882786782121299272/69455852972000499797421875:ℝ)],
![(33046558392793184356173073813/6667761885312047980552500000:ℝ), (1073009774501878865490026/98055321842824235008125:ℝ), (0:ℝ)]]
theorem admission02_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (112914553876897210609410542687/1137964695093256188680960000000:ℝ) admission02_05_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission02_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_05_coefficients]
def admission02_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(191268122532930118513509501289632248325123027118794074/4112461991727857075060055526821000141183986203125:ℝ), (1872625711346751674292001983559496301099637896998495042/20562309958639285375300277634105000705919931015625:ℝ), (916744957639984073056769574906295694149222761404524672/20562309958639285375300277634105000705919931015625:ℝ), (0:ℝ)],
![(254664108277656578660728927465260040983268512531843071/4112461991727857075060055526821000141183986203125:ℝ), (2789279331559418839081399684063639452549363209997082811/20562309958639285375300277634105000705919931015625:ℝ), (1800619182744643554884524435100124009786780449691376576/20562309958639285375300277634105000705919931015625:ℝ), (6314999686572049541491187817809720567825773385633536/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission02_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2249731015533954053603946410156914449547384044277151/11229762878744868386297324958572544385526404992000000:ℝ) admission02_06_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission02_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_06_coefficients]
def admission02_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(40352784484166852224188997633644655718814104612963/14226895538950424475883435336029405893825682000:ℝ), (750389003074490182928103618527755356990937608857684/185246035663416985363065564271216222575855234375:ℝ), (15337954367435139867728218286854270002605961575704/12349735710894465690871037618081081505057015625:ℝ)],
![(5347841292530623565487891510935272096037964390482669/3556723884737606118970858834007351473456420500000:ℝ), (273717123010531405364191793787322539746842123268342/185246035663416985363065564271216222575855234375:ℝ), (0:ℝ)]]
theorem admission02_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (285669400093479480036438065592660778798536034347487/607014209661884777637693241003921318136562432000000:ℝ) admission02_07_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission02_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_07_coefficients]
def admission02_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (919081417530595471407824963530573249906552129063763918436081073913657957/340857969223003494169512967988438566842499588823816601600000000000000:ℝ), (215791073139068282358226685350425019922137662175591857782273145255481231/40100937555647469902295643292757478452058775155743129600000000000000:ℝ), (1827248390331499971428821700263266932895024414990089206103970453035865013/681715938446006988339025935976877133684999177647633203200000000000000:ℝ)],
![(1364316375868066147126722256253304716719052668486787373001941283324869627/151492430765779330742005763550417140818888706143918489600000000000000:ℝ), (38713809398628692535382617538222561822495554073008841319525118289476999623/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ), (20317873674432650911658659425478285680900792422691144753190579352952001583/681715938446006988339025935976877133684999177647633203200000000000000:ℝ), (7097186925332495204311919784561130094144529055850520258207438955335415093/681715938446006988339025935976877133684999177647633203200000000000000:ℝ)]]
theorem admission02_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (2631143449600827906922701369630904889892077631560021530589369191485590809/317702654165315655024258871041284407702614087867130948301619200000000000000:ℝ) admission02_08_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission02_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_08_coefficients]
def admission02_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(50789757457297118138039157461518057703086692328908553/2963936570614671765809049028339459561213683750000:ℝ), (9612976977875174251439916057844737426107245774065701/222295242796100382435678677125459467091026281250:ℝ), (19588427720097034459944508304107468421815942390006784/555738106990250956089196692813648667727565703125:ℝ), (112908078618159629623393499947684211296802123528128/12349735710894465690871037618081081505057015625:ℝ)],
![(39399704397853112086396238583024787252089045027410963/5927873141229343531618098056678919122427367500000:ℝ), (5853357649976453024281473714148441942096282754397607/444590485592200764871357354250918934182052562500:ℝ), (3621076106053358013047344832849475966230853079854752/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission02_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (17288213379598584382314215947387416603390426749081/809352279549179703516924321338561757515416576000000:ℝ) admission02_09_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission02_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_09_coefficients]
def admission02_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(41765426531231139958246504722652/208367558916001499392265625:ℝ), (407901970527258364155630536484/817127682023535291734375:ℝ), (27705215219723488274747820080384/69455852972000499797421875:ℝ), (20872404003766315702004178160384/208367558916001499392265625:ℝ)],
![(185119820994185116630310934608732/625102676748004498176796875:ℝ), (434799122248022212164965885455708/625102676748004498176796875:ℝ), (316303364538988725180039453630464/625102676748004498176796875:ℝ), (22221393501550130082328167594496/208367558916001499392265625:ℝ)],
![(55199647068445900474034567954621/625102676748004498176796875:ℝ), (109475442989594906622790434274621/625102676748004498176796875:ℝ), (5106317453570948418104081536/58833193105694541004875:ℝ), (0:ℝ)]]
theorem admission02_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (759125767623099840617871110379/145659480971936792151162880000000:ℝ) admission02_10_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission02_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_10_coefficients]
def admission02_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21220210341020677230530853440400883398802812304764781/8891809711844015297427147085018378683641051250000:ℝ), (379288791717968165652197677901887338638481345789178/111147621398050191217839338562729733545513140625:ℝ), (64989143024298882186107880943690098607721985575704/61748678554472328454355188090405407525285078125:ℝ)],
![(892036096433508716188531281565958991631301964485207/711344776947521223794171766801470294691284100000:ℝ), (683087812931446438897656583125694021597044949901219/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission02_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (390830048292590966093708901152462421173861578430389/1011690349436474629396155401673202196894270720000000:ℝ) admission02_11_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission02_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_11_coefficients]
def admission02_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission02_12_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission02_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_12_coefficients]
def admission02_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission02_13_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission02_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_13_coefficients]
def admission02_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission02_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission02_14_coefficients (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission02_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission02_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission02_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission02_14_coefficients]
theorem admission02_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission02_00_pos hδ hp
 · exact admission02_01_pos hδ hp
 · exact admission02_02_pos hδ hp
 · exact admission02_03_pos hδ hp
 · exact admission02_04_pos hδ hp
 · exact admission02_05_pos hδ hp
 · exact admission02_06_pos hδ hp
 · exact admission02_07_pos hδ hp
 · exact admission02_08_pos hδ hp
 · exact admission02_09_pos hδ hp
 · exact admission02_10_pos hδ hp
 · exact admission02_11_pos hδ hp
 · exact admission02_12_pos hδ hp
 · exact admission02_13_pos hδ hp
 · exact admission02_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
