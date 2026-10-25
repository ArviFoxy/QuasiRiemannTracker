/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_single_stage_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission08_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission08_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]
def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission08_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission08_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]
def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission08_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission08_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]
def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(117360434574132614860159040/8001314262374457576663:ℝ), (154784808176930454691176512/8001314262374457576663:ℝ), (4206104472411216265668608/889034918041606397407:ℝ)],
![(79322047694687846234048000/8001314262374457576663:ℝ), (78880440875300044634048000/8001314262374457576663:ℝ), (0:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (165059830739918495312855/170694704263988428302144:ℝ) admission08_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission08_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]
def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5604778778627122436357729106549/2222587295104015993517500000:ℝ), (2496:ℝ), (0:ℝ)],
![(1099807474907033275492232817807/277823411888001999189687500:ℝ), (368430030124201863614841466176/69455852972000499797421875:ℝ), (95311523257940292066720733088/69455852972000499797421875:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (348482756911844192868947680353/2275929390186512377361920000000:ℝ) admission08_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission08_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]
def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5834179043177268123042674795907/2222587295104015993517500000:ℝ), (2209020535487937793570290742421/416735117832002998784531250:ℝ), (2219981784095847089937810021421/833470235664005997569062500:ℝ)],
![(0:ℝ), (10133685638224558189523731273/83347023566400599756906250:ℝ), (18166418314694664879197531273/166694047132801199513812500:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (4911398863173493012105893308279/58263792388774716860465152000000:ℝ) admission08_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission08_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]
def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7876271181615062705183214716726051828287627023622342622/20562309958639285375300277634105000705919931015625:ℝ), (15585425690668715666468022661561528474124748489574434526/20562309958639285375300277634105000705919931015625:ℝ), (7710150870129066109171490656724558020966721465952091904/20562309958639285375300277634105000705919931015625:ℝ), (0:ℝ)],
![(411118157662070555276142714404143987368711890173061456/822492398345571415012011105364200028236797240625:ℝ), (906371189875485651982418328566150103715495547313602896/822492398345571415012011105364200028236797240625:ℝ), (2931149520259322157777550303823424078028573969468321792/4112461991727857075060055526821000141183986203125:ℝ), (50519997492576396331929502542477764542606187085068288/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (9664959185328962064494934355787276764327410713874641/44919051514979473545189299834290177542105619968000000:ℝ) admission08_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission08_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]
def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(191176405938378985252571855185548680594280448825077437/17783619423688030594854294170036757367282102500000:ℝ), (2902356518052533242520022817302193124968250605521404/185246035663416985363065564271216222575855234375:ℝ), (61351817469740559470912873147417080010423846302816/12349735710894465690871037618081081505057015625:ℝ)],
![(2490686925514422343602772404750438054169172218142411/444590485592200764871357354250918934182052562500:ℝ), (205747099175701459065701214122014258064740387960096/37049207132683397072613112854243244515171046875:ℝ), (0:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (13420710071505747384262191000997486252280216378741/30350710483094238881884662050196065906828121600000:ℝ) admission08_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission08_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]
def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (2095372725696611020258204913603232245794932671836082316916998283689280603/340857969223003494169512967988438566842499588823816601600000000000000:ℝ), (8511517239625440169041482987181812120960788156269525760113044472424475761/681715938446006988339025935976877133684999177647633203200000000000000:ℝ), (862838316525473341838682421754184366621292876176912924882721538001182911/136343187689201397667805187195375426736999835529526640640000000000000:ℝ)],
![(1012833989371754185142173618977976203114319257625198893875434159061810399/15149243076577933074200576355041714081888870614391848960000000000000:ℝ), (27489112422835892906768307823035630730170809481682573855160669021886702421/136343187689201397667805187195375426736999835529526640640000000000000:ℝ), (27669696276782268681982776619368082284970530501883806213784482006890871869/136343187689201397667805187195375426736999835529526640640000000000000:ℝ), (9294739972527065714451639356630765424620500301553602608248271141680463039/136343187689201397667805187195375426736999835529526640640000000000000:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (55539038616708051591030350972174699935604352790897648278404576961013097281/3049945479987030288232885161996330313945095243524457103695544320000000000000:ℝ) admission08_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission08_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]
def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2142831671894320989147535200640438445284233127269108013/17783619423688030594854294170036757367282102500000:ℝ), (38740170770226974384425620499061472154144082812010079/123497357108944656908710376180810815050570156250:ℝ), (148010289753670758306687574693012260208325907513797248/555738106990250956089196692813648667727565703125:ℝ), (903264628945277036987147999581473690374416988225024/12349735710894465690871037618081081505057015625:ℝ)],
![(18696137581339857111903969113846053039278346020579211/444590485592200764871357354250918934182052562500:ℝ), (60842732050338353264724833164728543197223424936612/726455041817321511227708095181240088532765625:ℝ), (1482913333996150561437851573518772242285593828352/35567238847376061189708588340073514734564205:ℝ), (0:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (119956471943723517437176456373397191988528272087/8093522795491797035169243213385617575154165760000:ℝ) admission08_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission08_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]
def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(657923385378154984044290784012398/208367558916001499392265625:ℝ), (1701595127152203884155993957633646/208367558916001499392265625:ℝ), (1431560049736472655759929601551872/208367558916001499392265625:ℝ), (387918043971613626445026427930624/208367558916001499392265625:ℝ)],
![(549636701842129950335341277804384/125020535349600899635359375:ℝ), (1336112391299687296053645248288608/125020535349600899635359375:ℝ), (1025665067264731066553274976526336/125020535349600899635359375:ℝ), (79741991990776828297523668680704/41673511783200299878453125:ℝ)],
![(29590480553137075975730156753536/25004107069920179927071875:ℝ), (58965208080096913598734542033536/25004107069920179927071875:ℝ), (2764326952376003887943942144/2353327724227781640195:ℝ), (0:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1207275854624137947365415363/364148702429841980377907200000:ℝ) admission08_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission08_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]
def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(53456874084667432456698343578296349419689615170576257/5927873141229343531618098056678919122427367500000:ℝ), (7324466407033276252963613861653821392831430683691566/555738106990250956089196692813648667727565703125:ℝ), (259956572097195528744431523774760394430887942302816/61748678554472328454355188090405407525285078125:ℝ)],
![(689056951089433019037674319809781186351418843659143/148196828530733588290452451416972978060684187500:ℝ), (511628993368345543107413306982698499952543128975376/111147621398050191217839338562729733545513140625:ℝ), (0:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (732918239316957770547836891597157268391931667679/2023380698872949258792310803346404393788541440000:ℝ) admission08_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission08_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]
def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission08_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission08_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]
def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission08_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission08_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]
def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission08_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission08_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission08_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]
theorem admission08_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
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
