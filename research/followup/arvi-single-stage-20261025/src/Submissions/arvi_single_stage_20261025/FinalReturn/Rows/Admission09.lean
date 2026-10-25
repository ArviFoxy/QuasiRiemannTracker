/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_single_stage_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission09_00_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission09_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]
def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission09_01_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission09_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]
def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission09_02_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission09_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]
def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29404648691444148556266368/8001314262374457576663:ℝ), (38647580344675484354020736/8001314262374457576663:ℝ), (1051526118102804066417152/889034918041606397407:ℝ)],
![(19854710399889348360965216/8001314262374457576663:ℝ), (19622866819710752520965216/8001314262374457576663:ℝ), (0:ℝ)]]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (641755465414898128521431/682778817055953713208576:ℝ) admission09_03_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission09_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]
def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(72589482931725909652509977091/111129364755200799675875000:ℝ), (640:ℝ), (0:ℝ)],
![(457374265525953287847295076723/444517459020803198703500000:ℝ), (94330094826154481897227866544/69455852972000499797421875:ℝ), (23827880814485073016680183272/69455852972000499797421875:ℝ)]]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8935455305431902381255068727/56898234754662809434048000000:ℝ) admission09_04_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission09_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]
def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(17623606494909928938158009527/26148085824753129335500000:ℝ), (923273208440364395224805810969/666776188531204798055250000:ℝ), (939338673793304608604153410969/1333552377062409596110500000:ℝ)],
![(0:ℝ), (241256998059309496716985440733/3333880942656023990276250000:ℝ), (438393983921775511937122324733/6667761885312047980552500000:ℝ)]]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (234719212217346062845937495799/3427281905222042168262656000000:ℝ) admission09_05_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission09_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]
def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(40878019932817229412221394584062572684110015400697684/822492398345571415012011105364200028236797240625:ℝ), (400176607279526525533635334751831610137225941774923172/4112461991727857075060055526821000141183986203125:ℝ), (195888698494969932101931716897065554422275864771434752/4112461991727857075060055526821000141183986203125:ℝ), (0:ℝ)],
![(267786085408812607208326399095940656078695562416537417/4112461991727857075060055526821000141183986203125:ℝ), (2917536656610299792457574374263301202135855021873203629/20562309958639285375300277634105000705919931015625:ℝ), (1863317717579509142337413444679156087748937012144025664/20562309958639285375300277634105000705919931015625:ℝ), (6314999686572049541491187817809720567825773385633536/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (247174272326500267029699598187678743826000888986583/1122976287874486838629732495857254438552640499200000:ℝ) admission09_06_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission09_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]
def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2360537044915543659684996836671859945968359123832523/889180971184401529742714708501837868364105125000:ℝ), (143464500998536203972794613251629184531820866444248/37049207132683397072613112854243244515171046875:ℝ), (15337954367435139867728218286854270002605961575704/12349735710894465690871037618081081505057015625:ℝ)],
![(4701793351151085148180629449211547950207874732572011/3556723884737606118970858834007351473456420500000:ℝ), (240650624928722242300061241517713105415008846631898/185246035663416985363065564271216222575855234375:ℝ), (0:ℝ)]]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (251159002766750415334049574447238671292672620802153/607014209661884777637693241003921318136562432000000:ℝ) admission09_07_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission09_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]
def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (1955220756485781007273334616109398563401388286902720580027074593910189/34085796922300349416951296798843856684249958882381660160000000000000:ℝ), (13075695706335505080596428116011867171082253925396885303010058678934231/68171593844600698833902593597687713368499917764763320320000000000000:ℝ), (52235548828932019558886131703698701137609278301695238635169176160437/403382212098228987182855583418270493304733241211617280000000000000:ℝ)],
![(1364316375868066147126722256253304716719052668486787373001941283324869627/151492430765779330742005763550417140818888706143918489600000000000000:ℝ), (7023138511753148378008450213748928953081080217645978893796375395515755071/272686375378402795335610374390750853473999671059053281280000000000000:ℝ), (8390091194065922581187385027840589506967637352480026011961018235199081483/340857969223003494169512967988438566842499588823816601600000000000000:ℝ), (535821661252189034593761564687711396617206432119029600539690441001068861/68171593844600698833902593597687713368499917764763320320000000000000:ℝ)]]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (672409257720502634830286813839081904004923563702038364959519304146019969/31770265416531565502425887104128440770261408786713094830161920000000000000:ℝ) admission09_08_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission09_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]
def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(856116493545452323351719221927903019429347439840077/59278731412293435316180980566789191224273675000:ℝ), (843445316286251877216805565065359933604366632136973/22229524279610038243567867712545946709102628125:ℝ), (3627781143782556312893285269493244112156467424459456/111147621398050191217839338562729733545513140625:ℝ), (112908078618159629623393499947684211296802123528128/12349735710894465690871037618081081505057015625:ℝ)],
![(23431838837804108145489845852778973788850404353601557/5927873141229343531618098056678919122427367500000:ℝ), (699262003990228413147550579953233152393824769801133/88918097118440152974271470850183786836410512500:ℝ), (2171554104869105117569262876208228105197247812145248/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (6703081009146119105121075327292021794315227668319/809352279549179703516924321338561757515416576000000:ℝ) admission09_09_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission09_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]
def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(125371460861813341568112795545296/625102676748004498176796875:ℝ), (328897239863807509913857962926288/625102676748004498176796875:ℝ), (282307404624418911055645575071488/625102676748004498176796875:ℝ), (26268361994901573223300135896832/208367558916001499392265625:ℝ)],
![(166774606202241774890910087418792/625102676748004498176796875:ℝ), (415388899848633306982094727404456/625102676748004498176796875:ℝ), (331417081363659743286057015978496/625102676748004498176796875:ℝ), (27617351492685387603624125330944/208367558916001499392265625:ℝ)],
![(12259750336127545680420146462447/208367558916001499392265625:ℝ), (24404329393250380035039557902447/208367558916001499392265625:ℝ), (1142207752845641677347709312/19611064368564847001625:ℝ), (0:ℝ)]]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (175077974721902367735617677659/145659480971936792151162880000000:ℝ) admission09_10_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission09_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]
def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9898782630407559371890749155265419895501834326584073/4445904855922007648713573542509189341820525625000:ℝ), (1809340816147811808234208490714794899879674651581892/555738106990250956089196692813648667727565703125:ℝ), (64989143024298882186107880943690098607721985575704/61748678554472328454355188090405407525285078125:ℝ)],
![(3891122450085320186242914355881777515036852361787381/3556723884737606118970858834007351473456420500000:ℝ), (595984670489417418870876684331052228284312872537221/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (342088191024366804454127990444694847218070089248611/1011690349436474629396155401673202196894270720000000:ℝ) admission09_11_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission09_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]
def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission09_12_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission09_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]
def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission09_13_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission09_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]
def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission09_14_coefficients (15/32:ℝ) (63/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission09_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission09_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]
theorem admission09_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (63/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
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
