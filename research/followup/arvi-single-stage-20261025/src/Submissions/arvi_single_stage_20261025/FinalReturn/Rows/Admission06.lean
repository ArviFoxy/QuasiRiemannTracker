/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_single_stage_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission06_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission06_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission06_00_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission06_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_00_coefficients]
def admission06_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission06_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission06_01_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission06_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_01_coefficients]
def admission06_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission06_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission06_02_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission06_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_02_coefficients]
def admission06_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1874133967444143307163293184/8001314262374457576663:ℝ), (2478112825216715413259572736/8001314262374457576663:ℝ), (67297671558579460250697728/889034918041606397407:ℝ)],
![(1267688016394498790846639360/8001314262374457576663:ℝ), (1265976789969371059646639360/8001314262374457576663:ℝ), (0:ℝ)]]
theorem admission06_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (5374333871401271113661305/5462230536447629705668608:ℝ) admission06_03_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission06_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_03_coefficients]
def admission06_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(43924575851696962899433108236007/1111293647552007996758750000:ℝ), (39424:ℝ), (0:ℝ)],
![(137219100648494380829227661790161/2222587295104015993517500000:ℝ), (5805976990183069178096763458816/69455852972000499797421875:ℝ), (1524984372127044673067531729408/69455852972000499797421875:ℝ)]]
theorem admission06_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (688030058518256483356640291979/4551858780373024754723840000000:ℝ) admission06_04_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission06_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_04_coefficients]
def admission06_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(91467405380463278538009164934147/2222587295104015993517500000:ℝ), (274259848173748171906872469786483/3333880942656023990276250000:ℝ), (273793933449996322668740555354483/6667761885312047980552500000:ℝ)],
![(0:ℝ), (158842051620442066186403197463/666776188531204798055250000:ℝ), (252554561426496135877458525463/1333552377062409596110500000:ℝ)]]
theorem admission06_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (2796216030203389436469842314052329/29831061703052655032558157824000000:ℝ) admission06_05_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission06_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_05_coefficients]
def admission06_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(492059984971210858146960022788803030614721213250921770576/20562309958639285375300277634105000705919931015625:ℝ), (39259720003247112148888739961443725554813910682995444432/822492398345571415012011105364200028236797240625:ℝ), (489436949458828833389990505417313660352292153823964340224/20562309958639285375300277634105000705919931015625:ℝ), (0:ℝ)],
![(25583015897351642395347935037624031842751646272091460056/822492398345571415012011105364200028236797240625:ℝ), (284401985133598772948191176860065093576538391646945790264/4112461991727857075060055526821000141183986203125:ℝ), (185587216181880919299270771138170114499039724047487823872/4112461991727857075060055526821000141183986203125:ℝ), (3233279839524889365243488162718576930726795973444370432/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission06_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (19107906662926875512296819139854680539942196582160603/89838103029958947090378599668580355084211239936000000:ℝ) admission06_06_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission06_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_06_coefficients]
def admission06_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1536755926545395409200805649860375110180282419468775167/8891809711844015297427147085018378683641051250000:ℝ), (46702236273495005184833409494991965474146675901434016/185246035663416985363065564271216222575855234375:ℝ), (981629079515848951534605970358673280166781540845056/12349735710894465690871037618081081505057015625:ℝ)],
![(1139958834172340209936998395631392814270123332197957/12307003061375799719622348906599832088084500000:ℝ), (3424219579138459997307741635030665866363179313907312/37049207132683397072613112854243244515171046875:ℝ), (0:ℝ)]]
theorem admission06_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (446717920951548448647584357604630613825898630892379/971222735459015644220309185606274109018499891200000:ℝ) admission06_07_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission06_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_07_coefficients]
def admission06_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (24275078532744213469714794600124606205577786866266058921803229640624113897/42607246152875436771189120998554820855312448602977075200000000000000:ℝ), (19454243224555843031039824598565673619426525181024105656613914835489355327/17042898461150174708475648399421928342124979441190830080000000000000:ℝ), (48717811135293521810073778017305176286538825895396837807132096328518548841/85214492305750873542378241997109641710624897205954150400000000000000:ℝ)],
![(76449482788024326813388166330921939810634908177543186643998224148303280283/18936553845722416342750720443802142602361088267989811200000000000000:ℝ), (2147683639219693486120167894554760152634819518074555079436387656973433525271/170428984611501747084756483994219283421249794411908300800000000000000:ℝ), (1115816293451494335172110047351037861924845022895321610403587769632641755323/85214492305750873542378241997109641710624897205954150400000000000000:ℝ), (385993877375357216714592055412368418606507122910464425141754080475689753961/85214492305750873542378241997109641710624897205954150400000000000000:ℝ)]]
theorem admission06_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (638540797361687929049225770017014602109971375908184444619199361170724913203/37537790522917295855173971224570219248555018381839472045483622400000000000000:ℝ) admission06_08_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission06_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_08_coefficients]
def admission06_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(13974403348848164148854087055614629525272588764372504947/1778361942368803059485429417003675736728210250000:ℝ), (3777014085558743062440971732153765327902824793042829948/185246035663416985363065564271216222575855234375:ℝ), (9565427952310720716938602025577824516439008818016432128/555738106990250956089196692813648667727565703125:ℝ), (57808936252497730367177471973214316183962687246401536/12349735710894465690871037618081081505057015625:ℝ)],
![(11001760313882567689928602831520410847871322254251400101/3556723884737606118970858834007351473456420500000:ℝ), (45785031898301211610859537152447227170066585484607874/7409841426536679414522622570848648903034209375:ℝ), (342967370837126204942868937316274380010194134237104128/111147621398050191217839338562729733545513140625:ℝ), (0:ℝ)]]
theorem admission06_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (24485601696221995428544803329791248122702123074301/1294963647278687525627078914141698812024666521600000:ℝ) admission06_09_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission06_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_09_coefficients]
def admission06_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(497971718894051568828808025665902496/625102676748004498176796875:ℝ), (1278901085651328282804488835649476512/625102676748004498176796875:ℝ), (62608511675436754531427010131689472/36770745691059088128046875:ℝ), (5557190640980935154755622789316608/12256915230353029376015625:ℝ)],
![(47362938244043694379982719385060512/41673511783200299878453125:ℝ), (6688139129112649700036244061461152/2451383046070605875203125:ℝ), (85367824988497051622669323661508608/41673511783200299878453125:ℝ), (19032584703908242118714294001729536/41673511783200299878453125:ℝ)],
![(8414571262006788771762932374866344/25004107069920179927071875:ℝ), (16811453033305578555743626457426344/25004107069920179927071875:ℝ), (790289450143850554290286501888/2353327724227781640195:ℝ), (0:ℝ)]]
theorem admission06_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1687680238778921161638566326707/372888271288158187906976972800000:ℝ) admission06_10_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission06_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_10_coefficients]
def admission06_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(143223559456461396707619439291043974091558128256592953/987978856871557255269683009446486520404561250000:ℝ), (23577657530413730441526412195363655326360949511595408/111147621398050191217839338562729733545513140625:ℝ), (4159305153555128459910904380396166310894207076845056/61748678554472328454355188090405407525285078125:ℝ)],
![(1789498024782634425559556525346177400851881744014291/23246561338154288359286659045799682833048500000:ℝ), (8534476463661644769825732506901743172491618373062008/111147621398050191217839338562729733545513140625:ℝ), (0:ℝ)]]
theorem admission06_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (610705520087678297258059968631609601691441078734089/1618704559098359407033848642677123515030833152000000:ℝ) admission06_11_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission06_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_11_coefficients]
def admission06_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission06_12_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission06_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_12_coefficients]
def admission06_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission06_13_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission06_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_13_coefficients]
def admission06_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission06_14_coefficients (231/512:ℝ) (465/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission06_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission06_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission06_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission06_14_coefficients]
theorem admission06_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (465/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission06_00_pos hδ hp
 · exact admission06_01_pos hδ hp
 · exact admission06_02_pos hδ hp
 · exact admission06_03_pos hδ hp
 · exact admission06_04_pos hδ hp
 · exact admission06_05_pos hδ hp
 · exact admission06_06_pos hδ hp
 · exact admission06_07_pos hδ hp
 · exact admission06_08_pos hδ hp
 · exact admission06_09_pos hδ hp
 · exact admission06_10_pos hδ hp
 · exact admission06_11_pos hδ hp
 · exact admission06_12_pos hδ hp
 · exact admission06_13_pos hδ hp
 · exact admission06_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
