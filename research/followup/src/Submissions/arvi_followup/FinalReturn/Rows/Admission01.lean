/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_followup.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission01_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission01_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission01_00_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission01_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_00_coefficients]
def admission01_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission01_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission01_01_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission01_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_01_coefficients]
def admission01_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission01_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission01_02_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission01_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_02_coefficients]
def admission01_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29663258377332839348906720/8001314262374457576663:ℝ), (38939310542018260266661088/8001314262374457576663:ℝ), (1051526118102804066417152/889034918041606397407:ℝ)],
![(20113320085778039153605568/8001314262374457576663:ℝ), (19914597017053528433605568/8001314262374457576663:ℝ), (0:ℝ)]]
theorem admission01_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (348603519024612843355699/341389408527976856604288:ℝ) admission01_03_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission01_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_03_coefficients]
def admission01_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(72589482931725909652509977091/130740429123765646677500000:ℝ), (544:ℝ), (0:ℝ)],
![(60855967024546726772910160363/65370214561882823338750000:ℝ), (87662332940842433916675366544/69455852972000499797421875:ℝ), (23827880814485073016680183272/69455852972000499797421875:ℝ)]]
theorem admission01_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (8935455305431902381255068727/66939099711368011098880000000:ℝ) admission01_04_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission01_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_04_coefficients]
def admission01_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4762786485752109411733113202471/6667761885312047980552500000:ℝ), (283025064723333831822318961382/208367558916001499392265625:ℝ), (44357285260882786782121299272/69455852972000499797421875:ℝ)],
![(134383414775038766251410386543/3333880942656023990276250000:ℝ), (4508587983259671463237052/98055321842824235008125:ℝ), (0:ℝ)]]
theorem admission01_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (64774267924864127826353014957/568982347546628094340480000000:ℝ) admission01_05_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission01_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_05_coefficients]
def admission01_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(184707133967352104239710765474291940777409502176446901/4112461991727857075060055526821000141183986203125:ℝ), (1808497048821311197603914638459665426306391991060434633/20562309958639285375300277634105000705919931015625:ℝ), (885395690222551279330325070116779655168144480178200128/20562309958639285375300277634105000705919931015625:ℝ), (0:ℝ)],
![(248103119712078564386930191649919733435554987589495898/4112461991727857075060055526821000141183986203125:ℝ), (2725150669033978362393312338963808577756117304059022402/20562309958639285375300277634105000705919931015625:ℝ), (1769269915327210761158079930310607970805702168465052032/20562309958639285375300277634105000705919931015625:ℝ), (6314999686572049541491187817809720567825773385633536/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission01_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (4277450323336859490514843248593955910382143242965623/22459525757489736772594649917145088771052809984000000:ℝ) admission01_06_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission01_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_06_coefficients]
def admission01_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(612424711278322486158875319957236823683445351893887/209219052043388595233579931412197145497436500000:ℝ), (766922252115394764460168894662560074156854247175906/185246035663416985363065564271216222575855234375:ℝ), (15337954367435139867728218286854270002605961575704/12349735710894465690871037618081081505057015625:ℝ)],
![(2835432631610196387070761270898567084476504609718999/1778361942368803059485429417003675736728210250000:ℝ), (290250372051435986896257069922127256912758761586564/185246035663416985363065564271216222575855234375:ℝ), (0:ℝ)]]
theorem admission01_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (151462299378422006193816155582685916275733870560077/303507104830942388818846620501960659068281216000000:ℝ) admission01_07_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission01_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_07_coefficients]
def admission01_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (2737692045026928604150741544430625764085642504322264549507972475801871981/681715938446006988339025935976877133684999177647633203200000000000000:ℝ), (10874587773029127349463596671711557344318198231701215893865829821240200471/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ), (5393467093473604801231947538210549993762513564640402665018475451396456509/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ)],
![(1364316375868066147126722256253304716719052668486787373001941283324869627/151492430765779330742005763550417140818888706143918489600000000000000:ℝ), (40512867818560167858052800772961520351040630565398314744796738945426111757/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ), (44173438635166107572601208220753678028767102563113382235649701588457841783/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ), (15933344163475595266998143706806276316261522846361264769225412455995556669/1363431876892013976678051871953754267369998355295266406400000000000000:ℝ)]]
theorem admission01_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1169337771597457372465235970501895629626997257659680942172914532996572737/635405308330631310048517742082568815405228175734261896603238400000000000000:ℝ) admission01_08_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission01_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_08_coefficients]
def admission01_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(109563447694618738246531511288159022137792704994721809/5927873141229343531618098056678919122427367500000:ℝ), (20404477770763003982151692522880612942278071000827373/444590485592200764871357354250918934182052562500:ℝ), (20313188720689160907683549282428092352332745023861536/555738106990250956089196692813648667727565703125:ℝ), (112908078618159629623393499947684211296802123528128/12349735710894465690871037618081081505057015625:ℝ)],
![(23691818588938807028424717474073846991854182682157833/2963936570614671765809049028339459561213683750000:ℝ), (3515940732494554251776667060669790016079931103546789/222295242796100382435678677125459467091026281250:ℝ), (4345837106645484460786385811170099896747655713709504/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission01_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (11290389782412408510455393128717557003964013144731/404676139774589851758462160669280878757708288000000:ℝ) admission01_09_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission01_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_09_coefficients]
def admission01_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(123527911443550399606358220927829/625102676748004498176796875:ℝ), (300205592273064235291050501560789/625102676748004498176796875:ℝ), (46236801148472522631032175701888/125020535349600899635359375:ℝ), (3634885001639737388271239858432/41673511783200299878453125:ℝ)],
![(190830873357990668656622053100788/625102676748004498176796875:ℝ), (87535527099518939903037669859684/125020535349600899635359375:ℝ), (305381111303263170074806862376448/625102676748004498176796875:ℝ), (19523414505982501321680188726272/208367558916001499392265625:ℝ)],
![(6964340842488274752080775520756/69455852972000499797421875:ℝ), (13799263491050645251224417440756/69455852972000499797421875:ℝ), (643088114443028006846460416/6537021456188282333875:ℝ), (0:ℝ)]]
theorem admission01_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (250931063010559088187683143299/36414870242984198037790720000000:ℝ) admission01_10_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission01_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_10_coefficients]
def admission01_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2580180338955700761635944824157165317964986368301541/1046095260216942976167899657060985727487182500000:ℝ), (1939995529810855338274378338906757589848772767627889/555738106990250956089196692813648667727565703125:ℝ), (64989143024298882186107880943690098607721985575704/61748678554472328454355188090405407525285078125:ℝ)],
![(2372354749104327639146263716901901839858169276372681/1778361942368803059485429417003675736728210250000:ℝ), (726639384152460948911046532523014918253410988583218/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission01_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (207600488463351523456749678253173104075878661510639/505845174718237314698077700836601098447135360000000:ℝ) admission01_11_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission01_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_11_coefficients]
def admission01_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission01_12_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission01_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission01_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (51/128:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission01_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission01_12_coefficients]
def admission01_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission01_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission01_13_coefficients (51/128:ℝ) (27/64:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
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
