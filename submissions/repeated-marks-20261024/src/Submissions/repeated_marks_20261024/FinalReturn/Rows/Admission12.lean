/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(34483089485293/14483089485293:ℝ), (0:ℝ)]]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (52415447426465/28966178970586:ℝ) admission12_00_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission12_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]
def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(20000000000000/14483089485293:ℝ), (0:ℝ)]]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (18966178970586/14483089485293:ℝ) admission12_01_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission12_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]
def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(9560923431685/14483089485293:ℝ), (0:ℝ)]]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (19405255538901/28966178970586:ℝ) admission12_02_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission12_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]
def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1912052383693984960/130347805367637:ℝ), (2521569299872746688/130347805367637:ℝ), (68504101797640192/14483089485293:ℝ)],
![(1292517727058752000/130347805367637:ℝ), (1285317727058752000/130347805367637:ℝ), (0:ℝ)]]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2688018713602645/2780753181176256:ℝ) admission12_03_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission12_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]
def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2809435951471311/1114083806561:ℝ), (2496:ℝ), (0:ℝ)],
![(57330127691452104/14483089485293:ℝ), (76818672426019328/14483089485293:ℝ), (19870981671834624/14483089485293:ℝ)]]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (174647299850109/1140821817918464:ℝ) admission12_04_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission12_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]
def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(250064951457653703/95283483455875:ℝ), (143902913396406472444/27155792784924375:ℝ), (5561595265771784728/2088907137301875:ℝ)],
![(0:ℝ), (26291311033302992/217246342279395:ℝ), (23553556974291992/217246342279395:ℝ)]]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (19989765963599101621/237290938127040512000:ℝ) admission12_05_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission12_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]
def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(26751468425562706846026609970124608/69850040385988550335877517717:ℝ), (52934900239280159869560652424955712/69850040385988550335877517717:ℝ), (8728940270584022539858014151610368/23283346795329516778625839239:ℝ), (0:ℝ)],
![(34906976828250754199796947275886080/69850040385988550335877517717:ℝ), (5919682065749095528214551710000640/5373080029691426948913655209:ℝ), (16590736189733592189240012977766400/23283346795329516778625839239:ℝ), (857760294143685707369757108797440/7761115598443172259541946413:ℝ)]]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (5124779179136396661941503925465/23842147118417425181312859380736:ℝ) admission12_06_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission12_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]
def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20292069926333769934467726571649/1887838929351041900969662641:ℝ), (29570707021008222432330217073344/1887838929351041900969662641:ℝ), (1041546395132297325715880924160/209759881039004655663295849:ℝ)],
![(10578140704636907684591500038680/1887838929351041900969662641:ℝ), (10485827454724995707420141601280/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (11866576767457814583351507925/26849264772992595924901868672:ℝ) admission12_07_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission12_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]
def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (2866508288715375065580618902363240099851741384537/491624721185167161710849646093750000000000000:ℝ), (34967482073186277284686571737683365593202371136257/2949748327111002970265097876562500000000000000:ℝ), (3547989333990573992482712875916870186255884565807/589949665422200594053019575312500000000000000:ℝ)],
![(4373963873888843404499441929119092899933949987663/65549962824688954894779952812500000000000000:ℝ), (39509370539251416103124202722373057562607392869559/196649888474066864684339858437500000000000000:ℝ), (119124961498506092746274388301216396291954745799053/589949665422200594053019575312500000000000000:ℝ), (39956681531199402886875876687159916306038117079343/589949665422200594053019575312500000000000000:ℝ)]]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (245540569607789021765430745231798390496245848524497/13196950621221320749007766489661440000000000000000000:ℝ) admission12_08_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission12_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]
def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1777983588858233771170698433187010946391/14748741635555014851325489382812500:ℝ), (23139031801114761154560724014019612958351/73743708177775074256627446914062500:ℝ), (4910089402081804789297133756249659681264/18435927044443768564156861728515625:ℝ), (29954217243509807379446577382911341312/409687267654305968092374705078125:ℝ)],
![(14123096587245590746754895221365005598/335198673535341246621033849609375:ℝ), (309395019537797399649214409776403082706/3687185408888753712831372345703125:ℝ), (154014528753575979905726934033184896128/3687185408888753712831372345703125:ℝ), (0:ℝ)]]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (118963931193313470868769787935287877/8054779431897778777470560601600000000:ℝ) admission12_09_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission12_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]
def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(803938419959411150649586816/254585557358666015625:ℝ), (1154879521314638003457759584/141436420754814453125:ℝ), (88301450824627843789882528/12857856432255859375:ℝ), (2367801846634720257326468096/1272927786793330078125:ℝ)],
![(1119837339985391143357437952/254585557358666015625:ℝ), (2721559001422404311081835008/254585557358666015625:ℝ), (417679671495736157834271232/50917111471733203125:ℝ), (486751283541667621446959104/254585557358666015625:ℝ)],
![(268250050136758761332736/226298273207703125:ℝ), (253205380567388561262592/107193918887859375:ℝ), (2396345779549553811994624/2036684458869328125:ℝ), (0:ℝ)]]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (4990879522372458229939/1483068363294003200000000:ℝ) admission12_10_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission12_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]
def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5672306409358644361066393331029/629279643117013966989887547:ℝ), (24868824393088575319556743596224/1887838929351041900969662641:ℝ), (882524608721949445538465881088/209759881039004655663295849:ℝ)],
![(2925044535157869999739608599800/629279643117013966989887547:ℝ), (8687398968927155109321117094400/1887838929351041900969662641:ℝ), (0:ℝ)]]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (29146945700407764822936425845/80547794318977787774705606016:ℝ) admission12_11_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission12_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]
def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (41135459/2500000000:ℝ) admission12_12_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission12_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]
def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (525770610335894707/50000000000000000000:ℝ) admission12_13_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission12_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]
def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission12_14_coefficients (117/256:ℝ) (15/32:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission12_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission12_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]
theorem admission12_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (117/256:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission12_00_pos hδ hp
 · exact admission12_01_pos hδ hp
 · exact admission12_02_pos hδ hp
 · exact admission12_03_pos hδ hp
 · exact admission12_04_pos hδ hp
 · exact admission12_05_pos hδ hp
 · exact admission12_06_pos hδ hp
 · exact admission12_07_pos hδ hp
 · exact admission12_08_pos hδ hp
 · exact admission12_09_pos hδ hp
 · exact admission12_10_pos hδ hp
 · exact admission12_11_pos hδ hp
 · exact admission12_12_pos hδ hp
 · exact admission12_13_pos hδ hp
 · exact admission12_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
