/- Fourth density transition: exact return rectangle 025.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row025_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(209073008422751503312826608/13275943192079296875:ℝ), (570664440778694303820387056/13275943192079296875:ℝ), (514481957454846286829868988/13275943192079296875:ℝ), (10192653207688718254924736/885062879471953125:ℝ)],
![(260826370743232157487636608/13275943192079296875:ℝ), (671214526692289821140784256/13275943192079296875:ℝ), (560705918029148299822534688/13275943192079296875:ℝ), (10021082105890573990459136/885062879471953125:ℝ)],
![(434484976912576036881152/106207545536634375:ℝ), (865908680639406062658304/106207545536634375:ℝ), (431430147902543820777152/106207545536634375:ℝ), (0:ℝ)] ]
theorem row025_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (195125475056495716981259/618703795936788480000000:ℝ) row025_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row025_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row025_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row025_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_oldSmall_coefficients]
def row025_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1441961772171595997718512/1475104799119921875:ℝ), (32858160859668034890867056/13275943192079296875:ℝ), (8972867114102747077802996/4425314397359765625:ℝ), (1407489398240066877214208/2655188638415859375:ℝ)],
![(227177807762101870423168/163900533235546875:ℝ), (42741303280534292217264256/13275943192079296875:ℝ), (30560498624959183425574688/13275943192079296875:ℝ), (1243846105795560780017408/2655188638415859375:ℝ)],
![(5567158028820134160128/11800838392959375:ℝ), (99037897416377603778304/106207545536634375:ℝ), (48939231974585191337152/106207545536634375:ℝ), (0:ℝ)] ]
theorem row025_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6496950949654919858131/412469197291192320000000:ℝ) row025_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row025_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row025_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row025_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_oldSwitch_coefficients]
def row025_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(34060131519959513968/35498977734375:ℝ), (86139876872848094576/35498977734375:ℝ), (70449978405971785948/35498977734375:ℝ), (1224569547509817856/2366598515625:ℝ)],
![(48399341915922723968/35498977734375:ℝ), (112274708787552155776/35498977734375:ℝ), (80083124233613135648/35498977734375:ℝ), (1080279986878080256/2366598515625:ℝ)],
![(132485976238644992/283991821875:ℝ), (261932956573705984/283991821875:ℝ), (129461959530060992/283991821875:ℝ), (0:ℝ)] ]
theorem row025_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (55616639404268953/3308744540160000000:ℝ) row025_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row025_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row025_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row025_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_newSwitch_coefficients]
def row025_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(32206365762656652445392611/189063514125000000000:ℝ), (1572581697470823675649064581/4726587853125000000000:ℝ), (767847648599690075169016931/4726587853125000000000:ℝ), (0:ℝ)],
![(191167062170392937094478999/472658785312500000000:ℝ), (392175916361244542564314997/472658785312500000000:ℝ), (218959448459115716932501789/472658785312500000000:ℝ), (1984566726993492837260699/52517642812500000000:ℝ)],
![(259998312860628772576192759/945317570625000000000:ℝ), (584165576117991044309608997/945317570625000000000:ℝ), (396950492988579992952490117/945317570625000000000:ℝ), (8076558423313936752140431/105035285625000000000:ℝ)] ]
theorem row025_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (147869567236172315104546441/451123116685393920000000000000:ℝ) row025_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row025_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row025_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row025_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row025_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
