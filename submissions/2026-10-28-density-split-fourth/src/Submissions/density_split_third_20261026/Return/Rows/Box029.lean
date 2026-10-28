/- Fourth density transition: exact return rectangle 029.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row029_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5421320184987689103207636556/531037727683171875:ℝ), (349772842992800094418810814864/13275943192079296875:ℝ), (293040587328340360898640867328/13275943192079296875:ℝ), (26266901014488909453361676288/4425314397359765625:ℝ)],
![(191858437731473086644018756032/13275943192079296875:ℝ), (462163774709902596064803536128/13275943192079296875:ℝ), (69788086792229353360026959872/2655188638415859375:ℝ), (26211668180338880996691673088/4425314397359765625:ℝ)],
![(56490889095297303198140146432/13275943192079296875:ℝ), (112887543885042665177421169664/13275943192079296875:ℝ), (56396701316694015579181023232/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row029_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (511604319535257394894417/1546759489841971200000000:ℝ) row029_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row029_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row029_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row029_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_oldSmall_coefficients]
def row029_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(43955336746784647870926284/59004191964796875:ℝ), (23962521459396337578501934864/13275943192079296875:ℝ), (6096194056419787460361035776/4425314397359765625:ℝ), (4215970458765244912666148864/13275943192079296875:ℝ)],
![(15546854228437028278477316032/13275943192079296875:ℝ), (35191574710046262331149776128/13275943192079296875:ℝ), (4761945577341786335530319872/2655188638415859375:ℝ), (4164924823551386360704139264/13275943192079296875:ℝ)],
![(5708276419421502881886706432/13275943192079296875:ℝ), (3794281299672620844571429888/4425314397359765625:ℝ), (5674609043819350751727583232/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row029_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2744059323916584878963/171862165537996800000000:ℝ) row029_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row029_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row029_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row029_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_oldSwitch_coefficients]
def row029_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1041507357936778495276/1419959109375:ℝ), (63021752573929335593744/35498977734375:ℝ), (48016997190500702937088/35498977734375:ℝ), (3677607277848485429248/11832992578125:ℝ)],
![(40999248715675991617472/35498977734375:ℝ), (92722568387143929541888/35498977734375:ℝ), (12524283890694005850112/7099795546875:ℝ), (3632628301816605442048/11832992578125:ℝ)],
![(15097389620282385455872/35498977734375:ℝ), (30107400015539111404544/35498977734375:ℝ), (15010118545044625948672/35498977734375:ℝ), (0:ℝ)] ]
theorem row029_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (70343078137911307/4135930675200000000:ℝ) row029_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row029_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row029_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row029_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_newSwitch_coefficients]
def row029_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(707225818140255691392420918209/4726587853125000000000:ℝ), (87839051111154825306125644177/295411740820312500000:ℝ), (1363722361197983073608234104/9231616900634765625:ℝ), (0:ℝ)],
![(17987929659160903268054225441/59082348164062500000:ℝ), (2242679783574470815177652209/3692646760253906250:ℝ), (2817203718114331902074820992/9231616900634765625:ℝ), (7004231264318135168717824/3077205633544921875:ℝ)],
![(11613044457946725077825024153/73852935205078125000:ℝ), (2928420879060893181319601618/9231616900634765625:ℝ), (303983010886558634324744192/1846323380126953125:ℝ), (14357198571943428733467136/3077205633544921875:ℝ)] ]
theorem row029_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (13424704129445464765251/11747997830348800000000000000:ℝ) row029_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row029_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row029_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row029_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row029_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
