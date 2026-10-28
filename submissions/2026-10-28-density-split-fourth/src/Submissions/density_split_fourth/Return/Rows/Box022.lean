/- Fourth density transition: exact return rectangle 022.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row022_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(10546347207291015366220307596/13275943192079296875:ℝ), (1230195962749391066185812368/531037727683171875:ℝ), (29872229653604329004672806912/13275943192079296875:ℝ), (3221225688392331667916455936/4425314397359765625:ℝ)],
![(11233111971972220701473307296/13275943192079296875:ℝ), (1278448490799695803821818752/531037727683171875:ℝ), (30226080391238816054124019712/13275943192079296875:ℝ), (3165992854242303211246452736/4425314397359765625:ℝ)],
![(6817766025581195756522432/106207545536634375:ℝ), (13623402953582255778628864/106207545536634375:ℝ), (6805643372176773817106432/106207545536634375:ℝ), (0:ℝ)] ]
theorem row022_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5934253963235546089337/19334493623024640000000:ℝ) row022_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row022_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row022_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row022_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_oldSmall_coefficients]
def row022_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(558761786783525725655487596/13275943192079296875:ℝ), (21154224521497977752897456/177012575894390625:ℝ), (1497375669499871584873766912/13275943192079296875:ℝ), (469569967730064743126007808/13275943192079296875:ℝ)],
![(22267996291399949517518048/491701599706640625:ℝ), (64795912568935180198778752/531037727683171875:ℝ), (1437187614115964397972979712/13275943192079296875:ℝ), (418524332516206191163998208/13275943192079296875:ℝ)],
![(750776576762346285482432/106207545536634375:ℝ), (1496972987831751636548864/106207545536634375:ℝ), (248734055962331382022144/35402515178878125:ℝ), (0:ℝ)] ]
theorem row022_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (286315833041622080587/19334493623024640000000:ℝ) row022_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row022_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row022_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row022_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_oldSwitch_coefficients]
def row022_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1463195397902499351916/35498977734375:ℝ), (166092967219982394128/1419959109375:ℝ), (3916429157523083517952/35498977734375:ℝ), (409099561695195693056/11832992578125:ℝ)],
![(1575832111416096115616/35498977734375:ℝ), (169647092659636254592/1419959109375:ℝ), (3757710519623569866752/35498977734375:ℝ), (364120585663315705856/11832992578125:ℝ)],
![(1987692532315623872/283991821875:ℝ), (3963498706526911744/283991821875:ℝ), (1975821153406287872/283991821875:ℝ), (0:ℝ)] ]
theorem row022_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (820766314997627/51699133440000000:ℝ) row022_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row022_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row022_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row022_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_newSwitch_coefficients]
def row022_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(11268471692220082788221812889/4726587853125000000000:ℝ), (1399603045956701161359198697/295411740820312500000:ℝ), (21729691676332848640976824/9231616900634765625:ℝ), (0:ℝ)],
![(3558294764997341767637719727/590823481640625000000:ℝ), (474971911081979952687336031/36926467602539062500:ℝ), (71287682196572502428531264/9231616900634765625:ℝ), (2713770734946090287277056/3077205633544921875:ℝ)],
![(1789011071483280392610273353/295411740820312500000:ℝ), (283394299865305022142513049/18463233801269531250:ℝ), (115991688036683996944688512/9231616900634765625:ℝ), (10066738042571383852026368/3077205633544921875:ℝ)] ]
theorem row022_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (647907931098007406411/183562466099200000000000000:ℝ) row022_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row022_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row022_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row022_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row022_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
