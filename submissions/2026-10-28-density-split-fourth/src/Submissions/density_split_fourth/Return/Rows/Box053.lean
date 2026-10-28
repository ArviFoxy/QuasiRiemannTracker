/- Fourth density transition: exact return rectangle 053.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row053_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(550740169001553676700530624/13275943192079296875:ℝ), (1418690714421789918796536128/13275943192079296875:ℝ), (1186600584176922696553667584/13275943192079296875:ℝ), (21243161924368157832177472/885062879471953125:ℝ)],
![(776612006624200253383692032/13275943192079296875:ℝ), (1866398722448061302545529344/13275943192079296875:ℝ), (1405865942938692987015015392/13275943192079296875:ℝ), (21071590822570013567711872/885062879471953125:ℝ)],
![(228429097416237927118495408/13275943192079296875:ℝ), (455396507192601624260884016/13275943192079296875:ℝ), (226970166675286255065826108/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row053_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (27866871708084267819989209/79194085879908925440000000:ℝ) row053_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row053_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row053_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row053_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_oldSmall_coefficients]
def row053_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(13601385186229605861150208/4425314397359765625:ℝ), (99281102216994229081776128/13275943192079296875:ℝ), (76645254462942194675387584/13275943192079296875:ℝ), (3633195258702664240412416/2655188638415859375:ℝ)],
![(21047755654571209545417344/4425314397359765625:ℝ), (142625788531661130451049344/13275943192079296875:ℝ), (10759452661097884929819488/1475104799119921875:ℝ), (3469551966258158143215616/2655188638415859375:ℝ)],
![(7726139236087191486045136/4425314397359765625:ℝ), (45841281070847844515164016/13275943192079296875:ℝ), (22665326201110976417966108/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row053_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (115586457729340592150507/6599507156659077120000000:ℝ) row053_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row053_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row053_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row053_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_oldSwitch_coefficients]
def row053_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(107306067606981128704/35498977734375:ℝ), (260893969439069861888/35498977734375:ℝ), (201152771878738588864/35498977734375:ℝ), (3170586898178323712/2366598515625:ℝ)],
![(166284146430499993472/35498977734375:ℝ), (375350698333814909824/35498977734375:ℝ), (254473482146351208032/35498977734375:ℝ), (3026297337546586112/2366598515625:ℝ)],
![(61199615457386278768/35498977734375:ℝ), (121063516551754234736/35498977734375:ℝ), (59870309381228893468/35498977734375:ℝ), (0:ℝ)] ]
theorem row053_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (981041456643546841/52939912642560000000:ℝ) row053_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row053_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row053_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row053_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_newSwitch_coefficients]
def row053_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(592307095176583474867329799/945317570625000000000:ℝ), (5987709034710784028074221481/4726587853125000000000:ℝ), (3224980022354731443796138121/4726587853125000000000:ℝ), (4384008000006881883814303/105035285625000000000:ℝ)],
![(115037105444910100674793211/94531757062500000000:ℝ), (5621003974484915159311323097/2363293926562500000000:ℝ), (2752867951843642721570222897/2363293926562500000000:ℝ), (27658303067993080619527/10503528562500000000:ℝ)],
![(596759976605643692494800127/945317570625000000000:ℝ), (5825949328707379762102384309/4726587853125000000000:ℝ), (2843761510283986869950757299/4726587853125000000000:ℝ), (0:ℝ)] ]
theorem row053_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (557000691496866077975371897/1804492466741575680000000000000:ℝ) row053_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row053_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row053_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row053_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row053_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
