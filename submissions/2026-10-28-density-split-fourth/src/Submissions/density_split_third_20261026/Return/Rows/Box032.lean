/- Fourth density transition: exact return rectangle 032.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row032_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4856839888286684830832623216/13275943192079296875:ℝ), (10936286309780047402833341552/13275943192079296875:ℝ), (7325772821924523938230480156/13275943192079296875:ℝ), (83085365577693044419588288/885062879471953125:ℝ)],
![(8450008088168020167690445568/13275943192079296875:ℝ), (18096280782306644032642982656/13275943192079296875:ℝ), (10890072052977661756554377408/13275943192079296875:ℝ), (82913794475894900155122688/885062879471953125:ℝ)],
![(3595725459674926687293156352/13275943192079296875:ℝ), (7167682971692926870321531904/13275943192079296875:ℝ), (3572004038966653782928375552/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row032_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1344359164183654322319977/3959704293995446272000000:ℝ) row032_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row032_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row032_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row032_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_oldSmall_coefficients]
def row032_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(441443955400122469019903216/13275943192079296875:ℝ), (938029214974885194551501552/13275943192079296875:ℝ), (560289802788693835867460156/13275943192079296875:ℝ), (12732704817921089892484864/2655188638415859375:ℝ)],
![(820778022430903599591885568/13275943192079296875:ℝ), (1687265092926994282295462656/13275943192079296875:ℝ), (929414959671784865955017408/13275943192079296875:ℝ), (12569061525476583795288064/2655188638415859375:ℝ)],
![(380173373334017893977316352/13275943192079296875:ℝ), (751732472708290030889851904/13275943192079296875:ℝ), (123866887865754412270845184/4425314397359765625:ℝ), (0:ℝ)] ]
theorem row032_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8346141685773429953669/494963036749430784000000:ℝ) row032_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row032_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row032_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row032_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_oldSwitch_coefficients]
def row032_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1164250557293821597936/35498977734375:ℝ), (2472838970356164081392/35498977734375:ℝ), (1475122580894178639676/35498977734375:ℝ), (11095162425764181248/2366598515625:ℝ)],
![(2166290672327937936128/35498977734375:ℝ), (4452424005733157522176/35498977734375:ℝ), (2450611302934481240768/35498977734375:ℝ), (10950872865132443648/2366598515625:ℝ)],
![(1004261651667983752192/35498977734375:ℝ), (1986191823034002627584/35498977734375:ℝ), (982038321153918875392/35498977734375:ℝ), (0:ℝ)] ]
theorem row032_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (23681698200195649/1323497816064000000:ℝ) row032_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row032_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row032_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row032_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_newSwitch_coefficients]
def row032_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(10111380111632620554126547591/945317570625000000000:ℝ), (98736274662661470251338466701/4726587853125000000000:ℝ), (48206223399644187662532201371/4726587853125000000000:ℝ), (0:ℝ)],
![(10313765961156371792452477327/472658785312500000000:ℝ), (101271007322896329077164590337/2363293926562500000000:ℝ), (50258814520259862867873687857/2363293926562500000000:ℝ), (11769108846620991620466559/52517642812500000000:ℝ)],
![(10554847828013249191392604879/945317570625000000000:ℝ), (104377390397579521374544673569/4726587853125000000000:ℝ), (52874411269826970943821623969/4726587853125000000000:ℝ), (27645642662568934318552151/105035285625000000000:ℝ)] ]
theorem row032_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (1842968303830381551564800573/5774375893573042176000000000000:ℝ) row032_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row032_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row032_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row032_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row032_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
