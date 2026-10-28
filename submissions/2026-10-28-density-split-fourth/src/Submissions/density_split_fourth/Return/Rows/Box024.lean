/- Fourth density transition: exact return rectangle 024.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row024_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(287614433637460544015708864/2655188638415859375:ℝ), (4090966252126492298802609488/13275943192079296875:ℝ), (3868455840121064540634110416/13275943192079296875:ℝ), (45020778859196379607837324/491701599706640625:ℝ)],
![(326487483847236387566049664/2655188638415859375:ℝ), (4458283364652255932483250688/13275943192079296875:ℝ), (4020757242394104153608508416/13275943192079296875:ℝ), (44255917277270301209000224/491701599706640625:ℝ)],
![(1719630266117252235900608/106207545536634375:ℝ), (3433170206741581424593216/106207545536634375:ℝ), (1713546384800042983692608/106207545536634375:ℝ), (0:ℝ)] ]
theorem row024_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5475599004640094654728181/17598685751090872320000000:ℝ) row024_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row024_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row024_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row024_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_oldSmall_coefficients]
def row024_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(16096010630458412971228864/2655188638415859375:ℝ), (72738372660682414089216496/4425314397359765625:ℝ), (195256674804523401131390416/13275943192079296875:ℝ), (2130405945695703251257324/491701599706640625:ℝ)],
![(19622959735440242147169664/2655188638415859375:ℝ), (246733167879500545306290688/13275943192079296875:ℝ), (199677934962496132537788416/13275943192079296875:ℝ), (1891044389482202190920224/491701599706640625:ℝ)],
![(64481272593838372713536/35402515178878125:ℝ), (384574525446204589073216/106207545536634375:ℝ), (191136464482278265932608/106207545536634375:ℝ), (0:ℝ)] ]
theorem row024_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (268807241482953875833181/17598685751090872320000000:ℝ) row024_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row024_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row024_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row024_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_oldSwitch_coefficients]
def row024_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(42185787697437527744/7099795546875:ℝ), (571409420389442986448/35498977734375:ℝ), (510723124715015709136/35498977734375:ℝ), (5564479739715719404/1314776953125:ℝ)],
![(51518956799477724544/7099795546875:ℝ), (646902252695767771648/35498977734375:ℝ), (522462272859048667136/35498977734375:ℝ), (4931527651920630304/1314776953125:ℝ)],
![(511844742288075968/283991821875:ℝ), (1017686388743983936/283991821875:ℝ), (505856625650907968/283991821875:ℝ), (0:ℝ)] ]
theorem row024_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (768776721254460701/47057700126720000000:ℝ) row024_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row024_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row024_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row024_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_newSwitch_coefficients]
def row024_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2998042889051155960708773911/4726587853125000000000:ℝ), (5922738072754707581450254009/4726587853125000000000:ℝ), (2925120278898834331396247723/4726587853125000000000:ℝ), (0:ℝ)],
![(3712486910768813382122625551/2363293926562500000000:ℝ), (7829937795700611939838618333/2363293926562500000000:ℝ), (4600818069813157886362862933/2363293926562500000000:ℝ), (160973238751581983003424217/787764642187500000000:ℝ)],
![(5905603921444173191479329071/4726587853125000000000:ℝ), (14139143453150445561544017613/4726587853125000000000:ℝ), (10644791817671445055774252013/4726587853125000000000:ℝ), (803593755452737077820171157/1575529284375000000000:ℝ)] ]
theorem row024_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (2916739800395736643473083729/18044924667415756800000000000000:ℝ) row024_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row024_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row024_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row024_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row024_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
