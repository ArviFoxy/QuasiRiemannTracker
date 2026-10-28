/- Fourth density transition: exact return rectangle 004.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row004_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1053911779887441420763052656/1075351398558423046875:ℝ), (3112826605508518127121525872/1075351398558423046875:ℝ), (3064330494077859746263554076/1075351398558423046875:ℝ), (7447515578918410023475136/7965565915247578125:ℝ)],
![(175213889998604486125600768/215070279711684609375:ℝ), (509639191441384898519856128/215070279711684609375:ℝ), (493817037200794095902943232/215070279711684609375:ℝ), (5903375662735111643284736/7965565915247578125:ℝ)],
![(29295713386480395127005184/1075351398558423046875:ℝ), (58137784171155846940909568/1075351398558423046875:ℝ), (28844132920903866213904384/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row004_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13791105112358506710233/154675948984197120000000:ℝ) row004_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row004_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row004_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_oldSmall_coefficients]
def row004_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4459785082407034800470992/358450466186141015625:ℝ), (32468912185323310232926832/1075351398558423046875:ℝ), (24985201512401647933775036/1075351398558423046875:ℝ), (130993175564262098418304/23896697745742734375:ℝ)],
![(1280238606284192392997632/71690093237228203125:ℝ), (7583496173291705777952512/215070279711684609375:ℝ), (3743309981657297738959616/215070279711684609375:ℝ), (0:ℝ)],
![(24602678136406539108535168/358450466186141015625:ℝ), (207672743931791613473990528/1075351398558423046875:ℝ), (194247392243833585484265344/1075351398558423046875:ℝ), (1341796456436292776352896/23896697745742734375:ℝ)] ]
theorem row004_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (43023297010092258992533/3299753578329538560000000:ℝ) row004_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row004_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row004_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_oldSwitch_coefficients]
def row004_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(34336168948498646896/2875417196484375:ℝ), (82673706900356124272/2875417196484375:ℝ), (62821641258447604156/2875417196484375:ℝ), (107271311543827328/21299386640625:ℝ)],
![(10226937083896873216/575083439296875:ℝ), (20198144096415479552/575083439296875:ℝ), (9972585098458606336/575083439296875:ℝ), (0:ℝ)],
![(196742983814246253184/2875417196484375:ℝ), (553466813799465404288/2875417196484375:ℝ), (517558812436763645824/2875417196484375:ℝ), (1191334734141811072/21299386640625:ℝ)] ]
theorem row004_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (376784465573767679/26469956321280000000:ℝ) row004_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row004_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row004_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_newSwitch_coefficients]
def row004_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(62987284143490363597505641403/13668008101768828125000000:ℝ), (619330900923365719298835472391/68340040508844140625000000:ℝ), (1217811517109983050469992295879/273360162035376562500000000:ℝ), (0:ℝ)],
![(15303844260266826747627135733/213562626590137939453125:ℝ), (213700232460766870067364988582/1067813132950689697265625:ℝ), (198295596803440508007486270107/1067813132950689697265625:ℝ), (603575768433965383701006667/10546302547661132812500:ℝ)],
![(52038464854695466392944577409/427125253180275878906250:ℝ), (755185728918923989746174429583/2135626265901379394531250:ℝ), (730413208136883779441029430903/2135626265901379394531250:ℝ), (581274742825641754982000033/5273151273830566406250:ℝ)] ]
theorem row004_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2573779305073247324895943199/2516445807551447040000000000000:ℝ) row004_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row004_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row004_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
