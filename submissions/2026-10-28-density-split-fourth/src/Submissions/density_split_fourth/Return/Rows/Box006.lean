/- Fourth density transition: exact return rectangle 006.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row006_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3974421771384018449435924/215070279711684609375:ℝ), (56242872849902192093738504/1075351398558423046875:ℝ), (52977368672420636335071973/1075351398558423046875:ℝ), (615019976912624064910207/39827829576237890625:ℝ)],
![(18874609275087102572236544/1075351398558423046875:ℝ), (50926827934519459636289152/1075351398558423046875:ℝ), (45468572879802363755910272/1075351398558423046875:ℝ), (496792218501542999698432/39827829576237890625:ℝ)],
![(2093889061026859309057024/1075351398558423046875:ℝ), (4066634460745928789838848/1075351398558423046875:ℝ), (1974807535947483880781824/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row006_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (10002401837268314405987/96672468115123200000000:ℝ) row006_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row006_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row006_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_oldSmall_coefficients]
def row006_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(191712159726758486819677/358450466186141015625:ℝ), (1100581378829198895846737/1075351398558423046875:ℝ), (526396573556571108825206/1075351398558423046875:ℝ), (0:ℝ)],
![(503774671416074013705122/358450466186141015625:ℝ), (2916024504492258148525618/1075351398558423046875:ℝ), (1433074943188177973746738/1075351398558423046875:ℝ), (2858479650366240704054/119483488728713671875:ℝ)],
![(144774300016725502910429/71690093237228203125:ℝ), (5398443112837240139717081/1075351398558423046875:ℝ), (4371834444227000076740057/1075351398558423046875:ℝ), (127018183334692008964379/119483488728713671875:ℝ)] ]
theorem row006_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (194569058236480541121253/10999178594431795200000000:ℝ) row006_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row006_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row006_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_oldSwitch_coefficients]
def row006_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1520339954750558551/2875417196484375:ℝ), (2911329465086261777/2875417196484375:ℝ), (1393465758509140726/2875417196484375:ℝ), (0:ℝ)],
![(4054210455250698086/2875417196484375:ℝ), (7876131889310112178/2875417196484375:ℝ), (3942024543165963698/2875417196484375:ℝ), (4193062200242578/106496933203125:ℝ)],
![(1162948630299290327/575083439296875:ℝ), (14473638580156072601/2875417196484375:ℝ), (11738151816765689497/2875417196484375:ℝ), (113869001692817353/106496933203125:ℝ)] ]
theorem row006_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4970290218817223117/264699563212800000000:ℝ) row006_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row006_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_newSwitch_coefficients]
def row006_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(413317829616204746444965197391/1093440648141506250000000000:ℝ), (780963952891346147813598112601/1093440648141506250000000000:ℝ), (36858050842045118226768585271/109344064814150625000000000:ℝ), (0:ℝ)],
![(1255912790146523867342493195787/546720324070753125000000000:ℝ), (3077651887189221820451614257953/546720324070753125000000000:ℝ), (2451373328053706918965856032609/546720324070753125000000000:ℝ), (7757212554269078489498234203/6749633630503125000000000:ℝ)],
![(3232424550453007252286223284491/1093440648141506250000000000:ℝ), (8634955340422691114173373020961/1093440648141506250000000000:ℝ), (1531994561517306446847272399213/218688129628301250000000000:ℝ), (5569464944015102211636691999/2699853452201250000000000:ℝ)] ]
theorem row006_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (355141595723071215419387721461/100657832302057881600000000000000:ℝ) row006_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row006_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row006_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
