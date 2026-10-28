/- Fourth density transition: exact return rectangle 013.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row013_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(44988641234000615145287/106207545536634375:ℝ), (13381970019531408048455921/13275943192079296875:ℝ), (9998517005632851727814917/13275943192079296875:ℝ), (746384152924936359589957/4425314397359765625:ℝ)],
![(8851984342642160758332806/13275943192079296875:ℝ), (19692389191657610622155458/13275943192079296875:ℝ), (13042186025556052922938598/13275943192079296875:ℝ), (733247735323705130121982/4425314397359765625:ℝ)],
![(3266569480279242494604031/13275943192079296875:ℝ), (6426254719979642836011737/13275943192079296875:ℝ), (3160750542498087077345206/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row013_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (26847998858003603704306277/98992607349886156800000000:ℝ) row013_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row013_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row013_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row013_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_oldSmall_coefficients]
def row013_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(551701119773284455887902/13275943192079296875:ℝ), (1069674583066099339317002/13275943192079296875:ℝ), (19674461657760324402074/491701599706640625:ℝ), (12366282806408631676898/13275943192079296875:ℝ)],
![(222602930804679629653372/2655188638415859375:ℝ), (426061822725591294831524/2655188638415859375:ℝ), (203823010633402948928152/2655188638415859375:ℝ), (0:ℝ)],
![(576565719005458580811058/13275943192079296875:ℝ), (1104869098304748256902818/13275943192079296875:ℝ), (530684293032120469881287/13275943192079296875:ℝ), (1429239825183120352027/13275943192079296875:ℝ)] ]
theorem row013_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6998769137212566998957/395970429399544627200000:ℝ) row013_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row013_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row013_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row013_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_oldSwitch_coefficients]
def row013_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1454519643597219742/35498977734375:ℝ), (2819427621823080842/35498977734375:ℝ), (1397442634666772158/35498977734375:ℝ), (10089684399053686/11832992578125:ℝ)],
![(588128918203711612/7099795546875:ℝ), (1126446565569661604/7099795546875:ℝ), (539265081449699992/7099795546875:ℝ), (0:ℝ)],
![(1526629548050922418/35498977734375:ℝ), (2930198244987353378/35498977734375:ℝ), (1412334538410232327/35498977734375:ℝ), (2096531100121289/11832992578125:ℝ)] ]
theorem row013_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19856002502067437/1058798252851200000:ℝ) row013_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row013_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row013_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row013_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_newSwitch_coefficients]
def row013_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(91842601063990108972861599559/3374816815251562500000000:ℝ), (173183537014019264686184372129/3374816815251562500000000:ℝ), (8155466109668791467132921007/337481681525156250000000:ℝ), (0:ℝ)],
![(111748273425091059047033049853/1687408407625781250000000:ℝ), (226916795932986201206734997717/1687408407625781250000000:ℝ), (259524931556337138303838641347/3374816815251562500000000:ℝ), (3193445187604686240349839791/374979646139062500000000:ℝ)],
![(33788422248844425323546651341/843704203812890625000000:ℝ), (290713682996816081002235446199/3374816815251562500000000:ℝ), (150094257503273871692605904981/2699853452201250000000000:ℝ), (2828820585895690194039582757/299983716911250000000000:ℝ)] ]
theorem row013_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (56961167339441289171901624349/25164458075514470400000000000000:ℝ) row013_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row013_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row013_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row013_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row013_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
