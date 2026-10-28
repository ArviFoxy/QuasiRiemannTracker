/- Fourth density transition: exact return rectangle 070.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row070_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1395608081436171100121728/331898579801982421875:ℝ), (2867954147896676343670016/331898579801982421875:ℝ), (3357245890190796449280971/663797159603964843750:ℝ), (27007113780702107687293/44253143973597656250:ℝ)],
![(2556586310873522453682176/331898579801982421875:ℝ), (5047539821876919751239712/331898579801982421875:ℝ), (2697402571875852332361296/331898579801982421875:ℝ), (13209071613443965653584/22126571986798828125:ℝ)],
![(1164125119675473853560448/331898579801982421875:ℝ), (2190586449491728158989696/331898579801982421875:ℝ), (1031101136330186705429248/331898579801982421875:ℝ), (0:ℝ)] ]
theorem row070_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (15695503032337027807603/32224156038374400000000:ℝ) row070_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row070_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row070_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row070_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_oldSmall_coefficients]
def row070_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(148091180220880102361728/331898579801982421875:ℝ), (268504457671598318012516/331898579801982421875:ℝ), (275095125909832686335971/663797159603964843750:ℝ), (5523169736469006631879/132759431920792968750:ℝ)],
![(293896729518629475762176/331898579801982421875:ℝ), (508861668903950426199712/331898579801982421875:ℝ), (78144619751513588680432/110632859933994140625:ℝ), (2408525035934853120752/66379715960396484375:ℝ)],
![(148952439535871873400448/331898579801982421875:ℝ), (248046659741574998669696/331898579801982421875:ℝ), (103239128869635525269248/331898579801982421875:ℝ), (0:ℝ)] ]
theorem row070_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (909113791799435797603/32224156038374400000000:ℝ) row070_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row070_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row070_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row070_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_oldSwitch_coefficients]
def row070_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(386848276382159488/887474443359375:ℝ), (702848905951563236/887474443359375:ℝ), (721805698506080291/1774948886718750:ℝ), (4832940476359853/118329925781250:ℝ)],
![(767584929652100096/887474443359375:ℝ), (1331642060577086752/887474443359375:ℝ), (614939313567409616/887474443359375:ℝ), (2103934739494864/59164962890625:ℝ)],
![(389151225769940608/887474443359375:ℝ), (649328408046406016/887474443359375:ℝ), (270962202676465408/887474443359375:ℝ), (0:ℝ)] ]
theorem row070_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2502296246365363/86165222400000000:ℝ) row070_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row070_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row070_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row070_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_newSwitch_coefficients]
def row070_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(552378075641154759386009081/2636575636915283203125000:ℝ), (5404508346069086907775068301/16874084076257812500000000:ℝ), (85758121509648700425077432699/674963363050312500000000000:ℝ), (32997856529502988542164077/4999728615187500000000000:ℝ)],
![(598854706082806760010113081/1318287818457641601562500:ℝ), (356933501833381241821544029/527315127383056640625000:ℝ), (5189320235121004999896145649/21092605095322265625000000:ℝ), (843199763899076360895973/468724557673828125000000:ℝ)],
![(670329979600396260634217081/2636575636915283203125000:ℝ), (199927264949394794565776951/527315127383056640625000:ℝ), (180550084308237869502771337/1318287818457641601562500:ℝ), (0:ℝ)] ]
theorem row070_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (46779239063678275367267719/32766221452492800000000000000:ℝ) row070_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row070_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row070_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row070_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row070_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
