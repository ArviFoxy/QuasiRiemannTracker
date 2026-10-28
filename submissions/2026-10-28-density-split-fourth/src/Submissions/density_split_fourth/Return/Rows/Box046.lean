/- Fourth density transition: exact return rectangle 046.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row046_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1543290547815079951538353792/13275943192079296875:ℝ), (3710308503220791226236652544/13275943192079296875:ℝ), (2796603141151529749456420912/13275943192079296875:ℝ), (41971610543341882870958144/885062879471953125:ℝ)],
![(2447073472046711104783305152/13275943192079296875:ℝ), (5509405590315866344425782464/13275943192079296875:ℝ), (3689355063126818545146115472/13275943192079296875:ℝ), (41800039441543738606492544/885062879471953125:ℝ)],
![(181268036805044500736057072/2655188638415859375:ℝ), (361357117252281071740204144/2655188638415859375:ℝ), (180091345977760952058834572/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row046_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (109500067588117920520380673/316776343519635701760000000:ℝ) row046_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row046_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row046_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row046_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_oldSmall_coefficients]
def row046_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(126590974033405348778713792/13275943192079296875:ℝ), (284997033884468530899172544/13275943192079296875:ℝ), (192293214405521058510380912/13275943192079296875:ℝ), (6775460640071810189234432/2655188638415859375:ℝ)],
![(219609084972429738117465152/13275943192079296875:ℝ), (468107614989006178956902464/13275943192079296875:ℝ), (93859195238574697985291824/4425314397359765625:ℝ), (6611817347627304092037632/2655188638415859375:ℝ)],
![(18771483448452230548817072/2655188638415859375:ℝ), (37121435172143718240724144/2655188638415859375:ℝ), (18351975604875048434094572/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row046_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1360570849626806597254387/79194085879908925440000000:ℝ) row046_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row046_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row046_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row046_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_oldSwitch_coefficients]
def row046_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(333423038546466634432/35498977734375:ℝ), (750127796357781497024/35498977734375:ℝ), (505354967675680131952/35498977734375:ℝ), (5908305114461434624/2366598515625:ℝ)],
![(579076246061478396992/35498977734375:ℝ), (1233808262254950113344/35498977734375:ℝ), (741244208583573421712/35498977734375:ℝ), (5764015553829697024/2366598515625:ℝ)],
![(49574948829775835312/7099795546875:ℝ), (98057450710835560624/7099795546875:ℝ), (48487768004301912812/7099795546875:ℝ), (0:ℝ)] ]
theorem row046_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3854927876014092427/211759650570240000000:ℝ) row046_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row046_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row046_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row046_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_newSwitch_coefficients]
def row046_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1194764576849347073617478969/472658785312500000000:ℝ), (11670568011985654853622949343/2363293926562500000000:ℝ), (5706192375138869069319695323/2363293926562500000000:ℝ), (27658303067993080619527/10503528562500000000:ℝ)],
![(1216339026230440262738313041/236329392656250000000:ℝ), (2375102673241623891282802111/236329392656250000000:ℝ), (231883437343168528708009189/47265878531250000000:ℝ), (0:ℝ)],
![(1257261484278096532166246021/472658785312500000000:ℝ), (2473256785530950158996410313/472658785312500000000:ℝ), (308474115324763690069199447/118164696328125000000:ℝ), (3830841938647020271423763/105035285625000000000:ℝ)] ]
theorem row046_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (1112756759355672467322865079/3608984933483151360000000000000:ℝ) row046_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row046_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row046_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row046_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row046_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
