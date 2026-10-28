/- Fourth density transition: exact return rectangle 045.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row045_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1725337451888255042947951244/2655188638415859375:ℝ), (22248539111519245563166050932/13275943192079296875:ℝ), (18628665835450898395146687604/13275943192079296875:ℝ), (185437146510268067223208996/491701599706640625:ℝ)],
![(2439238544293149434645732632/2655188638415859375:ℝ), (29355165011367840288270185512/13275943192079296875:ℝ), (22145146336201834039705813544/13275943192079296875:ℝ), (184672284928341988824371896/491701599706640625:ℝ)],
![(718018798848049854044955788/2655188638415859375:ℝ), (1433691012633105753899529076/2655188638415859375:ℝ), (715674479315580280909260788/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row045_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1537389327951897929233054133/4505263552279263313920000000:ℝ) row045_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row045_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row045_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row045_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_oldSmall_coefficients]
def row045_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(42259547832156997749123748/885062879471953125:ℝ), (1539034433229289276023110932/13275943192079296875:ℝ), (1180474243360520786769507604/13275943192079296875:ℝ), (10197154676277320427388996/491701599706640625:ℝ)],
![(198044455532811456203292632/2655188638415859375:ℝ), (747021843662304570916048504/4425314397359765625:ℝ), (1519723636525590687298333544/13275943192079296875:ℝ), (9957793120063819367051896/491701599706640625:ℝ)],
![(72574958375896511733495788/2655188638415859375:ℝ), (144316972708189341464109076/2655188638415859375:ℝ), (71744038213476390472800788/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row045_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (75385392823883427762319133/4505263552279263313920000000:ℝ) row045_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row045_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row045_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row045_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_oldSwitch_coefficients]
def row045_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(333591831483060799724/7099795546875:ℝ), (4045952522146249700372/35498977734375:ℝ), (3098610754360958987284/35498977734375:ℝ), (26688583573428501316/1314776953125:ℝ)],
![(521921390763885466072/7099795546875:ℝ), (5901366826813333768552/35498977734375:ℝ), (3995313882188664818024/35498977734375:ℝ), (26055631485633412216/1314776953125:ℝ)],
![(191792508735986368748/7099795546875:ℝ), (381426454190751454996/7099795546875:ℝ), (189639211578007273748/7099795546875:ℝ), (0:ℝ)] ]
theorem row045_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (213974993926135414493/12046771232440320000000:ℝ) row045_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row045_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row045_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row045_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_newSwitch_coefficients]
def row045_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4535742676052629889773349933/472658785312500000000:ℝ), (45286048058517553386994190603/2363293926562500000000:ℝ), (4617932241760656503238322211/472658785312500000000:ℝ), (159700800446409145806474289/787764642187500000000:ℝ)],
![(4525785686948152380750320213/236329392656250000000:ℝ), (8939688313981086568090776859/236329392656250000000:ℝ), (4414556166737593202336013521/236329392656250000000:ℝ), (0:ℝ)],
![(4663695996739445110521575681/472658785312500000000:ℝ), (9262367609709055385114419093/472658785312500000000:ℝ), (2324003843704463131439091109/236329392656250000000:ℝ), (32449135411350964040074829/315105856875000000000:ℝ)] ]
theorem row045_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (4376268387897227357832600419/28871879467865210880000000000000:ℝ) row045_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row045_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row045_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row045_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row045_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
