/- Fourth density transition: exact return rectangle 034.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row034_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(259308294873489793295845924/13275943192079296875:ℝ), (532685461340687743419676616/13275943192079296875:ℝ), (58716526062594532585790177/2655188638415859375:ℝ), (6719849026669670956394231/4425314397359765625:ℝ)],
![(497546917425757710896175296/13275943192079296875:ℝ), (200601347701892365985138432/2655188638415859375:ℝ), (525672400611523827485295632/13275943192079296875:ℝ), (6706712609068439726926256/4425314397359765625:ℝ)],
![(238276787844155076229761472/13275943192079296875:ℝ), (470437112716627526768327744/13275943192079296875:ℝ), (232206851821126050438566272/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row034_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (36277519726747164280232861/98992607349886156800000000:ℝ) row034_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row034_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row034_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row034_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_oldSmall_coefficients]
def row034_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(29432688509146996988765924/13275943192079296875:ℝ), (57454841457182001420706616/13275943192079296875:ℝ), (5787402641242239852325177/2655188638415859375:ℝ), (873841133850533956247693/13275943192079296875:ℝ)],
![(58179667096341383447855296/13275943192079296875:ℝ), (22525126821437101820498432/2655188638415859375:ℝ), (55388594170374332133855632/13275943192079296875:ℝ), (860045611218942204218768/13275943192079296875:ℝ)],
![(28762230771949731347521472/13275943192079296875:ℝ), (55215027217746398803847744/13275943192079296875:ℝ), (8831453556262589118775424/4425314397359765625:ℝ), (0:ℝ)] ]
theorem row034_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1960415967632327939737861/98992607349886156800000000:ℝ) row034_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row034_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row034_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row034_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_oldSwitch_coefficients]
def row034_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(77465255603985900004/35498977734375:ℝ), (151283551662869249336/35498977734375:ℝ), (15240141206758017017/7099795546875:ℝ), (758559509844432751/11832992578125:ℝ)],
![(153158123607085543616/35498977734375:ℝ), (59328894410249871872/7099795546875:ℝ), (145940344879474589072/35498977734375:ℝ), (746373294345257776/11832992578125:ℝ)],
![(75733372603729227712/35498977734375:ℝ), (145478313427342236224/35498977734375:ℝ), (69853090611513008512/35498977734375:ℝ), (0:ℝ)] ]
theorem row034_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5504911816374710981/264699563212800000000:ℝ) row034_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row034_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row034_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row034_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_newSwitch_coefficients]
def row034_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2298924885934216602798880573/2363293926562500000000:ℝ), (4250316536761928453432248823/2363293926562500000000:ℝ), (31437060774409951064745673/37812702825000000000:ℝ), (0:ℝ)],
![(2335937028357489978823949239/1181646963281250000000:ℝ), (867600461131200080675273377/236329392656250000000:ℝ), (2031915674072886862935944689/1181646963281250000000:ℝ), (1815204916739152595364727/131294107031250000000:ℝ)],
![(2374915543221423071527560391/2363293926562500000000:ℝ), (4431254137451353423034105429/2363293926562500000000:ℝ), (2104268840217481223974736437/2363293926562500000000:ℝ), (3814133304278236835069711/262588214062500000000:ℝ)] ]
theorem row034_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (1658845777609274226738265273/1127807791713484800000000000000:ℝ) row034_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row034_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row034_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row034_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row034_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
