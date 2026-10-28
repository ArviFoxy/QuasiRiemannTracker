/- Fourth density transition: exact return rectangle 071.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row071_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(48194896286331161571113/3365829000000000:ℝ), (11624018059837957744/438258984375:ℝ), (16047318290279763208/1314776953125:ℝ)],
![(18367186766811669343789/1121943000000000:ℝ), (187466214240135145888/6573884765625:ℝ), (79860147249349172144/6573884765625:ℝ)],
![(28394745498466964206537/13463316000000000:ℝ), (2771486019130962704/1314776953125:ℝ), (0:ℝ)] ]
theorem row071_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (163951028329706047421/294110625792000000000:ℝ) row071_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row071_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row071_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row071_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_oldSmall_coefficients]
def row071_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1561435079770763379761/1262185875000000:ℝ), (9077860057762971392/3944330859375:ℝ), (4201362583918545472/3944330859375:ℝ)],
![(1760046936679967750399/1262185875000000:ℝ), (16039984045693843456/6573884765625:ℝ), (20649630344201062784/19721654296875:ℝ)],
![(98480164305002452361/560971500000000:ℝ), (689342608706598112/3944330859375:ℝ), (0:ℝ)] ]
theorem row071_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (10357900189865309551/330874454016000000000:ℝ) row071_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row071_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row071_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row071_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_oldSwitch_coefficients]
def row071_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(454770629083709/375000000:ℝ), (7940045721344/3515625:ℝ), (3679143763904/3515625:ℝ)],
![(1535080961027993/1125000000:ℝ), (42040337598976/17578125:ℝ), (18080892162688/17578125:ℝ)],
![(764069323153943/4500000000:ℝ), (66029129376/390625:ℝ), (0:ℝ)] ]
theorem row071_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (9552131551657/294912000000000:ℝ) row071_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row071_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row071_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row071_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_newSwitch_coefficients]
def row071_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(4544664332682858348113901131/10695150000000000000000:ℝ), (26107341189766060958758/32639007568359375:ℝ), (65394154032290056648913/174074707031250000:ℝ)],
![(4947596681296087373542437829/10695150000000000000000:ℝ), (1072211732864181527887361/1305560302734375000:ℝ), (156717863974598276368331/435186767578125000:ℝ)],
![(2281553594996989073406839339/42780600000000000000000:ℝ), (2197176688269386918117/41777929687500000:ℝ), (0:ℝ)] ]
theorem row071_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2045321758458458849632661/2803669401600000000000000000:ℝ) row071_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row071_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row071_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row071_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row071_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
