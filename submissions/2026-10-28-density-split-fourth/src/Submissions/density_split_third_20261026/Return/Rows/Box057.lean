/- Fourth density transition: exact return rectangle 057.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row057_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5488861824128570480103553792/13275943192079296875:ℝ), (16223478194216310209045132288/13275943192079296875:ℝ), (639228051507398597269651456/531037727683171875:ℝ), (1748694929571236975633235968/4425314397359765625:ℝ)],
![(5551564461402903541786540736/13275943192079296875:ℝ), (16182826950873550716932344576/13275943192079296875:ℝ), (15711649065722179852810502144/13275943192079296875:ℝ), (1693462095421208518963232768/4425314397359765625:ℝ)],
![(228158625790777195995291244/13275943192079296875:ℝ), (455960924597404039315660688/13275943192079296875:ℝ), (227802461924824598756306944/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row057_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (137433125315025024672481/386689872460492800000000:ℝ) row057_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row057_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row057_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row057_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_oldSmall_coefficients]
def row057_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(42465284252572804105657088/1475104799119921875:ℝ), (375558054063683338702724096/4425314397359765625:ℝ), (44275431638157012261011456/531037727683171875:ℝ), (362399071899678751468027904/13275943192079296875:ℝ)],
![(352112402663622943629420736/13275943192079296875:ℝ), (1015358447277628110034424576/13275943192079296875:ℝ), (324866580118872287228674048/4425314397359765625:ℝ), (311353436685820199506018304/13275943192079296875:ℝ)],
![(21297803401488081046311244/13275943192079296875:ℝ), (42474933454515874992700688/13275943192079296875:ℝ), (21177275772473010319826944/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row057_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6719312119328389058731/386689872460492800000000:ℝ) row057_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row057_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row057_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row057_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_oldSwitch_coefficients]
def row057_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1003205975484864754432/35498977734375:ℝ), (2957145363964373685248/35498977734375:ℝ), (116197254033812094976/1419959109375:ℝ), (316997220927297814528/11832992578125:ℝ)],
![(923658049697709553856/35498977734375:ℝ), (2662802598701088330496/35498977734375:ℝ), (2555199957753407258624/35498977734375:ℝ), (272018244895417827328/11832992578125:ℝ)],
![(56276927238701019724/35498977734375:ℝ), (112241437061232101648/35498977734375:ℝ), (55964888983404519424/35498977734375:ℝ), (0:ℝ)] ]
theorem row057_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19013584534322251/1033982668800000000:ℝ) row057_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row057_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row057_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row057_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_newSwitch_coefficients]
def row057_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(348402492163022012578163633/73852935205078125000:ℝ), (127101842493042623190412418/9231616900634765625:ℝ), (24719765181924934605910016/1846323380126953125:ℝ), (13349049247777541985860096/3077205633544921875:ℝ)],
![(166016927708932463821009061/59082348164062500000:ℝ), (27904910656109010639429781/3692646760253906250:ℝ), (61810708691869719160986752/9231616900634765625:ℝ), (5996081940152248421110784/3077205633544921875:ℝ)],
![(2409885434255023229562681089/4726587853125000000000:ℝ), (299270447857098803201904337/295411740820312500000:ℝ), (4645580298689389288570744/9231616900634765625:ℝ), (0:ℝ)] ]
theorem row057_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (2427209684278019076931/45890616524800000000000000:ℝ) row057_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row057_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row057_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row057_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row057_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
