/- Fourth density transition: exact return rectangle 054.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row054_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(99393773154048278030111938/13275943192079296875:ℝ), (238351379304930906276884678/13275943192079296875:ℝ), (179249099990211183919527142/13275943192079296875:ℝ), (1492180886969054396213126/491701599706640625:ℝ)],
![(31457234912793543933948148/2655188638415859375:ℝ), (353078587091751949520302732/13275943192079296875:ℝ), (235767003778031514081399644/13275943192079296875:ℝ), (1480341721257983329382876/491701599706640625:ℝ)],
![(58207675432348991146860202/13275943192079296875:ℝ), (115677614797454472497073254/13275943192079296875:ℝ), (57472696264028039273650552/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row054_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (190538084250066742281563381/527960572532726169600000000:ℝ) row054_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row054_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row054_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row054_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_oldSmall_coefficients]
def row054_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8236148209705017913901938/13275943192079296875:ℝ), (18423092275956422637374678/13275943192079296875:ℝ), (12392492808678272089137142/13275943192079296875:ℝ), (244801914589267265629378/1475104799119921875:ℝ)],
![(2862149694552243070888148/2655188638415859375:ℝ), (10067855632928700770454244/4425314397359765625:ℝ), (17995914920066368759419644/13275943192079296875:ℝ), (233144882599867773888628/1475104799119921875:ℝ)],
![(2061654814702977152256734/4425314397359765625:ℝ), (12105994619068444810643254/13275943192079296875:ℝ), (5923493013484219714810552/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row054_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9729800320602696839918381/527960572532726169600000000:ℝ) row054_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row054_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row054_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row054_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_oldSwitch_coefficients]
def row054_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(21666949348913862898/35498977734375:ℝ), (48443554157805956438/35498977734375:ℝ), (32545977901566449782/35498977734375:ℝ), (71151932329621682/438258984375:ℝ)],
![(7537156448767076308/7099795546875:ℝ), (79519976182351008172/35498977734375:ℝ), (47332278557819056124/35498977734375:ℝ), (67723635055134932/438258984375:ℝ)],
![(16311302066901718042/35498977734375:ℝ), (31938726235141930934/35498977734375:ℝ), (15633832455101150392/35498977734375:ℝ), (0:ℝ)] ]
theorem row054_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (27436097499190129901/1411731003801600000000:ℝ) row054_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row054_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row054_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row054_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_newSwitch_coefficients]
def row054_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(200883905505506372883256697/1181646963281250000000:ℝ), (386908956667500906086685211/1181646963281250000000:ℝ), (189081822036138461320997099/1181646963281250000000:ℝ), (178349666167010119722539/78776464218750000000:ℝ)],
![(205646171095763052648103049/590823481640625000000:ℝ), (393177730640676543106904407/590823481640625000000:ℝ), (187923683367708899456135483/590823481640625000000:ℝ), (0:ℝ)],
![(217022481634817271609198653/1181646963281250000000:ℝ), (209351062969391113605670997/590823481640625000000:ℝ), (205453668170967158982867071/1181646963281250000000:ℝ), (898935390878882880034753/315105856875000000000:ℝ)] ]
theorem row054_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (35380819335044268167166811/56390389585674240000000000000:ℝ) row054_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row054_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row054_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row054_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row054_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
