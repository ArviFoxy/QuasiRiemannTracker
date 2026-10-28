/- Fourth density transition: exact return rectangle 005.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row005_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(140511568515443225887181608/1075351398558423046875:ℝ), (3271133627010698634817312/8602811188467384375:ℝ), (396458208476311918405425826/1075351398558423046875:ℝ), (527065877829712461746938/4425314397359765625:ℝ)],
![(122641626200966143668015104/1075351398558423046875:ℝ), (347011265878188907882696192/1075351398558423046875:ℝ), (326557356900558814961430272/1075351398558423046875:ℝ), (420513386430072860274688/4425314397359765625:ℝ)],
![(7667253502316427866576896/1075351398558423046875:ℝ), (15102530363159348076603392/1075351398558423046875:ℝ), (7437338997071334610026496/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row005_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12088610408298438109907/128896624153497600000000:ℝ) row005_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row005_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row005_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_oldSmall_coefficients]
def row005_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(827719072404342144695672/358450466186141015625:ℝ), (5343885357412794866960224/1075351398558423046875:ℝ), (133355021064744951522082/43014055942336921875:ℝ), (5829576697669230638782/13275943192079296875:ℝ)],
![(344808331283494813257728/71690093237228203125:ℝ), (2018558187448821739529728/215070279711684609375:ℝ), (984662820816506439756544/215070279711684609375:ℝ), (0:ℝ)],
![(3876155472436950359840768/358450466186141015625:ℝ), (31116025275171289899759616/1075351398558423046875:ℝ), (5503036329449975003500544/215070279711684609375:ℝ), (99083711206926195027968/13275943192079296875:ℝ)] ]
theorem row005_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (75037857915452946137/5155864966139904000000:ℝ) row005_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row005_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row005_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_oldSwitch_coefficients]
def row005_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6423646665918597736/2875417196484375:ℝ), (13697076963719230304/2875417196484375:ℝ), (334880393032745122/115016687859375:ℝ), (1503571028593358/3944330859375:ℝ)],
![(2750598953417918464/575083439296875:ℝ), (5369887656296703488/575083439296875:ℝ), (2620666788818785024/575083439296875:ℝ), (0:ℝ)],
![(31019351031567145984/2875417196484375:ℝ), (82999002376111502336/2875417196484375:ℝ), (14676279965001473024/575083439296875:ℝ), (29351104441787392/3944330859375:ℝ)] ]
theorem row005_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (434097331830979/27572871168000000:ℝ) row005_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row005_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_newSwitch_coefficients]
def row005_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(693825273363113471706671766989/546720324070753125000000000:ℝ), (1344314803248438050584643595547/546720324070753125000000000:ℝ), (162739180614494867331874574327/136680081017688281250000000:ℝ), (0:ℝ)],
![(3207162140946294902304099648761/273360162035376562500000000:ℝ), (8488745068106243014876728703723/273360162035376562500000000:ℝ), (7415911595142795378309131565227/273360162035376562500000000:ℝ), (1756114124218304906693673671/224987787683437500000000:ℝ)],
![(9716358482667579054558112805369/546720324070753125000000000:ℝ), (27362929646786371069478775981547/546720324070753125000000000:ℝ), (25658693477797980808122443354603/546720324070753125000000000:ℝ), (1318719005108448198334749659/89995115073375000000000:ℝ)] ]
theorem row005_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (48449407301944759331391941257/26842088613882101760000000000000:ℝ) row005_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row005_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row005_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
