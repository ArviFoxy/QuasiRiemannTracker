/- Fourth density transition: exact return rectangle 017.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row017_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(630542066347309081924795324/13275943192079296875:ℝ), (1837697430554109268177241972/13275943192079296875:ℝ), (1783959186118436191899097972/13275943192079296875:ℝ), (21363097056709072205663012/491701599706640625:ℝ)],
![(659819206341183724422042488/13275943192079296875:ℝ), (75015978184991529927480424/531037727683171875:ℝ), (1771733049139825679955517736/13275943192079296875:ℝ), (20598235474782993806825912/491701599706640625:ℝ)],
![(49865672209651954233119164/13275943192079296875:ℝ), (99531187387613024403279428/13275943192079296875:ℝ), (49665758848355248043597764/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row017_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (93489657300270088940316361/351973715021817446400000000:ℝ) row017_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row017_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row017_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row017_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_oldSmall_coefficients]
def row017_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8370485515305849463405108/4425314397359765625:ℝ), (69216965640929496253501972/13275943192079296875:ℝ), (63172026235806798655357972/13275943192079296875:ℝ), (706160638527600035123012/491701599706640625:ℝ)],
![(25345990975923881180082488/13275943192079296875:ℝ), (2525566520915371739520424/531037727683171875:ℝ), (50397143050650314283397736/13275943192079296875:ℝ), (466799082314098974785912/491701599706640625:ℝ)],
![(6780266127786576677739164/13275943192079296875:ℝ), (4491987721759022610006476/4425314397359765625:ℝ), (6695914717155567463217764/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row017_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4846524350763377490321361/351973715021817446400000000:ℝ) row017_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row017_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row017_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row017_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_oldSwitch_coefficients]
def row017_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(65481065126963477404/35498977734375:ℝ), (180260450439632808212/35498977734375:ℝ), (164265770342974184212/35498977734375:ℝ), (1832811738165226052/1314776953125:ℝ)],
![(66145331041242139448/35498977734375:ℝ), (6571222924975188904/1419959109375:ℝ), (130532482462787530856/35498977734375:ℝ), (1199859650370136952/1314776953125:ℝ)],
![(17979013190087174044/35498977734375:ℝ), (35738088971420121188/35498977734375:ℝ), (17759642182143884644/35498977734375:ℝ), (0:ℝ)] ]
theorem row017_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14000925621465294481/941154002534400000000:ℝ) row017_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row017_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row017_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row017_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_newSwitch_coefficients]
def row017_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8737056637714904895047039/47265878531250000000:ℝ), (17266999135189529652906193/47265878531250000000:ℝ), (8531120046492028388481779/47265878531250000000:ℝ), (0:ℝ)],
![(98513208455458519709152783/118164696328125000000:ℝ), (244065137112193488807165947/118164696328125000000:ℝ), (96877471964458660588846811/59082348164062500000:ℝ), (32131025835057754740837347/78776464218750000000:ℝ)],
![(45454956634045526868042593/47265878531250000000:ℝ), (388684734546022370322282923/147705870410156250000:ℝ), (225307234189029072454086817/94531757062500000000:ℝ), (1124267794650728206630069663/1575529284375000000000:ℝ)] ]
theorem row017_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (13318802666884869692333993/45112311668539392000000000000:ℝ) row017_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row017_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row017_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row017_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row017_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
