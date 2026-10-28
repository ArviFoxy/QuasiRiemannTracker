/- Fourth density transition: exact return rectangle 027.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row027_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6198682785661894275283444/13275943192079296875:ℝ), (14777403812988218733335384/13275943192079296875:ℝ), (11055055986496008165682861/13275943192079296875:ℝ), (825202658532323736397807/4425314397359765625:ℝ)],
![(9773197854142843745985344/13275943192079296875:ℝ), (21788243491450590418041184/13275943192079296875:ℝ), (14452774851833050505345336/13275943192079296875:ℝ), (812066240931092506929832/4425314397359765625:ℝ)],
![(28901442882944864801072/106207545536634375:ℝ), (57013401810526495576144/106207545536634375:ℝ), (28118403103295425775072/106207545536634375:ℝ), (0:ℝ)] ]
theorem row027_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (422523896889377413387993/1237407591873576960000000:ℝ) row027_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row027_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row027_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row027_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_oldSmall_coefficients]
def row027_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2235061870709837760508/54633511078515625:ℝ), (1143865336589615551805384/13275943192079296875:ℝ), (77233880195792992826429/1475104799119921875:ℝ), (93710178770776023498421/13275943192079296875:ℝ)],
![(111593263901082339722816/1475104799119921875:ℝ), (2013283214217642166761184/13275943192079296875:ℝ), (1090225739424424193225336/13275943192079296875:ℝ), (79914656139184271469496/13275943192079296875:ℝ)],
![(423530244695640329008/11800838392959375:ℝ), (7309219562967341896144/106207545536634375:ℝ), (3503204178295373935072/106207545536634375:ℝ), (0:ℝ)] ]
theorem row027_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7777940786923132984331/412469197291192320000000:ℝ) row027_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row027_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row027_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row027_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_oldSwitch_coefficients]
def row027_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1426665285815215924/35498977734375:ℝ), (3003092663948062664/35498977734375:ℝ), (1821448557450730981/35498977734375:ℝ), (81110446293982247/11832992578125:ℝ)],
![(2641908271677045824/35498977734375:ℝ), (5295204678325514464/35498977734375:ℝ), (2863626657845390456/35498977734375:ℝ), (68924230794807272/11832992578125:ℝ)],
![(10045980691931312/283991821875:ℝ), (19276040426716624/283991821875:ℝ), (9245038929785312/283991821875:ℝ), (0:ℝ)] ]
theorem row027_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (65769755968659553/3308744540160000000:ℝ) row027_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row027_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row027_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row027_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_newSwitch_coefficients]
def row027_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(36571692866920608437686453/2363293926562500000000:ℝ), (67629258409935016070112863/2363293926562500000000:ℝ), (12508045256262305183924089/945317570625000000000:ℝ), (0:ℝ)],
![(41444007224912245025637847/1181646963281250000000:ℝ), (79285737384354143527330181/1181646963281250000000:ℝ), (40314258908730058089659191/1181646963281250000000:ℝ), (249866048442385529963123/131294107031250000000:ℝ)],
![(48282694023563598292131727/2363293926562500000000:ℝ), (96508279260054340698167981/2363293926562500000000:ℝ), (54612195149133792868959781/2363293926562500000000:ℝ), (683455567684702704266503/262588214062500000000:ℝ)] ]
theorem row027_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (26455827771059036847717073/17621996745523200000000000000:ℝ) row027_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row027_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row027_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row027_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row027_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
