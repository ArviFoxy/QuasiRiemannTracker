/- Fourth density transition: exact return rectangle 040.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row040_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1082371113832940486850827218/13275943192079296875:ℝ), (2311118006086450229199446294/13275943192079296875:ℝ), (1387070821388864968993635934/13275943192079296875:ℝ), (5862171056476577983380254/491701599706640625:ℝ)],
![(2002520028958520222226498692/13275943192079296875:ℝ), (4139144210228062157308888492/13275943192079296875:ℝ), (2294674367682659032297989908/13275943192079296875:ℝ), (5850331890765506916550004/491701599706640625:ℝ)],
![(920464189148009284882902874/13275943192079296875:ℝ), (1828976611152245357363097398/13275943192079296875:ℝ), (908558338770001772416132024/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row040_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2969150381264435154924963917/8447369160523618713600000000:ℝ) row040_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row040_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row040_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row040_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_oldSmall_coefficients]
def row040_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(108109758883251380595017218/13275943192079296875:ℝ), (219771655793789558243216294/13275943192079296875:ℝ), (119571023868281655223605934/13275943192079296875:ℝ), (874294370452473636850762/1475104799119921875:ℝ)],
![(208897696152540287491358692/13275943192079296875:ℝ), (138959693643312442090916164/4425314397359765625:ℝ), (215826615772556085306129908/13275943192079296875:ℝ), (862637338463074145110012/1475104799119921875:ℝ)],
![(33632767150113880304190958/4425314397359765625:ℝ), (197432945132386533166187398/13275943192079296875:ℝ), (96575662806370553127052024/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row040_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (151637567174702422647198917/8447369160523618713600000000:ℝ) row040_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row040_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row040_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row040_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_oldSwitch_coefficients]
def row040_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(284973429438583035778/35498977734375:ℝ), (579313080589592180774/35498977734375:ℝ), (314998970977549479214/35498977734375:ℝ), (253753053848105978/438258984375:ℝ)],
![(550864023124959087332/35498977734375:ℝ), (1099505283173303293132/35498977734375:ℝ), (569129614560026113268/35498977734375:ℝ), (250324756573619228/438258984375:ℝ)],
![(266183062858356250954/35498977734375:ℝ), (521054506794307991558/35498977734375:ℝ), (254978175381325178104/35498977734375:ℝ), (0:ℝ)] ]
theorem row040_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (428422869226960359557/22587696060825600000000:ℝ) row040_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row040_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row040_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row040_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_newSwitch_coefficients]
def row040_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(28390236774707713679373289/9453175706250000000:ℝ), (54307800414991339051401719/9453175706250000000:ℝ), (5194110669213357750009311/1890635141250000000:ℝ), (0:ℝ)],
![(721502585778455232831708409/118164696328125000000:ℝ), (1385816775143240042402280401/118164696328125000000:ℝ), (670763070882951454929186427/118164696328125000000:ℝ), (682040967460937823798883/15755292843750000000:ℝ)],
![(3672860305894885657591672217/1181646963281250000000:ℝ), (3544474160441706544840903763/590823481640625000000:ℝ), (3479999664042853776927638099/1181646963281250000000:ℝ), (15253153404765679834902569/315105856875000000000:ℝ)] ]
theorem row040_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (23700182436337689994891111/36089849334831513600000000000:ℝ) row040_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row040_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row040_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row040_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row040_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
