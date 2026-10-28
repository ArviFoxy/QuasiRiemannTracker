/- Fourth density transition: exact return rectangle 047.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row047_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(312449497203128145569699362/13275943192079296875:ℝ), (701566845611014432935068678/13275943192079296875:ℝ), (93749434295461740008275574/2655188638415859375:ℝ), (2948844276804895591935502/491701599706640625:ℝ)],
![(543157347007716816387358052/13275943192079296875:ℝ), (1159686976228342856817824908/13275943192079296875:ℝ), (139170224090933305802911732/2655188638415859375:ℝ), (2937005111093824525105252/491701599706640625:ℝ)],
![(46204624765403644064978018/2655188638415859375:ℝ), (91814107525592370627282286/2655188638415859375:ℝ), (45611748290713107616991768/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row047_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (149776507550928987792508753/422368458026180935680000000:ℝ) row047_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row047_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row047_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row047_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_oldSmall_coefficients]
def row047_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9610517458442916777136454/4425314397359765625:ℝ), (60699062272952852755558678/13275943192079296875:ℝ), (7193811170123190474445574/2655188638415859375:ℝ), (454632733210336056036506/1475104799119921875:ℝ)],
![(53781465581570795781018052/13275943192079296875:ℝ), (36471656408202426710321636/4425314397359765625:ℝ), (11928050783007209216971732/2655188638415859375:ℝ), (442975701220936564295756/1475104799119921875:ℝ)],
![(5012055477458955893168018/2655188638415859375:ℝ), (9808285389578638502412286/2655188638415859375:ℝ), (4798253793303243351431768/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row047_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7647450436519056655123753/422368458026180935680000000:ℝ) row047_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row047_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row047_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row047_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_oldSwitch_coefficients]
def row047_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(75938745067305304402/35498977734375:ℝ), (159835515339663020438/35498977734375:ℝ), (18923188043899979654/7099795546875:ℝ), (132018972835783114/438258984375:ℝ)],
![(141751133914546717892/35498977734375:ℝ), (288385983255191748268/35498977734375:ℝ), (31420530628753257172/7099795546875:ℝ), (128590675561296364/438258984375:ℝ)],
![(13220971603844322578/7099795546875:ℝ), (25882554425225121406/7099795546875:ℝ), (12666848944622986328/7099795546875:ℝ), (0:ℝ)] ]
theorem row047_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (21592426772695489513/1129384803041280000000:ℝ) row047_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row047_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row047_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row047_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_newSwitch_coefficients]
def row047_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(854605895676085843236273317/1181646963281250000000:ℝ), (1634356411165579179243804091/1181646963281250000000:ℝ), (781362580094318906329904399/1181646963281250000000:ℝ), (0:ℝ)],
![(35094340670167771246338581/23632939265625000000:ℝ), (337081040352358109490535853/118164696328125000000:ℝ), (32656901988033417015334703/23632939265625000000:ℝ), (898935390878882880034753/78776464218750000000:ℝ)],
![(181345036556220051655380997/236329392656250000000:ℝ), (175570961368293196274577283/118164696328125000000:ℝ), (174034128555807953165684791/236329392656250000000:ℝ), (5208075619062454879063921/315105856875000000000:ℝ)] ]
theorem row047_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (144220083512813721308771503/225561558342696960000000000000:ℝ) row047_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row047_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row047_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row047_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row047_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
