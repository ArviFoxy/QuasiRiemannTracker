/- Fourth density transition: exact return rectangle 019.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row019_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(12659627476151097026301538/13275943192079296875:ℝ), (34464082040541362857020614/13275943192079296875:ℝ), (30997818877875412386761614/13275943192079296875:ℝ), (340487516036818165270094/491701599706640625:ℝ)],
![(15574460061129083969445092/13275943192079296875:ℝ), (39922935222822118462984972/13275943192079296875:ℝ), (33222423657568529557665668/13275943192079296875:ℝ), (328648350325747098439844/491701599706640625:ℝ)],
![(3230106607407536450374954/13275943192079296875:ℝ), (6409260192914184859619558/13275943192079296875:ℝ), (3179397255900826282682104/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row019_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9157366004358214852629557/32997535783295385600000000:ℝ) row019_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row019_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row019_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row019_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_oldSmall_coefficients]
def row019_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(227149162842082795363846/4425314397359765625:ℝ), (1606441943291823416390614/13275943192079296875:ℝ), (1187467121403438801131614/13275943192079296875:ℝ), (29143640676468214120282/1475104799119921875:ℝ)],
![(1043236352495759686305092/13275943192079296875:ℝ), (2203269465779491365244972/13275943192079296875:ℝ), (1317808372676579836605668/13275943192079296875:ℝ), (17486608687068722379532/1475104799119921875:ℝ)],
![(472153045022245316444954/13275943192079296875:ℝ), (307449172908811028503186/4425314397359765625:ℝ), (450412153369264080002104/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row019_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (508660681532809241064557/32997535783295385600000000:ℝ) row019_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row019_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row019_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row019_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_oldSwitch_coefficients]
def row019_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1784148717403204498/35498977734375:ℝ), (4196816285986449494/35498977734375:ℝ), (3090309080209910494/35498977734375:ℝ), (8360165577566858/438258984375:ℝ)],
![(2741206665268721732/35498977734375:ℝ), (5776457959851431212/35498977734375:ℝ), (3435762446788448228/35498977734375:ℝ), (4931868303080108/438258984375:ℝ)],
![(1249527119845716634/35498977734375:ℝ), (2441945884461860918/35498977734375:ℝ), (1192985165427081784/35498977734375:ℝ), (0:ℝ)] ]
theorem row019_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1456502039597053997/88233187737600000000:ℝ) row019_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row019_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row019_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row019_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_newSwitch_coefficients]
def row019_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(666983552557602747943469/47265878531250000000:ℝ), (1277772761239871846755123/47265878531250000000:ℝ), (611966757699672729434279/47265878531250000000:ℝ), (0:ℝ)],
![(4895840032060355567209513/118164696328125000000:ℝ), (10553426769844150501630253/118164696328125000000:ℝ), (1347910309882889966449391/23632939265625000000:ℝ), (143398438937991323920237/15755292843750000000:ℝ)],
![(38897856455461026169757657/1181646963281250000000:ℝ), (46422784996187377965821423/590823481640625000000:ℝ), (70784470023340501478205779/1181646963281250000000:ℝ), (4480302834306749837329649/315105856875000000000:ℝ)] ]
theorem row019_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (127458712530250339900231/140975973964185600000000000:ℝ) row019_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row019_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row019_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row019_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row019_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
