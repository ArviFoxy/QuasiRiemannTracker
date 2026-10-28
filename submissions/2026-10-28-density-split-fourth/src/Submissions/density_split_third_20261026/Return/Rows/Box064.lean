/- Fourth density transition: exact return rectangle 064.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row064_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(91876523354095635498433/37398100000000000:ℝ), (17636370944148096448/3652158203125:ℝ), (77977926239100952664/32869423828125:ℝ)],
![(26115427167177841262807/10518215625000000:ℝ), (157703322945840217216/32869423828125:ℝ), (76095705228852733184/32869423828125:ℝ)],
![(109403106305154922117/1314776953125000:ℝ), (2733418213952518144/32869423828125:ℝ), (0:ℝ)] ]
theorem row064_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1730925316756562683/3446608896000000000:ℝ) row064_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row064_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row064_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row064_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_oldSmall_coefficients]
def row064_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(25031879836815729148369/126218587500000000:ℝ), (7683355508638415584/19721654296875:ℝ), (18863717467242739904/98608271484375:ℝ)],
![(741438616483822625039/3944330859375000:ℝ), (35607029036368606592/98608271484375:ℝ), (17077804590284417024/98608271484375:ℝ)],
![(1290373917150663503/164347119140625:ℝ), (256852489836038144/32869423828125:ℝ), (0:ℝ)] ]
theorem row064_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (3855977544590699/143608704000000000:ℝ) row064_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row064_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row064_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row064_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_oldSwitch_coefficients]
def row064_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(21892720687669783/112500000000:ℝ), (6721555984288/17578125:ℝ), (16506758878528/87890625:ℝ)],
![(215880368607491/1171875000:ℝ), (10372614629248/29296875:ℝ), (14932625594368/87890625:ℝ)],
![(3346173436763/439453125:ℝ), (666073114624/87890625:ℝ), (0:ℝ)] ]
theorem row064_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (32275550837/1152000000000:ℝ) row064_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row064_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row064_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row064_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_newSwitch_coefficients]
def row064_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(143294725115823138186867384929/13129410703125000000000:ℝ), (26492838426850144994492886577/820588168945312500000:ℝ), (272108018822187481908032808/8547793426513671875:ℝ), (53658978623514493709134336/5128676055908203125:ℝ)],
![(3710297128060965714547447529/410294084472656250000:ℝ), (670487888590400361815540377/25643380279541015625:ℝ), (645615538528279784248185088/25643380279541015625:ℝ), (41404033110805671101218816/5128676055908203125:ℝ)],
![(28025310216361004917521329/51286760559082031250:ℝ), (27841597052178981270686216/25643380279541015625:ℝ), (13829530718507180627236864/25643380279541015625:ℝ), (0:ℝ)] ]
theorem row064_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (445305804630367668251/717040883200000000000000:ℝ) row064_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row064_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row064_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row064_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row064_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
