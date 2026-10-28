/- Fourth density transition: exact return rectangle 010.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row010_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(107414739136003908488039/121169844000000000:ℝ), (101012937713796300914143/60584922000000000:ℝ), (2103049571461473474919/2692663200000000:ℝ)],
![(59090963812413165316991/60584922000000000:ℝ), (52760892631867833630187/30292461000000000:ℝ), (1032394141896954193733/1346331600000000:ℝ)],
![(12476090851270862397179/121169844000000000:ℝ), (6224167364830715576233/60584922000000000:ℝ), (0:ℝ)] ]
theorem row010_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (14589925202666001055579/48187084929761280000000:ℝ) row010_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row010_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row010_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_oldSmall_coefficients]
def row010_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(445815610660421769461/15146230500000000:ℝ), (312263828167669282397/7573115250000000:ℝ), (4029078951928017653/336582900000000:ℝ)],
![(330481003836201170749/7573115250000000:ℝ), (191912900643935884673/3786557625000000:ℝ), (1245276044657924623/168291450000000:ℝ)],
![(31671278521515256169/1682914500000000:ℝ), (141124695739364348987/7573115250000000:ℝ), (0:ℝ)] ]
theorem row010_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (541255401232759465237/30116928081100800000000:ℝ) row010_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row010_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row010_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_oldSwitch_coefficients]
def row010_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1149390833617081/40500000000:ℝ), (799025493987137/20250000000:ℝ), (10119850633913/900000000:ℝ)],
![(856856630951329/20250000000:ℝ), (493001637329333/10125000000:ℝ), (3025115328283/450000000:ℝ)],
![(749265780338341/40500000000:ℝ), (371011479081527/20250000000:ℝ), (0:ℝ)] ]
theorem row010_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1559624459602777/80530636800000000:ℝ) row010_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row010_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row010_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_newSwitch_coefficients]
def row010_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1139206548681144088513362217/96256350000000000000000:ℝ), (561732170080745969909104739/48128175000000000000000:ℝ), (0:ℝ)],
![(2711169782603970081614937883/48128175000000000000000:ℝ), (524070766792180215220437719/6016021875000000000000:ℝ), (66565826085401940045307261/2139030000000000000000:ℝ)],
![(583456368625930086478679789/12032043750000000000000:ℝ), (8025510569103451430551516933/96256350000000000000000:ℝ), (59996590627360958159157023/1711224000000000000000:ℝ)] ]
theorem row010_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (203443433130124028440825453/191397164482560000000000000000:ℝ) row010_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row010_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row010_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
