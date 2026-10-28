/- Fourth density transition: exact return rectangle 080.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row080_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(67269708341963789085671/121169844000000000:ℝ), (65471043089173232225887/60584922000000000:ℝ), (1415007018572605068263/2692663200000000:ℝ)],
![(34563308867926216243967/60584922000000000:ℝ), (32768421473752252433899/30292461000000000:ℝ), (137674573090503998081/269266320000000:ℝ)],
![(3565811756337083653499/121169844000000000:ℝ), (1781119673222621871913/60584922000000000:ℝ), (0:ℝ)] ]
theorem row080_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (34499100644745961997639/60233856162201600000000:ℝ) row080_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row080_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row080_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row080_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_oldSmall_coefficients]
def row080_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(781353676229058575989/15146230500000000:ℝ), (764737657541062663133/7573115250000000:ℝ), (16630544670779608693/336582900000000:ℝ)],
![(374210824408664609213/7573115250000000:ℝ), (356748580683386654081/3786557625000000:ℝ), (7546008904083720143/168291450000000:ℝ)],
![(4107009141103041769/1682914500000000:ℝ), (18322226444872507067/7573115250000000:ℝ), (0:ℝ)] ]
theorem row080_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (49118116762952215889/1505846404055040000000:ℝ) row080_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row080_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row080_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row080_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_oldSwitch_coefficients]
def row080_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2052575464717369/40500000000:ℝ), (2009691058700993/20250000000:ℝ), (43721315101753/900000000:ℝ)],
![(981591603120673/20250000000:ℝ), (936510638322101/10125000000:ℝ), (19825847562203/450000000:ℝ)],
![(95551093576741/40500000000:ℝ), (47363916353207/20250000000:ℝ), (0:ℝ)] ]
theorem row080_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (135594917091269/4026531840000000:ℝ) row080_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row080_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row080_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row080_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_newSwitch_coefficients]
def row080_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(7837285376491922311604568037/385025400000000000000000:ℝ), (7748396516027080866422570189/192512700000000000000000:ℝ), (170345186985969395440390117/8556120000000000000000:ℝ)],
![(3290853194724681955549224109/192512700000000000000000:ℝ), (3179071904302431379940633393/96256350000000000000000:ℝ), (68312769095386182412917023/4278060000000000000000:ℝ)],
![(282492742880020067945579233/385025400000000000000000:ℝ), (137432573757901747144142411/192512700000000000000000:ℝ), (0:ℝ)] ]
theorem row080_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (224406749249934936852142597/191397164482560000000000000000:ℝ) row080_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row080_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row080_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row080_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row080_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
