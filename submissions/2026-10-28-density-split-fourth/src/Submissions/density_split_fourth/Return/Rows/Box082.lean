/- Fourth density transition: exact return rectangle 082.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row082_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(4890036851558254899431/121169844000000000:ℝ), (4435963539283786625887/60584922000000000:ℝ), (17710347672861649147/538532640000000:ℝ)],
![(2843743939869717846527/60584922000000000:ℝ), (2390154792648560477419/30292461000000000:ℝ), (43106900249166978949/1346331600000000:ℝ)],
![(899490861340910710139/121169844000000000:ℝ), (447959225724535400233/60584922000000000:ℝ), (0:ℝ)] ]
theorem row082_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (733618582499377389421/1254872003379200000000:ℝ) row082_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row082_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row082_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row082_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row082_oldSmall_coefficients]
def row082_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(54815515334168519029/15146230500000000:ℝ), (50282203664146079453/7573115250000000:ℝ), (1022261407247539573/336582900000000:ℝ)],
![(30073938759052327613/7573115250000000:ℝ), (25282282239244777601/3786557625000000:ℝ), (92331953089315267/33658290000000:ℝ)],
![(368803210107116963/560971500000000:ℝ), (4819528646354898107/7573115250000000:ℝ), (0:ℝ)] ]
theorem row082_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (5273138583767072903/156859000422400000000:ℝ) row082_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row082_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row082_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row082_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row082_oldSwitch_coefficients]
def row082_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(143692903697209/40500000000:ℝ), (131993011851713/20250000000:ℝ), (2687681042233/900000000:ℝ)],
![(78585946167073/20250000000:ℝ), (66215504804021/10125000000:ℝ), (242571245407/90000000:ℝ)],
![(25740110352421/40500000000:ℝ), (12458424741047/20250000000:ℝ), (0:ℝ)] ]
theorem row082_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (14529460594163/419430400000000:ℝ) row082_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row082_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row082_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row082_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row082_newSwitch_coefficients]
def row082_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(514227201142153841048713957/385025400000000000000000:ℝ), (482966347816368419387740109/192512700000000000000000:ℝ), (10171805628821474917861093/8556120000000000000000:ℝ)],
![(248950544612839735627740589/192512700000000000000000:ℝ), (210829228888980985351757873/96256350000000000000000:ℝ), (3988709079495991984999967/4278060000000000000000:ℝ)],
![(87785275289492307715307233/385025400000000000000000:ℝ), (40078839962637867029006411/192512700000000000000000:ℝ), (0:ℝ)] ]
theorem row082_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (5915756999408866248003671/3987440926720000000000000000:ℝ) row082_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row082_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row082_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row082_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row082_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
