/- Fourth density transition: exact return rectangle 011.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row011_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(30162557917568482127719/121169844000000000:ℝ), (26935562782287065309663/60584922000000000:ℝ), (1582310804745550768181/8077989600000000:ℝ)],
![(18010704354871344191359/60584922000000000:ℝ), (2963750766111648314671/6058492200000000:ℝ), (3884572746761858576651/20194974000000000:ℝ)],
![(6279679608049578065659/121169844000000000:ℝ), (3125961743220073410473/60584922000000000:ℝ), (0:ℝ)] ]
theorem row011_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (276680120262805235391401/903507842433024000000000:ℝ) row011_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row011_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row011_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row011_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_oldSmall_coefficients]
def row011_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(58780605215430867367/5048743500000000:ℝ), (106969417238072359517/7573115250000000:ℝ), (8038705198339223197/3029246100000000:ℝ)],
![(50873534011947420607/2524371750000000:ℝ), (16128785176354721869/757311525000000:ℝ), (11359874285640966307/7573115250000000:ℝ)],
![(48902975389727188027/5048743500000000:ℝ), (71958405477136478267/7573115250000000:ℝ), (0:ℝ)] ]
theorem row011_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (700322710432085773673/37646160101376000000000:ℝ) row011_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row011_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row011_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row011_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_oldSwitch_coefficients]
def row011_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(457129727118521/40500000000:ℝ), (275213933134657/20250000000:ℝ), (6668750887979/2700000000:ℝ)],
![(397736252340641/20250000000:ℝ), (41765041892849/2025000000:ℝ), (8965904217749/6750000000:ℝ)],
![(385497123432101/40500000000:ℝ), (189127150628407/20250000000:ℝ), (0:ℝ)] ]
theorem row011_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (6035908168594999/301989888000000000:ℝ) row011_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row011_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row011_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row011_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_newSwitch_coefficients]
def row011_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(593216587120050267299410217/96256350000000000000000:ℝ), (288737189300199059302128739/48128175000000000000000:ℝ), (0:ℝ)],
![(1024212259104027729879430427/48128175000000000000000:ℝ), (35021708309916555432099371/1203204375000000000000:ℝ), (87331290773490332950087537/10695150000000000000000:ℝ)],
![(194244420903791535639150349/12032043750000000000000:ℝ), (2419117864618863278211717893/96256350000000000000000:ℝ), (78409875562806591184801691/8556120000000000000000:ℝ)] ]
theorem row011_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1047714511408251128781436003/717739366809600000000000000000:ℝ) row011_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row011_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row011_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row011_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row011_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
