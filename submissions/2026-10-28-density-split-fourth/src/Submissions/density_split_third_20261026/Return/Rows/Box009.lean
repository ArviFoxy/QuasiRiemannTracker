/- Fourth density transition: exact return rectangle 009.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row009_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(403417836200778656545639/121169844000000000:ℝ), (390666422204718667460063/60584922000000000:ℝ), (25196073508855752760373/8077989600000000:ℝ)],
![(210699858879165185932159/60584922000000000:ℝ), (39618709277231079221551/6058492200000000:ℝ), (61838049609062014352651/20194974000000000:ℝ)],
![(24868913337713431060219/121169844000000000:ℝ), (12420578608051999907753/60584922000000000:ℝ), (0:ℝ)] ]
theorem row009_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (4352108647462086885613481/14456125478928384000000000:ℝ) row009_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row009_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row009_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_oldSmall_coefficients]
def row009_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(428980293029863988647/5048743500000000:ℝ), (1025030328427774989917/7573115250000000:ℝ), (153143256985560402589/3029246100000000:ℝ)],
![(261952118593658406847/2524371750000000:ℝ), (102821079702463333453/757311525000000:ℝ), (245047065801594123427/7573115250000000:ℝ)],
![(187235555914182929467/5048743500000000:ℝ), (279457276263820090427/7573115250000000:ℝ), (0:ℝ)] ]
theorem row009_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (10637872468741006375273/602338561622016000000000:ℝ) row009_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row009_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row009_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_oldSwitch_coefficients]
def row009_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(3298376208255161/40500000000:ℝ), (2611111777333057/20250000000:ℝ), (128705364705323/2700000000:ℝ)],
![(2021323853241761/20250000000:ℝ), (261516191625713/2025000000:ℝ), (200273869693589/6750000000:ℝ)],
![(1476803094150821/40500000000:ℝ), (734780135987767/20250000000:ℝ), (0:ℝ)] ]
theorem row009_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (92100664482015799/4831838208000000000:ℝ) row009_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row009_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row009_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_newSwitch_coefficients]
def row009_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2231186471803331730941266217/96256350000000000000000:ℝ), (1107722131641839791123056739/48128175000000000000000:ℝ), (0:ℝ)],
![(8222110819489506335018919707/48128175000000000000000:ℝ), (70250068589951519152942447/240640875000000000000:ℝ), (1298719474153082112542315377/10695150000000000000000:ℝ)],
![(1966302420369943414593949549/12032043750000000000000:ℝ), (28909050478868407358210489093/96256350000000000000000:ℝ), (1172940419431280284372390811/8556120000000000000000:ℝ)] ]
theorem row009_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (9975419516004109975508260963/11483829868953600000000000000000:ℝ) row009_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row009_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row009_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
