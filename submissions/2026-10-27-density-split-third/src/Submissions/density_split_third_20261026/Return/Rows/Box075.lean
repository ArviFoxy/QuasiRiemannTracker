/- Fourth density transition: exact return rectangle 075.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row075_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(6172687770983790138311/13463316000000000:ℝ), (4366561228518288898687/6731658000000000:ℝ), (171648288374676486517/897554400000000:ℝ)],
![(1625506350654861793573/2243886000000000:ℝ), (3071764183902272180563/3365829000000000:ℝ), (85434487876342528619/448777200000000:ℝ)],
![(3591688092185350613851/13463316000000000:ℝ), (1788479714809722248137/6731658000000000:ℝ), (0:ℝ)] ]
theorem row075_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1726354940323570437307/3011692808110080000000:ℝ) row075_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row075_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row075_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row075_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_oldSmall_coefficients]
def row075_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(22345207745530425863/560971500000000:ℝ), (46482991130442238013/841457250000000:ℝ), (1813658436334843039/112194300000000:ℝ)],
![(160874365537453493543/2524371750000000:ℝ), (10947051800616328339/140242875000000:ℝ), (296779635147230123/18699050000000:ℝ)],
![(122183636194785161587/5048743500000000:ℝ), (19703449432368112283/841457250000000:ℝ), (0:ℝ)] ]
theorem row075_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (61464004568870031797/1882308005068800000000:ℝ) row075_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row075_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row075_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row075_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_oldSwitch_coefficients]
def row075_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(174421972090969/4500000000:ℝ), (121295229645473/2250000000:ℝ), (4764102045419/300000000:ℝ)],
![(139191414881201/2250000000:ℝ), (85457176270157/1125000000:ℝ), (2338389591349/150000000:ℝ)],
![(35107734842903/1500000000:ℝ), (50954725893143/2250000000:ℝ), (0:ℝ)] ]
theorem row075_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (169589425084537/5033164800000000:ℝ) row075_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row075_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row075_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row075_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_newSwitch_coefficients]
def row075_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(579491708578581295221921157/42780600000000000000000:ℝ), (388665967271163532476717869/21390300000000000000000:ℝ), (3044674765608160858142563/570408000000000000000:ℝ)],
![(472048195696349676613632253/21390300000000000000000:ℝ), (274832374653601453594883561/10695150000000000000000:ℝ), (7245955669048820320712881/1426020000000000000000:ℝ)],
![(376172614725892133284070017/42780600000000000000000:ℝ), (172263974258377632014519339/21390300000000000000000:ℝ), (0:ℝ)] ]
theorem row075_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (55765710164865590685331237/47849291120640000000000000000:ℝ) row075_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row075_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row075_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row075_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row075_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
