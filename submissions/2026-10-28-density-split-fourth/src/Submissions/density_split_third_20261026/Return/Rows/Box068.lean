/- Fourth density transition: exact return rectangle 068.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row068_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(4028654760097485981769/84145725000000000:ℝ), (7155705331507157780681/84145725000000000:ℝ), (166972412642727910843/4487772000000000:ℝ)],
![(50471167924446719233/876517968750000:ℝ), (246718384923486434351/2629553906250000:ℝ), (5096120297899086389/140242875000000:ℝ)],
![(13866224310925179791/1314776953125000:ℝ), (6899923281935491717/657388476562500:ℝ), (0:ℝ)] ]
theorem row068_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2030445999584430373/3921475010560000000:ℝ) row068_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row068_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row068_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row068_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_oldSmall_coefficients]
def row068_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(121433235002662684753/31554646875000000:ℝ), (70443275352161652379/10518215625000000:ℝ), (1615774683626069233/560971500000000:ℝ)],
![(4566863957770454363/986082714843750:ℝ), (261104239086524101/36521582031250:ℝ), (45339736136523679/17530359375000:ℝ)],
![(178867210058942189/164347119140625:ℝ), (172755742088469406/164347119140625:ℝ), (0:ℝ)] ]
theorem row068_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (69511889519192299/2450921881600000000:ℝ) row068_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row068_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row068_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row068_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_oldSwitch_coefficients]
def row068_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(35277964142557/9375000000:ℝ), (184483545537559/28125000000:ℝ), (4240164869093/1500000000:ℝ)],
![(3968664342941/878906250:ℝ), (6139213724689/878906250:ℝ), (118860954859/46875000:ℝ)],
![(463719287569/439453125:ℝ), (447911423926/439453125:ℝ), (0:ℝ)] ]
theorem row068_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (193214323879/6553600000000:ℝ) row068_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row068_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row068_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row068_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_newSwitch_coefficients]
def row068_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(22869295919898810338138153/820588168945312500000:ℝ), (242009929545824975806275751/3282352675781250000000:ℝ), (53038866386736709331491741/820588168945312500000:ℝ), (9849958312767272846131307/525176428125000000000:ℝ)],
![(859790230658711136485438/25643380279541015625:ℝ), (8097541651667287988028571/102573521118164062500:ℝ), (505130994772262526278712/8547793426513671875:ℝ), (223835465214241684830931/16411763378906250000:ℝ)],
![(577317389448639821118893/51286760559082031250:ℝ), (1103113130019106485071539/51286760559082031250:ℝ), (526973289587870294575271/51286760559082031250:ℝ), (0:ℝ)] ]
theorem row068_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (232594800734830553542087/220274959319040000000000000:ℝ) row068_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row068_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row068_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row068_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row068_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
