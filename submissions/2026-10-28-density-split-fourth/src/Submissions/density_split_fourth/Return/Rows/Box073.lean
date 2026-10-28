/- Fourth density transition: exact return rectangle 073.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row073_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(55374312514161708601031/13463316000000000:ℝ), (48235544181703861474687/6731658000000000:ℝ), (2740737699254224932469/897554400000000:ℝ)],
![(11569771479922984513573/2243886000000000:ℝ), (27577342981350774433363/3365829000000000:ℝ), (1363991968349184951659/448777200000000:ℝ)],
![(14234194405648247397211/13463316000000000:ℝ), (7109732871541170639817/6731658000000000:ℝ), (0:ℝ)] ]
theorem row073_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (135255664879729623058087/240935424648806400000000:ℝ) row073_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row073_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row073_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row073_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row073_oldSmall_coefficients]
def row073_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(197640076337223956743/560971500000000:ℝ), (518356805711452394813/841457250000000:ℝ), (29671193328797491103/112194300000000:ℝ)],
![(1104265202757541144103/2524371750000000:ℝ), (292739236219109630137/420728625000000:ℝ), (14579175520630050817/56097150000000:ℝ)],
![(453068088373952255347/5048743500000000:ℝ), (74850858128895961243/841457250000000:ℝ), (0:ℝ)] ]
theorem row073_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (952691141930246826677/30116928081100800000000:ℝ) row073_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row073_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row073_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row073_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row073_oldSwitch_coefficients]
def row073_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1551407128152409/4500000000:ℝ), (1358658419258273/2250000000:ℝ), (77946850256363/300000000:ℝ)],
![(960713455123121/2250000000:ℝ), (765893937945677/1125000000:ℝ), (38295155131957/150000000:ℝ)],
![(130189681144343/1500000000:ℝ), (193577645345303/2250000000:ℝ), (0:ℝ)] ]
theorem row073_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2633951491569017/80530636800000000:ℝ) row073_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row073_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row073_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row073_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row073_newSwitch_coefficients]
def row073_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(5060138873267266063484557957/42780600000000000000000:ℝ), (4479898196778792780278810669/21390300000000000000000:ℝ), (52402238689962477222696547/570408000000000000000:ℝ)],
![(3054565238704158138415461373/21390300000000000000000:ℝ), (2452138643082439691747816681/10695150000000000000000:ℝ), (125385655259040021287648689/1426020000000000000000:ℝ)],
![(1219888463021336709840998017/42780600000000000000000:ℝ), (594121898406099920292983339/21390300000000000000000:ℝ), (0:ℝ)] ]
theorem row073_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (635615803549927361295087653/765588657930240000000000000000:ℝ) row073_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row073_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row073_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row073_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row073_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
