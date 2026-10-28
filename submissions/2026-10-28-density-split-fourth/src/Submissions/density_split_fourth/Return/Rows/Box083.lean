/- Fourth density transition: exact return rectangle 083.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row083_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1454647809213357026599/121169844000000000:ℝ), (244934630738314036819/12116984400000000:ℝ), (332545499184778682441/40389948000000000:ℝ)],
![(942897282638470097599/60584922000000000:ℝ), (712857843242780468651/30292461000000000:ℝ), (162021089877400594699/20194974000000000:ℝ)],
![(455104045508215219579/121169844000000000:ℝ), (225765817808187654953/60584922000000000:ℝ), (0:ℝ)] ]
theorem row083_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (8478081768453223308521/14117310038016000000000:ℝ) row083_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row083_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row083_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row083_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row083_oldSmall_coefficients]
def row083_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(5333546722452390247/5048743500000000:ℝ), (2696222600066062009/1514623050000000:ℝ), (11214457165319090257/15146230500000000:ℝ)],
![(3368261089002099967/2524371750000000:ℝ), (7424891281443817409/3786557625000000:ℝ), (5029063021540042403/7573115250000000:ℝ)],
![(1818929135573207227/5048743500000000:ℝ), (2569079013268629947/7573115250000000:ℝ), (0:ℝ)] ]
theorem row083_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (6868025637289178851/196073750528000000000:ℝ) row083_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row083_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row083_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row083_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row083_oldSwitch_coefficients]
def row083_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(41840617075961/40500000000:ℝ), (7067628851789/4050000000:ℝ), (9829399445399/13500000000:ℝ)],
![(26315367092321/20250000000:ℝ), (19396679635189/10125000000:ℝ), (4403819651221/6750000000:ℝ)],
![(14104946481701/40500000000:ℝ), (6640842805687/20250000000:ℝ), (0:ℝ)] ]
theorem row083_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (169891459272439/4718592000000000:ℝ) row083_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row083_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row083_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row083_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row083_newSwitch_coefficients]
def row083_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(143897093595334178571308453/385025400000000000000000:ℝ), (24448181625211618832767721/38502540000000000000000:ℝ), (11845609051462820370372409/42780600000000000000000:ℝ)],
![(85196628466893011503314413/192512700000000000000000:ℝ), (59351975192766232116099697/96256350000000000000000:ℝ), (4476813036759650775345371/21390300000000000000000:ℝ)],
![(55334030691071014343595233/385025400000000000000000:ℝ), (23853217663427220343150411/192512700000000000000000:ℝ), (0:ℝ)] ]
theorem row083_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (88498585065722822218868107/44858710425600000000000000000:ℝ) row083_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row083_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row083_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row083_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row083_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
