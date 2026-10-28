/- Fourth density transition: exact return rectangle 008.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row008_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(100688625931832714994097/30292461000000000:ℝ), (76177575030361032016/11832992578125:ℝ), (12282876269783324248/3944330859375:ℝ)],
![(105163774960840305814373/30292461000000000:ℝ), (386226860083420426912/59164962890625:ℝ), (60285048742767689552/19721654296875:ℝ)],
![(24813401094494568570793/121169844000000000:ℝ), (2420473141883314192/11832992578125:ℝ), (0:ℝ)] ]
theorem row008_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (264117141501928242007/882331877376000000000:ℝ) row008_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row008_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row008_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_oldSmall_coefficients]
def row008_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(330459680560133396563/3786557625000000:ℝ), (1660194810532125952/11832992578125:ℝ), (629536830001899712/11832992578125:ℝ)],
![(133528250519054282789/1262185875000000:ℝ), (8314237037556299264/59164962890625:ℝ), (2076136423834504832/59164962890625:ℝ)],
![(556122437312731573307/15146230500000000:ℝ), (144096438046308064/3944330859375:ℝ), (0:ℝ)] ]
theorem row008_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1913909605036028293/110291484672000000000:ℝ) row008_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row008_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row008_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_oldSwitch_coefficients]
def row008_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(848224480095023/10125000000:ℝ), (4238072833792/31640625:ℝ), (530877195584/10546875:ℝ)],
![(1031569529440507/10125000000:ℝ), (21193432966144/158203125:ℝ), (1709906007424/52734375:ℝ)],
![(1462317449800247/40500000000:ℝ), (1136777052832/31640625:ℝ), (0:ℝ)] ]
theorem row008_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (5532125673353/294912000000000:ℝ) row008_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row008_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row008_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_newSwitch_coefficients]
def row008_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2199702054764027433550960739/96256350000000000000000:ℝ), (2132773287348022739117/94000341796875000:ℝ), (0:ℝ)],
![(16087879376905793879982759871/96256350000000000000000:ℝ), (3351157452708307876532009/11750042724609375000:ℝ), (77294053453618762656719/652780151367187500:ℝ)],
![(61581127093463722530961429451/385025400000000000000000:ℝ), (2761003174322974639223537/9400034179687500000:ℝ), (69956268090247248430117/522224121093750000:ℝ)] ]
theorem row008_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (474592130202641756711261/700917350400000000000000000:ℝ) row008_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row008_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row008_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
