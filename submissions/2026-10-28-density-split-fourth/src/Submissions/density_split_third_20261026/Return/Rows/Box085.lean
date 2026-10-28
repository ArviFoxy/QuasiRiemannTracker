/- Fourth density transition: exact return rectangle 085.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row085_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(10688718300793312355674095616/119483488728713671875:ℝ), (31980589075083599706862911488/119483488728713671875:ℝ), (31895023247787262346703536128/119483488728713671875:ℝ), (1178128052610774999501635584/13275943192079296875:ℝ)],
![(1853450819382121872044407552/23896697745742734375:ℝ), (27646291963264670107706181376/119483488728713671875:ℝ), (27490903817800267412908777472/119483488728713671875:ℝ), (1012429550160689629491625984/13275943192079296875:ℝ)],
![(67639692765294213358680844/119483488728713671875:ℝ), (135212399642542183699305488/119483488728713671875:ℝ), (67572725001492165389062144/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row085_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (50315584739135327404501/96672468115123200000000:ℝ) row085_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row085_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row085_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row085_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row085_oldSmall_coefficients]
def row085_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1393671904764442968123375616/119483488728713671875:ℝ), (4173195398407070170821951488/119483488728713671875:ℝ), (4165375082520811437273776128/119483488728713671875:ℝ), (461950529626061411525066752/39827829576237890625:ℝ)],
![(187199744488073131202167552/23896697745742734375:ℝ), (2798430420326925712776261376/119483488728713671875:ℝ), (2788872569840017323682537472/119483488728713671875:ℝ), (308813623984485755639037952/39827829576237890625:ℝ)],
![(4683448775106057197700844/119483488728713671875:ℝ), (9350857231295571552345488/119483488728713671875:ℝ), (4667424647238982840582144/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row085_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3008745558921250140751/96672468115123200000000:ℝ) row085_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row085_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row085_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row085_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row085_oldSwitch_coefficients]
def row085_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3673857805599075598336/319490799609375:ℝ), (11000662418949050728448/319490799609375:ℝ), (10979751421100874661888/319490799609375:ℝ), (405882978638988836864/35498977734375:ℝ)],
![(492757657333914395392/63898159921875:ℝ), (7366071788268193943296/319490799609375:ℝ), (7340797956488761843712/319490799609375:ℝ), (270946050543348875264/35498977734375:ℝ)],
![(12354158303202361324/319490799609375:ℝ), (24667190239800322448/319490799609375:ℝ), (12313074065583898624/319490799609375:ℝ), (0:ℝ)] ]
theorem row085_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8246320401272671/258495667200000000:ℝ) row085_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row085_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row085_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row085_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row085_newSwitch_coefficients]
def row085_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(808463386746895899891186502912/118645903661187744140625:ℝ), (2422272033704991990333540820736/118645903661187744140625:ℝ), (2419153907169296280993522132736/118645903661187744140625:ℝ), (9942534076681483833965034752/1464764242730712890625:ℝ)],
![(1667060352237009666694727878991/474583614644750976562500:ℝ), (4998501544108519872902665430863/474583614644750976562500:ℝ), (1248958204057766583371991953792/118645903661187744140625:ℝ), (5137011186294926318765525504/1464764242730712890625:ℝ)],
![(210886685712440129673988511251/30373351337264062500000000:ℝ), (104661290349898471739015441057/7593337834316015625000000:ℝ), (811572069980810525529002392/118645903661187744140625:ℝ), (0:ℝ)] ]
theorem row085_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (241033548466412957706220723/98298664357478400000000000000:ℝ) row085_newTop_coefficients (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row085_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row085_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row085_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row085_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
