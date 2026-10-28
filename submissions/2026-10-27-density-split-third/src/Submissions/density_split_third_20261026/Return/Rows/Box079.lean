/- Fourth density transition: exact return rectangle 079.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row079_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(261822169626067559865319/121169844000000000:ℝ), (51646143023851110311443/12116984400000000:ℝ), (84880732870609365318281/40389948000000000:ℝ)],
![(131028022064452245850879/60584922000000000:ℝ), (127444737007674540119531/30292461000000000:ℝ), (41288232272227315110859/20194974000000000:ℝ)],
![(7120906282998647577979/121169844000000000:ℝ), (3558666936553403834153/60584922000000000:ℝ), (0:ℝ)] ]
theorem row079_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2062825132401759072280361/3614031369732096000000000:ℝ) row079_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row079_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row079_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row079_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_oldSmall_coefficients]
def row079_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1022156105713212410407/5048743500000000:ℝ), (121349680897107067493/302924610000000:ℝ), (3001268599047731784337/15146230500000000:ℝ)],
![(477083959711459097407/2524371750000000:ℝ), (1396895519135138796929/3786557625000000:ℝ), (1362823222861559009123/7573115250000000:ℝ)],
![(24323425466435888827/5048743500000000:ℝ), (36325823509562652347/7573115250000000:ℝ), (0:ℝ)] ]
theorem row079_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (4887488250828785700073/150584640405504000000000:ℝ) row079_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row079_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row079_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row079_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_oldSwitch_coefficients]
def row079_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(8058469122858041/40500000000:ℝ), (318960214584553/810000000:ℝ), (2630064711087959/13500000000:ℝ)],
![(3757284965739041/20250000000:ℝ), (3668589969693109/10125000000:ℝ), (1193542813474261/6750000000:ℝ)],
![(188632404542501/40500000000:ℝ), (93904571836087/20250000000:ℝ), (0:ℝ)] ]
theorem row079_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (40489842722838199/1207959552000000000:ℝ) row079_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row079_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row079_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row079_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_newSwitch_coefficients]
def row079_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(31204236357141881594189496293/385025400000000000000000:ℝ), (6207702030764993090195893289/38502540000000000000000:ℝ), (3430978856590492520149602169/42780600000000000000000:ℝ)],
![(12838401136836903249244339373/192512700000000000000000:ℝ), (12628406546816796906525604657/96256350000000000000000:ℝ), (1380577328023209774228454811/21390300000000000000000:ℝ)],
![(542102699667390414919275233/385025400000000000000000:ℝ), (267237552151586920630990411/192512700000000000000000:ℝ), (0:ℝ)] ]
theorem row079_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (12922302255328705796209280587/11483829868953600000000000000000:ℝ) row079_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row079_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row079_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row079_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row079_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
