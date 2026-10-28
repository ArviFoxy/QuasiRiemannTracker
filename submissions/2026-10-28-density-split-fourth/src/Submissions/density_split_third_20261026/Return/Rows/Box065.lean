/- Fourth density transition: exact return rectangle 065.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row065_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(206826429449084958966409/84145725000000000:ℝ), (406543126026628747293001/84145725000000000:ℝ), (159776302994548211884789/67316580000000000:ℝ)],
![(6532939488931005474499/2629553906250000:ℝ), (12623936481069384508591/2629553906250000:ℝ), (4872995493259072501787/2103643125000000:ℝ)],
![(109535861799263314831/1314776953125000:ℝ), (54734742026104559237/657388476562500:ℝ), (0:ℝ)] ]
theorem row065_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (28468883496044677920389/56469240152064000000000:ℝ) row065_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row065_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row065_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row065_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_oldSmall_coefficients]
def row065_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2077926668865849552091/10518215625000000:ℝ), (4081002479602803142939/10518215625000000:ℝ), (4808174533688803915613/25243717500000000:ℝ)],
![(61530531551162233801/328694238281250:ℝ), (118133117369506878349/328694238281250:ℝ), (135900133692118155379/788866171875000:ℝ)],
![(1302596853091609069/164347119140625:ℝ), (144053931680126254/18260791015625:ℝ), (0:ℝ)] ]
theorem row065_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (190819382188872700751/7058655019008000000000:ℝ) row065_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row065_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row065_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row065_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_oldSwitch_coefficients]
def row065_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(5451749279124311/28125000000:ℝ), (10709920912903319/28125000000:ℝ), (4207220057571691/22500000000:ℝ)],
![(161225790264221/878906250:ℝ), (309693279450929/878906250:ℝ), (118820466166853/703125000:ℝ)],
![(3377789164049/439453125:ℝ), (3361981300406/439453125:ℝ), (0:ℝ)] ]
theorem row065_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (532148798350171/18874368000000000:ℝ) row065_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row065_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row065_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row065_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_newSwitch_coefficients]
def row065_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5924604614097927046441740179/547058779296875000000:ℝ), (105107380184045774757236472659/3282352675781250000000:ℝ), (41435949761917125743266174367/1312941070312500000000:ℝ), (9074683046695648061865461647/875294046875000000000:ℝ)],
![(458765221910103236168634047/51286760559082031250:ℝ), (883081199417759477525393653/34191173706054687500:ℝ), (203775233210681205243900307/8205881689453125000:ℝ), (217459477639945975724473751/27352938964843750000:ℝ)],
![(28762517971123906766107031/51286760559082031250:ℝ), (57154076966831555346675961/51286760559082031250:ℝ), (5678547308945010442238311/10257352111816406250:ℝ), (0:ℝ)] ]
theorem row065_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (378228044763430310995491761/563903895856742400000000000000:ℝ) row065_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row065_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row065_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row065_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row065_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
