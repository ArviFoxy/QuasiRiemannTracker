/- Fourth density transition: exact return rectangle 069.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row069_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1239788361034952239609/84145725000000000:ℝ), (2021410296443044329001/84145725000000000:ℝ), (628243280839654895029/67316580000000000:ℝ)],
![(52288837379468393299/2629553906250000:ℝ), (76028614576416659791/2629553906250000:ℝ), (19189721305927887707/2103643125000000:ℝ)],
![(7032678776043884431/1314776953125000:ℝ), (3483150514494844037/657388476562500:ℝ), (0:ℝ)] ]
theorem row069_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (117679143554355503429/220582969344000000000:ℝ) row069_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row069_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row069_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row069_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_oldSmall_coefficients]
def row069_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(12843913180800258091/10518215625000000:ℝ), (19771229103364366139/10518215625000000:ℝ), (17418146134269156893/25243717500000000:ℝ)],
![(571493583160642201/328694238281250:ℝ), (250242827625994783/109564746093750:ℝ), (484091487412629619/788866171875000:ℝ)],
![(98600806985180269/164347119140625:ℝ), (30829779671569162/54782373046875:ℝ), (0:ℝ)] ]
theorem row069_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (826725559605648911/27572871168000000000:ℝ) row069_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row069_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row069_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row069_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_oldSwitch_coefficients]
def row069_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(33484522350311/28125000000:ℝ), (51670048670519/28125000000:ℝ), (15231171604651/22500000000:ℝ)],
![(1485597800621/878906250:ℝ), (1955951076929/878906250:ℝ), (422757438533/703125000:ℝ)],
![(255571439249/439453125:ℝ), (239763575606/439453125:ℝ), (0:ℝ)] ]
theorem row069_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2289590965531/73728000000000:ℝ) row069_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row069_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row069_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row069_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_newSwitch_coefficients]
def row069_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(100735671163551814589111483/267378750000000000000000:ℝ), (134671849105656569233319627/267378750000000000000000:ℝ), (11159291865170392522124261/71301000000000000000000:ℝ)],
![(4990964523222745242982313/8355585937500000000000:ℝ), (5194727205004903279115357/8355585937500000000000:ℝ), (198103757352016494457963/2228156250000000000000:ℝ)],
![(1234398286753566164242397/4177792968750000000000:ℝ), (543760404201313932048799/2088896484375000000000:ℝ), (0:ℝ)] ]
theorem row069_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (530371831336574650621663/700917350400000000000000000:ℝ) row069_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row069_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row069_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row069_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row069_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
