/- Fourth density transition: exact return rectangle 074.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row074_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(17438087499153572065991/13463316000000000:ℝ), (1539379299261920984903/747962000000000:ℝ), (2057005905425673060191/2692663200000000:ℝ)],
![(12265259469253534592111/6731658000000000:ℝ), (192994794171983690879/74796200000000:ℝ), (5118780008530176535877/6731658000000000:ℝ)],
![(7139190196672982874971/13463316000000000:ℝ), (1187410255684512792899/2243886000000000:ℝ), (0:ℝ)] ]
theorem row074_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (510767291900398148317129/903507842433024000000000:ℝ) row074_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row074_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row074_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row074_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_oldSmall_coefficients]
def row074_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(558936972128112606527/5048743500000000:ℝ), (443268284615595051959/2524371750000000:ℝ), (66284629933053167767/1009748700000000:ℝ)],
![(392739456567345125927/2524371750000000:ℝ), (55164605129200669807/252437175000000:ℝ), (162799278595897222189/2524371750000000:ℝ)],
![(232478453587840859507/5048743500000000:ℝ), (114257756993632185809/2524371750000000:ℝ), (0:ℝ)] ]
theorem row074_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (10831042368808764863953/338815440912384000000000:ℝ) row074_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row074_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row074_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row074_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_oldSwitch_coefficients]
def row074_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(54027919283921/500000000:ℝ), (386583875626913/2250000000:ℝ), (58041904235969/900000000:ℝ)],
![(113569508770363/750000000:ℝ), (47989172302249/225000000:ℝ), (142536102922523/2250000000:ℝ)],
![(66801716943383/1500000000:ℝ), (98495699043863/2250000000:ℝ), (0:ℝ)] ]
theorem row074_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1108328928249119/33554432000000000:ℝ) row074_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row074_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row074_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row074_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_newSwitch_coefficients]
def row074_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1570813660506821916245814917/42780600000000000000000:ℝ), (1250182940805718980013763629/21390300000000000000000:ℝ), (64004173504098822560725999/2852040000000000000000:ℝ)],
![(1092168570967302878045818877/21390300000000000000000:ℝ), (151976498346312916095487637/2139030000000000000000:ℝ), (152889731306901785714538613/7130100000000000000000:ℝ)],
![(657411230824373658803046017/42780600000000000000000:ℝ), (312883282307618394774007339/21390300000000000000000:ℝ), (0:ℝ)] ]
theorem row074_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2688531379067561782316828203/2870957467238400000000000000000:ℝ) row074_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row074_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row074_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row074_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row074_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
