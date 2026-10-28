/- Fourth density transition: exact return rectangle 081.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row081_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(17727577398581785923559/121169844000000000:ℝ), (3365061354560390957587/12116984400000000:ℝ), (5308658048802225452681/40389948000000000:ℝ)],
![(9547506537856357902079/60584922000000000:ℝ), (8646817974984265052651/30292461000000000:ℝ), (2583124759299094382539/20194974000000000:ℝ)],
![(1788264493006301691259/121169844000000000:ℝ), (892346041557230890793/60584922000000000:ℝ), (0:ℝ)] ]
theorem row081_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (130263080356881628404521/225876960608256000000000:ℝ) row081_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row081_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row081_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row081_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_oldSmall_coefficients]
def row081_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(67655512836598117927/5048743500000000:ℝ), (38881131566756151289/1514623050000000:ℝ), (186097648489782800017/15146230500000000:ℝ)],
![(34019414328540323647/2524371750000000:ℝ), (93043057397323285889/3786557625000000:ℝ), (84311935534684308323/7573115250000000:ℝ)],
![(6319828401745743547/5048743500000000:ℝ), (9320427912527434427/7573115250000000:ℝ), (0:ℝ)] ]
theorem row081_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (310068486624278630633/9411540025344000000000:ℝ) row081_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row081_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row081_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row081_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_oldSwitch_coefficients]
def row081_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(532793025695801/40500000000:ℝ), (102139659158669/4050000000:ℝ), (163085364261719/13500000000:ℝ)],
![(267324558960161/20250000000:ℝ), (244050609785269/10125000000:ℝ), (73836709128661/6750000000:ℝ)],
![(49010438093861/40500000000:ℝ), (24093588611767/20250000000:ℝ), (0:ℝ)] ]
theorem row081_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2566292468855479/75497472000000000:ℝ) row081_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row081_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row081_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row081_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_newSwitch_coefficients]
def row081_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1983612777674200379673727973/385025400000000000000000:ℝ), (15465140709083170268045969/1540101600000000000000:ℝ), (209855350933663951212749689/42780600000000000000000:ℝ)],
![(870655398795613451758725293/192512700000000000000000:ℝ), (807980758172290759705206577/96256350000000000000000:ℝ), (83565568106796163544545691/21390300000000000000000:ℝ)],
![(152687764486334894458731233/385025400000000000000000:ℝ), (72530084561059160400718411/192512700000000000000000:ℝ), (0:ℝ)] ]
theorem row081_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (912148495407261030181929547/717739366809600000000000000000:ℝ) row081_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row081_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row081_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row081_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row081_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
