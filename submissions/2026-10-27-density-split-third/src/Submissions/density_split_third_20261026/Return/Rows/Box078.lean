/- Fourth density transition: exact return rectangle 078.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row078_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(65438990018760765928369/30292461000000000:ℝ), (252116644108999617296/59164962890625:ℝ), (41435850432873161656/19721654296875:ℝ)],
![(13097845827989691309121/6058492200000000:ℝ), (248825035329891246688/59164962890625:ℝ), (40306517826724229968/19721654296875:ℝ)],
![(7113761463214967758633/121169844000000000:ℝ), (694354399738586704/11832992578125:ℝ), (0:ℝ)] ]
theorem row078_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (125470664730135748567/220582969344000000000:ℝ) row078_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row078_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row078_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row078_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_oldSmall_coefficients]
def row078_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(256133468057222893937/1262185875000000:ℝ), (23758814010208826752/59164962890625:ℝ), (11753545473667189696/59164962890625:ℝ)],
![(143515624050050195203/757311525000000:ℝ), (21891936628545658816/59164962890625:ℝ), (10681997747492195968/59164962890625:ℝ)],
![(72333017638942942907/15146230500000000:ℝ), (18753746942385568/3944330859375:ℝ), (0:ℝ)] ]
theorem row078_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (890510970144495493/27572871168000000000:ℝ) row078_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row078_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row078_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row078_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_oldSwitch_coefficients]
def row078_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2019295004016431/10125000000:ℝ), (62448193630592/158203125:ℝ), (10299752708672/52734375:ℝ)],
![(376761432322463/2025000000:ℝ), (57494574905536/158203125:ℝ), (9355272738176/52734375:ℝ)],
![(186985882801847/40500000000:ℝ), (145439548384/31640625:ℝ), (0:ℝ)] ]
theorem row078_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (2459891164553/73728000000000:ℝ) row078_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row078_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row078_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row078_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_newSwitch_coefficients]
def row078_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(7851414304563347487237776483/96256350000000000000000:ℝ), (238387731733267648157639/1468755340576171875:ℝ), (210858032823613198399943/2611120605468750000:ℝ)],
![(1295204346114784523566077971/19251270000000000000000:ℝ), (1556254012028800817528231/11750042724609375000:ℝ), (85126453093426003438117/1305560302734375000:ℝ)],
![(526847508938957267604686411/385025400000000000000000:ℝ), (507050696850332708933/376001367187500000:ℝ), (0:ℝ)] ]
theorem row078_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (756558517235702424841589/700917350400000000000000000:ℝ) row078_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row078_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row078_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row078_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row078_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
