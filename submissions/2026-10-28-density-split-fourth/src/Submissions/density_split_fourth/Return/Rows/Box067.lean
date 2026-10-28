/- Fourth density transition: exact return rectangle 067.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row067_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(14285063132568610625929/84145725000000000:ℝ), (26781646550327499003721/84145725000000000:ℝ), (10000212466720291925749/67316580000000000:ℝ)],
![(492342283865182561219/2629553906250000:ℝ), (873456820225823732911/2629553906250000:ℝ), (305089528636882211867/2103643125000000:ℝ)],
![(27533315380687770511/1314776953125000:ℝ), (13733468816816787077/657388476562500:ℝ), (0:ℝ)] ]
theorem row067_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (1799868084245299565189/3529327509504000000000:ℝ) row067_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row067_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row067_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row067_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_oldSmall_coefficients]
def row067_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(142904702309169018331/10518215625000000:ℝ), (88701985061989974793/3506071875000000:ℝ), (296475594824437472093/25243717500000000:ℝ)],
![(4758080275065140041/328694238281250:ℝ), (8216764456812122189/328694238281250:ℝ), (8354769764283765619/788866171875000:ℝ)],
![(339400016206466029/164347119140625:ℝ), (111096182745331082/54782373046875:ℝ), (0:ℝ)] ]
theorem row067_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (12172740097248147791/441165938688000000000:ℝ) row067_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row067_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row067_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row067_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_oldSwitch_coefficients]
def row067_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(374333324171351/28125000000:ℝ), (697711922449559/28125000000:ℝ), (259385629171051/22500000000:ℝ)],
![(12434631551261/878906250:ℝ), (21505407267569/878906250:ℝ), (7303095390533/703125000:ℝ)],
![(880014984209/439453125:ℝ), (864207120566/439453125:ℝ), (0:ℝ)] ]
theorem row067_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (33898563314011/1179648000000000:ℝ) row067_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row067_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row067_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row067_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_newSwitch_coefficients]
def row067_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(20706170746734047846659837/109411755859375000000:ℝ), (1753680378475822420355365499/3282352675781250000000:ℝ), (3297153646756431737099906653/6564705351562500000000:ℝ), (5504224928837261184111571/35011761875000000000:ℝ)],
![(1923472368344069630987341/10257352111816406250:ℝ), (16748514397440538010187293/34191173706054687500:ℝ), (86259081668242354054684813/205147042236328125000:ℝ), (25844270452468400988991/218823511718750000:ℝ)],
![(402147521136430603416343/10257352111816406250:ℝ), (3924319658694977872944061/51286760559082031250:ℝ), (1914759602030228486484971/51286760559082031250:ℝ), (0:ℝ)] ]
theorem row067_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (1458610884742213824920353/1762199674552320000000000000:ℝ) row067_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row067_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row067_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row067_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row067_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
