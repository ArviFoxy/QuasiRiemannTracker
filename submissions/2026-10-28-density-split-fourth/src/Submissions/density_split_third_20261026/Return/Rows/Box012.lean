/- Fourth density transition: exact return rectangle 012.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row012_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(30347779873021570312834642/13275943192079296875:ℝ), (15583820220366202594496542/2655188638415859375:ℝ), (64999649353777578664732894/13275943192079296875:ℝ), (645457534940423130049438/491701599706640625:ℝ)],
![(42467066053415118488278916/13275943192079296875:ℝ), (101629372529674528457473708/13275943192079296875:ℝ), (76272040416021403344862868/13275943192079296875:ℝ), (633618369229352063219188/491701599706640625:ℝ)],
![(12434560202823097682675674/13275943192079296875:ℝ), (24660678438476944738646198/13275943192079296875:ℝ), (12227183538451533791908024/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row012_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (33724905110200955325295757/131990143133181542400000000:ℝ) row012_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row012_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row012_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row012_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_oldSmall_coefficients]
def row012_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2098457848551622842944642/13275943192079296875:ℝ), (287928472019577138235514/885062879471953125:ℝ), (2431185618864981051502894/13275943192079296875:ℝ), (23316185384737953018314/1475104799119921875:ℝ)],
![(3999055172200707579058916/13275943192079296875:ℝ), (7920705303934063758613708/13275943192079296875:ℝ), (4028403105853858749802868/13275943192079296875:ℝ), (11659153395338461277564/1475104799119921875:ℝ)],
![(670320501567272917448558/4425314397359765625:ℝ), (3927298219879171821736198/13275943192079296875:ℝ), (1917288389085000742828024/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row012_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1999668448054130034730757/131990143133181542400000000:ℝ) row012_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row012_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row012_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row012_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_oldSwitch_coefficients]
def row012_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5519379065248417282/35498977734375:ℝ), (2266319059088819182/7099795546875:ℝ), (6335752419304979374/35498977734375:ℝ), (6435439331673466/438258984375:ℝ)],
![(10554453279342257636/35498977734375:ℝ), (20878058209032773068/35498977734375:ℝ), (10571920606741389428/35498977734375:ℝ), (3007142057186716/438258984375:ℝ)],
![(5327543386074039754/35498977734375:ℝ), (10408767124185556358/35498977734375:ℝ), (5083699986284954104/35498977734375:ℝ), (0:ℝ)] ]
theorem row012_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5739129727410624197/352932750950400000000:ℝ) row012_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row012_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row012_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row012_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_newSwitch_coefficients]
def row012_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(153141969946061773478135686901/1687408407625781250000000:ℝ), (296316587644809491091748640563/1687408407625781250000000:ℝ), (35820370068019274273154043103/421852101906445312500000:ℝ), (0:ℝ)],
![(210623983322946125804432803139/843704203812890625000000:ℝ), (458570038477827767598905442427/843704203812890625000000:ℝ), (591543002792258969864263337971/1687408407625781250000000:ℝ), (706870018936617387886481227/12499321537968750000000:ℝ)],
![(140219448155683916104958455483/843704203812890625000000:ℝ), (657026434723877905495907806543/1687408407625781250000000:ℝ), (1934747658105053040726485927933/6749633630503125000000000:ℝ), (25358833296732317459733089/399978289215000000000:ℝ)] ]
theorem row012_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4980179960780225547298054033/6710522153470525440000000000000:ℝ) row012_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row012_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row012_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row012_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row012_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
