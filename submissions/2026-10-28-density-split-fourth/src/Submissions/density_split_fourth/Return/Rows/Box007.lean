/- Fourth density transition: exact return rectangle 007.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row007_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1755634628620713158176768/9678162587025807421875:ℝ), (814185729996097954973248/1935632517405161484375:ℝ), (6131281809402350558430827/19356325174051614843750:ℝ), (18290349584252297261443/238966977457427343750:ℝ)],
![(2420997412220759284922624/9678162587025807421875:ℝ), (5042471093537225334537952/9678162587025807421875:ℝ), (3260103866814635014370432/9678162587025807421875:ℝ), (7554954296827872404384/119483488728713671875:ℝ)],
![(757126102943698226745856/9678162587025807421875:ℝ), (1292325057471630911078912/9678162587025807421875:ℝ), (553758180583662284333056/9678162587025807421875:ℝ), (0:ℝ)] ]
theorem row007_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1003934614452279724999/8056039009593600000000:ℝ) row007_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row007_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row007_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_oldSmall_coefficients]
def row007_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(481473920010470960166653/19356325174051614843750:ℝ), (776757819028626581056831/19356325174051614843750:ℝ), (156207014677906871382589/9678162587025807421875:ℝ), (0:ℝ)],
![(645860868798524623775741/9678162587025807421875:ℝ), (1056602116534654577497303/9678162587025807421875:ℝ), (449618266549060883729783/9678162587025807421875:ℝ), (557177555382208518823/358450466186141015625:ℝ)],
![(993774456273882487384829/19356325174051614843750:ℝ), (71395802043942461875087/774253006962064593750:ℝ), (957319699225355516425463/19356325174051614843750:ℝ), (4927401299600639145671/716900932372282031250:ℝ)] ]
theorem row007_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (193854833609050027545859/8249383945823846400000000:ℝ) row007_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row007_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row007_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_oldSwitch_coefficients]
def row007_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1264897744469460413/51757509536718750:ℝ), (2045170476930292351/51757509536718750:ℝ), (412422599791353469/25878754768359375:ℝ), (0:ℝ)],
![(1704457371263478461/25878754768359375:ℝ), (2798529251886439063/25878754768359375:ℝ), (1198316187329193143/25878754768359375:ℝ), (521363449459661/319490799609375:ℝ)],
![(2634754866257496509/51757509536718750:ℝ), (189980160253938127/2070300381468750:ℝ), (2558896236353114423/51757509536718750:ℝ), (4418110284717997/638981599218750:ℝ)] ]
theorem row007_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (540885847797315139/22058296934400000000:ℝ) row007_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row007_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row007_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_newSwitch_coefficients]
def row007_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(386131975053329479869757273829/19681931666547112500000000000:ℝ), (119761562083277493889490627723/3936386333309422500000000000:ℝ), (114747383989317022880324369893/9840965833273556250000000000:ℝ), (0:ℝ)],
![(630083514754384405532518643429/9840965833273556250000000000:ℝ), (1092158995727434202070568641199/9840965833273556250000000000:ℝ), (555691981757754671012314664303/9840965833273556250000000000:ℝ), (288955747781316570952513031/40497801783018750000000000:ℝ)],
![(1060648925071589731195280013029/19681931666547112500000000000:ℝ), (405820465089209311478093755427/3936386333309422500000000000:ℝ), (1235935835677365947802962938031/19681931666547112500000000000:ℝ), (38670874085552846445010399/3239824142641500000000000:ℝ)] ]
theorem row007_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (64038285444939663488696076571/8388152691838156800000000000000:ℝ) row007_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row007_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row007_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
