/- Fourth density transition: exact return rectangle 062.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row062_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2346159776846956639680571/13275943192079296875:ℝ), (1201475638842136642722493/2655188638415859375:ℝ), (4997674420685722299538417/13275943192079296875:ℝ), (445442373269239941868841/4425314397359765625:ℝ)],
![(653147963888392997754814/2655188638415859375:ℝ), (7783967677598122115973538/13275943192079296875:ℝ), (5815435713067304039402066/13275943192079296875:ℝ), (432305955668008712400866/4425314397359765625:ℝ)],
![(957745334482166978525599/13275943192079296875:ℝ), (1892425031240879164673273/13275943192079296875:ℝ), (934842814956467622085174/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row062_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9707986551987880716558533/24748151837471539200000000:ℝ) row062_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row062_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row062_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row062_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_oldSmall_coefficients]
def row062_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(177770094185394825735571/13275943192079296875:ℝ), (86014230737309790387493/2655188638415859375:ℝ), (111253363939099139341139/4425314397359765625:ℝ), (81343895964367391821523/13275943192079296875:ℝ)],
![(53766657415426987824814/2655188638415859375:ℝ), (590214874663630069263538/13275943192079296875:ℝ), (389189017710766544932066/13275943192079296875:ℝ), (67548373332775639792598/13275943192079296875:ℝ)],
![(106315377647085001820599/13275943192079296875:ℝ), (204378288719972239388273/13275943192079296875:ℝ), (98208630518103611005174/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row062_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (520429297916571866823533/24748151837471539200000000:ℝ) row062_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row062_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row062_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row062_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_oldSwitch_coefficients]
def row062_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(466423405145671891/35498977734375:ℝ), (225661602552110053/7099795546875:ℝ), (875246477199664057/35498977734375:ℝ), (71020761894928561/11832992578125:ℝ)],
![(141124371685179694/7099795546875:ℝ), (1548946583849416498/35498977734375:ℝ), (1020502428385778786/35498977734375:ℝ), (58834546395753586/11832992578125:ℝ)],
![(279703053909810679/35498977734375:ℝ), (538031610050992433/35498977734375:ℝ), (258707717014619254/35498977734375:ℝ), (0:ℝ)] ]
theorem row062_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1455340112062926893/66174890803200000000:ℝ) row062_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row062_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row062_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row062_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_newSwitch_coefficients]
def row062_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(908431334913623865573311/295411740820312500000:ℝ), (374305517324581579961561/59082348164062500000:ℝ), (1137290152504941345944921/295411740820312500000:ℝ), (18831522747338087691103/32823526757812500000:ℝ)],
![(844256149664404275093557/147705870410156250000:ℝ), (1556420728533902794580047/147705870410156250000:ℝ), (286985419779125942915321/59082348164062500000:ℝ), (0:ℝ)],
![(820702015598119415545291/236329392656250000000:ℝ), (7748286932420125614219397/1181646963281250000000:ℝ), (15269772086909893197010187/4726587853125000000000:ℝ), (33071288821226942811433/262588214062500000000:ℝ)] ]
theorem row062_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (700661991835353505194737/550687398297600000000000000:ℝ) row062_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row062_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row062_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row062_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row062_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
