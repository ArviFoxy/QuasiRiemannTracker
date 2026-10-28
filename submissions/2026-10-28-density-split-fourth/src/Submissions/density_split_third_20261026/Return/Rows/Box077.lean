/- Fourth density transition: exact return rectangle 077.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row077_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2480213148180388283558573/26551886384158593750:ℝ), (191872625090769991838623/1062075455366343750:ℝ), (2406848818149157857937331/26551886384158593750:ℝ), (27713878445279119343443/8850628794719531250:ℝ)],
![(2433035426561574534246317/13275943192079296875:ℝ), (4658261870445044428631911/13275943192079296875:ℝ), (2273894433722190426736721/13275943192079296875:ℝ), (13798042167258142033709/4425314397359765625:ℝ)],
![(2386109456161810584934061/26551886384158593750:ℝ), (4520588175661757841411847/26551886384158593750:ℝ), (1070962885029600801676393/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row077_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4423155482988810734055763/8249383945823846400000000:ℝ) row077_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row077_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row077_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row077_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_oldSmall_coefficients]
def row077_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9990093161026565301799/983403199413281250:ℝ), (18641416950103914068623/1062075455366343750:ℝ), (209020313130515243167331/26551886384158593750:ℝ), (6370513333988167100329/26551886384158593750:ℝ)],
![(89674545981347105785439/4425314397359765625:ℝ), (459790818584010778511911/13275943192079296875:ℝ), (22264425910428441212969/1475104799119921875:ℝ), (3114644700534153511127/13275943192079296875:ℝ)],
![(89522170586471723854687/8850628794719531250:ℝ), (454161369296161536546847/26551886384158593750:ℝ), (96123789931398793428893/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row077_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (86782993127666865781921/2749794648607948800000000:ℝ) row077_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row077_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row077_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row077_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_oldSwitch_coefficients]
def row077_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(704320260663808733/70997955468750:ℝ), (48779224450840783/2839918218750:ℝ), (548423990114322851/70997955468750:ℝ), (5583025673204003/23665985156250:ℝ)],
![(702424770241364957/35498977734375:ℝ), (1203026640732141031/35498977734375:ℝ), (525696654057621041/35498977734375:ℝ), (2729005736864989/11832992578125:ℝ)],
![(701202445618921181/70997955468750:ℝ), (1188215490466933087/70997955468750:ℝ), (252161688534943453/35498977734375:ℝ), (0:ℝ)] ]
theorem row077_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (713081946214930723/22058296934400000000:ℝ) row077_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row077_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row077_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row077_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_newSwitch_coefficients]
def row077_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(132450855880525150085717924741/26998534522012500000000000:ℝ), (39704370608264998304491387427/5399706904402500000000000:ℝ), (73971249400348811420749410299/26998534522012500000000000:ℝ), (12360465477399679474658503/199989144607500000000000:ℝ)],
![(134574473254040132517672049541/13499267261006250000000000:ℝ), (200364780482194662260469191551/13499267261006250000000000:ℝ), (72939789164742514150848801977/13499267261006250000000000:ℝ), (85502373366123743852156663/1499918584556250000000000:ℝ)],
![(136954076732652714949626174341/26998534522012500000000000:ℝ), (40563240389662953190285256171/5399706904402500000000000:ℝ), (36196994807599995032750490757/13499267261006250000000000:ℝ), (0:ℝ)] ]
theorem row077_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16430195831784541947212686459/8388152691838156800000000000000:ℝ) row077_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row077_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row077_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row077_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row077_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
