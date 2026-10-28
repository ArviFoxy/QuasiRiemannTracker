/- Fourth density transition: exact return rectangle 048.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row048_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(70615721699628608733027811/13275943192079296875:ℝ), (149906698947558359293987481/13275943192079296875:ℝ), (89480301515633722910310829/13275943192079296875:ℝ), (3392765557337913551867053/4425314397359765625:ℝ)],
![(130582111362984803730001046/13275943192079296875:ℝ), (268283799165599569344207826/13275943192079296875:ℝ), (147862928456332038987654014/13275943192079296875:ℝ), (3379629139736682322399078/4425314397359765625:ℝ)],
![(12000910991048670725281067/2655188638415859375:ℝ), (23698587153178930062506509/2655188638415859375:ℝ), (11699941692654640391912942/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row048_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (118107958758872196352503817/316776343519635701760000000:ℝ) row048_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row048_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row048_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row048_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_oldSmall_coefficients]
def row048_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(7462953656209670289282811/13275943192079296875:ℝ), (14844819762377687121592481/13275943192079296875:ℝ), (7863126833771088634255829/13275943192079296875:ℝ), (471409373504246358196159/13275943192079296875:ℝ)],
![(14537295797177000648431046/13275943192079296875:ℝ), (28414911417937454007537826/13275943192079296875:ℝ), (1595022048071582291280446/1475104799119921875:ℝ), (457613850872654606167234/13275943192079296875:ℝ)],
![(1417918865144535049516067/2655188638415859375:ℝ), (2722865244660531601601509/2655188638415859375:ℝ), (1306970260699557294272942/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row048_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6362094762071661977988817/316776343519635701760000000:ℝ) row048_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row048_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row048_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row048_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_oldSwitch_coefficients]
def row048_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(19630621365062319931/35498977734375:ℝ), (39058639945202716001/35498977734375:ℝ), (20682887608594607509/35498977734375:ℝ), (409745293670153813/11832992578125:ℝ)],
![(38253535127792759366/35498977734375:ℝ), (74803785136274483746/35498977734375:ℝ), (37794886325650910894/35498977734375:ℝ), (397559078170978838/11832992578125:ℝ)],
![(3732683672672004707/7099795546875:ℝ), (7172507646006778789/7099795546875:ℝ), (3445090096576961582/7099795546875:ℝ), (0:ℝ)] ]
theorem row048_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17846941530002157457/847038602280960000000:ℝ) row048_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row048_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row048_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row048_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_newSwitch_coefficients]
def row048_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(136105552983102098357092837/590823481640625000000:ℝ), (251482180163524107004033007/590823481640625000000:ℝ), (46473063793133917523250793/236329392656250000000:ℝ), (0:ℝ)],
![(34998670280190969151443247/73852935205078125000:ℝ), (65088906921825674901110021/73852935205078125000:ℝ), (490399640058977476453000561/1181646963281250000000:ℝ), (316008626084839415585989/65647053515625000000:ℝ)],
![(288750804737181168048177521/1181646963281250000000:ℝ), (541241181872803119266504563/1181646963281250000000:ℝ), (1042644865317890434645889627/4726587853125000000000:ℝ), (1447757975139289306684213/262588214062500000000:ℝ)] ]
theorem row048_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (98481644577509653111258177/70487986982092800000000000000:ℝ) row048_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row048_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row048_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row048_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row048_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
