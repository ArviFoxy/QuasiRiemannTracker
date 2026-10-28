/- Fourth density transition: exact return rectangle 055.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row055_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(20472187566927082516816051/13275943192079296875:ℝ), (45723587145491299215991769/13275943192079296875:ℝ), (6080454336988142906916437/2655188638415859375:ℝ), (1716087405070803620135489/4425314397359765625:ℝ)],
![(35543378531943640906740614/13275943192079296875:ℝ), (15090140766103428657095114/2655188638415859375:ℝ), (45021543037263953888237498/13275943192079296875:ℝ), (1702950987469572390667514/4425314397359765625:ℝ)],
![(15109356256903717019356663/13275943192079296875:ℝ), (29842952232879284331796001/13275943192079296875:ℝ), (14736352874898125235876838/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row055_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (150179522616593680604530061/395970429399544627200000000:ℝ) row055_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row055_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row055_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row055_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_oldSmall_coefficients]
def row055_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(652481337684290278757017/4425314397359765625:ℝ), (4039246531618088251636769/13275943192079296875:ℝ), (468106400077638039501437/2655188638415859375:ℝ), (256397970699510807141467/13275943192079296875:ℝ)],
![(1230025966324627310203538/4425314397359765625:ℝ), (1470531974868286828265114/2655188638415859375:ℝ), (1303325658026047701109166/4425314397359765625:ℝ), (242602448067919055112542/13275943192079296875:ℝ)],
![(582628690225451994257221/4425314397359765625:ℝ), (3357647910466237011751001/13275943192079296875:ℝ), (1612224678314587389916838/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row055_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (298906325776505150445743/14665571459242393600000000:ℝ) row055_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row055_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row055_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row055_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_oldSwitch_coefficients]
def row055_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5144704772808488971/35498977734375:ℝ), (10616873491570433249/35498977734375:ℝ), (1229538240597692477/7099795546875:ℝ), (223151970083839369/11832992578125:ℝ)],
![(9704546543191869494/35498977734375:ℝ), (3868442705630227994/7099795546875:ℝ), (10283034428550763658/35498977734375:ℝ), (210965754584664394/11832992578125:ℝ)],
![(4600346371012964623/35498977734375:ℝ), (8842733075542832921/35498977734375:ℝ), (4248794991390805798/35498977734375:ℝ), (0:ℝ)] ]
theorem row055_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (22615985882755312181/1058798252851200000000:ℝ) row055_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row055_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row055_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row055_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_newSwitch_coefficients]
def row055_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(7909378556590151670150013/147705870410156250000:ℝ), (14603649066667123772530103/147705870410156250000:ℝ), (2696784498112727657038561/59082348164062500000:ℝ), (0:ℝ)],
![(16545242592513283317652253/147705870410156250000:ℝ), (6145980430323752396191883/29541174082031250000:ℝ), (57726045257999408621168567/590823481640625000000:ℝ), (33071288821226942811433/32823526757812500000:ℝ)],
![(70070098507714911519289163/1181646963281250000000:ℝ), (131793056130253640524244737/1181646963281250000000:ℝ), (256573183159635935705166899/4726587853125000000000:ℝ), (448293781369747186831721/262588214062500000000:ℝ)] ]
theorem row055_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (5902937534073870526860793/4405499186380800000000000000:ℝ) row055_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row055_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row055_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row055_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row055_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
