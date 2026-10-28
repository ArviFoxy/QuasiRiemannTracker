/- Fourth density transition: exact return rectangle 044.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row044_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(54344504020162678122861721396/13275943192079296875:ℝ), (148600484188011294568318128476/13275943192079296875:ℝ), (134190688931432879203956301564/13275943192079296875:ℝ), (13311565911996190842268714828/4425314397359765625:ℝ)],
![(68469374292411420791361486056/13275943192079296875:ℝ), (176661357849209730594357698296/13275943192079296875:ℝ), (147961247657504945421896302424/13275943192079296875:ℝ), (13256413915824042797497946728/4425314397359765625:ℝ)],
![(2858016074788955120529715652/2655188638415859375:ℝ), (5711350307104544237952103804/2655188638415859375:ℝ), (2853336497846113498477075652/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row044_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (109977527593839412124647468663/324378975764106958602240000000:ℝ) row044_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row044_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row044_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row044_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_oldSmall_coefficients]
def row044_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3629187330938981220297901396/13275943192079296875:ℝ), (9469543134488712332289708476/13275943192079296875:ℝ), (8059635226733902317890921564/13275943192079296875:ℝ), (2219269571830072380455364484/13275943192079296875:ℝ)],
![(5004087155659944999246966056/13275943192079296875:ℝ), (12159691891778149723472378296/13275943192079296875:ℝ), (3107840439299422620989740808/4425314397359765625:ℝ), (2167896612819052006087560184/13275943192079296875:ℝ)],
![(285320384172616001596375652/2655188638415859375:ℝ), (568984999663942442897923804/2655188638415859375:ℝ), (283666639372510002043735652/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row044_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5356418187276452798487883663/324378975764106958602240000000:ℝ) row044_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row044_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row044_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row044_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_oldSwitch_coefficients]
def row044_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9536064303689543621716/35498977734375:ℝ), (24860850971415629342396/35498977734375:ℝ), (21134521597506708484444/35498977734375:ℝ), (1936569765544393004588/11832992578125:ℝ)],
![(13170676904554791713576/35498977734375:ℝ), (31972799786254941426616/35498977734375:ℝ), (24476059284390128756504/35498977734375:ℝ), (1891294814535774264488/11832992578125:ℝ)],
![(754266050365797467492/7099795546875:ℝ), (1504241304785363307484/7099795546875:ℝ), (749980520542808027492/7099795546875:ℝ), (0:ℝ)] ]
theorem row044_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (15217633050090300476623/867367528735703040000000:ℝ) row044_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row044_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row044_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row044_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_newSwitch_coefficients]
def row044_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(91021450438929976986865939561/2363293926562500000000:ℝ), (186454935297647530144864448867/2363293926562500000000:ℝ), (100933584968362470662869553239/2363293926562500000000:ℝ), (610763997826140707136255187/262588214062500000000:ℝ)],
![(697509049825729259900084453/9453175706250000000:ℝ), (34654954069979321683162279891/236329392656250000000:ℝ), (17217881364040749200655725441/236329392656250000000:ℝ), (0:ℝ)],
![(17827115870579443065983009273/472658785312500000000:ℝ), (35473401299506941499157645869/472658785312500000000:ℝ), (8845100837880059097721523347/236329392656250000000:ℝ), (9611972335628937787374119/105035285625000000000:ℝ)] ]
theorem row044_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (17572420857534587365158692027/230975035742921687040000000000000:ℝ) row044_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row044_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row044_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row044_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row044_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
