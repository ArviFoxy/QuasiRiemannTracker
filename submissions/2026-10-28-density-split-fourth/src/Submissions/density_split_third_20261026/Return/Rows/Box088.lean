/- Fourth density transition: exact return rectangle 088.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row088_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(34425986992741097141858048/23896697745742734375:ℝ), (102208388137019074423581952/23896697745742734375:ℝ), (20227763059162971484317952/4779339549148546875:ℝ), (3706268239059653348873984/2655188638415859375:ℝ)],
![(153388231233354347158049024/119483488728713671875:ℝ), (450375888980954799771939328/119483488728713671875:ℝ), (440607629762535377610363584/119483488728713671875:ℝ), (3191554933665220555477184/2655188638415859375:ℝ)],
![(4273634411971015366764784/119483488728713671875:ℝ), (8530440792831592261046768/119483488728713671875:ℝ), (4256824505104771942719484/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row088_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (164322410889238452862801/309351897968394240000000:ℝ) row088_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row088_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row088_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row088_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_oldSmall_coefficients]
def row088_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4467147669259532795498048/23896697745742734375:ℝ), (13303689059200364217141952/23896697745742734375:ℝ), (2641187022124426009557952/4779339549148546875:ℝ), (1456464573560432875381952/7965565915247578125:ℝ)],
![(15085814947578713561969024/119483488728713671875:ℝ), (44652676211745429340179328/119483488728713671875:ℝ), (44049881707570434535083584/119483488728713671875:ℝ), (965534696226914583791552/7965565915247578125:ℝ)],
![(303833330411920232484784/119483488728713671875:ℝ), (603583721372096567486768/119483488728713671875:ℝ), (299766582009644820939484/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row088_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (39436106328274209243079/1237407591873576960000000:ℝ) row088_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row088_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row088_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row088_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_oldSwitch_coefficients]
def row088_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(11782259763377350208/63898159921875:ℝ), (35085391817029849792/63898159921875:ℝ), (6964800868785529792/12779631984375:ℝ), (1280096921141683264/7099795546875:ℝ)],
![(39718112725554975104/319490799609375:ℝ), (117556686226928649088/319490799609375:ℝ), (115963844267464844864/319490799609375:ℝ), (847228239246470464/7099795546875:ℝ)],
![(800643613474950064/319490799609375:ℝ), (1590816054862081328/319490799609375:ℝ), (790214570373068764/319490799609375:ℝ), (0:ℝ)] ]
theorem row088_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (107989994215174759/3308744540160000000:ℝ) row088_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row088_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row088_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row088_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_newSwitch_coefficients]
def row088_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(41342398715588525386901884289/379666891715800781250000:ℝ), (123403570839626434292701915267/379666891715800781250000:ℝ), (122779945532487292424698177667/379666891715800781250000:ℝ), (1508102718831458648848079507/14061736730214843750000:ℝ)],
![(10367543790639590607958294919/189833445857900390625000:ℝ), (31031868903086587925949722959/189833445857900390625000:ℝ), (12384873962703985121882648081/75933378343160156250000:ℝ), (30512177168334712553230199/562469469208593750000:ℝ)],
![(767658444614665129791647927/1518667566863203125000000:ℝ), (7476600313140798613401496331/7593337834316015625000000:ℝ), (14557206588203629111124386159/30373351337264062500000000:ℝ), (0:ℝ)] ]
theorem row088_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3257344329619853735303606911/1258222903775723520000000000000:ℝ) row088_newTop_coefficients (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row088_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row088_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row088_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row088_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
