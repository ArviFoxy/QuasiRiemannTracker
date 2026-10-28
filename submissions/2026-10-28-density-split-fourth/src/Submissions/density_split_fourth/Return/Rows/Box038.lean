/- Fourth density transition: exact return rectangle 038.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row038_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(24312028100379460360646596444/13275943192079296875:ℝ), (58528776622917504917233023572/13275943192079296875:ℝ), (44168445956566995457427657812/13275943192079296875:ℝ), (368579708274757899249906692/491701599706640625:ℝ)],
![(38592046734788423455734982328/13275943192079296875:ℝ), (17404208695152288867183251528/2655188638415859375:ℝ), (58360088827041928453628904296/13275943192079296875:ℝ), (367814846692831820851069592/491701599706640625:ℝ)],
![(14300607166624740406824257884/13275943192079296875:ℝ), (28554096016160873463076744868/13275943192079296875:ℝ), (14253534766301898756188424484/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row038_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (30471351777831890160223652641/90105271045585266278400000000:ℝ) row038_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row038_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row038_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row038_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_oldSmall_coefficients]
def row038_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1982757233983611951861616444/13275943192079296875:ℝ), (4480113653560831980857283572/13275943192079296875:ℝ), (3028654963666572961031117812/13275943192079296875:ℝ), (19676224683914137673766692/491701599706640625:ℝ)],
![(3436569080157039576360222328/13275943192079296875:ℝ), (54551375550456469374077464/98340319941328125:ℝ), (4452743418551492356921584296/13275943192079296875:ℝ), (19436863127700636613429592/491701599706640625:ℝ)],
![(486785859290402622795492628/4425314397359765625:ℝ), (2903875811534113655238684868/13275943192079296875:ℝ), (1443559252787231447725644484/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row038_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1492950687964732951991057641/90105271045585266278400000000:ℝ) row038_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row038_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row038_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row038_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_oldSwitch_coefficients]
def row038_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5225764568573464228924/35498977734375:ℝ), (11798272265376239661812/35498977734375:ℝ), (7962527413121356036852/35498977734375:ℝ), (51478310883471735332/1314776953125:ℝ)],
![(9068165404227801172088/35498977734375:ℝ), (3884467992188168177288/7099795546875:ℝ), (11727211293425527912616/35498977734375:ℝ), (50845358795676646232/1314776953125:ℝ)],
![(3859715582930145455164/35498977734375:ℝ), (7675785661851274431428/35498977734375:ℝ), (3816176810366502413764/35498977734375:ℝ), (0:ℝ)] ]
theorem row038_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4240891145360104488361/240935424648806400000000:ℝ) row038_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row038_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row038_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row038_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_newSwitch_coefficients]
def row038_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(14768071339591739726276683/378127028250000000:ℝ), (729307720028638083754726589/9453175706250000000:ℝ), (360158926244627753975827639/9453175706250000000:ℝ), (0:ℝ)],
![(9367954897036130058694182343/118164696328125000000:ℝ), (18555372296443920910891806959/118164696328125000000:ℝ), (1154678084598378363742232459/14770587041015625000:ℝ), (32449135411350964040074829/78776464218750000000:ℝ)],
![(1915959771255061581572516081/47265878531250000000:ℝ), (746021558160042429339113318/9231616900634765625:ℝ), (155028639924888930419236273/3781270282500000000:ℝ), (1130629986176592392614819303/1575529284375000000000:ℝ)] ]
theorem row038_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (353995367281140304311417013/2309750357429216870400000000000:ℝ) row038_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row038_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row038_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row038_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row038_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
