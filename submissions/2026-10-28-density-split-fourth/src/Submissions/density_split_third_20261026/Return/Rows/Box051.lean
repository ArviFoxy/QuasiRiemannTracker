/- Fourth density transition: exact return rectangle 051.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row051_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(23877478546696527060343686196/13275943192079296875:ℝ), (67964780882742108681835152284/13275943192079296875:ℝ), (12860567559341139634667598956/2655188638415859375:ℝ), (6738510950256317488290509564/4425314397359765625:ℝ)],
![(27314720016044020525208766824/13275943192079296875:ℝ), (14933600150685843553017825368/2655188638415859375:ℝ), (67403362964413987304777084408/13275943192079296875:ℝ), (6683358954084169443519741464/4425314397359765625:ℝ)],
![(3602451571043526399013894228/13275943192079296875:ℝ), (7199097745011394246974923756/13275943192079296875:ℝ), (3596648930866790405884467028/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row051_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (139967828100798550938734719859/405473719705133698252800000000:ℝ) row051_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row051_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row051_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row051_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_oldSmall_coefficients]
def row051_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(510441763009450719889288732/4425314397359765625:ℝ), (4247407034379536091591372284/13275943192079296875:ℝ), (780555660258774829135578956/2655188638415859375:ℝ), (1186694224431566751779388692/13275943192079296875:ℝ)],
![(610700877554487713531895608/4425314397359765625:ℝ), (959112879619777013203065368/2655188638415859375:ℝ), (1366262607802203658222908136/4425314397359765625:ℝ), (1135321265420546377411584392/13275943192079296875:ℝ)],
![(117493146592409069986878076/4425314397359765625:ℝ), (702933604749623797730903756/13275943192079296875:ℝ), (350456627810921294131207028/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row051_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2278075694111648507296104953/135157906568377899417600000000:ℝ) row051_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row051_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row051_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row051_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_oldSwitch_coefficients]
def row051_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4019032254139978162516/35498977734375:ℝ), (11141639557754686157564/35498977734375:ℝ), (2046241059608811366476/7099795546875:ℝ), (1036197309285124612444/11832992578125:ℝ)],
![(4813903354940330068904/35498977734375:ℝ), (2518062523809240955928/7099795546875:ℝ), (10749188809115229827768/35498977734375:ℝ), (990922358276505872344/11832992578125:ℝ)],
![(931588751764091151988/35498977734375:ℝ), (1857930770379023075276/35498977734375:ℝ), (926348426901792860788/35498977734375:ℝ), (0:ℝ)] ]
theorem row051_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19385148143652449284139/1084209410919628800000000:ℝ) row051_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row051_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row051_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row051_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_newSwitch_coefficients]
def row051_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(61987460321464748993550332663/4726587853125000000000:ℝ), (145887285764450750602258636837/4726587853125000000000:ℝ), (106321394223356924371332248261/4726587853125000000000:ℝ), (2491115852982707517481891343/525176428125000000000:ℝ)],
![(74552170303937879697080327/3781270282500000000:ℝ), (98162318625921787255145828821/2363293926562500000000:ℝ), (57065656661687060444686257629/2363293926562500000000:ℝ), (610763997826140707136255187/262588214062500000000:ℝ)],
![(42762287229247355311319821439/4726587853125000000000:ℝ), (84982153678170865526092779409/4726587853125000000000:ℝ), (8444295702705667157019066319/945317570625000000000:ℝ), (0:ℝ)] ]
theorem row051_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (46679490134054101595009878409/577437589357304217600000000000000:ℝ) row051_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row051_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row051_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row051_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row051_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
