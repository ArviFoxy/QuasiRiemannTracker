/- Fourth density transition: exact return rectangle 023.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row023_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(10579742872223029847212165984/13275943192079296875:ℝ), (30852137606564458372039349264/13275943192079296875:ℝ), (29966521915418367133980624376/13275943192079296875:ℝ), (3231375484697788632218334532/4425314397359765625:ℝ)],
![(11269787409163608764982656384/13275943192079296875:ℝ), (32065250455749987272230008064/13275943192079296875:ℝ), (30324135042655032295902550976/13275943192079296875:ℝ), (3176223488525640587447566432/4425314397359765625:ℝ)],
![(6842037109092894815354432/106207545536634375:ℝ), (13671925788078512511292864/106207545536634375:ℝ), (6829895123161331490938432/106207545536634375:ℝ), (0:ℝ)] ]
theorem row023_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (391570457588347403103181207/1267105374078542807040000000:ℝ) row023_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row023_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row023_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row023_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_oldSmall_coefficients]
def row023_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6853842432014785435936864/163900533235546875:ℝ), (1574708538166907109814469264/13275943192079296875:ℝ), (494820888434308721803234792/4425314397359765625:ℝ), (464914714688232439970183596/13275943192079296875:ℝ)],
![(22164914576815078122865792/491701599706640625:ℝ), (1609344723064270307659128064/13275943192079296875:ℝ), (1424435152411652602756630976/13275943192079296875:ℝ), (413541755677212065602379296/13275943192079296875:ℝ)],
![(28146237843829842382016/3933612797653125:ℝ), (1515299407421104169212864/106207545536634375:ℝ), (755356742455287219898432/106207545536634375:ℝ), (0:ℝ)] ]
theorem row023_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2117474059390392910124023/140789486008726978560000000:ℝ) row023_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row023_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row023_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row023_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_oldSwitch_coefficients]
def row023_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1453364524642882375264/35498977734375:ℝ), (4120092510736477376144/35498977734375:ℝ), (3881463507297077306296/35498977734375:ℝ), (404911277121015455972/11832992578125:ℝ)],
![(1568083774543430113664/35498977734375:ℝ), (4212217191416379890944/35498977734375:ℝ), (3723045952768952424896/35498977734375:ℝ), (359636326112396715872/11832992578125:ℝ)],
![(2011495206914295872/283991821875:ℝ), (4011059118139255744/283991821875:ℝ), (1999578890419959872/283991821875:ℝ), (0:ℝ)] ]
theorem row023_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (54566183615120273647/3388154409123840000000:ℝ) row023_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row023_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row023_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row023_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_newSwitch_coefficients]
def row023_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(11555911180876542198924241391/4726587853125000000000:ℝ), (22967252427034289271187733281/4726587853125000000000:ℝ), (2282353268270605956583651903/945317570625000000000:ℝ), (0:ℝ)],
![(15419268910914509791006422599/2363293926562500000000:ℝ), (33649571048547849215691087877/2363293926562500000000:ℝ), (21195456974029237086650328797/2363293926562500000000:ℝ), (329411929752142698036562891/262588214062500000000:ℝ)],
![(30842161311742232066608349159/4726587853125000000000:ℝ), (78876691860839450778254201077/4726587853125000000000:ℝ), (65390707020216583657437462677/4726587853125000000000:ℝ), (1928411716834711499282506751/525176428125000000000:ℝ)] ]
theorem row023_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (11778007222289350948860428441/144359397339326054400000000000000:ℝ) row023_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row023_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row023_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row023_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row023_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
