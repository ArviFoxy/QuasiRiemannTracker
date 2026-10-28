/- Fourth density transition: exact return rectangle 015.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row015_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4796345967212781814250995504/13275943192079296875:ℝ), (14175603679039553833661160512/13275943192079296875:ℝ), (13962548692120632522363584512/13275943192079296875:ℝ), (1527763592971123148953223168/4425314397359765625:ℝ)],
![(965671340327420549466128272/2655188638415859375:ℝ), (14073526592280692091878194624/13275943192079296875:ℝ), (13662762610143953744803463168/13275943192079296875:ℝ), (1472530758821094692283219968/4425314397359765625:ℝ)],
![(197466722940765067391950156/13275943192079296875:ℝ), (394535081181301789645482512/13275943192079296875:ℝ), (197068601910930900126969856/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row015_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (101201212462825814949049/386689872460492800000000:ℝ) row015_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row015_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row015_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row015_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_oldSmall_coefficients]
def row015_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(60559433022689288347105168/4425314397359765625:ℝ), (521429999002475869502120512/13275943192079296875:ℝ), (165989470293067399308181504/4425314397359765625:ℝ), (158216531044244543619989504/13275943192079296875:ℝ)],
![(31317144059505939456288272/2655188638415859375:ℝ), (420032714372230941088114624/13275943192079296875:ℝ), (370618285686296465120903168/13275943192079296875:ℝ), (107170895830385991657979904/13275943192079296875:ℝ)],
![(26280380240482206607930156/13275943192079296875:ℝ), (17464454579230950884147504/4425314397359765625:ℝ), (26113201176875722355449856/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row015_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1707589497493763008433/128896624153497600000000:ℝ) row015_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row015_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row015_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row015_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_oldSwitch_coefficients]
def row015_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(473359342034196843184/35498977734375:ℝ), (1357591185776966783552/35498977734375:ℝ), (1295476262241947287552/35498977734375:ℝ), (137081316799777865728/11832992578125:ℝ)],
![(81452838979959722512/7099795546875:ℝ), (1090031051624344352704/35498977734375:ℝ), (959074908847895625728/35498977734375:ℝ), (92102340767897878528/11832992578125:ℝ)],
![(69729705891457989676/35498977734375:ℝ), (139024068171895025552/35498977734375:ℝ), (69294928681247973376/35498977734375:ℝ), (0:ℝ)] ]
theorem row015_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (14846555126859379/1033982668800000000:ℝ) row015_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row015_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row015_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row015_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_newSwitch_coefficients]
def row015_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(32904168775857101712629681/47265878531250000000:ℝ), (4087720603960804512241537/2954117408203125000:ℝ), (253910456535415422764512/369264676025390625:ℝ), (0:ℝ)],
![(1048591591945726977686971547/236329392656250000000:ℝ), (172598263715456072298958603/14770587041015625000:ℝ), (18608673953033703373729696/1846323380126953125:ℝ), (1741970535019667741677568/615441126708984375:ℝ)],
![(29107705677302664311360891561/4726587853125000000000:ℝ), (5177329769058782888895737593/295411740820312500000:ℝ), (153129305868227474456669752/9231616900634765625:ℝ), (16062819982723632273137152/3077205633544921875:ℝ)] ]
theorem row015_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (50773764176238103731/458906165248000000000000:ℝ) row015_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row015_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row015_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row015_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row015_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
