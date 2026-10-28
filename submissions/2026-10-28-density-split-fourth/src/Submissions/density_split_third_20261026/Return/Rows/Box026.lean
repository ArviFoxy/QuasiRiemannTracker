/- Fourth density transition: exact return rectangle 026.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row026_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(33670721977403795929583368/13275943192079296875:ℝ), (86499237693391009636339712/13275943192079296875:ℝ), (14434908197628972708605834/2655188638415859375:ℝ), (716492529206849531030938/491701599706640625:ℝ)],
![(47221306127602272678387968/13275943192079296875:ℝ), (113087203648993946263256512/13275943192079296875:ℝ), (16978613765501943686157424/2655188638415859375:ℝ), (704653363495778464200688/491701599706640625:ℝ)],
![(110926865381024210048288/106207545536634375:ℝ), (220306983729890927044576/106207545536634375:ℝ), (109386562524580511996288/106207545536634375:ℝ), (0:ℝ)] ]
theorem row026_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (534477991326194829817249/1649876789164769280000000:ℝ) row026_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row026_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row026_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row026_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_oldSmall_coefficients]
def row026_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2426300319918346024023368/13275943192079296875:ℝ), (208259385850214911566656/491701599706640625:ℝ), (807335586982381331075834/2655188638415859375:ℝ), (93258377321134903462814/1475104799119921875:ℝ)],
![(3992555028617749843827968/13275943192079296875:ℝ), (8575738001825764016216512/13275943192079296875:ℝ), (1063792465074194338077424/2655188638415859375:ℝ), (81601345331735411722064/1475104799119921875:ℝ)],
![(4470983706005700896096/35402515178878125:ℝ), (26226036640869812324576/106207545536634375:ℝ), (12818842340441504636288/106207545536634375:ℝ), (0:ℝ)] ]
theorem row026_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (27618807127375578112249/1649876789164769280000000:ℝ) row026_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row026_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row026_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row026_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_oldSwitch_coefficients]
def row026_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6374551933536729928/35498977734375:ℝ), (14757837637390626752/35498977734375:ℝ), (2114479721111189114/7099795546875:ℝ), (27005222978593966/438258984375:ℝ)],
![(10509983984037686528/35498977734375:ℝ), (22556717629344559552/35498977734375:ℝ), (2792004437230411504/7099795546875:ℝ), (23576925704107216/438258984375:ℝ)],
![(35423209779849248/283991821875:ℝ), (69289473620406496/283991821875:ℝ), (33881243035557248/283991821875:ℝ), (0:ℝ)] ]
theorem row026_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (78468213744710329/4411659386880000000:ℝ) row026_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row026_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row026_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row026_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_newSwitch_coefficients]
def row026_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(230229871806034853731279733/4726587853125000000000:ℝ), (440528710292858457515357419/4726587853125000000000:ℝ), (210723933682106314438845311/4726587853125000000000:ℝ), (0:ℝ)],
![(53242116556347674009193889/472658785312500000000:ℝ), (848141989662287871828271/3781270282500000000:ℝ), (56632030046399695255098979/472658785312500000000:ℝ), (1255634723212903119479831/157552928437500000000:ℝ)],
![(65729494710526408629131233/945317570625000000000:ℝ), (139334252416944314121370979/945317570625000000000:ℝ), (86069772133728384735703459/945317570625000000000:ℝ), (4123603501972729597884571/315105856875000000000:ℝ)] ]
theorem row026_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (38612674506181947166438687/56390389585674240000000000000:ℝ) row026_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row026_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row026_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row026_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row026_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
