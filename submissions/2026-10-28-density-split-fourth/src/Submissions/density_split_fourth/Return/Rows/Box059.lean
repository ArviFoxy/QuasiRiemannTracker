/- Fourth density transition: exact return rectangle 059.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row059_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(720516281430989075080373596/13275943192079296875:ℝ), (2100275597329811624157213716/13275943192079296875:ℝ), (2039168116161498241604148244/13275943192079296875:ℝ), (24422543384413385801011412/491701599706640625:ℝ)],
![(757413507645434463789711032/13275943192079296875:ℝ), (2153239134908456782572910888/13275943192079296875:ℝ), (406916665183617347883381256/2655188638415859375:ℝ), (23657681802487307402174312/491701599706640625:ℝ)],
![(57485758430222700445209436/13275943192079296875:ℝ), (114792700895579202809207972/13275943192079296875:ℝ), (57307105583554257799936036/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row059_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (126681595258222814847066529/351973715021817446400000000:ℝ) row059_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row059_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row059_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row059_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_oldSmall_coefficients]
def row059_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(49990029052841495987553596/13275943192079296875:ℝ), (16094107749345511023221524/1475104799119921875:ℝ), (139774441138923194586168244/13275943192079296875:ℝ), (1663606863381604276471412/491701599706640625:ℝ)],
![(5435578799850088980363448/1475104799119921875:ℝ), (136184108095955417016950888/13275943192079296875:ℝ), (25143756249526979760861256/2655188638415859375:ℝ), (1424245307168103216134312/491701599706640625:ℝ)],
![(5475911843589548723589436/13275943192079296875:ℝ), (10890904135168088403467972/13275943192079296875:ℝ), (5415138011023756053316036/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row059_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6264807642875029133511529/351973715021817446400000000:ℝ) row059_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row059_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row059_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row059_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_oldSwitch_coefficients]
def row059_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(131222406053710137916/35498977734375:ℝ), (380159231290526368436/35498977734375:ℝ), (366781867233046956724/35498977734375:ℝ), (4364620089345582452/1314776953125:ℝ)],
![(128369023791501412472/35498977734375:ℝ), (357206269679474015848/35498977734375:ℝ), (65918591198722184776/7099795546875:ℝ), (3731668001550493352/1314776953125:ℝ)],
![(14461365013599786556/35498977734375:ℝ), (28765004675620854212/35498977734375:ℝ), (14304018822894505156/35498977734375:ℝ), (0:ℝ)] ]
theorem row059_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (17699571360405767209/941154002534400000000:ℝ) row059_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row059_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row059_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row059_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_newSwitch_coefficients]
def row059_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2885083314506326371572977031/4726587853125000000000:ℝ), (8165071485399240622178778517/4726587853125000000000:ℝ), (7687027485472720804835313173/4726587853125000000000:ℝ), (802321317147564240623221229/1575529284375000000000:ℝ)],
![(1024295841928601500365625031/2363293926562500000000:ℝ), (503132489023259781279481649/472658785312500000000:ℝ), (1972462445513937160651459973/2363293926562500000000:ℝ), (160337019598995564404949253/787764642187500000000:ℝ)],
![(642181358308579017101124911/4726587853125000000000:ℝ), (1268259339337286453933072929/4726587853125000000000:ℝ), (626173362499117130912380643/4726587853125000000000:ℝ), (0:ℝ)] ]
theorem row059_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (848960550433741020223126649/4511231166853939200000000000000:ℝ) row059_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row059_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row059_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row059_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row059_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
