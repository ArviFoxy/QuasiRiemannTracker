/- Fourth density transition: exact return rectangle 030.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row030_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(135962247544254133205340611104/13275943192079296875:ℝ), (350872603567554804591268135376/13275943192079296875:ℝ), (58790503493892272293582845848/2655188638415859375:ℝ), (26347371843131641460683589156/4425314397359765625:ℝ)],
![(192476488202856593106850190336/13275943192079296875:ℝ), (92728250665485920616060969728/2655188638415859375:ℝ), (350041517107152104610468121472/13275943192079296875:ℝ), (26292219846959493415912821056/4425314397359765625:ℝ)],
![(56679450760298492835658392832/13275943192079296875:ℝ), (113264527634199083652757662464/13275943192079296875:ℝ), (56585123400849244416999269632/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row030_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (33749168220591133722418247459/101368429926283424563200000000:ℝ) row030_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row030_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row030_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row030_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_oldSmall_coefficients]
def row030_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9922437766958992821272931104/13275943192079296875:ℝ), (23993076289728052672916215376/13275943192079296875:ℝ), (3650470778099685680317685848/2655188638415859375:ℝ), (4181674348605042889071707468/13275943192079296875:ℝ)],
![(15646513098334648134045070336/13275943192079296875:ℝ), (7071204254247840880692009728/2655188638415859375:ℝ), (23839892144046890048393881472/13275943192079296875:ℝ), (4130301389594022514703903168/13275943192079296875:ℝ)],
![(5775777427517771541804952832/13275943192079296875:ℝ), (11517721222541426553850782464/13275943192079296875:ℝ), (637998373249627345771758848/1475104799119921875:ℝ), (0:ℝ)] ]
theorem row030_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1640810001433141005281842459/101368429926283424563200000000:ℝ) row030_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row030_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row030_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row030_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_oldSwitch_coefficients]
def row030_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(26118244218811920810784/35498977734375:ℝ), (63090025414969752777296/35498977734375:ℝ), (9582436451148056466008/7099795546875:ℝ), (3646764776045692308676/11832992578125:ℝ)],
![(41253890937757686035456/35498977734375:ℝ), (18627558554262379551488/7099795546875:ℝ), (62688586185217707427712/35498977734375:ℝ), (3601489825037073568576/11832992578125:ℝ)],
![(15272364369909504470272/35498977734375:ℝ), (30457025065429649433344/35498977734375:ℝ), (15184768845308044963072/35498977734375:ℝ), (0:ℝ)] ]
theorem row030_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4668978147050383483739/271052352729907200000000:ℝ) row030_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row030_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row030_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row030_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_newSwitch_coefficients]
def row030_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(725333153734615687529736922631/4726587853125000000000:ℝ), (1441558941081759736627162897801/4726587853125000000000:ℝ), (143250527328457973855850489559/945317570625000000000:ℝ), (0:ℝ)],
![(744680480904129673582874626943/2363293926562500000000:ℝ), (298494537572618034913025995193/472658785312500000000:ℝ), (760110602290188388442053937453/2363293926562500000000:ℝ), (1365707580686715481083122159/262588214062500000000:ℝ)],
![(775587342744433414319532076607/4726587853125000000000:ℝ), (1577931236835198654121156812733/4726587853125000000000:ℝ), (838380127351598046871910491709/4726587853125000000000:ℝ), (4001003018703857065375625287/525176428125000000000:ℝ)] ]
theorem row030_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (717783435058183747138686792641/9239001429716867481600000000000000:ℝ) row030_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row030_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row030_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row030_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row030_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
