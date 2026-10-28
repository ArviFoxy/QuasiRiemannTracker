/- Fourth density transition: exact return rectangle 061.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row061_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2876934506765899337624906/2655188638415859375:ℝ), (39199245356438238773498198/13275943192079296875:ℝ), (35286494535912783665333206/13275943192079296875:ℝ), (387844178881102432591094/491701599706640625:ℝ)],
![(17763454086767685264165476/13275943192079296875:ℝ), (9118326762416430656263868/2655188638415859375:ℝ), (37980605068812435667696652/13275943192079296875:ℝ), (376005013170031365760844/491701599706640625:ℝ)],
![(3694055575367738083272346/13275943192079296875:ℝ), (7342795466277343761476342/13275943192079296875:ℝ), (3648903009107361114141496/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row061_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12328306140089217941532653/32997535783295385600000000:ℝ) row061_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row061_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row061_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row061_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_oldSmall_coefficients]
def row061_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(205561870773007983454906/2655188638415859375:ℝ), (908171481966112927196066/4425314397359765625:ℝ), (2378766146091670394063206/13275943192079296875:ℝ), (75771768634066181083282/1475104799119921875:ℝ)],
![(47944568850459506805388/491701599706640625:ℝ), (627466897207492309803868/2655188638415859375:ℝ), (2420122813668550844356652/13275943192079296875:ℝ), (64114736644666689342532/1475104799119921875:ℝ)],
![(377058186150100782702346/13275943192079296875:ℝ), (738340036377887904086342/13275943192079296875:ℝ), (361427569673003494821496/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row061_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (631062699530412358647653/32997535783295385600000000:ℝ) row061_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row061_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row061_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row061_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_oldSwitch_coefficients]
def row061_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(539695192473338426/7099795546875:ℝ), (7151189406518848358/35498977734375:ℝ), (6240954756768778726/35498977734375:ℝ), (22073354675513858/438258984375:ℝ)],
![(3399984467274899396/35498977734375:ℝ), (1647197471705742428/7099795546875:ℝ), (6346926604512008492/35498977734375:ℝ), (18645057401027108/438258984375:ℝ)],
![(993977676888406666/35498977734375:ℝ), (1947102162606742982/35498977734375:ℝ), (953503646591773816/35498977734375:ℝ), (0:ℝ)] ]
theorem row061_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1774790536602501413/88233187737600000000:ℝ) row061_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row061_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row061_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row061_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_newSwitch_coefficients]
def row061_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(66483813742927102527158957/4726587853125000000000:ℝ), (159205742775865276971227911/4726587853125000000000:ℝ), (122332792988266160779466759/4726587853125000000000:ℝ), (1969033387880943598369987/315105856875000000000:ℝ)],
![(44789899537993625507008301/2363293926562500000000:ℝ), (88452031449320725654573543/2363293926562500000000:ℝ), (46422160433085313348232327/2363293926562500000000:ℝ), (178349666167010119722539/157552928437500000000:ℝ)],
![(49552165128250305271854653/4726587853125000000000:ℝ), (94720805422496362674792739/4726587853125000000000:ℝ), (45264021764655751483370711/4726587853125000000000:ℝ), (0:ℝ)] ]
theorem row061_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (8978967083386324631583607/14097597396418560000000000000:ℝ) row061_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row061_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row061_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row061_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row061_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
