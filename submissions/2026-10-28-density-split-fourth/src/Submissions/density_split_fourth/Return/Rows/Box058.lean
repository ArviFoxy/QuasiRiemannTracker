/- Fourth density transition: exact return rectangle 058.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row058_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5504140977028764745235474836/13275943192079296875:ℝ), (3253730904598047653763505804/2655188638415859375:ℝ), (16025216873182781083590316732/13275943192079296875:ℝ), (1753567732779264428036087516/4425314397359765625:ℝ)],
![(1113560496265641044660734216/2655188638415859375:ℝ), (16230163044318156310547865208/13275943192079296875:ℝ), (15757608062799207357815152376/13275943192079296875:ℝ), (1698415736607116383265319416/4425314397359765625:ℝ)],
![(228871605995473412217009844/13275943192079296875:ℝ), (457386395652203205451285388/13275943192079296875:ℝ), (228514952774927548670213044/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row058_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9063856957093174315934537627/25342107481570856140800000000:ℝ) row058_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row058_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row058_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row058_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_oldSmall_coefficients]
def row058_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(380878524027725611710854836/13275943192079296875:ℝ), (224509286252624768472925804/2655188638415859375:ℝ), (122506419693713018050930748/1475104799119921875:ℝ), (360889754871667155904602548/13275943192079296875:ℝ)],
![(70143173884581694134214216/2655188638415859375:ℝ), (1010727962800651258823505208/13275943192079296875:ℝ), (969529148295181065464232376/13275943192079296875:ℝ), (309516795860646781536798248/13275943192079296875:ℝ)],
![(21539441537299087993029844/13275943192079296875:ℝ), (42957772567802239765825388/13275943192079296875:ℝ), (21418476749948368146233044/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row058_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (445681289902677325614572627/25342107481570856140800000000:ℝ) row058_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row058_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row058_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row058_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_oldSwitch_coefficients]
def row058_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(999660459691433579956/35498977734375:ℝ), (589198163818016325484/7099795546875:ℝ), (2893259707228711782172/35498977734375:ℝ), (315643016082054578236/11832992578125:ℝ)],
![(183969065824096420936/7099795546875:ℝ), (2650224595889362464568/35498977734375:ℝ), (2541484136052962874296/35498977734375:ℝ), (270368065073435838136/11832992578125:ℝ)],
![(56902520392787770324/35498977734375:ℝ), (113491485886785290348/35498977734375:ℝ), (56589344654870957524/35498977734375:ℝ), (0:ℝ)] ]
theorem row058_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1260143507851018296467/67763088182476800000000:ℝ) row058_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row058_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row058_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row058_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_newSwitch_coefficients]
def row058_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(21728675214330315608470641407/4726587853125000000000:ℝ), (63321483118412376268506635773/4726587853125000000000:ℝ), (61480757331397560067835633789/4726587853125000000000:ℝ), (2209763784908709508382199047/525176428125000000000:ℝ)],
![(6321052073164667379232113983/2363293926562500000000:ℝ), (3369087828600418762733735033/472658785312500000000:ℝ), (14755263527468954819119071533/2363293926562500000000:ℝ), (470087963789141702586409039/262588214062500000000:ℝ)],
![(2472963602788773833513331911/4726587853125000000000:ℝ), (4914197358369852976890473161/4726587853125000000000:ℝ), (19530633096411910699660591/37812702825000000000:ℝ), (0:ℝ)] ]
theorem row058_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (4318720800681154328271681281/36089849334831513600000000000000:ℝ) row058_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row058_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row058_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row058_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row058_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
