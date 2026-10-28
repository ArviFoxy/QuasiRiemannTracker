/- Fourth density transition: exact return rectangle 036.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row036_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(136105329087653311870781261104/13275943192079296875:ℝ), (351249257306037665642802270272/13275943192079296875:ℝ), (294276073577361740493219807232/13275943192079296875:ℝ), (26377366682788966366701682688/4425314397359765625:ℝ)],
![(38534434936072473391314968368/2655188638415859375:ℝ), (464123379000497411449929550144/13275943192079296875:ℝ), (350417697091414306633918496768/13275943192079296875:ℝ), (26322133848638937910031679488/4425314397359765625:ℝ)],
![(56732301581225499220105885036/13275943192079296875:ℝ), (113370733862399909338555728272/13275943192079296875:ℝ), (56638478197940175818385780736/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row036_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (33043277276685713417438569/98992607349886156800000000:ℝ) row036_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row036_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row036_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row036_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_oldSmall_coefficients]
def row036_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3319466858629461498699860368/4425314397359765625:ℝ), (24201868940214953447424030272/13275943192079296875:ℝ), (18561570571143202182758367232/13275943192079296875:ℝ), (4318061729192962016590168064/13275943192079296875:ℝ)],
![(3116201585227732996004808368/2655188638415859375:ℝ), (11787562791649206168953690048/4425314397359765625:ℝ), (24048778037737048370683936768/13275943192079296875:ℝ), (4267016093979103464628158464/13275943192079296875:ℝ)],
![(5673980309261300858292265036/13275943192079296875:ℝ), (11314610083100602840503488272/13275943192079296875:ℝ), (1880223597654542547694886912/4425314397359765625:ℝ), (0:ℝ)] ]
theorem row036_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1596660821556960446864819/98992607349886156800000000:ℝ) row036_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row036_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row036_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row036_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_oldSwitch_coefficients]
def row036_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(26216806149062795460784/35498977734375:ℝ), (63650808036332225832512/35498977734375:ℝ), (48736802899471010332672/35498977734375:ℝ), (3767565229912245403648/11832992578125:ℝ)],
![(8217168682182189066928/7099795546875:ℝ), (93167510907300675106624/35498977734375:ℝ), (63249638307260044771328/35498977734375:ℝ), (3722586253880365416448/11832992578125:ℝ)],
![(15004862114874006094156/35498977734375:ℝ), (29923287073292966730512/35498977734375:ℝ), (14918531689864334073856/35498977734375:ℝ), (0:ℝ)] ]
theorem row036_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4544043876106877299/264699563212800000000:ℝ) row036_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row036_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row036_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row036_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_newSwitch_coefficients]
def row036_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6994486220148649754713844369/47265878531250000000:ℝ), (872455165047143640626008417/2954117408203125000:ℝ), (54876644147419730806649824/369264676025390625:ℝ), (154034067018649039215616/123088225341796875:ℝ)],
![(70031369952507157987224810761/236329392656250000000:ℝ), (1739590403627852589388811333/2954117408203125000:ℝ), (540144761611292721775315168/1846323380126953125:ℝ), (0:ℝ)],
![(712605067751252019201996207041/4726587853125000000000:ℝ), (88847660413216636770421010833/295411740820312500000:ℝ), (1395241401887414681867464312/9231616900634765625:ℝ), (3502115632159067584358912/3077205633544921875:ℝ)] ]
theorem row036_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (131692690707695717791/234959956606976000000000000:ℝ) row036_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row036_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row036_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row036_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row036_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
