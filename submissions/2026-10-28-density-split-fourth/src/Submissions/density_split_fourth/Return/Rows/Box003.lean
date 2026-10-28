/- Fourth density transition: exact return rectangle 003.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row003_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8157796382393030475582562816/1075351398558423046875:ℝ), (24281042408715476679723192464/1075351398558423046875:ℝ), (4817902904776274264180478416/215070279711684609375:ℝ), (32782993548379125226443724/4425314397359765625:ℝ)],
![(6604604830076215875206346752/1075351398558423046875:ℝ), (19500942319843646569681447936/1075351398558423046875:ℝ), (19189855606672053011944188416/1075351398558423046875:ℝ), (25899239311044419636909824/4425314397359765625:ℝ)],
![(114479557161147650229415936/1075351398558423046875:ℝ), (228062139799827485832630272/1075351398558423046875:ℝ), (113584644774908250003214336/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row003_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (119482144261514969308261/1374897324303974400000000:ℝ) row003_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row003_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row003_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_oldSmall_coefficients]
def row003_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1121434480504896055600256/14338018647445640625:ℝ), (223118266868696553920841616/1075351398558423046875:ℝ), (194278951347182290635321232/1075351398558423046875:ℝ), (227437526100597914448812/4425314397359765625:ℝ)],
![(4926672377964379831923968/71690093237228203125:ℝ), (29366811475050227531477248/215070279711684609375:ℝ), (14587323968375257175705344/215070279711684609375:ℝ), (0:ℝ)],
![(34666451143453216548431488/71690093237228203125:ℝ), (1507570818955658501972919424/1075351398558423046875:ℝ), (1455792298581970193892623488/1075351398558423046875:ℝ), (1926816479820911628585088/4425314397359765625:ℝ)] ]
theorem row003_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (108313854034771571073937/8799342875545436160000000:ℝ) row003_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row003_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row003_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_oldSwitch_coefficients]
def row003_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8572697726771129728/115016687859375:ℝ), (565445289175044584336/2875417196484375:ℝ), (488888859959676406672/2875417196484375:ℝ), (566907562575047852/11832992578125:ℝ)],
![(39385770680777891584/575083439296875:ℝ), (78266971648499249408/575083439296875:ℝ), (38882579053661357824/575083439296875:ℝ), (0:ℝ)],
![(277021187915020137344/575083439296875:ℝ), (4015044838287981413504/2875417196484375:ℝ), (3876451370357403960448/2875417196484375:ℝ), (5129661227580754048/11832992578125:ℝ)] ]
theorem row003_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (317825006429816977/23528850063360000000:ℝ) row003_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row003_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row003_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_newSwitch_coefficients]
def row003_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4788078525779266094594017822279/273360162035376562500000000:ℝ), (9492989508897866081902084283321/273360162035376562500000000:ℝ), (4705144579404927432532829695417/273360162035376562500000000:ℝ), (0:ℝ)],
![(67366814197012797076714389056839/136680081017688281250000000:ℝ), (194441200534527147603490753727573/136680081017688281250000000:ℝ), (186895924178035830850841085492757/136680081017688281250000000:ℝ), (246177830604908135481534470461/562469469208593750000000:ℝ)],
![(245854339870429414720729071508039/273360162035376562500000000:ℝ), (725190849062178972027582726430421/273360162035376562500000000:ℝ), (712974358558717357663793113951957/273360162035376562500000000:ℝ), (38458830812863393804572900581/44997557536687500000000:ℝ)] ]
theorem row003_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (932185724021751134319245706289/1431578059407045427200000000000000:ℝ) row003_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row003_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row003_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
