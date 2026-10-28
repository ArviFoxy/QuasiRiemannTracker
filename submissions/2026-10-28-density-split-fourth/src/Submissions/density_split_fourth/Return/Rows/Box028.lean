/- Fourth density transition: exact return rectangle 028.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row028_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1213399165465566553657768/119483488728713671875:ℝ), (2377017651418335605444792/119483488728713671875:ℝ), (511164575664435718008967/47793395491485468750:ℝ), (23944466900868390510643/26551886384158593750:ℝ)],
![(2296593970931932859378768/119483488728713671875:ℝ), (4377976824205400214000592/119483488728713671875:ℝ), (440263431884062729638676/23896697745742734375:ℝ), (11795542284289942341284/13275943192079296875:ℝ)],
![(8674621487616723245768/955867909829709375:ℝ), (16039355615769592952536/955867909829709375:ℝ), (7422731709577024706768/955867909829709375:ℝ), (0:ℝ)] ]
theorem row028_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (38973533449498230386639/103117299322798080000000:ℝ) row028_oldSmall_coefficients (57/128:ℝ) (15/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row028_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row028_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row028_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_oldSmall_coefficients]
def row028_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(185097210363982773097768/119483488728713671875:ℝ), (306179975736981327367292/119483488728713671875:ℝ), (51881902180780377843967/47793395491485468750:ℝ), (1851347480552644601929/79655659152475781250:ℝ)],
![(379396593374178708818768/119483488728713671875:ℝ), (621308150601403840860592/119483488728713671875:ℝ), (51271653669192808218676/23896697745742734375:ℝ), (713837840896532183852/39827829576237890625:ℝ)],
![(1563458107967360285768/955867909829709375:ℝ), (2543171010621942032536/955867909829709375:ℝ), (1031524260953736746768/955867909829709375:ℝ), (0:ℝ)] ]
theorem row028_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2440809702233486756639/103117299322798080000000:ℝ) row028_oldSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row028_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row028_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row028_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_oldSwitch_coefficients]
def row028_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(484444563603372328/319490799609375:ℝ), (802704939664647932/319490799609375:ℝ), (136236204315948607/127796319843750:ℝ), (1582571290035203/70997955468750:ℝ)],
![(993495116939413328/319490799609375:ℝ), (1629974880027837232/319490799609375:ℝ), (134786334302636596/63898159921875:ℝ), (603764345806564/35498977734375:ℝ)],
![(4096638395488328/2555926396875:ℝ), (6677301052757656/2555926396875:ℝ), (2715475412269328/2555926396875:ℝ), (0:ℝ)] ]
theorem row028_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6788883399983519/275728711680000000:ℝ) row028_newSwitch_coefficients (57/128:ℝ) (15/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row028_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row028_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row028_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_newSwitch_coefficients]
def row028_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(249897305524886855906029865501/242986810698112500000000000:ℝ), (75828799264923845332095401939/48597362139622500000000000:ℝ), (70362130536182779216586509597/121493405349056250000000000:ℝ), (0:ℝ)],
![(267787532374823803201892239901/121493405349056250000000000:ℝ), (412055009783497721757031342903/121493405349056250000000000:ℝ), (159484611238416459928346647883/121493405349056250000000000:ℝ), (116128922636344117965742403/4499755753668750000000000:ℝ)],
![(287981634170639150497754614301/242986810698112500000000000:ℝ), (450442469469630113430089190103/242986810698112500000000000:ℝ), (182615907579041320084495367303/242986810698112500000000000:ℝ), (275464551558931349178177463/8999511507337500000000000:ℝ)] ]
theorem row028_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (20289141039832309085524489699/8388152691838156800000000000000:ℝ) row028_newTop_coefficients (57/128:ℝ) (15/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row028_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row028_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row028_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row028_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
