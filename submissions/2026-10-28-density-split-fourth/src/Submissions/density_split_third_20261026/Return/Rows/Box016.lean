/- Fourth density transition: exact return rectangle 016.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row016_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4812692903931169709838871348/13275943192079296875:ℝ), (14223885413693503756555038044/13275943192079296875:ℝ), (14010071955414841849668962044/13275943192079296875:ℝ), (1532959748090672248953015116/4425314397359765625:ℝ)],
![(4845746741917146889105718504/13275943192079296875:ℝ), (14124136323021827940906680056/13275943192079296875:ℝ), (548472531195893359510158104/531037727683171875:ℝ), (1477807751918524204182247016/4425314397359765625:ℝ)],
![(198263939682010113415660756/13275943192079296875:ℝ), (396128783652609348072591212/13275943192079296875:ℝ), (197865087640993412530367956/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row016_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6681689340698943875348862803/25342107481570856140800000000:ℝ) row016_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row016_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row016_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row016_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_oldSmall_coefficients]
def row016_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(179146307008317087943211348/13275943192079296875:ℝ), (513546862964666480588058044/13275943192079296875:ℝ), (489798654684484700921982044/13275943192079296875:ℝ), (155397918827585658433385348/13275943192079296875:ℝ)],
![(154059819952556339267038504/13275943192079296875:ℝ), (411833790324835828498160056/13275943192079296875:ℝ), (14471973038802160118118104/531037727683171875:ℝ), (104024959816565284065581048/13275943192079296875:ℝ)],
![(26615609086355480356640756/13275943192079296875:ℝ), (53063168390444171217051212/13275943192079296875:ℝ), (8815925661251255723782652/4425314397359765625:ℝ), (0:ℝ)] ]
theorem row016_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (342295850983374309213977803/25342107481570856140800000000:ℝ) row016_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row016_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row016_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row016_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_oldSwitch_coefficients]
def row016_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(466488861358810599508/35498977734375:ℝ), (1336234505870068302524/35498977734375:ℝ), (1273375748753840306524/35498977734375:ℝ), (134543212047579617836/11832992578125:ℝ)],
![(400372736310193126184/35498977734375:ℝ), (1067742805799353627576/35498977734375:ℝ), (37407035297027975384/1419959109375:ℝ), (89268261038960877736/11832992578125:ℝ)],
![(70601525915121772276/35498977734375:ℝ), (140766009016789778252/35498977734375:ℝ), (70165049502478943476/35498977734375:ℝ), (0:ℝ)] ]
theorem row016_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (990416263266720759563/67763088182476800000000:ℝ) row016_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row016_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row016_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row016_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_newSwitch_coefficients]
def row016_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(33716139650574571432664471/47265878531250000000:ℝ), (67023938765755600744066297/47265878531250000000:ℝ), (33308976664198432942024451/47265878531250000000:ℝ), (0:ℝ)],
![(554153008273565914053370519/118164696328125000000:ℝ), (293159542827213608556881863/23632939265625000000:ℝ), (635713067237837914489900301/59082348164062500000:ℝ), (79949989354128440062297193/26258821406250000000:ℝ)],
![(7588510259168733525597029753/1181646963281250000000:ℝ), (1351161201244456300859835961/73852935205078125000:ℝ), (40968853563059164566022321789/2363293926562500000000:ℝ), (2868587644412994904455324829/525176428125000000000:ℝ)] ]
theorem row016_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (72834281684504386106007473/360898493348315136000000000000:ℝ) row016_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row016_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row016_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row016_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row016_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
