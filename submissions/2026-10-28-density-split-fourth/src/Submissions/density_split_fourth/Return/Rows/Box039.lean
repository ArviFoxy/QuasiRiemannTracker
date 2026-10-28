/- Fourth density transition: exact return rectangle 039.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row039_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(975357670564046001789786752/2655188638415859375:ℝ), (2196285039040728283497491968/2655188638415859375:ℝ), (294244390788529560954402736/531037727683171875:ℝ), (83428507781289332948519488/885062879471953125:ℝ)],
![(8484790497647927823052398656/13275943192079296875:ℝ), (18171181554821171580927437632/13275943192079296875:ℝ), (10935336332728059998604597296/13275943192079296875:ℝ), (83256936679491188684053888/885062879471953125:ℝ)],
![(3610559404621289164538798896/13275943192079296875:ℝ), (7197444858783860403951868592/13275943192079296875:ℝ), (3586931370928336939349007196/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row039_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (434089559050223744599560841/1267105374078542807040000000:ℝ) row039_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row039_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row039_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row039_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_oldSmall_coefficients]
def row039_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9793991688513224920238528/295020959823984375:ℝ), (187665714897005179223531968/2655188638415859375:ℝ), (22517575325586099999402736/531037727683171875:ℝ), (13059991402810102086878464/2655188638415859375:ℝ)],
![(30284101888532421391217728/491701599706640625:ℝ), (1682870622434913799135997632/13275943192079296875:ℝ), (103307011882817531193364144/1475104799119921875:ℝ), (12896348110365595989681664/2655188638415859375:ℝ)],
![(41975603478946335506386544/1475104799119921875:ℝ), (747038642706068846164228592/13275943192079296875:ℝ), (369299230519877487480187196/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row039_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1797089269029999809246893/105592114506545233920000000:ℝ) row039_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row039_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row039_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row039_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_oldSwitch_coefficients]
def row039_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(232451019960186310592/7099795546875:ℝ), (494683476766591150528/7099795546875:ℝ), (59280949188091311856/1419959109375:ℝ), (11383741547027656448/2366598515625:ℝ)],
![(2157856684074423018176/35498977734375:ℝ), (4440367257372722491072/35498977734375:ℝ), (2451314402323457005616/35498977734375:ℝ), (11239451986395918848/2366598515625:ℝ)],
![(997823120907358879216/35498977734375:ℝ), (1973556661196775925232/35498977734375:ℝ), (975840271734790483516/35498977734375:ℝ), (0:ℝ)] ]
theorem row039_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (15286308282802139359/847038602280960000000:ℝ) row039_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row039_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row039_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row039_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_newSwitch_coefficients]
def row039_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(99201815644334795275587127/9453175706250000000:ℝ), (193723233548737230826575161/9453175706250000000:ℝ), (94574407610185598929006159/9453175706250000000:ℝ), (0:ℝ)],
![(504193569831205230263522231/23632939265625000000:ℝ), (4941234951007757038377987227/118164696328125000000:ℝ), (1219419732418926044980952909/59082348164062500000:ℝ), (3830841938647020271423763/26258821406250000000:ℝ)],
![(2571564311536963960899093589/236329392656250000000:ℝ), (6334964480024374974586616761/295411740820312500000:ℝ), (25414690208686358502289801423/2363293926562500000000:ℝ), (3886158544783006432662817/21007057125000000000:ℝ)] ]
theorem row039_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (90399643846366724683541761/288718794678652108800000000000:ℝ) row039_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row039_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row039_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row039_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row039_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
