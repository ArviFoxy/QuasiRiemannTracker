/- Fourth density transition: exact return rectangle 020.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row020_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2081860198684972097024323/13275943192079296875:ℝ), (5317739132357788202726969/13275943192079296875:ℝ), (4414770422756817271443469/13275943192079296875:ℝ), (392896702864315023996941/4425314397359765625:ℝ)],
![(2889801830666630421189974/13275943192079296875:ℝ), (6868031745306093143451346/13275943192079296875:ℝ), (1023590761501807502419654/2655188638415859375:ℝ), (379760285263083794528966/4425314397359765625:ℝ)],
![(846106923868816953597751/13275943192079296875:ℝ), (1666128160801745203036577/13275943192079296875:ℝ), (820264907327106122876326/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row020_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7271787829194603195769037/24748151837471539200000000:ℝ) row020_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row020_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row020_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row020_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_oldSmall_coefficients]
def row020_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(145279686758649226239323/13275943192079296875:ℝ), (306898527656730585371969/13275943192079296875:ℝ), (187960546885731586588469/13275943192079296875:ℝ), (26161805438000383705823/13275943192079296875:ℝ)],
![(264861211245023293859974/13275943192079296875:ℝ), (520807893575557824381346/13275943192079296875:ℝ), (53741749269234563689654/2655188638415859375:ℝ), (12366282806408631676898/13275943192079296875:ℝ)],
![(134833709241718956052751/13275943192079296875:ℝ), (258143933661718361071577/13275943192079296875:ℝ), (41175968028358571985442/4425314397359765625:ℝ), (0:ℝ)] ]
theorem row020_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (440514641777387595354037/24748151837471539200000000:ℝ) row020_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row020_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row020_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row020_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_oldSwitch_coefficients]
def row020_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(380764596317539483/35498977734375:ℝ), (802859362418952449/35498977734375:ℝ), (489390565639848949/35498977734375:ℝ), (22275899898228661/11832992578125:ℝ)],
![(696322643287970054/35498977734375:ℝ), (1367621439014725666/35498977734375:ℝ), (140519533716033334/7099795546875:ℝ), (10089684399053686/11832992578125:ℝ)],
![(356062647600014671/35498977734375:ℝ), (682155115557899417/35498977734375:ℝ), (326658868768822246/35498977734375:ℝ), (0:ℝ)] ]
theorem row020_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1248567419678505077/66174890803200000000:ℝ) row020_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row020_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row020_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row020_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_newSwitch_coefficients]
def row020_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(713679982216760756152143439/134992672610062500000000:ℝ), (1339523552136442864451115353/134992672610062500000000:ℝ), (313804946722893777116454707/67496336305031250000000:ℝ), (0:ℝ)],
![(4859018505356760353581441181/337481681525156250000000:ℝ), (2011643604721263863864134949/67496336305031250000000:ℝ), (12058639302976760045147936281/674963363050312500000000:ℝ), (182312300854498023155128517/74995929227812500000000:ℝ)],
![(8561982176833569201248232763/843704203812890625000000:ℝ), (77157719577515064856878686519/3374816815251562500000000:ℝ), (217002002392728909412659584017/13499267261006250000000000:ℝ), (5016568196149666471901124961/1499918584556250000000000:ℝ)] ]
theorem row020_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (118120535740942909247914997/251644580755144704000000000000:ℝ) row020_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row020_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row020_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row020_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row020_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
