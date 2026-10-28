/- Fourth density transition: exact return rectangle 086.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row086_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(10706644435324355502474790132/119483488728713671875:ℝ), (32034367478676729147264995036/119483488728713671875:ℝ), (31948801651380391787105619676/119483488728713671875:ℝ), (1180119845336446460257268308/13275943192079296875:ℝ)],
![(9287527220849934184627135976/119483488728713671875:ℝ), (27706946971077134024596420024/119483488728713671875:ℝ), (5510278892321444154694792024/23896697745742734375:ℝ), (1014663856820002325944964008/13275943192079296875:ℝ)],
![(67773700789875089491668244/119483488728713671875:ℝ), (135480361318971350819967788/119483488728713671875:ℝ), (67706678653340456376737044/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row086_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3314392084655296370121047747/6335526870392714035200000000:ℝ) row086_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row086_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row086_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row086_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row086_oldSmall_coefficients]
def row086_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1396808771875595644473850132/119483488728713671875:ℝ), (4182605999740528199873375036/119483488728713671875:ℝ), (4174785683854269466325199676/119483488728713671875:ℝ), (462996151996445636975224924/39827829576237890625:ℝ)],
![(936205468391587663034215976/119483488728713671875:ℝ), (2799034865166066001521340024/119483488728713671875:ℝ), (557892244332926376020512024/23896697745742734375:ℝ), (308877274963384513871812024/39827829576237890625:ℝ)],
![(4715561795038079855688244/119483488728713671875:ℝ), (9415034698011211410507788/119483488728713671875:ℝ), (4699489094022600040757044/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row086_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (198352011143239563523682747/6335526870392714035200000000:ℝ) row086_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row086_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row086_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row086_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row086_oldSwitch_coefficients]
def row086_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3682414645144049303572/319490799609375:ℝ), (11026332937583971844156/319490799609375:ℝ), (11005421939735795777596/319490799609375:ℝ), (406833738588430359668/35498977734375:ℝ)],
![(2464392281764779129896/319490799609375:ℝ), (7367845293631635626104/319490799609375:ℝ), (1468506596386004750104/63898159921875:ℝ), (271008885562574139368/35498977734375:ℝ)],
![(12436495294383036724/319490799609375:ℝ), (24831737835203860748/319490799609375:ℝ), (12395284669806761524/319490799609375:ℝ), (0:ℝ)] ]
theorem row086_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (543519393393606356987/16940772045619200000000:ℝ) row086_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row086_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row086_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row086_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row086_newSwitch_coefficients]
def row086_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(207553980714631011833514540362221/30373351337264062500000000:ℝ), (621863701750754933909498836958663/30373351337264062500000000:ℝ), (621065461357616832318454052830663/30373351337264062500000000:ℝ), (7657620011907144823795176156823/1124938938417187500000000:ℝ)],
![(53221134100353940082904145105261/15186675668632031250000000:ℝ), (159576967675377970561827334933703/15186675668632031250000000:ℝ), (159490878160895899683480493444903/15186675668632031250000000:ℝ), (1967964614291550711279900133943/562469469208593750000000:ℝ)],
![(217151054218880348964521746549/30373351337264062500000000:ℝ), (431161975728673113777074156699/30373351337264062500000000:ℝ), (8560595829509060082636150781/1214934053490562500000000:ℝ), (0:ℝ)] ]
theorem row086_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16007261318007279725908869813779/6442101267331704422400000000000000:ℝ) row086_newTop_coefficients (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row086_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row086_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row086_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row086_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
