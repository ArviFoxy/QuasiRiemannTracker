/- Fourth density transition: exact return rectangle 090.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row090_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2988984863848843410197107/119483488728713671875:ℝ), (8632713078670212417468761/119483488728713671875:ℝ), (8298471565793894604346201/119483488728713671875:ℝ), (294971483441391733008283/13275943192079296875:ℝ)],
![(2922133121027957278143206/119483488728713671875:ℝ), (8139189942622992072567634/119483488728713671875:ℝ), (300684675893372687834546/4779339549148546875:ℝ), (255562230637698044604358/13275943192079296875:ℝ)],
![(276635884163541532834999/119483488728713671875:ℝ), (548996794633742015908673/119483488728713671875:ℝ), (272379034714395531511174/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row090_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3488355857058300580950413/6187037959367884800000000:ℝ) row090_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row090_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row090_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row090_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_oldSmall_coefficients]
def row090_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(380190076298513174132107/119483488728713671875:ℝ), (1110022119964841344473761/119483488728713671875:ℝ), (1079474011034143166551201/119483488728713671875:ℝ), (116547322455938332069849/39827829576237890625:ℝ)],
![(264267366528266957373206/119483488728713671875:ℝ), (753523465036094007537634/119483488728713671875:ℝ), (28589534487652651124546/4779339549148546875:ℝ), (75160754561163075983074/39827829576237890625:ℝ)],
![(21346953027857779129999/119483488728713671875:ℝ), (41612454757272761623673/119483488728713671875:ℝ), (20281692778883468431174/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row090_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (211808530399806138615413/6187037959367884800000000:ℝ) row090_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row090_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row090_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row090_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_oldSwitch_coefficients]
def row090_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1004494681080777547/319490799609375:ℝ), (2931800457897894881/319490799609375:ℝ), (2850116872553457121/319490799609375:ℝ), (102534566192926643/35498977734375:ℝ)],
![(696041519253368726/319490799609375:ℝ), (1984663818197234914/319490799609375:ℝ), (75296223048099266/12779631984375:ℝ), (65975919695401718/35498977734375:ℝ)],
![(56088243838848079/319490799609375:ℝ), (109400710958475833/319490799609375:ℝ), (53354596105565254/319490799609375:ℝ), (0:ℝ)] ]
theorem row090_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (578469712025608373/16543722700800000000:ℝ) row090_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row090_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row090_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row090_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_newSwitch_coefficients]
def row090_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(222239076754352806771116875779/121493405349056250000000000:ℝ), (654244724120275582953275875337/121493405349056250000000000:ℝ), (641772217977492745593201123337/121493405349056250000000000:ℝ), (7769132244872961830038597177/4499755753668750000000000:ℝ)],
![(50973042031399973576812282339/60746702674528125000000000:ℝ), (151245043316222136368239441097/60746702674528125000000000:ℝ), (149657238338689054140606758497/60746702674528125000000000:ℝ), (1829082853846921901821466657/2249877876834375000000000:ℝ)],
![(5697762839132058609863476711/121493405349056250000000000:ℝ), (10535975727234647681396631041/121493405349056250000000000:ℝ), (485410979983753808493859183/12149340534905625000000000:ℝ), (0:ℝ)] ]
theorem row090_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19468397685863344880022708221/6291114518878617600000000000000:ℝ) row090_newTop_coefficients (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row090_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row090_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row090_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row090_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
