/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_single_stage_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row003_coefficients : Fin 3 → Fin 4 → ℝ := ![![(5310750527608427417096551/1069179702803550281250000:ℝ), (13982392056133991237654993/1069179702803550281250000:ℝ), (12032532529442700224020333/1069179702803550281250000:ℝ), (1120297000305712134487297/356393234267850093750000:ℝ)],
![(826027469526402009230477/267294925700887570312500:ℝ), (7781794751847674769016807/1069179702803550281250000:ℝ), (597745035308791256699189/106917970280355028125000:ℝ), (499921826448615278298997/356393234267850093750000:ℝ)],
![(2270078161711381744825357/1069179702803550281250000:ℝ), (1663080484199339903119207/534589851401775140625000:ℝ), (1199037118131522686413057/1069179702803550281250000:ℝ), (0:ℝ)]]
theorem row003_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (880784211799834564711409/60824445315046416000000000:ℝ) row003_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row003_coefficients,Fin.sum_univ_succ] <;> ring
theorem row003_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row003_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row003_coefficients]
def row004_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1207984360553721864909541/427671881121420112500000:ℝ), (11151618374834897117167801/2138359405607100562500000:ℝ), (6897370674300582877517087/2138359405607100562500000:ℝ), (499921826448615278298997/712786468535700187500000:ℝ)],
![(7275968248085764777276511/1069179702803550281250000:ℝ), (5011072779892290980313911/534589851401775140625000:ℝ), (3317994557475715683351311/1069179702803550281250000:ℝ), (0:ℝ)],
![(17065452315831322480005317/2138359405607100562500000:ℝ), (27946189290104259353841043/2138359405607100562500000:ℝ), (2849371405924693835213707/427671881121420112500000:ℝ), (740828521265578434077603/712786468535700187500000:ℝ)]]
theorem row004_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (261802944253823294525827/121648890630092832000000000:ℝ) row004_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldSwitch,edgeC_oldSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row004_coefficients,Fin.sum_univ_succ] <;> ring
theorem row004_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row004_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row004_coefficients]
end
end QRH.RepeatedMarks.Return
