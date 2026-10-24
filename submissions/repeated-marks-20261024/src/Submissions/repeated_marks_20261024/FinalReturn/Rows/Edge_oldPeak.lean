/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(1682627767787898905345201/213280100235564187500000:ℝ), (1487395556618867203778791/71093366745188062500000:ℝ), (430721115149945167404127/23697788915062687500000:ℝ), (1096931134280803800645971/213280100235564187500000:ℝ)],
![(321902756930138255059447/53320025058891046875000:ℝ), (943703117555649564946199/71093366745188062500000:ℝ), (195367279324135009433833/21328010023556418750000:ℝ), (410174468294954419737521/213280100235564187500000:ℝ)],
![(458103660874910864892587/213280100235564187500000:ℝ), (30226325039015995086401/8886670843148507812500:ℝ), (289321726830720767181037/213280100235564187500000:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (177217094343267922850179/3033316981128024000000000:ℝ) row002_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end QRH.RepeatedMarks.Return
