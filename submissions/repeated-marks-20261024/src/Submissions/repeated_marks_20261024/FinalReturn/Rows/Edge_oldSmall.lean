/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(39004127345316116402167/2132884097452687500000:ℝ), (103910350216460966546591/2132884097452687500000:ℝ), (90808318396973583886681/2132884097452687500000:ℝ), (8634031841942911247419/710961365817562500000:ℝ)],
![(2326903799111344407281/133305256090792968750:ℝ), (83433926987262665525749/2132884097452687500000:ℝ), (5944072242349135188701/213288409745268750000:ℝ), (4412418740670065625919/710961365817562500000:ℝ)],
![(6757869830276144114329/2132884097452687500000:ℝ), (5365742169130619173579/1066442048726343750000:ℝ), (4290659044714844232829/2132884097452687500000:ℝ), (0:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2600977805722999557293/30334351608216000000000:ℝ) row001_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end QRH.RepeatedMarks.Return
