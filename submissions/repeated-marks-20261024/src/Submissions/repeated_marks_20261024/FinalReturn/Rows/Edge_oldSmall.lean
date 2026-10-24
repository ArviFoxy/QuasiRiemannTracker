/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(433736715562227333699557/23697788915062687500000:ℝ), (3466406412483999620835683/71093366745188062500000:ℝ), (3029182384907953238375353/71093366745188062500000:ℝ), (863986119110635618638341/71093366745188062500000:ℝ)],
![(103561218135504707605729/5924447228765671875000:ℝ), (2785047714541888723922287/71093366745188062500000:ℝ), (7348685855196776058629/263308765722918750000:ℝ), (441832083987297303176291/71093366745188062500000:ℝ)],
![(75299312640042246723359/23697788915062687500000:ℝ), (22429540710351639027269/4443335421574253906250:ℝ), (143544504660248734266227/71093366745188062500000:ℝ), (0:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (29056258802008831221103/337035220125336000000000:ℝ) row001_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end QRH.RepeatedMarks.Return
