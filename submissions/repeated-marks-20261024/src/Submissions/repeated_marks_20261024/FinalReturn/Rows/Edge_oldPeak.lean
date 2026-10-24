/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row002_coefficients : Fin 3 → Fin 4 → ℝ := ![![(186639459524912007793489/23696170058566687500000:ℝ), (4454325669871806361516973/213265530527100187500000:ℝ), (3869385932570988512609743/213265530527100187500000:ℝ), (1094815398423390221234171/213265530527100187500000:ℝ)],
![(35701442872261336261883/5924042514641671875000:ℝ), (2825751105546190598541397/213265530527100187500000:ℝ), (64989517703313743503931/7108851017570006250000:ℝ), (409186368954629812004321/213265530527100187500000:ℝ)],
![(50950992198400087254043/23696170058566687500000:ℝ), (90790261686267207358453/26658191315887523437500:ℝ), (22288187923210509506249/16405040809776937500000:ℝ), (0:ℝ)]]
theorem row002_identity (δ p : ℝ) : rowMargin .oldPeak .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19739597763248624811331/337012196388504000000000:ℝ) row002_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldPeak,edgeC_oldPeak,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row002_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldPeak .old δ p := by
 rw [row002_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_coefficients]
end
end QRH.RepeatedMarks.Return
