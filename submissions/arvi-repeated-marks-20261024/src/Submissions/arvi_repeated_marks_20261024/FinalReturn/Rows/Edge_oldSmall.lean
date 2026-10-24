/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3904936291375747695570157/213265530527100187500000:ℝ), (10402516928785291644004361/213265530527100187500000:ℝ), (9090224983443340201298251/213265530527100187500000:ℝ), (864214782011265417621349/71088510175700062500000:ℝ)],
![(932609611995796561692329/53316382631775046875000:ℝ), (8360162215660551360549229/213265530527100187500000:ℝ), (595594428063665128510901/21326553052710018750000:ℝ), (442073504319762057109699/71088510175700062500000:ℝ)],
![(678564278715839301199159/213265530527100187500000:ℝ), (67385610262450863168323/13329095657943761718750:ℝ), (33178729646582635345693/16405040809776937500000:ℝ), (0:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (262101807875741160666503/3033109767496536000000000:ℝ) row001_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end QRH.RepeatedMarks.Return
