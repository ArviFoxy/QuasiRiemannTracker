/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_followup.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row001_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9038920850453965878449/493660460795062500000:ℝ), (216712412452459827535193/4442944147155562500000:ℝ), (189373961942662576352263/4442944147155562500000:ℝ), (54011837144288441723111/4442944147155562500000:ℝ)],
![(1079369007187156752539/61707557599382812500:ℝ), (174162836732527825693927/4442944147155562500000:ℝ), (179821023193132811947/6439049488631250000:ℝ), (27628237788209100732311/4442944147155562500000:ℝ)],
![(1570673050223538141863/493660460795062500000:ℝ), (11230164859495147430467/2221472073577781250000:ℝ), (8985115878062701584167/4442944147155562500000:ℝ), (0:ℝ)]]
theorem row001_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (606615361311084910171/7020948775752000000000:ℝ) row001_coefficients (0:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_oldSmall,edgeC_oldSmall,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row001_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_coefficients]
end
end QRH.RepeatedMarks.Return
