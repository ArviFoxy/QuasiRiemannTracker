/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(43112565571689074924377303/8553877637527558265625000:ℝ), (113477995738270634902845179/8553877637527558265625000:ℝ), (97618294761474045032558449/8553877637527558265625000:ℝ), (9084288198297495018030191/2851292545842519421875000:ℝ)],
![(27228330141605038285496549/8553877637527558265625000:ℝ), (128203087480716648847905317/17107755275055116531250000:ℝ), (2458572604558071799698571/427693881876377913281250:ℝ), (8198825661605433237010207/5702585091685038843750000:ℝ)],
![(9165637560013098211809623/4276938818763779132812500:ℝ), (53863447191490037702815309/17107755275055116531250000:ℝ), (19487674859384989480576817/17107755275055116531250000:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7248972619181310497343077/486620594490456648000000000:ℝ) row005_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19584315492984217081101521/6843102110022046612500000:ℝ), (181516325337428974538722481/34215510550110233062500000:ℝ), (112764780673218878094245497/34215510550110233062500000:ℝ), (8198825661605433237010207/11405170183370077687500000:ℝ)],
![(116790017661815794528991491/17107755275055116531250000:ℝ), (80520066119846200548223891/8553877637527558265625000:ℝ), (53397226209665985067456291/17107755275055116531250000:ℝ), (0:ℝ)],
![(272520500059151435902475377/34215510550110233062500000:ℝ), (445796641516585144975373783/34215510550110233062500000:ℝ), (45358478429226701431233767/6843102110022046612500000:ℝ), (11740675808373680361090143/11405170183370077687500000:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4399413491908942278341687/1946482377961826592000000000:ℝ) row006_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end QRH.RepeatedMarks.Return
