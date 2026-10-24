/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row005_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42465114790528609773021767/8553536291995426265625000:ℝ), (111804231688197256467000331/8553536291995426265625000:ℝ), (96213119004808683614935361/8553536291995426265625000:ℝ), (8958000702380012306985599/2851178763998475421875000:ℝ)],
![(26405110406144360419185061/8553536291995426265625000:ℝ), (124381766446823799250395013/17107072583990852531250000:ℝ), (2388671875431251892556979/427676814599771313281250:ℝ), (7991776460904999096751423/5702357527996950843750000:ℝ)],
![(9077070391798727854331647/4276768145997713132812500:ℝ), (53196266232917510413333901/17107072583990852531250000:ℝ), (2739287973881756517286759/2443867511998693218750000:ℝ), (0:ℝ)]]
theorem row005_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7042741134376892739368053/486601175722406472000000000:ℝ) row005_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row005_coefficients,Fin.sum_univ_succ] <;> ring
theorem row005_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row005_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row005_coefficients]
def row006_coefficients : Fin 3 → Fin 4 → ℝ := ![![(19318378503420964024981489/6842829033596341012500000:ℝ), (178318520613980012697430609/34214145167981705062500000:ℝ), (110276019782489583112777433/34214145167981705062500000:ℝ), (7991776460904999096751423/11404715055993901687500000:ℝ)],
![(116398234839205922121190499/17107072583990852531250000:ℝ), (11452091902356516733835957/1221933755999346609375000:ℝ), (53079176399584098652512899/17107072583990852531250000:ℝ), (0:ℝ)],
![(273061157833233844367473553/34214145167981705062500000:ℝ), (447185978976978904043855287/34214145167981705062500000:ℝ), (45598218127151557697889223/6842829033596341012500000:ℝ), (1693810489543578848241161/1629245007999128812500000:ℝ)]]
theorem row006_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4195635154792573667217943/1946404702889625888000000000:ℝ) row006_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row006_coefficients,Fin.sum_univ_succ] <;> ring
theorem row006_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row006_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row006_coefficients]
end
end QRH.RepeatedMarks.Return
