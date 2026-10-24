/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(89773387163464150495481/20985265013366531250000:ℝ), (238117583129297998526983/20985265013366531250000:ℝ), (206915004768203545567523/20985265013366531250000:ℝ), (2169289214902581390223/777232037532093750000:ℝ)],
![(5612024788754056915931/2623158126670816406250:ℝ), (107145536631003087301667/20985265013366531250000:ℝ), (8523488572721671577599/2098526501336653125000:ℝ), (851316570601706807473/777232037532093750000:ℝ)],
![(39063871200034429831967/20985265013366531250000:ℝ), (6826466128714486720523/2623158126670816406250:ℝ), (18384200009776088932217/20985265013366531250000:ℝ), (0:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (9309455221791487261279/1193828409649296000000000:ℝ) row007_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(109261226579235892351219/10492632506683265625000:ℝ), (202623910596932885590223/10492632506683265625000:ℝ), (103816497006605685026539/10492632506683265625000:ℝ), (22310226910768837747/25907734584403125000:ℝ)],
![(175724314759308701024191/5246316253341632812500:ℝ), (152198232147735399413191/2623158126670816406250:ℝ), (131508491716256722802191/5246316253341632812500:ℝ), (0:ℝ)],
![(577951643153246009697163/10492632506683265625000:ℝ), (1280982929370827072041541/10492632506683265625000:ℝ), (922255536693090664280593/10492632506683265625000:ℝ), (527287817568692227003/25907734584403125000:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (16846415821613555204353/955062727719436800000000:ℝ) row008_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(15803089505201858013191/524631625334163281250:ℝ), (160336771268006323033931/2623158126670816406250:ℝ), (105725042238290429269747/2623158126670816406250:ℝ), (851316570601706807473/97154004691511718750:ℝ)],
![(238392405045051521351/4197053002673306250:ℝ), (955070785732773330268/10492632506683265625:ℝ), (752215652401424553781/20985265013366531250:ℝ), (0:ℝ)],
![(50250643052277337433743/1049263250668326562500:ℝ), (443095949239327760886013/5246316253341632812500:ℝ), (55855982965727259958064/1311579063335408203125:ℝ), (466656073699167775277/97154004691511718750:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2850454696183973048669/955062727719436800000000:ℝ) row009_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(226053787281631627303757/5246316253341632812500:ℝ), (367497665300062581291139/5246316253341632812500:ℝ), (73912823961821930118691/2623158126670816406250:ℝ), (0:ℝ)],
![(328311749389861113628097/2623158126670816406250:ℝ), (285912959053098504805076/1311579063335408203125:ℝ), (277222623236374830847013/2623158126670816406250:ℝ), (466656073699167775277/48577002345755859375:ℝ)],
![(135465828876295366391078/1311579063335408203125:ℝ), (53119413491064258987452/262315812667081640625:ℝ), (163359925447059890345786/1311579063335408203125:ℝ), (1125642395849605066652/48577002345755859375:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1678249216924837198489/298457102412324000000000:ℝ) row010_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
end
end QRH.RepeatedMarks.Return
