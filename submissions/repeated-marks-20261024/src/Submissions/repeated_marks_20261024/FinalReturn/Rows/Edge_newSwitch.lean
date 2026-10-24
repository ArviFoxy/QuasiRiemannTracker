/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.repeated_marks_20261024.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def row007_coefficients : Fin 3 → Fin 4 → ℝ := ![![(13794825272437949474689/3228576773913703125000:ℝ), (36590237587349251312577/3228576773913703125000:ℝ), (31795999357384654201087/3228576773913703125000:ℝ), (111118358549053732879/39858972517453125000:ℝ)],
![(6885214002559849549037/3228576773913703125000:ℝ), (32867739413041172282921/6457153547827406250000:ℝ), (326916653666188509989/80714419347842578125:ℝ), (87111368955229723633/79717945034906250000:ℝ)],
![(1501173956444178143587/807144193478425781250:ℝ), (16785887821262630232517/6457153547827406250000:ℝ), (5649035793439330083821/6457153547827406250000:ℝ), (0:ℝ)]]
theorem row007_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1429276427510713194251/183670145360424000000000:ℝ) row007_coefficients (0:ℝ) (3/8:ℝ) (0:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row007_coefficients,Fin.sum_univ_succ] <;> ring
theorem row007_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row007_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row007_coefficients]
def row008_coefficients : Fin 3 → Fin 4 → ℝ := ![![(33555131489165705078347/3228576773913703125000:ℝ), (62180820200701824807899/3228576773913703125000:ℝ), (3975210129935109930704/403572096739212890625:ℝ), (2536780107481201126/2989422938808984375:ℝ)],
![(54051842085140007476983/1614288386956851562500:ℝ), (46814961162073683293983/807144193478425781250:ℝ), (40450619862737484110983/1614288386956851562500:ℝ), (0:ℝ)],
![(177863009446352809875619/3228576773913703125000:ℝ), (394247956761290579517533/3228576773913703125000:ℝ), (283870350640676442612709/3228576773913703125000:ℝ), (486965363542803133117/23915383510471875000:ℝ)]]
theorem row008_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (5183329307426740214089/293872232576678400000000:ℝ) row008_coefficients (3/8:ℝ) (3/4:ℝ) (0:ℝ) (1/4:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row008_coefficients,Fin.sum_univ_succ] <;> ring
theorem row008_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (1/4:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row008_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row008_coefficients]
def row009_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2427817851850130034679/80714419347842578125:ℝ), (24626011032131056621489/403572096739212890625:ℝ), (32466134242999483010461/807144193478425781250:ℝ), (87111368955229723633/9964743129363281250:ℝ)],
![(2156076918631666046/37983256163690625:ℝ), (587334161670315508193/6457153547827406250:ℝ), (231271560987693780373/6457153547827406250:ℝ), (0:ℝ)],
![(30926774120808906541943/645715354782740625000:ℝ), (272768480189575668409463/3228576773913703125000:ℝ), (34404391787278664047789/807144193478425781250:ℝ), (470725286153411946/97693560091796875:ℝ)]]
theorem row009_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (875638106942419587947/293872232576678400000000:ℝ) row009_coefficients (3/8:ℝ) (9/16:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row009_coefficients,Fin.sum_univ_succ] <;> ring
theorem row009_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (9/16:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row009_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row009_coefficients]
def row010_coefficients : Fin 3 → Fin 4 → ℝ := ![![(139077341347246574718307/3228576773913703125000:ℝ), (226098892419181794435239/3228576773913703125000:ℝ), (22736994844680195554233/807144193478425781250:ℝ), (0:ℝ)],
![(101038971454722650236511/807144193478425781250:ℝ), (88008458047794646449113/403572096739212890625:ℝ), (5021989890615058626907/47479070204613281250:ℝ), (941450572306823892/97693560091796875:ℝ)],
![(83389647766500536603653/807144193478425781250:ℝ), (1923759586984240424831/9495814040922656250:ℝ), (100598414202592225614811/807144193478425781250:ℝ), (231153306518173779109/9964743129363281250:ℝ)]]
theorem row010_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8267322848911587437587/1469361162883392000000000:ℝ) row010_coefficients (9/16:ℝ) (3/4:ℝ) (1/4:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,edgeD_newSwitch,edgeC_newSwitch,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,row010_coefficients,Fin.sum_univ_succ] <;> ring
theorem row010_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/16:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (1/4:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row010_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row010_coefficients]
end
end QRH.RepeatedMarks.Return
