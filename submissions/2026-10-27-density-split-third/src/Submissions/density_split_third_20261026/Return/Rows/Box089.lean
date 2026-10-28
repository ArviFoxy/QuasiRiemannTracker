/- Fourth density transition: exact return rectangle 089.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row089_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(22319003620472080045305922/119483488728713671875:ℝ), (65620044809910968883427526/119483488728713671875:ℝ), (64283078758405697630937286/119483488728713671875:ℝ), (259037500851442083861922/1475104799119921875:ℝ)],
![(20562594231298009748932868/119483488728713671875:ℝ), (59220036013428149280614668/119483488728713671875:ℝ), (56762562083306679084746732/119483488728713671875:ℝ), (223520003718228883371172/1475104799119921875:ℝ)],
![(1081056812691875268709546/119483488728713671875:ℝ), (2153654299218043680083942/119483488728713671875:ℝ), (1072615610770363459811896/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row089_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4470965007295754896482293/8249383945823846400000000:ℝ) row089_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row089_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row089_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row089_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row089_oldSmall_coefficients]
def row089_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2876180562708510679815922/119483488728713671875:ℝ), (8506349252402739327757526/119483488728713671875:ℝ), (8384156816679946616067286/119483488728713671875:ℝ), (101999560258730295115766/4425314397359765625:ℝ)],
![(1961947756999895243872868/119483488728713671875:ℝ), (5732676986436291354554668/119483488728713671875:ℝ), (5580497765280755247806732/119483488728713671875:ℝ), (67028464290531819893516/4425314397359765625:ℝ)],
![(79044823765990710139546/119483488728713671875:ℝ), (156007700182438256693942/119483488728713671875:ℝ), (76979067465916032491896/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row089_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (269237236572076399797293/8249383945823846400000000:ℝ) row089_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row089_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row089_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row089_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row089_oldSwitch_coefficients]
def row089_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(7590566241804226162/319490799609375:ℝ), (22444964384034927446/319490799609375:ℝ), (22118230042657176406/319490799609375:ℝ), (29892312347434054/1314776953125:ℝ)],
![(5166421169895939428/319490799609375:ℝ), (15095040531981277228/319490799609375:ℝ), (14693222549410972172/319490799609375:ℝ), (19607420523973804/1314776953125:ℝ)],
![(208077475913507866/319490799609375:ℝ), (410814043318262582/319490799609375:ℝ), (202778696390692216/319490799609375:ℝ), (0:ℝ)] ]
theorem row089_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (736613370048559853/22058296934400000000:ℝ) row089_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row089_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row089_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row089_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row089_newSwitch_coefficients]
def row089_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(169590938874852571361845790029/12149340534905625000000000:ℝ), (503783814167444579141507469287/12149340534905625000000000:ℝ), (498794811710331444197477568487/12149340534905625000000000:ℝ), (2032122671823943659479208509/149991858455625000000000:ℝ)],
![(41285872028690108912355770797/6074670267452812500000000:ℝ), (123257005215234974699840128679/6074670267452812500000000:ℝ), (122673649904488563089525889631/6074670267452812500000000:ℝ), (502500206394366633358537429/74995929227812500000000:ℝ)],
![(8888411927982979165060455029/60746702674528125000000000:ℝ), (16957016184273861325304181427/60746702674528125000000000:ℝ), (2019138178039589166736611287/15186675668632031250000000:ℝ), (0:ℝ)] ]
theorem row089_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4599011921031360023668691857/1677630538367631360000000000000:ℝ) row089_newTop_coefficients (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row089_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row089_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row089_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row089_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
