/- Fourth density transition: exact return rectangle 049.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row049_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(36595199851661833429857749/238966977457427343750:ℝ), (69135463995632272246009471/238966977457427343750:ℝ), (6724604952352009445840719/47793395491485468750:ℝ), (98251543929493102839097/26551886384158593750:ℝ)],
![(36069850889722136038110677/119483488728713671875:ℝ), (67615388964370650216408703/119483488728713671875:ℝ), (257498071299207780168781/955867909829709375:ℝ), (48949080798602298505511/13275943192079296875:ℝ)],
![(7109353537750777369272721/47793395491485468750:ℝ), (13220646898295459441566067/47793395491485468750:ℝ), (3076036454991770528334173/23896697745742734375:ℝ), (0:ℝ)] ]
theorem row049_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (10842405812493405589815407/26398028626636308480000000:ℝ) row049_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row049_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row049_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row049_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_oldSmall_coefficients]
def row049_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5667503087379278557527749/238966977457427343750:ℝ), (9324425871807248283439471/238966977457427343750:ℝ), (773072087149482126710719/47793395491485468750:ℝ), (10371092513527640047291/79655659152475781250:ℝ)],
![(5699780256021234808020677/119483488728713671875:ℝ), (9349145862463732065648703/119483488728713671875:ℝ), (30752059092918746028781/955867909829709375:ℝ), (4973710357384029906533/39827829576237890625:ℝ)],
![(1146864637126927851702721/47793395491485468750:ℝ), (1875880451209371265801067/47793395491485468750:ℝ), (382722837693268386736673/23896697745742734375:ℝ), (0:ℝ)] ]
theorem row049_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (648334468934683085625407/26398028626636308480000000:ℝ) row049_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row049_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row049_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row049_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_oldSwitch_coefficients]
def row049_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(14831024419249885829/638981599218750:ℝ), (24447440340538223791/638981599218750:ℝ), (2031682565083539199/127796319843750:ℝ), (8955583349095337/70997955468750:ℝ)],
![(14917331393780560517/319490799609375:ℝ), (24516129578406318463/319490799609375:ℝ), (80840338895280301/2555926396875:ℝ), (4290270375336631/35498977734375:ℝ)],
![(3001939372102247041/127796319843750:ℝ), (4919920839747489707/127796319843750:ℝ), (1006385843002308833/63898159921875:ℝ), (0:ℝ)] ]
theorem row049_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1798302100222846847/70586550190080000000:ℝ) row049_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row049_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row049_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row049_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_newSwitch_coefficients]
def row049_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(941707532220674635123309442189/60746702674528125000000000:ℝ), (284906881083041324976022530659/12149340534905625000000000:ℝ), (263176308762411194230445543053/30373351337264062500000000:ℝ), (0:ℝ)],
![(958445821597672382419171816589/30373351337264062500000000:ℝ), (1454707195760458171688415229507/30373351337264062500000000:ℝ), (1085854989207172621251154338859/60746702674528125000000000:ℝ), (189051138986445122684792149/2249877876834375000000000:ℝ)],
![(975760079711139729715034190989/60746702674528125000000000:ℝ), (1486249097662523192640843684217/60746702674528125000000000:ℝ), (2242380432903974889822028101743/242986810698112500000000000:ℝ), (799411262232023603985861253/8999511507337500000000000:ℝ)] ]
theorem row049_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (69781221584332635659458481011/33552610767352627200000000000000:ℝ) row049_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row049_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row049_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row049_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row049_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
