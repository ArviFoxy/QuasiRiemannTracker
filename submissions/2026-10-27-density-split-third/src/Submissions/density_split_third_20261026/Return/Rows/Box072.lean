/- Fourth density transition: exact return rectangle 072.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row072_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(192868464778852272389831/13463316000000000:ℝ), (19846611932563477490503/747962000000000:ℝ), (32876967929371536415583/2692663200000000:ℝ)],
![(110263720924549873541231/6731658000000000:ℝ), (1280383920164318309657/44877720000000:ℝ), (81808375102403051856197/6731658000000000:ℝ)],
![(28424202823598776441691/13463316000000000:ℝ), (1578304120057381684673/747962000000000:ℝ), (0:ℝ)] ]
theorem row072_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (8086915689960178607043529/14456125478928384000000000:ℝ) row072_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row072_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row072_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row072_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_oldSmall_coefficients]
def row072_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(6235062157129723445567/5048743500000000:ℝ), (5795328722452783275959/2524371750000000:ℝ), (1071883768067606289559/1009748700000000:ℝ)],
![(3518498951659584194087/2524371750000000:ℝ), (614837866240326197359/252437175000000:ℝ), (2633772394614913429549/2524371750000000:ℝ)],
![(894247357946175047027/5048743500000000:ℝ), (445142209172799279569/2524371750000000:ℝ), (0:ℝ)] ]
theorem row072_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (170590158189498253754833/5421047054598144000000000:ℝ) row072_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row072_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row072_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row072_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_oldSwitch_coefficients]
def row072_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(605300871557841/500000000:ℝ), (5068796513194913/2250000000:ℝ), (938635645170113/900000000:ℝ)],
![(1022868712185403/750000000:ℝ), (537134582924713/225000000:ℝ), (2306092598902043/2250000000:ℝ)],
![(256965609546263/1500000000:ℝ), (383741537948183/2250000000:ℝ), (0:ℝ)] ]
theorem row072_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (52422064221834077/1610612736000000000:ℝ) row072_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row072_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row072_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row072_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_newSwitch_coefficients]
def row072_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(18065514534404005978725866117/42780600000000000000000:ℝ), (16966053944340792001572726829/21390300000000000000000:ℝ), (1059806915715629621269917679/2852040000000000000000:ℝ)],
![(9867982242957664089175823357/21390300000000000000000:ℝ), (1745054922912797068861930133/2139030000000000000000:ℝ), (2537879922531728557892678773/7130100000000000000000:ℝ)],
![(2344842927415262811916902017/42780600000000000000000:ℝ), (1156599130603062971330935339/21390300000000000000000:ℝ), (0:ℝ)] ]
theorem row072_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (35792105285580378865788357163/45935319475814400000000000000000:ℝ) row072_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row072_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row072_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row072_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row072_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
