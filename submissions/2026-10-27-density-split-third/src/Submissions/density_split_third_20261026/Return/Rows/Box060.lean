/- Fourth density transition: exact return rectangle 060.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row060_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(98280138896820082265793088/13275943192079296875:ℝ), (279355952504286300295560896/13275943192079296875:ℝ), (263954757866076290759163328/13275943192079296875:ℝ), (5525254358339719788626368/885062879471953125:ℝ)],
![(110228675361730688656575872/13275943192079296875:ℝ), (300589230077032485805454464/13275943192079296875:ℝ), (270666093551332550786290112/13275943192079296875:ℝ), (5353683256541575524160768/885062879471953125:ℝ)],
![(14505796258501956826116784/13275943192079296875:ℝ), (28921776739076426021784368/13275943192079296875:ℝ), (14416143598772224631605084/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row060_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1803915307705564076148283/4949630367494307840000000:ℝ) row060_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row060_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row060_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row060_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_oldSmall_coefficients]
def row060_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(6870453545726233561833088/13275943192079296875:ℝ), (19279647065291166666240896/13275943192079296875:ℝ), (5991191102357734137467776/4425314397359765625:ℝ), (1112852930231298681599104/2655188638415859375:ℝ)],
![(7446033446562938680335872/13275943192079296875:ℝ), (19582000642638615112574464/13275943192079296875:ℝ), (16882274441801135129250112/13275943192079296875:ℝ), (949209637786792584402304/2655188638415859375:ℝ)],
![(1414886204073468523836784/13275943192079296875:ℝ), (2798948333528391592224368/13275943192079296875:ℝ), (1384207848900139441825084/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row060_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (45118942770916132330079/2474815183747153920000000:ℝ) row060_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row060_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row060_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row060_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_oldSwitch_coefficients]
def row060_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(18037737838127122048/35498977734375:ℝ), (50604695231905721216/35498977734375:ℝ), (47162387107692393088/35498977734375:ℝ), (973008675334252928/2366598515625:ℝ)],
![(19550405212653850112/35498977734375:ℝ), (51386505013711865344/35498977734375:ℝ), (44267560585370745152/35498977734375:ℝ), (828719114702515328/2366598515625:ℝ)],
![(3734204008394142064/35498977734375:ℝ), (7388597438815330928/35498977734375:ℝ), (3654772591294626364/35498977734375:ℝ), (0:ℝ)] ]
theorem row060_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (127274596482071759/6617489080320000000:ℝ) row060_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row060_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row060_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row060_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_newSwitch_coefficients]
def row060_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(16361998051535048496088451/189063514125000000000:ℝ), (1092244691730633841795364449/4726587853125000000000:ℝ), (963632848104089881061982689/4726587853125000000000:ℝ), (6230283211660409317977367/105035285625000000000:ℝ)],
![(38833580936540838992903503/472658785312500000000:ℝ), (428918012225833153050680257/2363293926562500000000:ℝ), (282599201524884829899054257/2363293926562500000000:ℝ), (1061429121166729120179167/52517642812500000000:ℝ)],
![(34553188948532596119562567/945317570625000000000:ℝ), (337241747169365935859955661/4726587853125000000000:ℝ), (164571183897112649342575451/4726587853125000000000:ℝ), (0:ℝ)] ]
theorem row060_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (37278547718558000933106289/112780779171348480000000000000:ℝ) row060_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row060_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row060_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row060_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row060_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
