/- Fourth density transition: exact return rectangle 018.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row018_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(17232440959145028422799104/2655188638415859375:ℝ), (48962658814320572468490112/2655188638415859375:ℝ), (46247167984715183456732912/2655188638415859375:ℝ), (4838969951147142730763968/885062879471953125:ℝ)],
![(96221846333906210094316736/13275943192079296875:ℝ), (262257909876986571946796992/13275943192079296875:ℝ), (236047489320395662253205776/13275943192079296875:ℝ), (4667398849348998466298368/885062879471953125:ℝ)],
![(12616901331772418415655216/13275943192079296875:ℝ), (25133114971713950116237232/13275943192079296875:ℝ), (12516457310335709574019516/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row018_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1334177083991943420345511/4949630367494307840000000:ℝ) row018_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row018_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row018_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row018_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_oldSmall_coefficients]
def row018_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(771432399574406839319104/2655188638415859375:ℝ), (1993826140212182902050112/2655188638415859375:ℝ), (1680709481200980324292912/2655188638415859375:ℝ), (458279760453274292811904/2655188638415859375:ℝ)],
![(4776675563801593571196736/13275943192079296875:ℝ), (10947346938901883384156992/13275943192079296875:ℝ), (7644249496353360447285776/13275943192079296875:ℝ), (294636468008768195615104/2655188638415859375:ℝ)],
![(1758819869166322779935216/13275943192079296875:ℝ), (3474810994021912019797232/13275943192079296875:ℝ), (63563289056320946325908/491701599706640625:ℝ), (0:ℝ)] ]
theorem row018_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (35401395069388313736193/2474815183747153920000000:ℝ) row018_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row018_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row018_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row018_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_oldSwitch_coefficients]
def row018_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2015588649913438784/7099795546875:ℝ), (5199734873851385152/7099795546875:ℝ), (4371791142328603952/7099795546875:ℝ), (395850432807302528/2366598515625:ℝ)],
![(12516962571003649856/35498977734375:ℝ), (28601613916451021632/35498977734375:ℝ), (19859094247737095696/35498977734375:ℝ), (251560872175564928/2366598515625:ℝ)],
![(4660555955303869936/35498977734375:ℝ), (9209727204203282672/35498977734375:ℝ), (4549737649710350236/35498977734375:ℝ), (0:ℝ)] ]
theorem row018_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (101955534289616753/6617489080320000000:ℝ) row018_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row018_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row018_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row018_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_newSwitch_coefficients]
def row018_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2341366088135041772586611/47265878531250000000:ℝ), (4576231233606434400022717/47265878531250000000:ℝ), (2236042694488796258058731/47265878531250000000:ℝ), (0:ℝ)],
![(812429471078187531925891/4726587853125000000:ℝ), (9375972727525096943655067/23632939265625000000:ℝ), (8357273509656753948198049/29541174082031250000:ℝ), (1522997924080110978719933/26258821406250000000:ℝ)],
![(38588647446515707886910949/236329392656250000000:ℝ), (124326364787044338767668831/295411740820312500000:ℝ), (838282560523816938256132183/2363293926562500000000:ℝ), (2039883333129478998499753/21007057125000000000:ℝ)] ]
theorem row018_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (2756982413074971823422629/5639038958567424000000000000:ℝ) row018_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row018_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row018_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row018_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row018_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
