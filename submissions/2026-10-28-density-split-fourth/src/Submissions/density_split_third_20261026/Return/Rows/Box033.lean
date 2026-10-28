/- Fourth density transition: exact return rectangle 033.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row033_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1078103492724479052825336232/13275943192079296875:ℝ), (2301894521881654661190397472/13275943192079296875:ℝ), (1381476249499411076243432098/13275943192079296875:ℝ), (5838492725054435849719754/491701599706640625:ℝ)],
![(398923066957291290637995904/2655188638415859375:ℝ), (4122598055839737879798101248/13275943192079296875:ℝ), (2285394808856166665021138336/13275943192079296875:ℝ), (5826653559343364782889504/491701599706640625:ℝ)],
![(916827116084406949871874688/13275943192079296875:ℝ), (1821653940968716647861358976/13275943192079296875:ℝ), (904873351832963297889484288/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row033_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (45982455687526409275019141/131990143133181542400000000:ℝ) row033_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row033_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row033_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row033_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_oldSmall_coefficients]
def row033_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(36185708069534904264298744/4425314397359765625:ℝ), (220409413407175748807157472/13275943192079296875:ℝ), (119552131081159768768022098/13275943192079296875:ℝ), (850980306473674653369262/1475104799119921875:ℝ)],
![(42002631033070483983915904/2655188638415859375:ℝ), (418805636149187237673941248/13275943192079296875:ℝ), (216428972002504558484018336/13275943192079296875:ℝ), (839323274484275161628512/1475104799119921875:ℝ)],
![(101566395137800441142914688/13275943192079296875:ℝ), (2453354848620373506215296/163900533235546875:ℝ), (97196911823440912760524288/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row033_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2349392136171748604174141/131990143133181542400000000:ℝ) row033_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row033_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row033_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row033_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_oldSwitch_coefficients]
def row033_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(286181676061585981672/35498977734375:ℝ), (581050346403997183712/35498977734375:ℝ), (314974014991014370258/35498977734375:ℝ), (246896459299132478/438258984375:ℝ)],
![(110773090942985075584/7099795546875:ℝ), (1104704423223307057408/35498977734375:ℝ), (570774766184652983456/35498977734375:ℝ), (243468162024645728/438258984375:ℝ)],
![(267976247825319595648/35498977734375:ℝ), (524516381029906752896/35498977734375:ℝ), (256648282992487157248/35498977734375:ℝ), (0:ℝ)] ]
theorem row033_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (6642027609787844861/352932750950400000000:ℝ) row033_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row033_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row033_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row033_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_newSwitch_coefficients]
def row033_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(14462643922508057432843150333/4726587853125000000000:ℝ), (27669401380319196766156614499/4726587853125000000000:ℝ), (13233606752956959515139936791/4726587853125000000000:ℝ), (0:ℝ)],
![(14724033430518495406575671021/2363293926562500000000:ℝ), (28308859160988048276838236583/2363293926562500000000:ℝ), (13738343991469345524266760647/2363293926562500000000:ℝ), (8432743730156301596913739/157552928437500000000:ℝ)],
![(15011879118324123537093188717/4726587853125000000000:ℝ), (29025339426956619975856732231/4726587853125000000000:ℝ), (14317833723868482818959957319/4726587853125000000000:ℝ), (18477821515859526552752387/315105856875000000000:ℝ)] ]
theorem row033_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (2415777703848066038993818807/3608984933483151360000000000000:ℝ) row033_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row033_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row033_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row033_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row033_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
