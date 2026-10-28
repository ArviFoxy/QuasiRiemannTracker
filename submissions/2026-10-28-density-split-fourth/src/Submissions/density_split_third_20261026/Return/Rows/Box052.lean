/- Fourth density transition: exact return rectangle 052.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row052_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3454150506840188289789574972/13275943192079296875:ℝ), (1887963666039828498589199908/2655188638415859375:ℝ), (8520048805206743372797648564/13275943192079296875:ℝ), (93865865628023151209860148/491701599706640625:ℝ)],
![(4338533050540420327981981304/13275943192079296875:ℝ), (11185021727929091478074019304/13275943192079296875:ℝ), (9360221151409573850327160296/13275943192079296875:ℝ), (93101004046097072811023048/491701599706640625:ℝ)],
![(904971075916009349928278332/13275943192079296875:ℝ), (1807032561046883029521530564/13275943192079296875:ℝ), (902064242029796237516689732/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row052_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1956506124910547674145669353/5631579440349079142400000000:ℝ) row052_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row052_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row052_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row052_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_oldSmall_coefficients]
def row052_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(234970320653823398290834972/13275943192079296875:ℝ), (123264331926372254119139908/2655188638415859375:ℝ), (528709401645551952993268564/13275943192079296875:ℝ), (5457619672458911804200148/491701599706640625:ℝ)],
![(318067099261759983077301304/13275943192079296875:ℝ), (86114902217916175594593256/1475104799119921875:ℝ), (597864782388754359195840296/13275943192079296875:ℝ), (5218258116245410743863048/491701599706640625:ℝ)],
![(29880836768572276224779444/4425314397359765625:ℝ), (178266226112706580351150564/13275943192079296875:ℝ), (88626178645514458037749732/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row052_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (96143707531656282283034353/5631579440349079142400000000:ℝ) row052_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row052_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row052_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row052_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_oldSwitch_coefficients]
def row052_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(617312278014582461212/35498977734375:ℝ), (323606277640178259268/7099795546875:ℝ), (1386655614557269711444/35498977734375:ℝ), (14293719918406884308/1314776953125:ℝ)],
![(836839380971957564984/35498977734375:ℝ), (2037357735088853362984/35498977734375:ℝ), (1569371555723251768616/35498977734375:ℝ), (13660767830611795208/1314776953125:ℝ)],
![(236841850233183615772/35498977734375:ℝ), (471044313174635273444/35498977734375:ℝ), (234208871228312595172/35498977734375:ℝ), (0:ℝ)] ]
theorem row052_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (272472851827687112113/15058464040550400000000:ℝ) row052_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row052_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row052_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row052_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_newSwitch_coefficients]
def row052_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(12678048369464438483896812479/4726587853125000000000:ℝ), (27501589338978105893765608573/4726587853125000000000:ℝ), (17228213709567396725434531997/4726587853125000000000:ℝ), (801048878842391403426271301/1575529284375000000000:ℝ)],
![(11149590434984348550838811999/2363293926562500000000:ℝ), (22511976915862056083908267309/2363293926562500000000:ℝ), (11843057377508116606478214677/2363293926562500000000:ℝ), (159700800446409145806474289/787764642187500000000:ℝ)],
![(11099805489461961005723663399/4726587853125000000000:ℝ), (21924370427249935537367961001/4726587853125000000000:ℝ), (10826177002392800101966671227/4726587853125000000000:ℝ), (0:ℝ)] ]
theorem row052_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (11180222170412682113291212481/72179698669663027200000000000000:ℝ) row052_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row052_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row052_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row052_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row052_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
