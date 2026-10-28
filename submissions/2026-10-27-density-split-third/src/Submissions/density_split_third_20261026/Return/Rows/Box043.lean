/- Fourth density transition: exact return rectangle 043.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row043_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(54178004995810175719475197744/13275943192079296875:ℝ), (29629483852792673106977545024/2655188638415859375:ℝ), (133784023073607457652173815808/13275943192079296875:ℝ), (13271532592619525868355846144/4425314397359765625:ℝ)],
![(68255856267115334777831946704/13275943192079296875:ℝ), (35222809277251488817816211648/2655188638415859375:ℝ), (147507111747785108772712890368/13275943192079296875:ℝ), (13216299758469497411685842944/4425314397359765625:ℝ)],
![(2848661451964320638533810652/2655188638415859375:ℝ), (5692647858046848417124356304/2655188638415859375:ℝ), (2843988671613052159645233152/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row043_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13338056912945353023073/39597042939954462720000:ℝ) row043_oldSmall_coefficients (111/256:ℝ) (225/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row043_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row043_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row043_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_oldSmall_coefficients]
def row043_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3629354283503928000332717744/13275943192079296875:ℝ), (1897247267853619764894665024/2655188638415859375:ℝ), (2697497074845179495274151936/4425314397359765625:ℝ), (2235599317417268836238098432/13275943192079296875:ℝ)],
![(1662688678722254415280755568/4425314397359765625:ℝ), (809624441937278526188017216/885062879471953125:ℝ), (9340874244056836063910330368/13275943192079296875:ℝ), (2184553682203410284276088832/13275943192079296875:ℝ)],
![(282016942334771123975470652/2655188638415859375:ℝ), (562384187631803369882676304/2655188638415859375:ℝ), (280369269178215806649393152/2655188638415859375:ℝ), (0:ℝ)] ]
theorem row043_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (645253167931245119323/39597042939954462720000:ℝ) row043_oldSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row043_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row043_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row043_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_oldSwitch_coefficients]
def row043_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9538236911464693826224/35498977734375:ℝ), (4981863405357382007104/7099795546875:ℝ), (21224858985481488007168/35498977734375:ℝ), (1951251079003942682624/11832992578125:ℝ)],
![(13130939673270352418384/35498977734375:ℝ), (6387682613248579375808/7099795546875:ℝ), (24526341660971388796928/35498977734375:ℝ), (1906272102972062695424/11832992578125:ℝ)],
![(745705522966302962492/7099795546875:ℝ), (1487136048356100859984/7099795546875:ℝ), (741435791513040084992/7099795546875:ℝ), (0:ℝ)] ]
theorem row043_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1834864095379483/105879825285120000:ℝ) row043_newSwitch_coefficients (111/256:ℝ) (225/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row043_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row043_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row043_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_newSwitch_coefficients]
def row043_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(45986160416526110904849238409/1181646963281250000000:ℝ), (5983562671003124808090773977/73852935205078125000:ℝ), (422302506825280117970774752/9231616900634765625:ℝ), (11203818983091519545139712/3077205633544921875:ℝ)],
![(17295088970523391089094436027/236329392656250000000:ℝ), (433342319344117800832844783/2954117408203125000:ℝ), (138036683792082016779864736/1846323380126953125:ℝ), (154034067018649039215616/123088225341796875:ℝ)],
![(277413485536539540946201913/7562540565000000000:ℝ), (172272942444360181960496813/2363293926562500000:ℝ), (2674516877212594472685464/73852935205078125:ℝ), (0:ℝ)] ]
theorem row043_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (5642331685611903403/4699199132139520000000000:ℝ) row043_newTop_coefficients (111/256:ℝ) (225/512:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row043_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row043_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row043_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row043_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
