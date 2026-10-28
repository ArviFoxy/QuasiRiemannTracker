/- Fourth density transition: exact return rectangle 031.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row031_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(24210956764619195453034535168/13275943192079296875:ℝ), (11657028962028847720341515344/2655188638415859375:ℝ), (43984583560285263894819256336/13275943192079296875:ℝ), (367049985110905742452232492/491701599706640625:ℝ)],
![(38431081127699448263982603776/13275943192079296875:ℝ), (86657438176848779793652385536/13275943192079296875:ℝ), (58116147826132396848386457344/13275943192079296875:ℝ), (366285123528979664053395392/491701599706640625:ℝ)],
![(14240712895296030122683940608/13275943192079296875:ℝ), (28434122530021475236338319616/13275943192079296875:ℝ), (14193456161674098713554379008/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row031_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (471813504515604857084132473/1407894860087269785600000000:ℝ) row031_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row031_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row031_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row031_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_oldSmall_coefficients]
def row031_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(659563373433786842773325056/4425314397359765625:ℝ), (891774687764914327007835344/2655188638415859375:ℝ), (2998556880077689427526136336/13275943192079296875:ℝ), (19197501571487135553092492/491701599706640625:ℝ)],
![(3441526316188097217052683776/13275943192079296875:ℝ), (7361062801405747215055265536/13275943192079296875:ℝ), (4431488847178349393581977344/13275943192079296875:ℝ), (18958140015273634492755392/491701599706640625:ℝ)],
![(1469381927584516932620580608/13275943192079296875:ℝ), (973914376121499283537199872/4425314397359765625:ℝ), (1452402765002972017891019008/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row031_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (23102383777908087505097473/1407894860087269785600000000:ℝ) row031_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row031_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row031_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row031_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_oldSwitch_coefficients]
def row031_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5215450564042947497728/35498977734375:ℝ), (2348598121037936111824/7099795546875:ℝ), (7883381753704908541456/35498977734375:ℝ), (50212406707881557132/1314776953125:ℝ)],
![(9082166889718384733696/35498977734375:ℝ), (19415212573141069094656/35498977734375:ℝ), (11671905834717293997824/35498977734375:ℝ), (49579454620086468032/1314776953125:ℝ)],
![(3884031072951245747968/35498977734375:ℝ), (7723939934238061742336/35498977734375:ℝ), (3840017011074715994368/35498977734375:ℝ), (0:ℝ)] ]
theorem row031_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (65675497505143645633/3764616010137600000000:ℝ) row031_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row031_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row031_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row031_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_newSwitch_coefficients]
def row031_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(188204087166976380979407150191/4726587853125000000000:ℝ), (371787367902352392288092645089/4726587853125000000000:ℝ), (183610130030521831490511967523/4726587853125000000000:ℝ), (0:ℝ)],
![(192440966351759937962775111431/2363293926562500000000:ℝ), (15305718390056627915675300989/94531757062500000000:ℝ), (192647436400892456315800115333/2363293926562500000000:ℝ), (806138632063082752214071013/787764642187500000000:ℝ)],
![(198156518525501197334085924551/4726587853125000000000:ℝ), (397900557534982932758989439317/4726587853125000000000:ℝ), (206053018728207044755533037013/4726587853125000000000:ℝ), (2093924542075738616241464749/1575529284375000000000:ℝ)] ]
theorem row031_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (180389573599099929333552964409/1154875178714608435200000000000000:ℝ) row031_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row031_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row031_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row031_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row031_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
