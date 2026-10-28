/- Fourth density transition: exact return rectangle 050.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row050_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4761276931051370398694688704/2655188638415859375:ℝ), (67762914721371715201696921856/13275943192079296875:ℝ), (64112379318610444152747261952/13275943192079296875:ℝ), (6718615547534805619182927872/4425314397359765625:ℝ)],
![(27231780471228307387763054048/13275943192079296875:ℝ), (74442209036028459850189750912/13275943192079296875:ℝ), (13440116413946153136860594176/2655188638415859375:ℝ), (6663382713384777162512924672/4425314397359765625:ℝ)],
![(3590851804487899528601914828/13275943192079296875:ℝ), (7175906482596908179921277456/13275943192079296875:ℝ), (3585057435007931209242800128/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row050_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2122041551966500489144657/6187037959367884800000000:ℝ) row050_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row050_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row050_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row050_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_oldSmall_coefficients]
def row050_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1263483922595252298603328/10926702215703125:ℝ), (4262703269860520738069401856/13275943192079296875:ℝ), (3921940746947834903303421952/13275943192079296875:ℝ), (1194368111529422246062063616/13275943192079296875:ℝ)],
![(1832198748463875959458894048/13275943192079296875:ℝ), (1601257406082218678647570304/4425314397359765625:ℝ), (822980147729797288484274176/2655188638415859375:ℝ), (1143322476315563694100054016/13275943192079296875:ℝ)],
![(348438741521664791023654828/13275943192079296875:ℝ), (694859596754073078939757456/13275943192079296875:ℝ), (38491479785659221586337792/1475104799119921875:ℝ), (0:ℝ)] ]
theorem row050_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (102952841140053242860907/6187037959367884800000000:ℝ) row050_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row050_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row050_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row050_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_oldSwitch_coefficients]
def row050_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(805942569293718056384/7099795546875:ℝ), (11183709024927835525376/35498977734375:ℝ), (10283284255682594209792/35498977734375:ℝ), (1043094003549791322112/11832992578125:ℝ)],
![(4815008912055950506208/35498977734375:ℝ), (12614139151541174541952/35498977734375:ℝ), (2158697558443759108096/7099795546875:ℝ), (998115027517911334912/11832992578125:ℝ)],
![(921120918613216444588/35498977734375:ℝ), (1837014328937856472976/35498977734375:ℝ), (915899818611500965888/35498977734375:ℝ), (0:ℝ)] ]
theorem row050_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (292280089019762347/16543722700800000000:ℝ) row050_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row050_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row050_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row050_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_newSwitch_coefficients]
def row050_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4006496037741458441053288193/295411740820312500000:ℝ), (598634936010805405356393169/18463233801269531250:ℝ), (44802305771176705938875264/1846323380126953125:ℝ), (16631360452983700119693824/3077205633544921875:ℝ)],
![(11795192476863558440935471421/590823481640625000000:ℝ), (1577613765655959999050285773/36926467602539062500:ℝ), (237944865333803297053371584/9231616900634765625:ℝ), (9278393145358406554944512/3077205633544921875:ℝ)],
![(41683893927018967399515589001/4726587853125000000000:ℝ), (5176887704220535400840714713/295411740820312500000:ℝ), (80367033994364110516129336/9231616900634765625:ℝ), (0:ℝ)] ]
theorem row050_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (6352229063714515934619/734249864396800000000000000:ℝ) row050_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row050_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row050_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row050_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row050_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
