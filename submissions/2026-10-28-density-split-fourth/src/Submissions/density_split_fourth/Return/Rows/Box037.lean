/- Fourth density transition: exact return rectangle 037.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row037_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(136533349002206915061269689108/13275943192079296875:ℝ), (352346088661374322711068204284/13275943192079296875:ℝ), (295185812476205707921567641244/13275943192079296875:ℝ), (26457675835475937550225125356/4425314397359765625:ℝ)],
![(193288270915370090950410719144/13275943192079296875:ℝ), (465596467766420068992463088056/13275943192079296875:ℝ), (70303171918864758993776838136/2655188638415859375:ℝ), (26402523839303789505454357256/4425314397359765625:ℝ)],
![(56920132014859208823289843636/13275943192079296875:ℝ), (113746256979370031445115832972/13275943192079296875:ℝ), (56826170881276588321761926836/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row037_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2179707295000181289330280529243/6487579515282139172044800000000:ℝ) row037_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row037_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row037_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row037_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_oldSmall_coefficients]
def row037_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1110091994453267074414981012/1475104799119921875:ℝ), (24232960793160099771380424284/13275943192079296875:ℝ), (18526593587331450954296661244/13275943192079296875:ℝ), (4284420266627083637807316068/13275943192079296875:ℝ)],
![(1742209919143470819211471016/1475104799119921875:ℝ), (35526237796042748953774568056/13275943192079296875:ℝ), (1605298488421104414901972712/885062879471953125:ℝ), (4233047307616063263439511768/13275943192079296875:ℝ)],
![(637862602039327770244580404/1475104799119921875:ℝ), (11448053243912924005701092972/13275943192079296875:ℝ), (5707330844683299734373306836/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row037_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (11784139853208031673367316027/720842168364682130227200000000:ℝ) row037_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row037_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row037_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row037_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_oldSwitch_coefficients]
def row037_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(26297265041504738716468/35498977734375:ℝ), (63720658198273634249564/35498977734375:ℝ), (48635442513422528649724/35498977734375:ℝ), (3737314678062929788876/11832992578125:ℝ)],
![(41338497281215843355624/35498977734375:ℝ), (93580542919744651795576/35498977734375:ℝ), (12663675373784192067256/7099795546875:ℝ), (3692039727054311048776/11832992578125:ℝ)],
![(15177949890674843884756/35498977734375:ℝ), (30269142430558521999212/35498977734375:ℝ), (15091299271329051551956/35498977734375:ℝ), (0:ℝ)] ]
theorem row037_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (301549674993258812190803/17347350574714060800000000:ℝ) row037_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row037_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row037_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row037_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_newSwitch_coefficients]
def row037_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1422708959605529027675186059/9453175706250000000:ℝ), (2827491173838076067122247621/9453175706250000000:ℝ), (1404835203938330202825079687/9453175706250000000:ℝ), (0:ℝ)],
![(35957113615074437260360549423/118164696328125000000:ℝ), (71505726575479521494051556503/118164696328125000000:ℝ), (8898300102544406016353578357/29541174082031250000:ℝ), (9611972335628937787374119/26258821406250000000:ℝ)],
![(184622399867750682815087173193/1181646963281250000000:ℝ), (46282133696591277119343694007/147705870410156250000:ℝ), (377860986925725500235543879109/2363293926562500000000:ℝ), (1461827304043004858956863349/525176428125000000000:ℝ)] ]
theorem row037_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (281850795728718681363230009/3695600571886746992640000000000:ℝ) row037_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row037_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row037_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row037_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row037_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
