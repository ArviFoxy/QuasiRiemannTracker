/- Fourth density transition: exact return rectangle 041.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row041_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(260256585406589814751611883/13275943192079296875:ℝ), (534686839820427801988101809/13275943192079296875:ℝ), (294713930609942008576230469/13275943192079296875:ℝ), (6746121861872133415330181/4425314397359765625:ℝ)],
![(499367167908183436548843014/13275943192079296875:ℝ), (1006777824373235066537918146/13275943192079296875:ℝ), (4221606705282501976123294/106207545536634375:ℝ), (6732985444270902185862206/4425314397359765625:ℝ)],
![(239148747793480780426663231/13275943192079296875:ℝ), (472206820100660704812128537/13275943192079296875:ℝ), (233103989072945624321402806/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row041_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2341920809591827526804085797/6335526870392714035200000000:ℝ) row041_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row041_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row041_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row041_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_oldSmall_coefficients]
def row041_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3251089942444935383402987/1475104799119921875:ℝ), (57161601430551784412946809/13275943192079296875:ℝ), (28843701751332298266375469/13275943192079296875:ℝ), (901432179113717460305543/13275943192079296875:ℝ)],
![(6422600519171726288301446/1475104799119921875:ℝ), (111950684918439292842848146/13275943192079296875:ℝ), (146977098270312696467098/35402515178878125:ℝ), (887636656482125708276618/13275943192079296875:ℝ)],
![(1057735087973943075278453/491701599706640625:ℝ), (54833318055630399551963537/13275943192079296875:ℝ), (26315489804659597392882806/13275943192079296875:ℝ), (0:ℝ)] ]
theorem row041_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (42113487687439840699823599/2111842290130904678400000000:ℝ) row041_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row041_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row041_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row041_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_oldSwitch_coefficients]
def row041_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(77002469275968442243/35498977734375:ℝ), (150496540387720620089/35498977734375:ℝ), (75948189399124275949/35498977734375:ℝ), (782931940842782701/11832992578125:ℝ)],
![(152151541749791459894/35498977734375:ℝ), (294835663423027848466/35498977734375:ℝ), (1161667264627887694/283991821875:ℝ), (770745725343607726/11832992578125:ℝ)],
![(75189577074452601751/35498977734375:ℝ), (144456516074269354577/35498977734375:ℝ), (69373670445190190326/35498977734375:ℝ), (0:ℝ)] ]
theorem row041_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (354590034777514801037/16940772045619200000000:ℝ) row041_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row041_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row041_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row041_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_newSwitch_coefficients]
def row041_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(4515774301584869858689577/4726587853125000000:ℝ), (8347143187334763418020283/4726587853125000000:ℝ), (7715727477282950496679537/9453175706250000000:ℝ), (0:ℝ)],
![(57323323019376214717282867/29541174082031250000:ℝ), (106392282491504314731015977/29541174082031250000:ℝ), (398155490904134621181954551/236329392656250000000:ℝ), (163148144593922095102447/13129410703125000000:ℝ)],
![(1164972531599160982358191673/1181646963281250000000:ℝ), (2171688534277122269592378571/1181646963281250000000:ℝ), (4115753660385876054598225763/4726587853125000000000:ℝ), (3446686362678373546389197/262588214062500000000:ℝ)] ]
theorem row041_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (130226048027613509185661/90224623337078784000000000:ℝ) row041_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row041_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row041_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row041_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row041_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
