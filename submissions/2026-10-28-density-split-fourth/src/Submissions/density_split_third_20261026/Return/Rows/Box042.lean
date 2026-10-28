/- Fourth density transition: exact return rectangle 042.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row042_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(143946057222774633579200141/238966977457427343750:ℝ), (269689897369186447412558503/238966977457427343750:ℝ), (128318417602948079714604083/238966977457427343750:ℝ), (195442940862120688193969/26551886384158593750:ℝ)],
![(142899890820838135195705997/119483488728713671875:ℝ), (266665588423399741395401767/119483488728713671875:ℝ), (125464628877981545239092293/119483488728713671875:ℝ), (97544779264916091182947/13275943192079296875:ℝ)],
![(141855990179873085012211853/238966977457427343750:ℝ), (263649200035981304399267431/238966977457427343750:ℝ), (61309855819945409116965289/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row042_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (215089129782109025602562419/527960572532726169600000000:ℝ) row042_oldSmall_coefficients (225/512:ℝ) (453/1024:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row042_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row042_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row042_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_oldSmall_coefficients]
def row042_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(22995706251430886652230141/238966977457427343750:ℝ), (37692849550864414170548503/238966977457427343750:ℝ), (15484154034407724323994083/238966977457427343750:ℝ), (19471169630776539391907/79655659152475781250:ℝ)],
![(23064792110657695553215997/119483488728713671875:ℝ), (37753362338030662697261767/119483488728713671875:ℝ), (15450596015043405551532293/119483488728713671875:ℝ), (9523748916008479578841/39827829576237890625:ℝ)],
![(23136143730855952654201853/238966977457427343750:ℝ), (37819411528123551705122431/238966977457427343750:ℝ), (7710806017564747386397789/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row042_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12908275869801332094332419/527960572532726169600000000:ℝ) row042_oldSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row042_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row042_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row042_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_oldSwitch_coefficients]
def row042_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(60189861792171260861/638981599218750:ℝ), (98851639845328754263/638981599218750:ℝ), (40708656770471313443/638981599218750:ℝ), (16786038902924449/70997955468750:ℝ)],
![(60374592725632610237/319490799609375:ℝ), (99018589085991014407/319490799609375:ℝ), (40626288906697414853/319490799609375:ℝ), (8205498152251187/35498977734375:ℝ)],
![(60565382151293959613/638981599218750:ℝ), (99200323709116309951/638981599218750:ℝ), (20278053787272112669/319490799609375:ℝ), (0:ℝ)] ]
theorem row042_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (35814967654330616899/1411731003801600000000:ℝ) row042_newSwitch_coefficients (225/512:ℝ) (453/1024:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row042_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row042_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row042_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_newSwitch_coefficients]
def row042_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(31051649718114354252420148081/485973621396225000000000:ℝ), (47041952627274390869124159803/485973621396225000000000:ℝ), (8710512482652723911596693361/242986810698112500000000:ℝ), (0:ℝ)],
![(156643389239649159045769730357/1214934053490562500000000:ℝ), (1188665576442685780109075376959/6074670267452812500000000:ℝ), (177037067832639664124722644181/2429868106981125000000000:ℝ), (84261796851826671723255391/449975575366875000000000:ℝ)],
![(158051568638185330829438720309/2429868106981125000000000:ℝ), (6007780797574372416594359672713/60746702674528125000000000:ℝ), (8997565246785816459536546147831/242986810698112500000000000:ℝ), (1728442643322776547711800477/8999511507337500000000000:ℝ)] ]
theorem row042_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2405671923340761439563617423/1073683544555284070400000000000:ℝ) row042_newTop_coefficients (225/512:ℝ) (453/1024:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row042_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row042_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row042_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row042_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
