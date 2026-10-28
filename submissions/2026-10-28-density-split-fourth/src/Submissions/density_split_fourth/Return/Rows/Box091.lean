/- Fourth density transition: exact return rectangle 091.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row091_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(393149838078600729674789/2150702797116846093750:ℝ), (1012328757797643282463087/2150702797116846093750:ℝ), (845208001359484375901807/2150702797116846093750:ℝ), (8371447468164511967167/79655659152475781250:ℝ)],
![(263209474236063693722213/1075351398558423046875:ℝ), (617416942076356485227143/1075351398558423046875:ℝ), (452910024202829217024647/1075351398558423046875:ℝ), (3655650235649497241471/39827829576237890625:ℝ)],
![(153660959136560457769637/2150702797116846093750:ℝ), (293790151669490877192799/2150702797116846093750:ℝ), (70227714464220645649081/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row091_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (313749311768486842815451/515586496613990400000000:ℝ) row091_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row091_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row091_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row091_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_oldSmall_coefficients]
def row091_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(45177648071237038544789/2150702797116846093750:ℝ), (120258889748362026673087/2150702797116846093750:ℝ), (104984835283012937711807/2150702797116846093750:ℝ), (3322621511765327731501/238966977457427343750:ℝ)],
![(19792183712760060512213/1075351398558423046875:ℝ), (48076297389316059917143/1075351398558423046875:ℝ), (37516341196245641034647/1075351398558423046875:ℝ), (1025803057743293514413/119483488728713671875:ℝ)],
![(14798568097316882479637/2150702797116846093750:ℝ), (25721331370034423487799/2150702797116846093750:ℝ), (5607101081575143941581/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row091_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (19429623618971993145451/515586496613990400000000:ℝ) row091_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row091_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row091_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row091_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_oldSwitch_coefficients]
def row091_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(119875662442379669/5750834392968750:ℝ), (318785194654920127/5750834392968750:ℝ), (277943401982701247/5750834392968750:ℝ), (2927180361857807/212993866406250:ℝ)],
![(51996640891881173/2875417196484375:ℝ), (126517245080571703/2875417196484375:ℝ), (98848313837676887/2875417196484375:ℝ), (901026283295791/106496933203125:ℝ)],
![(38644049141382677/5750834392968750:ℝ), (67317737673541879/5750834392968750:ℝ), (14716005139517101/2875417196484375:ℝ), (0:ℝ)] ]
theorem row091_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (52879829655371371/1378643558400000000:ℝ) row091_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row091_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row091_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row091_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_newSwitch_coefficients]
def row091_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(24281362564326481026808492589/2186881296283012500000000000:ℝ), (66607834621588024400388101767/2186881296283012500000000000:ℝ), (60371581550196605720350725767/2186881296283012500000000000:ℝ), (222779129542408177120631069/26998534522012500000000000:ℝ)],
![(4868814723011991498705273389/1093440648141506250000000000:ℝ), (13251735977378869507628777287/1093440648141506250000000000:ℝ), (12155861187055870922835904367/1093440648141506250000000000:ℝ), (46579505341839418690276549/13499267261006250000000000:ℝ)],
![(6191141394603101970602054189/2186881296283012500000000000:ℝ), (1836730675690956760680215747/437376259256602500000000000:ℝ), (1639328197540382037048449773/1093440648141506250000000000:ℝ), (0:ℝ)] ]
theorem row091_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2097180043749616957490515411/524259543239884800000000000000:ℝ) row091_newTop_coefficients (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row091_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row091_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row091_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row091_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
