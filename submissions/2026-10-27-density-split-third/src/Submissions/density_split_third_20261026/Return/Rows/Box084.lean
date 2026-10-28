/- Fourth density transition: exact return rectangle 084.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row084_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(743066804039027179318829/238966977457427343750:ℝ), (1560429509156319553492039/238966977457427343750:ℝ), (947090618192121209913491/238966977457427343750:ℝ), (14269218610309483137809/26551886384158593750:ℝ)],
![(134006892127871671070089/23896697745742734375:ℝ), (1344678315551742481469143/119483488728713671875:ℝ), (738787554675862592762501/119483488728713671875:ℝ), (6957918139010488654867/13275943192079296875:ℝ)],
![(599267878211137731382061/238966977457427343750:ℝ), (1136847680315434430468647/238966977457427343750:ℝ), (269677989017705722980793/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row084_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1126574279581162023021523/2062345986455961600000000:ℝ) row084_oldSmall_coefficients (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row084_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row084_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row084_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row084_oldSmall_coefficients]
def row084_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(70232893685908311388829/238966977457427343750:ℝ), (136001189370060038362039/238966977457427343750:ℝ), (77972672542523495943491/238966977457427343750:ℝ), (3679540432213593823427/79655659152475781250:ℝ)],
![(13380763321789238540089/23896697745742734375:ℝ), (121097878690538947409143/119483488728713671875:ℝ), (60437913187126593842501/119483488728713671875:ℝ), (1627934316727006794601/39827829576237890625:ℝ)],
![(65840500503432274012061/238966977457427343750:ℝ), (111730970937658337603647/238966977457427343750:ℝ), (23738596641068842733293/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row084_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (66679873179247191111523/2062345986455961600000000:ℝ) row084_oldSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row084_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row084_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row084_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row084_oldSwitch_coefficients]
def row084_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(183637759378380509/638981599218750:ℝ), (356455639132716919/638981599218750:ℝ), (204912729554686211/638981599218750:ℝ), (3229062534761089/70997955468750:ℝ)],
![(34947206308942969/63898159921875:ℝ), (316989300861363703/319490799609375:ℝ), (158635193848924421/319490799609375:ℝ), (1427009968169507/35498977734375:ℝ)],
![(171892795911049181/638981599218750:ℝ), (292308345053045887/638981599218750:ℝ), (62272094881935853/319490799609375:ℝ), (0:ℝ)] ]
theorem row084_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (182457755808635683/5514574233600000000:ℝ) row084_newSwitch_coefficients (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row084_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row084_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row084_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row084_newSwitch_coefficients]
def row084_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(28628571085602501043297382309/242986810698112500000000000:ℝ), (48326630035389414696271811599/242986810698112500000000000:ℝ), (24706642101893335779055094843/242986810698112500000000000:ℝ), (143111315081114561514413539/8999511507337500000000000:ℝ)],
![(29510122199996574691228569509/121493405349056250000000000:ℝ), (45614574969440024226786679231/121493405349056250000000000:ℝ), (18788505573909931213229091629/121493405349056250000000000:ℝ), (49952304397435724133860441/4499755753668750000000000:ℝ)],
![(32695548260269048339159756709/242986810698112500000000000:ℝ), (9675793226148906066761012171/48597362139622500000000000:ℝ), (8620657610250242654189089573/121493405349056250000000000:ℝ), (0:ℝ)] ]
theorem row084_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (4524714667808374669072896091/2097038172959539200000000000000:ℝ) row084_newTop_coefficients (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row084_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row084_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row084_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row084_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
