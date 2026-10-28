/- Fourth density transition: exact return rectangle 056.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row056_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(9455348711985244467823541/238966977457427343750:ℝ), (18148663667013880667961631/238966977457427343750:ℝ), (9187195605150815541593039/238966977457427343750:ℝ), (49655845463179310161661/26551886384158593750:ℝ)],
![(1838081694008789514390001/23896697745742734375:ℝ), (17380705593014800632138847/119483488728713671875:ℝ), (8460441193595470717189979/119483488728713671875:ℝ), (24651231565445402166793/13275943192079296875:ℝ)],
![(8927733989074098876076469/238966977457427343750:ℝ), (16620668077383989617338463/238966977457427343750:ℝ), (3871279134457966681568497/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row056_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (13774073239458116468657227/32997535783295385600000000:ℝ) row056_oldSmall_coefficients (27/64:ℝ) (111/256:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row056_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row056_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row056_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_oldSmall_coefficients]
def row056_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1379086044789165858853541/238966977457427343750:ℝ), (2288587922066531579691631/238966977457427343750:ℝ), (968932239364390841963039/238966977457427343750:ℝ), (5821053954903190374983/79655659152475781250:ℝ)],
![(278591773627739156820001/23896697745742734375:ℝ), (2295411514468132989648847/119483488728713671875:ℝ), (953681675347699158259979/119483488728713671875:ℝ), (2698691078071805070379/39827829576237890625:ℝ)],
![(1409097452459673909346469/238966977457427343750:ℝ), (2307771509796374880753463/238966977457427343750:ℝ), (471502575390707734140997/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row056_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (818196405553499587067227/32997535783295385600000000:ℝ) row056_oldSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row056_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row056_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row056_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_oldSwitch_coefficients]
def row056_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(3607357559946332261/638981599218750:ℝ), (5997506042123103151/638981599218750:ℝ), (2544710013876397919/638981599218750:ℝ), (5040355572180781/70997955468750:ℝ)],
![(728890511002333921/63898159921875:ℝ), (6017065278594115087/319490799609375:ℝ), (2505838250501859659/319490799609375:ℝ), (2332656486879353/35498977734375:ℝ)],
![(3687606042277006949/638981599218750:ℝ), (6051409897528162423/638981599218750:ℝ), (1239576509374015237/319490799609375:ℝ), (0:ℝ)] ]
theorem row056_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2268027687814023067/88233187737600000000:ℝ) row056_newSwitch_coefficients (27/64:ℝ) (111/256:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row056_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row056_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row056_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_newSwitch_coefficients]
def row056_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(55381276880881344906698626181/15186675668632031250000000:ℝ), (16705577894600909399067001067/3037335133726406250000000:ℝ), (15360956146592471130158627077/7593337834316015625000000:ℝ), (0:ℝ)],
![(57329570868888663318681422981/7593337834316015625000000:ℝ), (86957210376957621810341357737/7593337834316015625000000:ℝ), (26016470233695648091673657119/6074670267452812500000000:ℝ), (36461108175050502359524873/1124938938417187500000000:ℝ)],
![(59421857041013381730664219781/15186675668632031250000000:ℝ), (181457618340228130322758359527/30373351337264062500000000:ℝ), (553479158831440806162845309027/242986810698112500000000000:ℝ), (334895571686647132122891641/8999511507337500000000000:ℝ)] ]
theorem row056_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3796190071799572693258775419/2097038172959539200000000000000:ℝ) row056_newTop_coefficients (27/64:ℝ) (111/256:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row056_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row056_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row056_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row056_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
