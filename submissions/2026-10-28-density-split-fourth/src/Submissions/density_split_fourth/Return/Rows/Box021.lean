/- Fourth density transition: exact return rectangle 021.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row021_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(645143282544058131479381/238966977457427343750:ℝ), (1311398044689638345390143/238966977457427343750:ℝ), (772859050552602830029643/238966977457427343750:ℝ), (11442159952001436513209/26551886384158593750:ℝ)],
![(581173983030182107510997/119483488728713671875:ℝ), (1127329084558137357456847/119483488728713671875:ℝ), (600041934539574094278953/119483488728713671875:ℝ), (5544388809856465342567/13275943192079296875:ℝ)],
![(519470444487754283542613/238966977457427343750:ℝ), (951180682794905390545951/238966977457427343750:ℝ), (218048152701176414439169/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row021_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (676491229421951679113899/2062345986455961600000000:ℝ) row021_oldSmall_coefficients (15/32:ℝ) (33/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row021_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row021_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row021_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_oldSmall_coefficients]
def row021_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(49393444254652408068139/119483488728713671875:ℝ), (81080229223952885930417/119483488728713671875:ℝ), (33841268296821470750167/119483488728713671875:ℝ), (178459460224133045963/39827829576237890625:ℝ)],
![(104520855318135497447894/119483488728713671875:ℝ), (169402759474946605497538/119483488728713671875:ℝ), (68443935039878014299644/119483488728713671875:ℝ), (0:ℝ)],
![(11252058309841437875951/23896697745742734375:ℝ), (91090731714313960140821/119483488728713671875:ℝ), (73779372936521080824029/238966977457427343750:ℝ), (66752878311314142299/79655659152475781250:ℝ)] ]
theorem row021_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (23872718641662468428501/1031172993227980800000000:ℝ) row021_oldSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row021_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row021_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row021_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_oldSwitch_coefficients]
def row021_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(129378419637075019/319490799609375:ℝ), (212741067232871057/319490799609375:ℝ), (88934015967610807/319490799609375:ℝ), (150941086451641/35498977734375:ℝ)],
![(274089080240484374/319490799609375:ℝ), (445157326046530498/319490799609375:ℝ), (180336622712296124/319490799609375:ℝ), (0:ℝ)],
![(29547981340681871/63898159921875:ℝ), (239808950045177141/319490799609375:ℝ), (194991745110079709/638981599218750:ℝ), (73160425518793/70997955468750:ℝ)] ]
theorem row021_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (66530364221770421/2757287116800000000:ℝ) row021_newSwitch_coefficients (15/32:ℝ) (33/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row021_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row021_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row021_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_newSwitch_coefficients]
def row021_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(701360228196370010174859557/2429868106981125000000000:ℝ), (1070324601983391685366642039/2429868106981125000000000:ℝ), (200379098628459851001328741/1214934053490562500000000:ℝ), (0:ℝ)],
![(802330737175446746654171429/1214934053490562500000000:ℝ), (50490476016562145749277251/48597362139622500000000:ℝ), (5164146789600440027834010791/12149340534905625000000000:ℝ), (7966781446129361560621753/449975575366875000000000:ℝ)],
![(926339995613307483133483301/2429868106981125000000000:ℝ), (37724091527931364196556391273/60746702674528125000000000:ℝ), (67578062240890789017389558351/242986810698112500000000000:ℝ), (202542335208830344459127717/8999511507337500000000000:ℝ)] ]
theorem row021_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (69316709829808638783338203/20970381729595392000000000000:ℝ) row021_newTop_coefficients (15/32:ℝ) (33/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row021_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row021_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row021_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row021_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
