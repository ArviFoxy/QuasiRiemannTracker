/- Fourth density transition: exact return rectangle 035.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row035_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(71804307882825489050526112/119483488728713671875:ℝ), (134453538396657491832894272/119483488728713671875:ℝ), (127877588397224497500451691/238966977457427343750:ℝ), (194736176197543676537819/26551886384158593750:ℝ)],
![(28512943024937185583511616/23896697745742734375:ℝ), (265890688405896546669654208/119483488728713671875:ℝ), (125032671159133770495289976/119483488728713671875:ℝ), (97191396932627585354872/13275943192079296875:ℝ)],
![(70761540122346162967031968/119483488728713671875:ℝ), (131441110288423189347271136/119483488728713671875:ℝ), (61098312703959425480239168/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row035_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (3333382878067673945526907/8249383945823846400000000:ℝ) row035_oldSmall_coefficients (453/1024:ℝ) (57/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row035_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row035_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row035_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_oldSmall_coefficients]
def row035_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(11596007604477862395486112/119483488728713671875:ℝ), (18993512981211434057716772/119483488728713671875:ℝ), (15589226469428811183106691/238966977457427343750:ℝ), (18623826033257378923457/79655659152475781250:ℝ)],
![(4652673365830796378391616/23896697745742734375:ℝ), (38053075152515757123294208/119483488728713671875:ℝ), (15560242489514900404369976/119483488728713671875:ℝ), (9100077117248899344616/39827829576237890625:ℝ)],
![(11668492105161843596471968/119483488728713671875:ℝ), (19062330372767643306151136/119483488728713671875:ℝ), (7767916274525698809679168/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row035_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (200818818620336874336907/8249383945823846400000000:ℝ) row035_oldSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row035_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row035_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row035_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_oldSwitch_coefficients]
def row035_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(30354852867324341152/319490799609375:ℝ), (49816647229590239012/319490799609375:ℝ), (40989078324608393411/638981599218750:ℝ), (16035953706080299/70997955468750:ℝ)],
![(12180099032062006336/63898159921875:ℝ), (99815029082305773568/319490799609375:ℝ), (40918896992455203896/319490799609375:ℝ), (7830455553829112/35498977734375:ℝ)],
![(30548671539085690528/319490799609375:ℝ), (50005774543947052256/319490799609375:ℝ), (20430451095961361728/319490799609375:ℝ), (0:ℝ)] ]
theorem row035_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (557353813608998347/22058296934400000000:ℝ) row035_newSwitch_coefficients (453/1024:ℝ) (57/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row035_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row035_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row035_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_newSwitch_coefficients]
def row035_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(15758488912448818116155653418021/242986810698112500000000000:ℝ), (4778223867237668953202556570443/48597362139622500000000000:ℝ), (4428780696338335779585945154597/121493405349056250000000000:ℝ), (0:ℝ)],
![(15899306852302435294522552413221/121493405349056250000000000:ℝ), (24148930997632118830208714003887/121493405349056250000000000:ℝ), (360130929913220192498892169919/4859736213962250000000000:ℝ), (885824674804509830479246567/4499755753668750000000000:ℝ)],
![(16042428667101930872889451408421/242986810698112500000000000:ℝ), (24412219105303146790981148669551/242986810698112500000000000:ℝ), (9153356049158912024433693277487/242986810698112500000000000:ℝ), (1814856055895262774205185791/8999511507337500000000000:ℝ)] ]
theorem row035_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1249503913040095686570027324379/536841772277642035200000000000000:ℝ) row035_newTop_coefficients (453/1024:ℝ) (57/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row035_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row035_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row035_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row035_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
