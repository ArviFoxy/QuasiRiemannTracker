/- Fourth density transition: exact return rectangle 014.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row014_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2274299334115253334050189/238966977457427343750:ℝ), (878795079934466032364603/47793395491485468750:ℝ), (2333637890102119915152563/238966977457427343750:ℝ), (21824172907137355542193/26551886384158593750:ℝ)],
![(2150892257030397686113421/119483488728713671875:ℝ), (4041678596145866228001223/119483488728713671875:ℝ), (2005746631827677384351333/119483488728713671875:ℝ), (10735395287424424857059/13275943192079296875:ℝ)],
![(2029750940916990238176653/238966977457427343750:ℝ), (3697302350987671315201831/238966977457427343750:ℝ), (843363430214521161950089/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row014_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2509547361523570516575859/8249383945823846400000000:ℝ) row014_oldSmall_coefficients (33/64:ℝ) (69/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row014_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row014_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row014_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_oldSmall_coefficients]
def row014_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(224640648926960872665226/119483488728713671875:ℝ), (363161375047652186001902/119483488728713671875:ℝ), (146357194063438507086676/119483488728713671875:ℝ), (0:ℝ)],
![(465280753414479507953684/119483488728713671875:ℝ), (751880158002667001572012/119483488728713671875:ℝ), (303385263920163147222122/119483488728713671875:ℝ), (133505756622628284598/39827829576237890625:ℝ)],
![(241772984973242735288458/119483488728713671875:ℝ), (78297396883667011228762/23896697745742734375:ℝ), (318630179163857273995967/238966977457427343750:ℝ), (690683312004836803421/79655659152475781250:ℝ)] ]
theorem row014_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (47945695918258879283899/2062345986455961600000000:ℝ) row014_oldSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row014_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row014_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row014_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_oldSwitch_coefficients]
def row014_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(589642739154299146/319490799609375:ℝ), (955285137202693742/319490799609375:ℝ), (386032827242144596/319490799609375:ℝ), (0:ℝ)],
![(1222066944641266964/319490799609375:ℝ), (1979491422493035052/319490799609375:ℝ), (801375899279856362/319490799609375:ℝ), (146320851037586/35498977734375:ℝ)],
![(635453451586967818/319490799609375:ℝ), (206319795304371802/63898159921875:ℝ), (842872675696132607/638981599218750:ℝ), (667684300497247/70997955468750:ℝ)] ]
theorem row014_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (133719172273209979/5514574233600000000:ℝ) row014_newSwitch_coefficients (33/64:ℝ) (69/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row014_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row014_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row014_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_newSwitch_coefficients]
def row014_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(87165356510692329012951881741/60746702674528125000000000:ℝ), (26898087391962039777007244003/12149340534905625000000000:ℝ), (25586066544487765558100106637/30373351337264062500000000:ℝ), (0:ℝ)],
![(93365819432585365836917475341/30373351337264062500000000:ℝ), (146825524994970245091552438811/30373351337264062500000000:ℝ), (118280860522837450971449876989/60746702674528125000000000:ℝ), (122874520747536728852910187/2249877876834375000000000:ℝ)],
![(100142251090948002660883068941/60746702674528125000000000:ℝ), (32105944917388753088438907221/12149340534905625000000000:ℝ), (272805855910021638081973745591/242986810698112500000000000:ℝ), (106940957855278005731666681/1799902301467500000000000:ℝ)] ]
theorem row014_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (12400314033619283178730268659/2097038172959539200000000000000:ℝ) row014_newTop_coefficients (33/64:ℝ) (69/128:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row014_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row014_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row014_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row014_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
