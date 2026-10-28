/- Fourth density transition: exact return rectangle 002.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row002_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2567307775951394355318682144/43014055942336921875:ℝ), (191785234287902620525601491664/1075351398558423046875:ℝ), (191024016694892897058293588728/1075351398558423046875:ℝ), (2348943545943419915886044932/39827829576237890625:ℝ)],
![(51253231102142030659673606144/1075351398558423046875:ℝ), (152522452710743407592473111552/1075351398558423046875:ℝ), (151288765243562568128126070272/1075351398558423046875:ℝ), (1852575580394087512949132032/39827829576237890625:ℝ)],
![(452554940735839442760454144/1075351398558423046875:ℝ), (903326243107885328268505088/1075351398558423046875:ℝ), (450773364508274299908050944/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row002_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (8492227340750991988739603/98992607349886156800000000:ℝ) row002_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row002_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row002_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_oldSmall_coefficients]
def row002_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(195684098933287258131737056/358450466186141015625:ℝ), (1647248911120199679177084368/1075351398558423046875:ℝ), (1534065573244149739735301432/1075351398558423046875:ℝ), (52652000805544909697776748/119483488728713671875:ℝ)],
![(19321832808039923827562752/71690093237228203125:ℝ), (115547199398858285745243392/215070279711684609375:ℝ), (57582230601956683402555136/215070279711684609375:ℝ), (0:ℝ)],
![(1296881660944050544892043904/358450466186141015625:ℝ), (11467362609326352437412017792/1075351398558423046875:ℝ), (11264061141318575353648043648/1075351398558423046875:ℝ), (409704630293638459612461952/119483488728713671875:ℝ)] ]
theorem row002_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2524056587428111753323071/211184229013090467840000000:ℝ) row002_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row002_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row002_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_oldSwitch_coefficients]
def row002_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1488388469691473933728/2875417196484375:ℝ), (4162712421704555710928/2875417196484375:ℝ), (3862145799080492930872/2875417196484375:ℝ), (43993310030342137636/106496933203125:ℝ)],
![(154528067218232363776/575083439296875:ℝ), (308053885440051660032/575083439296875:ℝ), (153527196307759296256/575083439296875:ℝ), (0:ℝ)],
![(10358381594462566778752/2875417196484375:ℝ), (30527431441583563298432/2875417196484375:ℝ), (29983048364738512647808/2875417196484375:ℝ), (363481249047226523264/106496933203125:ℝ)] ]
theorem row002_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (22279775200375602173/1694077204561920000000:ℝ) row002_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row002_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row002_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_newSwitch_coefficients]
def row002_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(18655411213730014741683232231069/273360162035376562500000000:ℝ), (37145655323570334494918377911539/273360162035376562500000000:ℝ), (3698095541225329439691981782969/54672032407075312500000000:ℝ), (0:ℝ)],
![(497225113909671430117786242807253/136680081017688281250000000:ℝ), (1461946199060783090014148902315007/136680081017688281250000000:ℝ), (1432443037771418923010633499624511/136680081017688281250000000:ℝ), (5774341081688622959410111056997/1687408407625781250000000:ℝ)],
![(1887754588718890953643926200467669/273360162035376562500000000:ℝ), (5615015098179544838629970597950079/273360162035376562500000000:ℝ), (1113415015444155206780967563545523/54672032407075312500000000:ℝ), (4542750902669875224505269956161/674963363050312500000000:ℝ)] ]
theorem row002_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (48461960915836066929302458621739/103073620277307270758400000000000000:ℝ) row002_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row002_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row002_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row002_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row002_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
