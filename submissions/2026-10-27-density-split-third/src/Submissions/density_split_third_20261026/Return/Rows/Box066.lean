/- Fourth density transition: exact return rectangle 066.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_third_20261026.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row066_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(53512582174895088553609/84145725000000000:ℝ), (103462933582736638728521/84145725000000000:ℝ), (2664215123919094757563/4487772000000000:ℝ)],
![(581639211088420955713/876517968750000:ℝ), (3268369269263289327791/2629553906250000:ℝ), (81263947223119362869/140242875000000:ℝ)],
![(54867497520212951951/1314776953125000:ℝ), (27400559886579377797/657388476562500:ℝ), (0:ℝ)] ]
theorem row066_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (476306989297399020587/941154002534400000000:ℝ) row066_oldSmall_coefficients (43/128:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row066_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row066_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row066_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_oldSmall_coefficients]
def row066_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(1609187374794477992593/31554646875000000:ℝ), (1034705664198441266459/10518215625000000:ℝ), (26594139603573154289/560971500000000:ℝ)],
![(49699436363436992603/986082714843750:ℝ), (30624044935806693389/328694238281250:ℝ), (750935255183943967/17530359375000:ℝ)],
![(660465628501513709/164347119140625:ℝ), (654354160531040926/164347119140625:ℝ), (0:ℝ)] ]
theorem row066_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (3202032984032738497/117644250316800000000:ℝ) row066_oldSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row066_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row066_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row066_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_oldSwitch_coefficients]
def row066_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(468844984671517/9375000000:ℝ), (2714574208985239/28125000000:ℝ), (69807610301669/1500000000:ℝ)],
![(43365902462621/878906250:ℝ), (80236467342769/878906250:ℝ), (1969528448107/46875000:ℝ)],
![(1712606377489/439453125:ℝ), (1696798513846/439453125:ℝ), (0:ℝ)] ]
theorem row066_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (8925443125237/314572800000000:ℝ) row066_newSwitch_coefficients (43/128:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row066_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row066_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row066_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_newSwitch_coefficients]
def row066_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(2303144029845789768893495797/1641176337890625000000:ℝ), (13416809930503793971286678851/3282352675781250000000:ℝ), (26047871335685180223572118599/6564705351562500000000:ℝ), (3370682653443563224561959109/2625882140625000000000:ℝ)],
![(63399237194116803407586667/51286760559082031250:ℝ), (353251281123350867899224751/102573521118164062500:ℝ), (217844715185151208724147213/68382347412109375000:ℝ), (80248037193571084527283997/82058816894531250000:ℝ)],
![(7470615047869275776614271/51286760559082031250:ℝ), (14752806735486913383902929/51286760559082031250:ℝ), (7283369236635041237911283/51286760559082031250:ℝ), (0:ℝ)] ]
theorem row066_newTop_identity (δ p : ℝ) : rowMargin .newTop .fourthC δ p =
 Record12518109.Bernstein.bsum 2 3 (50873820341819277220199849/70487986982092800000000000000:ℝ) row066_newTop_coefficients (43/128:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row066_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row066_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .fourthC δ p := by
 rw [row066_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row066_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
