/- Fourth density transition: exact return rectangle 001.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row001_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(63870471653025503714778860908/1075351398558423046875:ℝ), (190851825485600627272812633488/1075351398558423046875:ℝ), (190093864131658582997072637952/1075351398558423046875:ℝ), (2337500341991876361196404736/39827829576237890625:ℝ)],
![(50917532495746694821337860352/1075351398558423046875:ℝ), (151522454255598604884767205376/1075351398558423046875:ℝ), (150295855259496485190621495296/1075351398558423046875:ℝ), (1840404834641620251166375936/39827829576237890625:ℝ)],
![(448995912553165985855647744/1075351398558423046875:ℝ), (896214373151223657658892288/1075351398558423046875:ℝ), (447220522734286086203244544/1075351398558423046875:ℝ), (0:ℝ)] ]
theorem row001_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (255816931092462667823/3021014628597600000000:ℝ) row001_oldSmall_coefficients (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row001_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row001_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_oldSmall_coefficients]
def row001_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(616868062335479021286045772/1075351398558423046875:ℝ), (347628527102399977192561616/215070279711684609375:ℝ), (180711430044352829957103616/119483488728713671875:ℝ), (56125260616527439695970304/119483488728713671875:ℝ)],
![(57200022034229933602422016/215070279711684609375:ℝ), (114017835500733117404710912/215070279711684609375:ℝ), (77940113983156862746624/295020959823984375:ℝ), (0:ℝ)],
![(3830341727728320970518212608/1075351398558423046875:ℝ), (2257797811958925193488613376/215070279711684609375:ℝ), (1232024253446858795887099904/119483488728713671875:ℝ), (403285456308199527962116096/119483488728713671875:ℝ)] ]
theorem row001_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (448531016614570592153/38668987246049280000000:ℝ) row001_oldSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row001_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row001_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_oldSwitch_coefficients]
def row001_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1569142074742153288012/2875417196484375:ℝ), (881747707520736016336/575083439296875:ℝ), (4111929786982183297024/2875417196484375:ℝ), (47123364736017891328/106496933203125:ℝ)],
![(152529081569166228736/575083439296875:ℝ), (304060048399739389952/575083439296875:ℝ), (151532344916513161216/575083439296875:ℝ), (0:ℝ)],
![(10195316428198031699968/2875417196484375:ℝ), (6008976418536186167296/575083439296875:ℝ), (29507130785699652960256/2875417196484375:ℝ), (357687419550901993472/106496933203125:ℝ)] ]
theorem row001_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (1323483793670413/103398266880000000:ℝ) row001_newSwitch_coefficients (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row001_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row001_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_newSwitch_coefficients]
def row001_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(18326011391095934545686112067371/273360162035376562500000000:ℝ), (9121889116790289109649606821817/68340040508844140625000000:ℝ), (70944447938873239602097962712/1067813132950689697265625:ℝ), (0:ℝ)],
![(15188988718996074820559534615129/4271252531802758789062500:ℝ), (11163005953926090928904209455298/1067813132950689697265625:ℝ), (2187205646171463622117658105344/213562626590137939453125:ℝ), (14692456450988383169734299136/4394292728192138671875:ℝ)],
![(7258359870985919533087189235596/1067813132950689697265625:ℝ), (21589014259532455333125103562288/1067813132950689697265625:ℝ), (21404149259552039444309725196032/1067813132950689697265625:ℝ), (5821805024429611143066565376/878858545638427734375:ℝ)] ]
theorem row001_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (459838096996156805169927163/1572778629719654400000000000000:ℝ) row001_newTop_coefficients (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row001_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row001_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
 (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row001_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row001_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
