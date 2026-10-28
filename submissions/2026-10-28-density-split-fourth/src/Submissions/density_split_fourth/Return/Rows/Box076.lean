/- Fourth density transition: exact return rectangle 076.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row076_oldSmall_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(2465666101732470759431/13463316000000000:ℝ), (172034798992484500103/747962000000000:ℝ), (129049983939921976223/2692663200000000:ℝ)],
![(2140470610312300840751/6731658000000000:ℝ), (81572344931731019453/224388600000000:ℝ), (321207739944808691717/6731658000000000:ℝ)],
![(1817937039941534483291/13463316000000000:ℝ), (300534729562604727619/2243886000000000:ℝ), (0:ℝ)] ]
theorem row076_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (33267077154113283352969/56469240152064000000000:ℝ) row076_oldSmall_coefficients (21/64:ℝ) (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row076_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row076_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSmall .capP δ p := by
 rw [row076_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_oldSmall_coefficients]
def row076_oldSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(85212257259382627967/5048743500000000:ℝ), (50559756537970727159/2524371750000000:ℝ), (3946161675749433559/1009748700000000:ℝ)],
![(75916265538809271527/2524371750000000:ℝ), (8169626400324070447/252437175000000:ℝ), (9672682335667082989/2524371750000000:ℝ)],
![(67036227498257312627/5048743500000000:ℝ), (31536643948840412369/2524371750000000:ℝ), (0:ℝ)] ]
theorem row076_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (722015960448484148113/21175965057024000000000:ℝ) row076_oldSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row076_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row076_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
 rw [row076_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_oldSwitch_coefficients]
def row076_newSwitch_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(8188275313041/500000000:ℝ), (43838063113313/2250000000:ℝ), (3454938378113/900000000:ℝ)],
![(21851399136763/750000000:ℝ), (7066834378729/225000000:ℝ), (8467052588123/2250000000:ℝ)],
![(19260743792663/1500000000:ℝ), (27184239317783/2250000000:ℝ), (0:ℝ)] ]
theorem row076_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (220763715066397/6291456000000000:ℝ) row076_newSwitch_coefficients (21/64:ℝ) (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row076_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row076_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
 rw [row076_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_newSwitch_coefficients]
def row076_newTop_coefficients : Fin 3 → Fin 3 → ℝ := ![ ![(272165896227456347858843717/42780600000000000000000:ℝ), (146242644116881171857064429/21390300000000000000000:ℝ), (3388651564211486032297519/2852040000000000000000:ℝ)],
![(252257497710241683085697597/21390300000000000000000:ℝ), (24515361152797699468352981/2139030000000000000000:ℝ), (7989631747538128610796853/7130100000000000000000:ℝ)],
![(235553306676651370524582017/42780600000000000000000:ℝ), (101954320233757250634775339/21390300000000000000000:ℝ), (0:ℝ)] ]
theorem row076_newTop_identity (δ p : ℝ) : rowMargin .newTop .capP δ p =
 Record12518109.Bernstein.bsum 2 2 (303164566799718998391009643/179434841702400000000000000000:ℝ) row076_newTop_coefficients (21/64:ℝ) (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row076_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row076_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (43/128:ℝ))
 (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newTop .capP δ p := by
 rw [row076_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row076_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
