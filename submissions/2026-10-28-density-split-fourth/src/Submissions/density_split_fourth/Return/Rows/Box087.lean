/- Fourth density transition: exact return rectangle 087.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row087_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(1351250298640894391662734076/119483488728713671875:ℝ), (4032359439098598834948358388/119483488728713671875:ℝ), (4010967982274514494908514548/119483488728713671875:ℝ), (16418010392800124094109756/1475104799119921875:ℝ)],
![(1182947241278317772107985912/119483488728713671875:ℝ), (701970173792806181168036552/23896697745742734375:ℝ), (3470901105094486134437671784/119483488728713671875:ℝ), (14123425647021888897598456/1475104799119921875:ℝ)],
![(16993732579419186068099836/119483488728713671875:ℝ), (33953899717838470433421572/119483488728713671875:ℝ), (16960185262663479413759236/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row087_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (46268548747955071423527289/87993428755454361600000000:ℝ) row087_oldSmall_coefficients (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row087_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row087_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row087_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row087_oldSmall_coefficients]
def row087_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(175966730231634378964314076/119483488728713671875:ℝ), (525945111723338453505898388/119483488728713671875:ℝ), (523990032751773770118854548/119483488728713671875:ℝ), (2148291990865057970089756/1475104799119921875:ℝ)],
![(118246126355994617891945912/119483488728713671875:ℝ), (70467019511709348123596552/23896697745742734375:ℝ), (349935764302741060641391784/119483488728713671875:ℝ), (1430207322224554789078456/1475104799119921875:ℝ)],
![(1190981404382433918479836/119483488728713671875:ℝ), (2373877885108722471681572/119483488728713671875:ℝ), (1182912671775757039139236/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row087_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (2771262522111098381772289/87993428755454361600000000:ℝ) row087_oldSwitch_coefficients (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row087_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row087_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row087_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row087_oldSwitch_coefficients]
def row087_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(463975018193252299996/319490799609375:ℝ), (1386697305117712883348/319490799609375:ℝ), (1381469555655668866708/319490799609375:ℝ), (5663546527545781276/3944330859375:ℝ)],
![(311282419293222016952/319490799609375:ℝ), (185499026000580144392/63898159921875:ℝ), (921152622106680337064/319490799609375:ℝ), (3764690264160513976/3944330859375:ℝ)],
![(3140126582246324956/319490799609375:ℝ), (6259521465246699812/319490799609375:ℝ), (3119437011986312356/319490799609375:ℝ), (0:ℝ)] ]
theorem row087_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (7592062739127807169/235288500633600000000:ℝ) row087_newSwitch_coefficients (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row087_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row087_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row087_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row087_newSwitch_coefficients]
def row087_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(26116663805836041833329948358959/30373351337264062500000000:ℝ), (78150431319223600102228649044877/30373351337264062500000000:ℝ), (77950871220939074704467453012877/30373351337264062500000000:ℝ), (319964243303105141179861139839/374979646139062500000000:ℝ)],
![(6647279092788734292732857461999/15186675668632031250000000:ℝ), (19919883510743461647939038397197/15186675668632031250000000:ℝ), (19898102298721609821948633855037/15186675668632031250000000:ℝ), (81796270132924474898054974319/187489823069531250000000:ℝ)],
![(56648824428436381235134477999/30373351337264062500000000:ℝ), (111717646932494627260905889361/30373351337264062500000000:ℝ), (55072796731991983279122770737/30373351337264062500000000:ℝ), (0:ℝ)] ]
theorem row087_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (225339060725363334373241549449/89473628712940339200000000000000:ℝ) row087_newTop_coefficients (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row087_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row087_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row087_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row087_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
