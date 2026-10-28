/- Fourth density transition. Exact rational admission certificate.
Generated from the audited receipt; inherited Bernstein layout by Sil and Hailey Collet. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def admission18_00_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(6357/2357:ℝ), (0:ℝ)] ]
theorem admission18_00_identity (δ p : ℝ) : admissionGuard .fourthC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (7785/4714:ℝ) admission18_00_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 0 := by
 rw [admission18_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_00_coefficients]
def admission18_01_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(4000/2357:ℝ), (0:ℝ)] ]
theorem admission18_01_identity (δ p : ℝ) : admissionGuard .fourthC δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2714/2357:ℝ) admission18_01_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 1 := by
 rw [admission18_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_01_coefficients]
def admission18_02_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(987987/1178500:ℝ), (0:ℝ)] ]
theorem admission18_02_identity (δ p : ℝ) : admissionGuard .fourthC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1369013/2357000:ℝ) admission18_02_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 2 := by
 rw [admission18_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_02_coefficients]
def admission18_03_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(426002368/7071:ℝ), (549739264/7071:ℝ), (41541632/2357:ℝ)],
![(300758560/7071:ℝ), (299858560/7071:ℝ), (0:ℝ)] ]
theorem admission18_03_identity (δ p : ℝ) : admissionGuard .fourthC δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (2180625/2413568:ℝ) admission18_03_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 3 := by
 rw [admission18_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_03_coefficients]
def admission18_04_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(5617931519/589250:ℝ), (9472:ℝ), (0:ℝ)],
![(16995176273/1178500:ℝ), (5632138624/294625:ℝ), (1401869312/294625:ℝ)] ]
theorem admission18_04_identity (δ p : ℝ) : admissionGuard .fourthC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (151960443/1206784000:ℝ) admission18_04_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 4 := by
 rw [admission18_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_04_coefficients]
def admission18_05_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(30286532093/2946250:ℝ), (28686053552/1473125:ℝ), (13497630208/1473125:ℝ)],
![(1138894999/1178500:ℝ), (293877256/294625:ℝ), (0:ℝ)] ]
theorem admission18_05_identity (δ p : ℝ) : admissionGuard .fourthC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (18952821/193085440:ℝ) admission18_05_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 5 := by
 rw [admission18_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_05_coefficients]
def admission18_06_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(210467049443399104/77081854875:ℝ), (418319162689430336/77081854875:ℝ), (207861992024031232/77081854875:ℝ), (0:ℝ)],
![(51736021709728928/15416370975:ℝ), (22444643069143904/3083274195:ℝ), (69768559277809664/15416370975:ℝ), (3093121062273024/5138790325:ℝ)] ]
theorem admission18_06_identity (δ p : ℝ) : admissionGuard .fourthC δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (3895448092827/21048485171200:ℝ) admission18_06_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 6 := by
 rw [admission18_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_06_coefficients]
def admission18_07_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(173495732736767/4166586750:ℝ), (119167165076608/2083293375:ℝ), (2182710518784/138886225:ℝ)],
![(42572457582941/1666634700:ℝ), (10579784676032/416658675:ℝ), (0:ℝ)] ]
theorem admission18_07_identity (δ p : ℝ) : admissionGuard .fourthC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (85972647387/227551191040:ℝ) admission18_07_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 7 := by
 rw [admission18_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_07_coefficients]
def admission18_08_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(305170976165862323/1302058359375:ℝ), (604038617186375314/1302058359375:ℝ), (298917914033551616/1302058359375:ℝ), (0:ℝ)],
![(344407042522451321/520823343750:ℝ), (89969954482179967/52082334375:ℝ), (384409106228491648/260411671875:ℝ), (35584221534400512/86803890625:ℝ)] ]
theorem admission18_08_identity (δ p : ℝ) : admissionGuard .fourthC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (232653799230117/11377559552000000:ℝ) admission18_08_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 8 := by
 rw [admission18_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_08_coefficients]
def admission18_09_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(1576028140218341518/1302058359375:ℝ), (3937104926932942274/1302058359375:ℝ), (3149490783842488576/1302058359375:ℝ), (52562741122879488/86803890625:ℝ)],
![(152194677418704437/260411671875:ℝ), (303758388790460227/260411671875:ℝ), (30311642826433408/52082334375:ℝ), (0:ℝ)] ]
theorem admission18_09_identity (δ p : ℝ) : admissionGuard .fourthC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (2065792543107/36408190566400:ℝ) admission18_09_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 9 := by
 rw [admission18_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_09_coefficients]
def admission18_10_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(26481363089344/530325:ℝ), (318710247285632/2651625:ℝ), (240800594894848/2651625:ℝ), (54498641575936/2651625:ℝ)],
![(8382323130176/106065:ℝ), (94682795440768/530325:ℝ), (63867677499392/530325:ℝ), (11097097109504/530325:ℝ)],
![(203004339664/7071:ℝ), (404447857184/7071:ℝ), (201439467520/7071:ℝ), (0:ℝ)] ]
theorem admission18_10_identity (δ p : ℝ) : admissionGuard .fourthC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (42406797/4942987264:ℝ) admission18_10_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 10 := by
 rw [admission18_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_10_coefficients]
def admission18_11_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(53398517552619/1388862250:ℝ), (36529118775232/694431125:ℝ), (9935932048384/694431125:ℝ)],
![(13211042363041/555544900:ℝ), (131274521760/5555449:ℝ), (0:ℝ)] ]
theorem admission18_11_identity (δ p : ℝ) : admissionGuard .fourthC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (386524333123/1137755955200:ℝ) admission18_11_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 11 := by
 rw [admission18_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_11_coefficients]
def admission18_12_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission18_12_identity (δ p : ℝ) : admissionGuard .fourthC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission18_12_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 12 := by
 rw [admission18_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_12_coefficients]
def admission18_13_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission18_13_identity (δ p : ℝ) : admissionGuard .fourthC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (522765643/10000000000:ℝ) admission18_13_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 13 := by
 rw [admission18_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_13_coefficients]
def admission18_14_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission18_14_identity (δ p : ℝ) : admissionGuard .fourthC δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission18_14_coefficients (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission18_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission18_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 14 := by
 rw [admission18_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission18_14_coefficients]
theorem admission18_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0 < admissionGuard .fourthC δ p j := by
 fin_cases j
 · exact admission18_00_pos hδ hp
 · exact admission18_01_pos hδ hp
 · exact admission18_02_pos hδ hp
 · exact admission18_03_pos hδ hp
 · exact admission18_04_pos hδ hp
 · exact admission18_05_pos hδ hp
 · exact admission18_06_pos hδ hp
 · exact admission18_07_pos hδ hp
 · exact admission18_08_pos hδ hp
 · exact admission18_09_pos hδ hp
 · exact admission18_10_pos hδ hp
 · exact admission18_11_pos hδ hp
 · exact admission18_12_pos hδ hp
 · exact admission18_13_pos hδ hp
 · exact admission18_14_pos hδ hp
end
end QRH.DensitySplitThird.Return
