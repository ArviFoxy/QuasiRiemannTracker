/- Fourth density transition. Exact rational admission certificate.
Generated from the audited receipt; inherited Bernstein layout by Sil and Hailey Collet. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def admission26_00_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(6357/2357:ℝ), (0:ℝ)] ]
theorem admission26_00_identity (δ p : ℝ) : admissionGuard .fourthC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (7785/4714:ℝ) admission26_00_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 0 := by
 rw [admission26_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_00_coefficients]
def admission26_01_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(4000/2357:ℝ), (0:ℝ)] ]
theorem admission26_01_identity (δ p : ℝ) : admissionGuard .fourthC δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2714/2357:ℝ) admission26_01_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 1 := by
 rw [admission26_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_01_coefficients]
def admission26_02_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(987987/1178500:ℝ), (0:ℝ)] ]
theorem admission26_02_identity (δ p : ℝ) : admissionGuard .fourthC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1369013/2357000:ℝ) admission26_02_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 2 := by
 rw [admission26_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_02_coefficients]
def admission26_03_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(26718784/7071:ℝ), (34279840/7071:ℝ), (2596352/2357:ℝ)],
![(18784000/7071:ℝ), (18544000/7071:ℝ), (0:ℝ)] ]
theorem admission26_03_identity (δ p : ℝ) : admissionGuard .fourthC δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (131535/150848:ℝ) admission26_03_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 3 := by
 rw [admission26_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_03_coefficients]
def admission26_04_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(735299753/1178500:ℝ), (608:ℝ), (0:ℝ)],
![(281116767/294625:ℝ), (363793664/294625:ℝ), (87616832/294625:ℝ)] ]
theorem admission26_04_identity (δ p : ℝ) : admissionGuard .fourthC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (78033741/603392000:ℝ) admission26_04_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 4 := by
 rw [admission26_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_04_coefficients]
def admission26_05_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(3640024643/5892500:ℝ), (353040498/294625:ℝ), (843601888/1473125:ℝ)],
![(417693/58925:ℝ), (181176/11785:ℝ), (0:ℝ)] ]
theorem admission26_05_identity (δ p : ℝ) : admissionGuard .fourthC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (24670803/301696000:ℝ) admission26_05_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 5 := by
 rw [admission26_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_05_coefficients]
def admission26_06_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(694349302994744/15416370975:ℝ), (6773002339934552/77081854875:ℝ), (3303792267960832/77081854875:ℝ), (0:ℝ)],
![(863033164793888/15416370975:ℝ), (1835617187008288/15416370975:ℝ), (1118108060008448/15416370975:ℝ), (48330016598016/5138790325:ℝ)] ]
theorem admission26_06_identity (δ p : ℝ) : admissionGuard .fourthC δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1983122007789/10524242585600:ℝ) admission26_06_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 6 := by
 rw [admission26_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_06_coefficients]
def admission26_07_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(4305020376149/1666634700:ℝ), (7349582050672/2083293375:ℝ), (136419407424/138886225:ℝ)],
![(125341694023/83331735:ℝ), (612053658944/416658675:ℝ), (0:ℝ)] ]
theorem admission26_07_identity (δ p : ℝ) : admissionGuard .fourthC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (4973624229/14221949440:ℝ) admission26_07_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 7 := by
 rw [admission26_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_07_coefficients]
def admission26_08_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(23136894506813021/5208233437500:ℝ), (8899467679679939/1041646687500:ℝ), (5353018908676856/1302058359375:ℝ), (0:ℝ)],
![(622042113690323/52082334375:ℝ), (7787088259633829/260411671875:ℝ), (6347605535771488/260411671875:ℝ), (556003461475008/86803890625:ℝ)] ]
theorem admission26_08_identity (δ p : ℝ) : admissionGuard .fourthC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (129358230743379/5688779776000000:ℝ) admission26_08_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 8 := by
 rw [admission26_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_08_coefficients]
def admission26_09_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(95706360243593791/5208233437500:ℝ), (48000554356024651/1041646687500:ℝ), (48386532164661496/1302058359375:ℝ), (821292830044992/86803890625:ℝ)],
![(1979816335020341/260411671875:ℝ), (3937248694953757/260411671875:ℝ), (1955966429376416/260411671875:ℝ), (0:ℝ)] ]
theorem admission26_09_identity (δ p : ℝ) : admissionGuard .fourthC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (13732872905001/284438988800000:ℝ) admission26_09_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 9 := by
 rw [admission26_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_09_coefficients]
def admission26_10_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(7154468632/35355:ℝ), (1304311947448/2651625:ℝ), (1007498663552/2651625:ℝ), (239869333504/2651625:ℝ)],
![(32731051456/106065:ℝ), (125033887168/176775:ℝ), (29162568704/58925:ℝ), (51057754112/530325:ℝ)],
![(10553898112/106065:ℝ), (20806911872/106065:ℝ), (2049738752/21213:ℝ), (0:ℝ)] ]
theorem admission26_10_identity (δ p : ℝ) : admissionGuard .fourthC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (648193/96542720:ℝ) admission26_10_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 10 := by
 rw [admission26_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_10_coefficients]
def admission26_11_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(6627230370621/2777724500:ℝ), (2252077491144/694431125:ℝ), (620995753024/694431125:ℝ)],
![(194448531871/138886225:ℝ), (189620224096/138886225:ℝ), (0:ℝ)] ]
theorem admission26_11_identity (δ p : ℝ) : admissionGuard .fourthC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (893537893/2844389888:ℝ) admission26_11_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 11 := by
 rw [admission26_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_11_coefficients]
def admission26_12_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission26_12_identity (δ p : ℝ) : admissionGuard .fourthC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission26_12_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 12 := by
 rw [admission26_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_12_coefficients]
def admission26_13_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission26_13_identity (δ p : ℝ) : admissionGuard .fourthC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (522765643/10000000000:ℝ) admission26_13_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 13 := by
 rw [admission26_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_13_coefficients]
def admission26_14_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission26_14_identity (δ p : ℝ) : admissionGuard .fourthC δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission26_14_coefficients (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission26_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission26_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 14 := by
 rw [admission26_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission26_14_coefficients]
theorem admission26_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
 (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) (j : Fin 15) : 0 < admissionGuard .fourthC δ p j := by
 fin_cases j
 · exact admission26_00_pos hδ hp
 · exact admission26_01_pos hδ hp
 · exact admission26_02_pos hδ hp
 · exact admission26_03_pos hδ hp
 · exact admission26_04_pos hδ hp
 · exact admission26_05_pos hδ hp
 · exact admission26_06_pos hδ hp
 · exact admission26_07_pos hδ hp
 · exact admission26_08_pos hδ hp
 · exact admission26_09_pos hδ hp
 · exact admission26_10_pos hδ hp
 · exact admission26_11_pos hδ hp
 · exact admission26_12_pos hδ hp
 · exact admission26_13_pos hδ hp
 · exact admission26_14_pos hδ hp
end
end QRH.DensitySplitThird.Return
