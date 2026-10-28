/- Fourth density transition. Exact rational admission certificate.
Generated from the audited receipt; inherited Bernstein layout by Sil and Hailey Collet. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(6357/2357:ℝ), (0:ℝ)] ]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .fourthC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (7785/4714:ℝ) admission28_00_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 0 := by
 rw [admission28_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]
def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(4000/2357:ℝ), (0:ℝ)] ]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .fourthC δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2714/2357:ℝ) admission28_01_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 1 := by
 rw [admission28_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]
def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(987987/1178500:ℝ), (0:ℝ)] ]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .fourthC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1369013/2357000:ℝ) admission28_02_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 2 := by
 rw [admission28_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]
def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(6703264/7071:ℝ), (8530528/7071:ℝ), (649088/2357:ℝ)],
![(4689136/7071:ℝ), (4557136/7071:ℝ), (0:ℝ)] ]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .fourthC δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (247857/301696:ℝ) admission28_03_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 3 := by
 rw [admission28_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]
def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(19843987/117850:ℝ), (160:ℝ), (0:ℝ)],
![(305900689/1178500:ℝ), (95662416/294625:ℝ), (21904208/294625:ℝ)] ]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .fourthC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (4107039/30169600:ℝ) admission28_04_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 4 := by
 rw [admission28_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]
def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(956746251/5892500:ℝ), (969832101/2946250:ℝ), (958508601/5892500:ℝ)],
![(0:ℝ), (70878499/2946250:ℝ), (114906713/5892500:ℝ)] ]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .fourthC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (5019131157/96542720000:ℝ) admission28_05_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 5 := by
 rw [admission28_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]
def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(94252036921672/15416370975:ℝ), (35875456349992/3083274195:ℝ), (85392238828288/15416370975:ℝ), (0:ℝ)],
![(593205922949708/77081854875:ℝ), (245582106725276/15416370975:ℝ), (726791858797952/77081854875:ℝ), (6041252074752/5138790325:ℝ)] ]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .fourthC δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (2775564771/14221949440:ℝ) admission28_06_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 6 := by
 rw [admission28_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]
def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(525310751779/833317350:ℝ), (357642525872/416658675:ℝ), (34104851856/138886225:ℝ)],
![(2794511439889/8333173500:ℝ), (666701307064/2083293375:ℝ), (0:ℝ)] ]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .fourthC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (43341582567/142219494400:ℝ) admission28_07_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 7 := by
 rw [admission28_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]
def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(773130452942633/1041646687500:ℝ), (1439482723862341/1041646687500:ℝ), (167946797812052/260411671875:ℝ), (0:ℝ)],
![(19051477077824051/10416466875000:ℝ), (45119374718553319/10416466875000:ℝ), (4308466710808486/1302058359375:ℝ), (69500432684376/86803890625:ℝ)] ]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .fourthC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (7771044650001/284438988800000:ℝ) admission28_08_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 8 := by
 rw [admission28_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]
def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(2232306434842621/1041646687500:ℝ), (1135420000155961/208329337500:ℝ), (1168450237472668/260411671875:ℝ), (102661603755624/86803890625:ℝ)],
![(6466787558216431/10416466875000:ℝ), (12981824845842959/10416466875000:ℝ), (810348351921566/1302058359375:ℝ), (0:ℝ)] ]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .fourthC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (98830627641651/2844389888000000:ℝ) admission28_09_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 9 := by
 rw [admission28_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]
def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(34836825392/2651625:ℝ), (86643364976/2651625:ℝ), (69662517376/2651625:ℝ), (17882977792/2651625:ℝ)],
![(49144074064/2651625:ℝ), (12955514768/294625:ℝ), (29068855424/883875:ℝ), (19810407424/2651625:ℝ)],
![(11752877708/2651625:ℝ), (22961989468/2651625:ℝ), (2235288352/530325:ℝ), (0:ℝ)] ]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .fourthC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (29891609/9654272000:ℝ) admission28_10_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 10 := by
 rw [admission28_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]
def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(808689975627/1388862250:ℝ), (547523156632/694431125:ℝ), (155248938256/694431125:ℝ)],
![(866077206357/2777724500:ℝ), (206032847812/694431125:ℝ), (0:ℝ)] ]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .fourthC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (194275297327/711097472000:ℝ) admission28_11_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 11 := by
 rw [admission28_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]
def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .fourthC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission28_12_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 12 := by
 rw [admission28_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]
def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .fourthC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (522765643/10000000000:ℝ) admission28_13_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 13 := by
 rw [admission28_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]
def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .fourthC δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission28_14_coefficients (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission28_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 14 := by
 rw [admission28_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]
theorem admission28_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) (j : Fin 15) : 0 < admissionGuard .fourthC δ p j := by
 fin_cases j
 · exact admission28_00_pos hδ hp
 · exact admission28_01_pos hδ hp
 · exact admission28_02_pos hδ hp
 · exact admission28_03_pos hδ hp
 · exact admission28_04_pos hδ hp
 · exact admission28_05_pos hδ hp
 · exact admission28_06_pos hδ hp
 · exact admission28_07_pos hδ hp
 · exact admission28_08_pos hδ hp
 · exact admission28_09_pos hδ hp
 · exact admission28_10_pos hδ hp
 · exact admission28_11_pos hδ hp
 · exact admission28_12_pos hδ hp
 · exact admission28_13_pos hδ hp
 · exact admission28_14_pos hδ hp
end
end QRH.DensitySplitThird.Return
