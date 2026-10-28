/- Fourth density transition. Exact rational admission certificate.
Generated from the audited receipt; inherited Bernstein layout by Sil and Hailey Collet. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(6357/2357:ℝ), (0:ℝ)] ]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .fourthC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (7785/4714:ℝ) admission16_00_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 0 := by
 rw [admission16_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]
def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(4000/2357:ℝ), (0:ℝ)] ]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .fourthC δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2714/2357:ℝ) admission16_01_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 1 := by
 rw [admission16_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]
def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(987987/1178500:ℝ), (0:ℝ)] ]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .fourthC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1369013/2357000:ℝ) admission16_02_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 2 := by
 rw [admission16_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]
def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(106722592/7071:ℝ), (137434816/7071:ℝ), (10385408/2357:ℝ)],
![(75262912/7071:ℝ), (74806912/7071:ℝ), (0:ℝ)] ]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .fourthC δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (541353/603392:ℝ) admission16_03_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 3 := by
 rw [admission16_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]
def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(2827243519/1178500:ℝ), (2368:ℝ), (0:ℝ)],
![(2152762409/589250:ℝ), (1417462656/294625:ℝ), (350467328/294625:ℝ)] ]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .fourthC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (151960443/1206784000:ℝ) admission16_04_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 4 := by
 rw [admission16_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]
def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(15098108749/5892500:ℝ), (7171513388/1473125:ℝ), (3374407552/1473125:ℝ)],
![(577611947/2946250:ℝ), (311994856/1473125:ℝ), (0:ℝ)] ]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .fourthC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (572503737/6033920000:ℝ) admission16_05_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 5 := by
 rw [admission16_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]
def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(26636483052345872/77081854875:ℝ), (52614292666349776/77081854875:ℝ), (25982749003003904/77081854875:ℝ), (0:ℝ)],
![(32896684237500128/77081854875:ℝ), (70921153478710624/77081854875:ℝ), (43829144118972416/77081854875:ℝ), (386640132784128/5138790325:ℝ)] ]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .fourthC δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (3895448092827/21048485171200:ℝ) admission16_06_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 6 := by
 rw [admission16_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]
def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(87069225441919/8333173500:ℝ), (29791791269152/2083293375:ℝ), (545677629696/138886225:ℝ)],
![(26367936747113/4166586750:ℝ), (13027999311808/2083293375:ℝ), (0:ℝ)] ]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .fourthC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (105867144303/284438988800:ℝ) admission16_07_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 7 := by
 rw [admission16_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]
def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(7788114608106257/260411671875:ℝ), (152560351576411849/2604116718750:ℝ), (37364739254193952/1302058359375:ℝ), (0:ℝ)],
![(22248713929392206/260411671875:ℝ), (287482735798817423/1302058359375:ℝ), (242985397400417728/1302058359375:ℝ), (4448027691800064/86803890625:ℝ)] ]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .fourthC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (232653799230117/11377559552000000:ℝ) admission16_08_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 8 := by
 rw [admission16_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]
def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(15793934908499701/104164668750:ℝ), (985137909177621089/2604116718750:ℝ), (393686347980311072/1302058359375:ℝ), (6570342640359936/86803890625:ℝ)],
![(18431227206346639/260411671875:ℝ), (183596900873119543/1302058359375:ℝ), (91426838501094848/1302058359375:ℝ), (0:ℝ)] ]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .fourthC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (313155559508379/5688779776000000:ℝ) admission16_09_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 9 := by
 rw [admission16_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]
def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(8374637880128/2651625:ℝ), (20142235089008/2651625:ℝ), (609402817024/106065:ℝ), (693568569344/530325:ℝ)],
![(13184765846272/2651625:ℝ), (3312786595392/294625:ℝ), (6740250871808/883875:ℝ), (3591198343168/2651625:ℝ)],
![(4677241695488/2651625:ℝ), (9283882184128/2651625:ℝ), (921250121728/530325:ℝ), (0:ℝ)] ]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .fourthC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (317839049/38617088000:ℝ) admission16_10_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 10 := by
 rw [admission16_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]
def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(26805330825771/2777724500:ℝ), (9132279693808/694431125:ℝ), (2483983012096/694431125:ℝ)],
![(8183591298909/1388862250:ℝ), (4040343940384/694431125:ℝ), (0:ℝ)] ]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .fourthC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (475878122423/1422194944000:ℝ) admission16_11_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 11 := by
 rw [admission16_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]
def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .fourthC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission16_12_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 12 := by
 rw [admission16_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]
def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .fourthC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (522765643/10000000000:ℝ) admission16_13_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 13 := by
 rw [admission16_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]
def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .fourthC δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission16_14_coefficients (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission16_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 14 := by
 rw [admission16_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]
theorem admission16_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
 (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) (j : Fin 15) : 0 < admissionGuard .fourthC δ p j := by
 fin_cases j
 · exact admission16_00_pos hδ hp
 · exact admission16_01_pos hδ hp
 · exact admission16_02_pos hδ hp
 · exact admission16_03_pos hδ hp
 · exact admission16_04_pos hδ hp
 · exact admission16_05_pos hδ hp
 · exact admission16_06_pos hδ hp
 · exact admission16_07_pos hδ hp
 · exact admission16_08_pos hδ hp
 · exact admission16_09_pos hδ hp
 · exact admission16_10_pos hδ hp
 · exact admission16_11_pos hδ hp
 · exact admission16_12_pos hδ hp
 · exact admission16_13_pos hδ hp
 · exact admission16_14_pos hδ hp
end
end QRH.DensitySplitThird.Return
