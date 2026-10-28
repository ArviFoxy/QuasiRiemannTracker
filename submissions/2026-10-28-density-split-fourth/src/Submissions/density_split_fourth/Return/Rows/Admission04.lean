/- Fourth density transition. Exact rational admission certificate.
Generated from the audited receipt; inherited Bernstein layout by Sil and Hailey Collet. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(6357/2357:ℝ), (0:ℝ)] ]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .fourthC δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (7785/4714:ℝ) admission04_00_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 0 := by
 rw [admission04_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]
def admission04_01_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(4000/2357:ℝ), (0:ℝ)] ]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .fourthC δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (2714/2357:ℝ) admission04_01_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 1 := by
 rw [admission04_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]
def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![ ![(987987/1178500:ℝ), (0:ℝ)] ]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .fourthC δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (1369013/2357000:ℝ) admission04_02_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 2 := by
 rw [admission04_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]
def admission04_03_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(13136336/11785:ℝ), (16209776/11785:ℝ), (649088/2357:ℝ)],
![(9779456/11785:ℝ), (9587456/11785:ℝ), (0:ℝ)] ]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .fourthC δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (36687/37712:ℝ) admission04_03_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 3 := by
 rw [admission04_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]
def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(853291441/5892500:ℝ), (688/5:ℝ), (0:ℝ)],
![(347648884/1473125:ℝ), (89062816/294625:ℝ), (21904208/294625:ℝ)] ]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .fourthC δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (58867559/603392000:ℝ) admission04_04_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 4 := by
 rw [admission04_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]
def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(6130889511/29462500:ℝ), (2613464789/7365625:ℝ), (210900472/1473125:ℝ)],
![(336789564/7365625:ℝ), (366080784/7365625:ℝ), (0:ℝ)] ]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .fourthC δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (50610423/377120000:ℝ) admission04_05_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 5 := by
 rw [admission04_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]
def admission04_06_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(765000944969668/128469758125:ℝ), (291697744452148/25693951625:ℝ), (695401234291072/128469758125:ℝ), (0:ℝ)],
![(968243842205248/128469758125:ℝ), (402039119411008/25693951625:ℝ), (1195119008718592/128469758125:ℝ), (6041252074752/5138790325:ℝ)] ]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .fourthC δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (1652741034951/10524242585600:ℝ) admission04_06_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 6 := by
 rw [admission04_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]
def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(12160512808859/13888622500:ℝ), (3792782750984/3472155625:ℝ), (34104851856/138886225:ℝ)],
![(2015713169756/3472155625:ℝ), (1923597213824/3472155625:ℝ), (0:ℝ)] ]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .fourthC δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (7815695217/17777436800:ℝ) admission04_07_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 7 := by
 rw [admission04_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]
def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(0:ℝ), (369495785256973/8680389062500:ℝ), (89665330076581/694431125000:ℝ), (1424741156692079/17360778125000:ℝ)],
![(3773390849465907/3472155625000:ℝ), (51946570703730461/17360778125000:ℝ), (9698280575044841/3472155625000:ℝ), (15324827693567279/17360778125000:ℝ)] ]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .fourthC δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (1049650377938641/1820409528320000000:ℝ) admission04_08_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 8 := by
 rw [admission04_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]
def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![ ![(60582009137325221/17360778125000:ℝ), (139931595154527109/17360778125000:ℝ), (12479985428211586/2170097265625:ℝ), (102661603755624/86803890625:ℝ)],
![(4269360144205282/2170097265625:ℝ), (8368704568908578/2170097265625:ℝ), (4093480702475296/2170097265625:ℝ), (0:ℝ)] ]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .fourthC δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (26790616483341/355548736000000:ℝ) admission04_09_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 9 := by
 rw [admission04_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]
def admission04_10_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(121654725548/7365625:ℝ), (778262718964/22096875:ℝ), (95905703008/4419375:ℝ), (13279276544/4419375:ℝ)],
![(223126758016/7365625:ℝ), (1385996914048/22096875:ℝ), (159740683264/4419375:ℝ), (16491659264/4419375:ℝ)],
![(94376557568/7365625:ℝ), (183149513728/7365625:ℝ), (17740767232/1473125:ℝ), (0:ℝ)] ]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .fourthC δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (1751369/150848000:ℝ) admission04_10_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 10 := by
 rw [admission04_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]
def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![ ![(11298502816341/13888622500:ℝ), (3501512412516/3472155625:ℝ), (155248938256/694431125:ℝ)],
![(1885497272964/3472155625:ℝ), (1794060868416/3472155625:ℝ), (0:ℝ)] ]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .fourthC δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (35200353137/88887184000:ℝ) admission04_11_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 11 := by
 rw [admission04_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]
def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .fourthC δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission04_12_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 12 := by
 rw [admission04_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]
def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .fourthC δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (522765643/10000000000:ℝ) admission04_13_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 13 := by
 rw [admission04_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]
def admission04_14_coefficients : Fin 1 → Fin 1 → ℝ := ![ ![(0:ℝ)] ]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .fourthC δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_14_coefficients (43/128:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission04_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .fourthC δ p 14 := by
 rw [admission04_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]
theorem admission04_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (43/128:ℝ) (3/8:ℝ))
 (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) (j : Fin 15) : 0 < admissionGuard .fourthC δ p j := by
 fin_cases j
 · exact admission04_00_pos hδ hp
 · exact admission04_01_pos hδ hp
 · exact admission04_02_pos hδ hp
 · exact admission04_03_pos hδ hp
 · exact admission04_04_pos hδ hp
 · exact admission04_05_pos hδ hp
 · exact admission04_06_pos hδ hp
 · exact admission04_07_pos hδ hp
 · exact admission04_08_pos hδ hp
 · exact admission04_09_pos hδ hp
 · exact admission04_10_pos hδ hp
 · exact admission04_11_pos hδ hp
 · exact admission04_12_pos hδ hp
 · exact admission04_13_pos hδ hp
 · exact admission04_14_pos hδ hp
end
end QRH.DensitySplitThird.Return
