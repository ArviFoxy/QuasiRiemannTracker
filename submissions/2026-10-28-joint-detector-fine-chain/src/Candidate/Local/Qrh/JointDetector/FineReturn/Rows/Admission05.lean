/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.PowerAdmissions
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn
open QRH.Record1252270103Return
noncomputable section

def admission05_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission05_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission05_00_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission05_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission05_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_00_coefficients]

def admission05_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission05_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission05_01_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission05_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission05_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_01_coefficients]

def admission05_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission05_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission05_02_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission05_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission05_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_02_coefficients]

def admission05_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37084692112/38073609:ℝ), (6635565424/5439087:ℝ), (1112473984/4230401:ℝ)],
![(26601604000/38073609:ℝ), (3697372000/5439087:ℝ), (0:ℝ)]]
theorem admission05_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (661056265/812236992:ℝ) admission05_03_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission05_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission05_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_03_coefficients]

def admission05_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3220957607827077/21152005000000:ℝ), (144:ℝ), (0:ℝ)],
![(2520682056518769/10576002500000:ℝ), (98583835205094/330500078125:ℝ), (22851911352547/330500078125:ℝ)]]
theorem admission05_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (617001606518769/5414913280000000:ℝ) admission05_04_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission05_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission05_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_04_coefficients]

def admission05_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10170468420855793/63456015000000:ℝ), (296616543641407/991500234375:ℝ), (44571227649547/330500078125:ℝ)],
![(34304270657641/6345601500000:ℝ), (89532238/9065145:ℝ), (0:ℝ)]]
theorem admission05_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (41576239691359/541491328000000:ℝ) admission05_05_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission05_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission05_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_05_coefficients]

def admission05_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(10288118106825177166550273/1862332950852104062500:ℝ), (3898017222935484403404653/372466590170420812500:ℝ), (2309160298671811212618248/465583237713026015625:ℝ), (0:ℝ)],
![(1281222184078652529206441/186233295085210406250:ℝ), (2624370833898309810677641/186233295085210406250:ℝ), (763322645361918829352416/93116647542605203125:ℝ), (9980225810510020957424/10346294171400578125:ℝ)]]
theorem admission05_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (82140053126549171522719/508541051112681216000000:ℝ) admission05_06_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission05_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission05_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_06_coefficients]

def admission05_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(75747735747921803072533/115047595419435000000:ℝ), (339561214497184885969/399470817428593750:ℝ), (60109690473650981347/279629572200015625:ℝ)],
![(4520484071789086015549/11504759541943500000:ℝ), (14870059392497146517/39947081742859375:ℝ), (0:ℝ)]]
theorem admission05_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (60109690473650981347/196347896182502400000:ℝ) admission05_07_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission05_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission05_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_07_coefficients]

def admission05_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(86536576244074245637355417551/201333291984011250000000000:ℝ), (17411496218349349197977339351/22370365776001250000000000:ℝ), (4450906737360311981324711663/12583330749000703125000000:ℝ), (0:ℝ)],
![(5961163663822501159402062491/4026665839680225000000000:ℝ), (8105464757245449184782184207/2237036577600125000000000:ℝ), (3671772173483410486263382121/1258333074900070312500000:ℝ), (53779820385820672712541731/69907393050003906250000:ℝ)]]
theorem admission05_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (232515333066559731937139537/18325803643700224000000000000:ℝ) admission05_08_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission05_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission05_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_08_coefficients]

def admission05_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1942241576434299643305107/805333167936045000000:ℝ), (4934745087328713452864/838888716600046875:ℝ), (11519192550578456094167/2516666149800140625:ℝ), (99239990681325904/89481463104005:ℝ)],
![(77637104383427275794491/80533316793604500000:ℝ), (1596163053928976603012/838888716600046875:ℝ), (2354926846512839741462/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission05_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (20262669780087425261/458145091092505600000:ℝ) admission05_09_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission05_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission05_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_09_coefficients]

def admission05_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(21335502279347453/1699714687500:ℝ), (116743987713939449/3966000937500:ℝ), (3076188674106896/141642890625:ℝ), (14406437859648272/2974500703125:ℝ)],
![(1672671413747453/84985734375:ℝ), (8714502152852729/198300046875:ℝ), (17699257202489024/594900140625:ℝ), (3276600640163008/594900140625:ℝ)],
![(105917146547453/16997146875:ℝ), (478567789544057/39660009375:ℝ), (221738669696/38073609:ℝ), (0:ℝ)]]
theorem admission05_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (3020223402547/495077785600000:ℝ) admission05_10_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission05_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission05_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_10_coefficients]

def admission05_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(23711762199675635075561/38349198473145000000:ℝ), (1145873641863918972763/1438094942742937500:ℝ), (281530196441380181347/1398147861000078125:ℝ)],
![(1409976573095107318289/3834919847314500000:ℝ), (35696276060564783441/102721067338781250:ℝ), (0:ℝ)]]
theorem admission05_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3612457937788082793/13089859745500160000:ℝ) admission05_11_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission05_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission05_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_11_coefficients]

def admission05_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission05_12_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission05_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission05_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_12_coefficients]

def admission05_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission05_13_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission05_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission05_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_13_coefficients]

def admission05_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission05_14_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission05_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission05_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission05_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission05_14_coefficients]

theorem admission05_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission05_00_pos hδ hp
  · exact admission05_01_pos hδ hp
  · exact admission05_02_pos hδ hp
  · exact admission05_03_pos hδ hp
  · exact admission05_04_pos hδ hp
  · exact admission05_05_pos hδ hp
  · exact admission05_06_pos hδ hp
  · exact admission05_07_pos hδ hp
  · exact admission05_08_pos hδ hp
  · exact admission05_09_pos hδ hp
  · exact admission05_10_pos hδ hp
  · exact admission05_11_pos hδ hp
  · exact admission05_12_pos hδ hp
  · exact admission05_13_pos hδ hp
  · exact admission05_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
