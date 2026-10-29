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

def admission03_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission03_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission03_00_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission03_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission03_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_00_coefficients]

def admission03_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission03_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission03_01_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission03_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission03_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_01_coefficients]

def admission03_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission03_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission03_02_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission03_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission03_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_02_coefficients]

def admission03_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9532878592/38073609:ℝ), (11747945056/38073609:ℝ), (278118496/4230401:ℝ)],
![(6830401000/38073609:ℝ), (924343000/5439087:ℝ), (0:ℝ)]]
theorem admission03_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (661056265/812236992:ℝ) admission03_03_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission03_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission03_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_03_coefficients]

def admission03_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(188668138647453/5288001250000:ℝ), (32:ℝ), (0:ℝ)],
![(1308971274878017/21152005000000:ℝ), (49291917602547/661000156250:ℝ), (22851911352547/1322000312500:ℝ)]]
theorem admission03_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (68555734057641/676864160000000:ℝ) admission03_04_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission03_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission03_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_04_coefficients]

def admission03_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(140165900736041/3172800750000:ℝ), (158006566427141/1983000468750:ℝ), (44571227649547/1322000312500:ℝ)],
![(2967987357641/12691203000000:ℝ), (44766119/18130290:ℝ), (0:ℝ)]]
theorem admission03_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (41576239691359/541491328000000:ℝ) admission03_05_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission03_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission03_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_05_coefficients]

def admission03_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(94521427131604832105699/133023782203721718750:ℝ), (1191204301029454101671557/931166475426052031250:ℝ), (268629731869110138465832/465583237713026015625:ℝ), (0:ℝ)],
![(701396179620914077087657/744933180340841625000:ℝ), (1367191640058242717823257/744933180340841625000:ℝ), (95415330670239853669052/93116647542605203125:ℝ), (1247528226313752619678/10346294171400578125:ℝ)]]
theorem admission03_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (9565772013517160591771/63567631389085152000000:ℝ) admission03_06_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission03_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission03_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_06_coefficients]

def admission03_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(36990894997221642730571/201333291984011250000:ℝ), (627689759003192130109/2796295722000156250:ℝ), (60109690473650981347/1118518288800062500:ℝ)],
![(339885074181356702443/3287074154841000000:ℝ), (14870059392497146517/159788326971437500:ℝ), (0:ℝ)]]
theorem admission03_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (60109690473650981347/196347896182502400000:ℝ) admission03_07_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission03_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission03_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_07_coefficients]

def admission03_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(876271253771788715925200041/33555548664001875000000000:ℝ), (3621204492501694166618236979/100666645992005625000000000:ℝ), (153149343528710295598517107/12583330749000703125000000:ℝ), (0:ℝ)],
![(1069108747392216854739201601/5368887786240300000000000:ℝ), (37433710446149005494643571719/80533316793604500000000000:ℝ), (3671772173483410486263382121/10066664599200562500000000:ℝ), (53779820385820672712541731/559259144400031250000000:ℝ)]]
theorem admission03_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (8896983988637214224939293/2290725455462528000000000000:ℝ) admission03_08_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission03_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission03_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_08_coefficients]

def admission03_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(23679240517633870629641/67111097328003750000:ℝ), (2080802553602428759069/2516666149800140625:ℝ), (1538760505113399912109/2516666149800140625:ℝ), (12404998835165738/89481463104005:ℝ)],
![(6620230855646372260537/53688877862403000000:ℝ), (1216781157637045033787/5033332299600281250:ℝ), (1177463423256419870731/10066664599200562500:ℝ), (0:ℝ)]]
theorem admission03_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (20262669780087425261/458145091092505600000:ℝ) admission03_09_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission03_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission03_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_09_coefficients]

def admission03_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(501373033289812/594900140625:ℝ), (5575460172459248/2974500703125:ℝ), (3840062038415282/2974500703125:ℝ), (776867032405094/2974500703125:ℝ)],
![(166817750147453/118980028125:ℝ), (598987467252547/198300046875:ℝ), (388320397010188/198300046875:ℝ), (204787540010188/594900140625:ℝ)],
![(43733706048019/105760025000:ℝ), (742770025832171/951840225000:ℝ), (13858666856/38073609:ℝ), (0:ℝ)]]
theorem admission03_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (3020223402547/495077785600000:ℝ) admission03_10_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission03_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission03_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_10_coefficients]

def admission03_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(34889973915642619362781/201333291984011250000:ℝ), (2653112844813638196896/12583330749000703125:ℝ), (281530196441380181347/5592591444000312500:ℝ)],
![(2230938259893694082171/23009519083887000000:ℝ), (35696276060564783441/410884269355125000:ℝ), (0:ℝ)]]
theorem admission03_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3612457937788082793/13089859745500160000:ℝ) admission03_11_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission03_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission03_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_11_coefficients]

def admission03_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission03_12_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission03_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission03_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_12_coefficients]

def admission03_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission03_13_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission03_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission03_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_13_coefficients]

def admission03_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission03_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission03_14_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission03_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission03_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission03_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission03_14_coefficients]

theorem admission03_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission03_00_pos hδ hp
  · exact admission03_01_pos hδ hp
  · exact admission03_02_pos hδ hp
  · exact admission03_03_pos hδ hp
  · exact admission03_04_pos hδ hp
  · exact admission03_05_pos hδ hp
  · exact admission03_06_pos hδ hp
  · exact admission03_07_pos hδ hp
  · exact admission03_08_pos hδ hp
  · exact admission03_09_pos hδ hp
  · exact admission03_10_pos hδ hp
  · exact admission03_11_pos hδ hp
  · exact admission03_12_pos hδ hp
  · exact admission03_13_pos hδ hp
  · exact admission03_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
