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

def admission10_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission10_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission10_00_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission10_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission10_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_00_coefficients]

def admission10_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission10_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission10_01_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission10_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission10_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_01_coefficients]

def admission10_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission10_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission10_02_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission10_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission10_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_02_coefficients]

def admission10_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(332045794432/5439087:ℝ), (2959705575808/38073609:ℝ), (71198334976/4230401:ℝ)],
![(239894995456/5439087:ℝ), (1673792968192/38073609:ℝ), (0:ℝ)]]
theorem admission10_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (388920841/464135424:ℝ) admission10_03_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission10_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission10_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_03_coefficients]

def admission10_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8180726215942359/846080200000:ℝ), (9600:ℝ), (0:ℝ)],
![(15042324651861947/1057600250000:ℝ), (6140149413126016/330500078125:ℝ), (1462522326563008/330500078125:ℝ)]]
theorem admission10_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (205667202172923/1732772249600000:ℝ) admission10_04_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission10_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission10_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_04_coefficients]

def admission10_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(635329334170916611/63456015000000:ℝ), (18517940651941048/991500234375:ℝ), (2852558569571008/330500078125:ℝ)],
![(19419666710087179/15864003750000:ℝ), (1425618880928/1133143125:ℝ), (0:ℝ)]]
theorem admission10_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (965238476775821/10829826560000000:ℝ) admission10_05_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission10_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission10_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_05_coefficients]

def admission10_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(245974920389205606331726766/93116647542605203125:ℝ), (488567189650824740531672494/93116647542605203125:ℝ), (242606716422800384199945728/93116647542605203125:ℝ), (0:ℝ)],
![(1470234445636026839097967576/465583237713026015625:ℝ), (3153331470546357052528856024/465583237713026015625:ℝ), (1913114626534466096289937408/465583237713026015625:ℝ), (5109875614981130730201088/10346294171400578125:ℝ)]]
theorem admission10_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (134792411213525806509481/813665681780289945600000:ℝ) admission10_06_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission10_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission10_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_06_coefficients]

def admission10_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6390205010275333117028149/161066633587209000000:ℝ), (14891149126595944526644/279629572200015625:ℝ), (3847020190313662806208/279629572200015625:ℝ)],
![(5140280047252436675679329/201333291984011250000:ℝ), (35450221591713197296528/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission10_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (8956343880573996220703/27488705465550336000000:ℝ) admission10_07_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission10_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission10_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_07_coefficients]

def admission10_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(395094171058250120787174664801/1677777433200093750000000:ℝ), (2344344639985396465987509981913/5033332299600281250000000:ℝ), (1811375594650975388008296709/7864581718125439453125:ℝ), (0:ℝ)],
![(1354743556220773294219140381149/2097221791500117187500000:ℝ), (10572625720022274554695264552181/6291665374500351562500000:ℝ), (280838925922150320434924270452/196614542953135986328125:ℝ), (1720954252346261526801335392/4369212065625244140625:ℝ)]]
theorem admission10_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (3750625676807782255855987/234570286639362867200000000:ℝ) admission10_08_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission10_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission10_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_08_coefficients]

def admission10_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2941220971011137973829771/2556613231543000000:ℝ), (147188560577668095069904/51360533669390625:ℝ), (5745975419753050825294144/2516666149800140625:ℝ), (50810875228838862848/89481463104005:ℝ)],
![(1796960026184366163419039/3195766539428750000:ℝ), (57619449976815095259712/51360533669390625:ℝ), (1408190766938732207521024/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission10_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (13240052218331082917/261797194910003200000:ℝ) admission10_09_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission10_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission10_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_09_coefficients]

def admission10_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(140705591218823296646/2974500703125:ℝ), (112887229635602390146/991500234375:ℝ), (85316989089641936896/991500234375:ℝ), (57996768018441936896/2974500703125:ℝ)],
![(222410958764181398192/2974500703125:ℝ), (502358668019508042416/2974500703125:ℝ), (338952631228445966336/2974500703125:ℝ), (59008769473119322112/2974500703125:ℝ)],
![(26883929846142287392/991500234375:ℝ), (160578227701102062176/2974500703125:ℝ), (3653690914865152/135977175:ℝ), (0:ℝ)]]
theorem admission10_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (10380965593410557/1386217799680000000:ℝ) admission10_10_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission10_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission10_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_10_coefficients]

def admission10_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(29930403218507472276322423/805333167936045000000:ℝ), (627623871133108342125494/12583330749000703125:ℝ), (18017932572248331606208/1398147861000078125:ℝ)],
![(4812457495599993795062431/201333291984011250000:ℝ), (298612628729076279006488/12583330749000703125:ℝ), (0:ℝ)]]
theorem admission10_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (13488193371582430319541/45814509109250560000000:ℝ) admission10_11_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission10_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission10_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_11_coefficients]

def admission10_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission10_12_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission10_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission10_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_12_coefficients]

def admission10_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission10_13_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission10_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission10_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_13_coefficients]

def admission10_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission10_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission10_14_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission10_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission10_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission10_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission10_14_coefficients]

theorem admission10_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission10_00_pos hδ hp
  · exact admission10_01_pos hδ hp
  · exact admission10_02_pos hδ hp
  · exact admission10_03_pos hδ hp
  · exact admission10_04_pos hδ hp
  · exact admission10_05_pos hδ hp
  · exact admission10_06_pos hδ hp
  · exact admission10_07_pos hδ hp
  · exact admission10_08_pos hδ hp
  · exact admission10_09_pos hδ hp
  · exact admission10_10_pos hδ hp
  · exact admission10_11_pos hδ hp
  · exact admission10_12_pos hδ hp
  · exact admission10_13_pos hδ hp
  · exact admission10_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
