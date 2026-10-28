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

def admission14_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission14_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission14_00_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission14_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission14_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_00_coefficients]

def admission14_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission14_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission14_01_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission14_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission14_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_01_coefficients]

def admission14_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission14_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission14_02_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission14_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission14_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_02_coefficients]

def admission14_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(36613869856/38073609:ℝ), (45906135712/38073609:ℝ), (1112473984/4230401:ℝ)],
![(26130781744/38073609:ℝ), (25338781744/38073609:ℝ), (0:ℝ)]]
theorem admission14_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1243891703/1624473984:ℝ) admission14_03_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission14_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission14_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_03_coefficients]

def admission14_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(357884178647453/2115200500000:ℝ), (160:ℝ), (0:ℝ)],
![(5399248291684991/21152005000000:ℝ), (103871836455094/330500078125:ℝ), (22851911352547/330500078125:ℝ)]]
theorem admission14_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (68555734057641/541491328000000:ℝ) admission14_04_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission14_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission14_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_04_coefficients]

def admission14_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(467972653060923/3021715000000:ℝ), (9797745840702973/31728007500000:ℝ), (9484383007702973/63456015000000:ℝ)],
![(0:ℝ), (619379277177949/31728007500000:ℝ), (926707298989949/63456015000000:ℝ)]]
theorem admission14_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (2446344342109541/49507778560000000:ℝ) admission14_05_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission14_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission14_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_05_coefficients]

def admission14_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(157368302784210307424687/26604756440744343750:ℝ), (59583961146593390827907/5320951288148868750:ℝ), (1906782040456170901552/359523735685734375:ℝ), (0:ℝ)],
![(52277547987861272761553/7190474713714687500:ℝ), (788800246446096082272017/53209512881488687500:ℝ), (3976735670528524251653672/465583237713026015625:ℝ), (9980225810510020957424/10346294171400578125:ℝ)]]
theorem admission14_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (1253627573499443690161/7264872158752588800000:ℝ) admission14_06_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission14_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission14_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_06_coefficients]

def admission14_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(48954979358935084736779/80533316793604500000:ℝ), (224309796694781988313/279629572200015625:ℝ), (60109690473650981347/279629572200015625:ℝ)],
![(275749528379134246948489/805333167936045000000:ℝ), (907073622942325937537/2796295722000156250:ℝ), (0:ℝ)]]
theorem admission14_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (3666691118892709862167/13744352732775168000000:ℝ) admission14_07_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission14_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission14_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_07_coefficients]

def admission14_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(14317230047996152055798293927/20133329198401125000000000:ℝ), (2942602000206664604378178031/2237036577600125000000000:ℝ), (767661872649094159786128647/1258333074900070312500000:ℝ), (0:ℝ)],
![(354693907427012332890730646269/201333291984011250000000000:ℝ), (93069171356171788693626283029/22370365776001250000000000:ℝ), (39943433723964734479170396017/12583330749000703125000000:ℝ), (53779820385820672712541731/69907393050003906250000:ℝ)]]
theorem admission14_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (39385479422402175007476473/1832580364370022400000000000:ℝ) admission14_08_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission14_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission14_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_08_coefficients]

def admission14_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(166953095996620589394491/80533316793604500000:ℝ), (4387287791841267653012/838888716600046875:ℝ), (1532614437178530413066/359523735685734375:ℝ), (99239990681325904/89481463104005:ℝ)],
![(503660427366179008584713/805333167936045000000:ℝ), (209741151688306160632/167777743320009375:ℝ), (31919088901716255893/51360533669390625:ℝ), (0:ℝ)]]
theorem admission14_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (28895653152206971147/916290182185011200000:ℝ) admission14_09_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission14_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission14_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_09_coefficients]

def admission14_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(36895069187786083/2974500703125:ℝ), (30323763280583233/991500234375:ℝ), (10343148456563632/424928671875:ℝ), (18359568541981808/2974500703125:ℝ)],
![(52317640186019861/2974500703125:ℝ), (41003405274105671/991500234375:ℝ), (10106051057716192/330500078125:ℝ), (20336133883148576/2974500703125:ℝ)],
![(51006804606940963/11898002812500:ℝ), (4718470226482903/566571562500:ℝ), (3833417611936/951840225:ℝ), (0:ℝ)]]
theorem admission14_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (966683347909037/346554449920000000:ℝ) admission14_10_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission14_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission14_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_10_coefficients]

def admission14_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(76376078916701253549427/134222194656007500000:ℝ), (18880674706728058471537/25166661498001406250:ℝ), (281530196441380181347/1398147861000078125:ℝ)],
![(85468182552330573850157/268444389312015000000:ℝ), (15146947217895696782459/50333322996002812500:ℝ), (0:ℝ)]]
theorem admission14_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (5477210801805004343709/22907254554625280000000:ℝ) admission14_11_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission14_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission14_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_11_coefficients]

def admission14_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission14_12_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission14_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission14_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_12_coefficients]

def admission14_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission14_13_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission14_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission14_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_13_coefficients]

def admission14_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission14_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission14_14_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission14_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission14_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission14_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission14_14_coefficients]

theorem admission14_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission14_00_pos hδ hp
  · exact admission14_01_pos hδ hp
  · exact admission14_02_pos hδ hp
  · exact admission14_03_pos hδ hp
  · exact admission14_04_pos hδ hp
  · exact admission14_05_pos hδ hp
  · exact admission14_06_pos hδ hp
  · exact admission14_07_pos hδ hp
  · exact admission14_08_pos hδ hp
  · exact admission14_09_pos hδ hp
  · exact admission14_10_pos hδ hp
  · exact admission14_11_pos hδ hp
  · exact admission14_12_pos hδ hp
  · exact admission14_13_pos hδ hp
  · exact admission14_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
