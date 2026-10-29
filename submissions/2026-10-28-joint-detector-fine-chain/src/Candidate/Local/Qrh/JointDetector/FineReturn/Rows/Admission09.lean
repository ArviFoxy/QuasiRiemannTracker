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

def admission09_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission09_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission09_00_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission09_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission09_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_00_coefficients]

def admission09_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission09_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission09_01_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission09_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission09_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_01_coefficients]

def admission09_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission09_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission09_02_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission09_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission09_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_02_coefficients]

def admission09_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2328591139072/38073609:ℝ), (2964048153856/38073609:ℝ), (71198334976/4230401:ℝ)],
![(1683535546240/38073609:ℝ), (1678135546240/38073609:ℝ), (0:ℝ)]]
theorem admission09_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (10968004375/12995791872:ℝ) admission09_03_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission09_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission09_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_03_coefficients]

def admission09_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(100895623329955761/10576002500000:ℝ), (9472:ℝ), (0:ℝ)],
![(298119584298591487/21152005000000:ℝ), (6097845403126016/330500078125:ℝ), (1462522326563008/330500078125:ℝ)]]
theorem admission09_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (2536562160132717/21659653120000000:ℝ) admission09_04_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission09_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission09_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_04_coefficients]

def admission09_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(64528875614385097/6345601500000:ℝ), (18673113365644048/991500234375:ℝ), (2852558569571008/330500078125:ℝ)],
![(3505523552531323/2538240600000:ℝ), (320591825032/226628625:ℝ), (0:ℝ)]]
theorem admission09_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (159786703602077/1732772249600000:ℝ) admission09_05_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission09_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission09_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_05_coefficients]

def admission09_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1219459160930180107078349044/465583237713026015625:ℝ), (2422173633984343001365015796/465583237713026015625:ℝ), (1202785745715990394286666752/465583237713026015625:ℝ), (0:ℝ)],
![(291963800924035782903536558/93116647542605203125:ℝ), (125306766251063054049420374/18623329508521040625:ℝ), (380573358027290913915375104/93116647542605203125:ℝ), (5109875614981130730201088/10346294171400578125:ℝ)]]
theorem admission09_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (334174089524608572879427/2034164204450724864000000:ℝ) admission09_06_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission09_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission09_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_06_coefficients]

def admission09_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16130755882820117792842567/402666583968022500000:ℝ), (74991067771109619907832/1398147861000078125:ℝ), (3847020190313662806208/279629572200015625:ℝ)],
![(4174321380654663340652341/161066633587209000000:ℝ), (7197108745968618914228/279629572200015625:ℝ), (0:ℝ)]]
theorem admission09_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (7273272547311768742987/21990964372440268800000:ℝ) admission09_07_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission09_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission09_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_07_coefficients]

def admission09_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(918099825102115081226874538027/4194443583000234375000000:ℝ), (5445516500154132812110558592083/12583330749000703125000000:ℝ), (6008382553877679297667263274/28087791850447998046875:ℝ), (0:ℝ)],
![(1055940603959214547078887455329/1677777433200093750000000:ℝ), (1658392507218815260522585019333/1006666459920056250000000:ℝ), (7931806112371991166239648447/5617558370089599609375:ℝ), (1720954252346261526801335392/4369212065625244140625:ℝ)]]
theorem admission09_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1091400793423700945886183341/73303214574800896000000000000:ℝ) admission09_08_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission09_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission09_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_08_coefficients]

def admission09_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(52379856004389271372175439/44740731552002500000:ℝ), (7313958290314254596324704/2516666149800140625:ℝ), (5796592475134090390267264/2516666149800140625:ℝ), (50810875228838862848/89481463104005:ℝ)],
![(10426371751310193247208397/17896292620801000000:ℝ), (2925071870872457605625296/2516666149800140625:ℝ), (1458807822319771772494144/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission09_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (382351148521238201051/7330321457480089600000:ℝ) admission09_09_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission09_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission09_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_09_coefficients]

def admission09_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(28131093773383063096/594900140625:ℝ), (336517343233988848408/2974500703125:ℝ), (251832791326160699392/2974500703125:ℝ), (55972765109087166464/2974500703125:ℝ)],
![(8976714802969116584/118980028125:ℝ), (100861495899413803592/594900140625:ℝ), (9624875135331590144/84985734375:ℝ), (1628136187536130048/84985734375:ℝ)],
![(73518953955894542/2644000625:ℝ), (439123692937283626/7932001875:ℝ), (349698829711360/12691203:ℝ), (0:ℝ)]]
theorem admission09_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (1385401064724561/177435878359040000:ℝ) admission09_10_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission09_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission09_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_10_coefficients]

def admission09_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(15116323646499965183609657/402666583968022500000:ℝ), (632312327236670436332756/12583330749000703125:ℝ), (18017932572248331606208/1398147861000078125:ℝ)],
![(3910414811378486654229323/161066633587209000000:ℝ), (485281735732221397142/20133329198401125:ℝ), (0:ℝ)]]
theorem admission09_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (10959472815130772364441/36651607287400448000000:ℝ) admission09_11_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission09_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission09_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_11_coefficients]

def admission09_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission09_12_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission09_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission09_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_12_coefficients]

def admission09_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission09_13_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission09_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission09_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_13_coefficients]

def admission09_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission09_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission09_14_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission09_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission09_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission09_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission09_14_coefficients]

theorem admission09_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission09_00_pos hδ hp
  · exact admission09_01_pos hδ hp
  · exact admission09_02_pos hδ hp
  · exact admission09_03_pos hδ hp
  · exact admission09_04_pos hδ hp
  · exact admission09_05_pos hδ hp
  · exact admission09_06_pos hδ hp
  · exact admission09_07_pos hδ hp
  · exact admission09_08_pos hδ hp
  · exact admission09_09_pos hδ hp
  · exact admission09_10_pos hδ hp
  · exact admission09_11_pos hδ hp
  · exact admission09_12_pos hδ hp
  · exact admission09_13_pos hδ hp
  · exact admission09_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
