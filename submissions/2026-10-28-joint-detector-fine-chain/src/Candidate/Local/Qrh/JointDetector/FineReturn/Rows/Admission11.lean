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

def admission11_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission11_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission11_00_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission11_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission11_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_00_coefficients]

def admission11_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission11_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission11_01_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission11_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission11_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_01_coefficients]

def admission11_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission11_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission11_02_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission11_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission11_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_02_coefficients]

def admission11_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9286482244096/38073609:ℝ), (11838822303232/38073609:ℝ), (284793339904/4230401:ℝ)],
![(6714729028864/38073609:ℝ), (6703857028864/38073609:ℝ), (0:ℝ)]]
theorem admission11_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (21857787923/25991583744:ℝ) admission11_03_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission11_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission11_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_03_coefficients]

def admission11_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(16303096135942359/423040100000:ℝ), (38400:ℝ), (0:ℝ)],
![(170713555396556493/3021715000000:ℝ), (24475989632504064/330500078125:ℝ), (5850089306252032/330500078125:ℝ)]]
theorem admission11_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (205667202172923/1732772249600000:ℝ) admission11_04_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission11_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission11_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_04_coefficients]

def admission11_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(181826612933930021/4532572500000:ℝ), (74071762607764192/991500234375:ℝ), (11410234278284032/330500078125:ℝ)],
![(334917123994559791/63456015000000:ℝ), (6057156012176/1133143125:ℝ), (0:ℝ)]]
theorem admission11_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (7855621497155209/86638612480000000:ℝ) admission11_05_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission11_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission11_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_05_coefficients]

def admission11_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1954297652925661462126689976/93116647542605203125:ℝ), (3179691828559756763858168/76013589830698125:ℝ), (1940853731382403073599565824/93116647542605203125:ℝ), (0:ℝ)],
![(11652369077705154526092534908/465583237713026015625:ℝ), (5015318817647947775337478988/93116647542605203125:ℝ), (15263925666683682663467251712/465583237713026015625:ℝ), (40879004919849045841608704/10346294171400578125:ℝ)]]
theorem admission11_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (134792411213525806509481/813665681780289945600000:ℝ) admission11_06_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission11_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission11_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_06_coefficients]

def admission11_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2550324655514785477599857/16106663358720900000:ℝ), (59564596506383778106576/279629572200015625:ℝ), (15388080761254651224832/279629572200015625:ℝ)],
![(82579727917499487521755789/805333167936045000000:ℝ), (142871530643112583735336/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission11_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (72191738258854828597747/219909643724402688000000:ℝ) admission11_07_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission11_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission11_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_07_coefficients]

def admission11_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1172226883434192769168585967519/629166537450035156250000:ℝ), (1554301800379548320879376589811/419444358300023437500000:ℝ), (14491004757207803104066373672/7864581718125439453125:ℝ), (0:ℝ)],
![(31963010558742985135707115152167/6291665374500351562500000:ℝ), (55745961467465401415479798621787/4194443583000234375000000:ℝ), (2233808559420680045013247864388/196614542953135986328125:ℝ), (13767634018770092214410683136/4369212065625244140625:ℝ)]]
theorem admission11_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (3750625676807782255855987/234570286639362867200000000:ℝ) admission11_08_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission11_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission11_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_08_coefficients]

def admission11_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(740243947773734231930119733/80533316793604500000:ℝ), (19222696947171412341618112/838888716600046875:ℝ), (45967803358024406602353152/2516666149800140625:ℝ), (406487001830710902784/89481463104005:ℝ)],
![(3678956178285787370383208333/805333167936045000000:ℝ), (1530989613100454031117536/167777743320009375:ℝ), (11467994357034015920060672/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission11_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (753072610634508522727/14660642914960179200000:ℝ) admission11_09_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission11_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission11_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_09_coefficients]

def admission11_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2237215761719502786608/2974500703125:ℝ), (1796099506734135534608/991500234375:ℝ), (1356975813796851908608/991500234375:ℝ), (919852276657651908608/2974500703125:ℝ)],
![(3546633516757522172656/2974500703125:ℝ), (381396503618474673968/141642890625:ℝ), (5390626058775516971008/2974500703125:ℝ), (927948288295070990336/2974500703125:ℝ)],
![(1301156248967966996012/2974500703125:ℝ), (288489982605213310668/330500078125:ℝ), (414478687725264896/951840225:ℝ), (0:ℝ)]]
theorem admission11_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (678664700504100997/88717939179520000000:ℝ) admission11_10_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission11_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission11_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_10_coefficients]

def admission11_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6635555756601263018575359/44740731552002500000:ℝ), (2510495484532433368501976/12583330749000703125:ℝ), (72071730288993326424832/1398147861000078125:ℝ)],
![(8591597967471349577054619/89481463104005000000:ℝ), (1203827427123429304440476/12583330749000703125:ℝ), (0:ℝ)]]
theorem admission11_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (108750137561983583100369/366516072874004480000000:ℝ) admission11_11_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission11_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission11_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_11_coefficients]

def admission11_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission11_12_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission11_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission11_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_12_coefficients]

def admission11_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission11_13_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission11_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission11_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_13_coefficients]

def admission11_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission11_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission11_14_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission11_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission11_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission11_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission11_14_coefficients]

theorem admission11_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission11_00_pos hδ hp
  · exact admission11_01_pos hδ hp
  · exact admission11_02_pos hδ hp
  · exact admission11_03_pos hδ hp
  · exact admission11_04_pos hδ hp
  · exact admission11_05_pos hδ hp
  · exact admission11_06_pos hδ hp
  · exact admission11_07_pos hδ hp
  · exact admission11_08_pos hδ hp
  · exact admission11_09_pos hδ hp
  · exact admission11_10_pos hδ hp
  · exact admission11_11_pos hδ hp
  · exact admission11_12_pos hδ hp
  · exact admission11_13_pos hδ hp
  · exact admission11_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
