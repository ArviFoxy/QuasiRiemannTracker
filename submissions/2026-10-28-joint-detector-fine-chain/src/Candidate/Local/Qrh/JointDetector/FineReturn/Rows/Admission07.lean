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

def admission07_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission07_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission07_00_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission07_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission07_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_00_coefficients]

def admission07_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission07_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission07_01_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission07_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission07_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_01_coefficients]

def admission07_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission07_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission07_02_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission07_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission07_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_02_coefficients]

def admission07_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(585579073792/38073609:ℝ), (106169046784/5439087:ℝ), (17799583744/4230401:ℝ)],
![(423283531072/38073609:ℝ), (420619531072/38073609:ℝ), (0:ℝ)]]
theorem admission07_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (5523112601/6497895936:ℝ) admission07_03_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission07_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission07_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_03_coefficients]

def admission07_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(12358623767827077/5288001250000:ℝ), (2304:ℝ), (0:ℝ)],
![(10601147530709127/3021715000000:ℝ), (1513885348281504/330500078125:ℝ), (365630581640752/330500078125:ℝ)]]
theorem admission07_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (617001606518769/5414913280000000:ℝ) admission07_04_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission07_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission07_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_04_coefficients]

def admission07_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8289563534773373/3172800750000:ℝ), (4745864698262512/991500234375:ℝ), (713139642392752/330500078125:ℝ)],
![(23874564221620717/63456015000000:ℝ), (445074842348/1133143125:ℝ), (0:ℝ)]]
theorem admission07_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (2064190636500283/21659653120000000:ℝ) admission07_05_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission07_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission07_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_05_coefficients]

def admission07_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(21698306743291806695982428/66511891101860859375:ℝ), (299639733131203564479444868/465583237713026015625:ℝ), (147786259114995917607567872/465583237713026015625:ℝ), (0:ℝ)],
![(183277440517771962841135037/465583237713026015625:ℝ), (10569624947834992779506233/12583330749000703125:ℝ), (236577369217305380357976704/465583237713026015625:ℝ), (638734451872641341275136/10346294171400578125:ℝ)]]
theorem admission07_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (82140053126549171522719/508541051112681216000000:ℝ) admission07_06_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission07_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission07_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_06_coefficients]

def admission07_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2064552649822082333010163/201333291984011250000:ℝ), (2716489715977479087752/199735408714296875:ℝ), (961755047578415701552/279629572200015625:ℝ)],
![(761720303397190360873537/115047595419435000000:ℝ), (9130216466993247961438/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission07_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (18453674975410851273529/54977410931100672000000:ℝ) admission07_07_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission07_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission07_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_07_coefficients]

def admission07_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2395155088638783198587004119/100666645992005625000000:ℝ), (194663504250578030996322791269/4194443583000234375000000:ℝ), (4450906737360311981324711663/196614542953135986328125:ℝ), (0:ℝ)],
![(777426853181154887304415714787/10066664599200562500000000:ℝ), (3396094495384260760845797846257/16777774332000937500000000:ℝ), (137193750971944530600925560419/786458171812543945312500:ℝ), (215119281543282690850166924/4369212065625244140625:ℝ)]]
theorem admission07_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (232515333066559731937139537/18325803643700224000000000000:ℝ) admission07_08_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission07_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission07_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_08_coefficients]

def admission07_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(30573223734836352082754387/201333291984011250000:ℝ), (104532031865326679953056/279629572200015625:ℝ), (737228323237021190026688/2516666149800140625:ℝ), (6351359403604857856/89481463104005:ℝ)],
![(61003505187282969550293191/805333167936045000000:ℝ), (8429810084334245589208/55925914440003125:ℝ), (26954015673228773883344/359523735685734375:ℝ), (0:ℝ)]]
theorem admission07_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (196990417464603040213/3665160728740044800000:ℝ) admission07_09_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission07_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission07_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_09_coefficients]

def admission07_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8882508505676963504/2974500703125:ℝ), (6991162344865879952/991500234375:ℝ), (5133029558495538176/991500234375:ℝ), (3308547546565938176/2974500703125:ℝ)],
![(2871991075046536472/594900140625:ℝ), (3551038297328567224/330500078125:ℝ), (3004791132732147712/424928671875:ℝ), (3435047728400611328/2974500703125:ℝ)],
![(5340450951047318627/2974500703125:ℝ), (3528522996159506209/991500234375:ℝ), (1678289919977984/951840225:ℝ), (0:ℝ)]]
theorem admission07_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (45001936504731373/5544871198720000000:ℝ) admission07_10_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission07_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission07_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_10_coefficients]

def admission07_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(129102036338257817164067/13422219465600750000:ℝ), (4583494567455675891052/359523735685734375:ℝ), (4504483143062082901552/1398147861000078125:ℝ)],
![(238063162414916104870741/38349198473145000000:ℝ), (76997385234050116855253/12583330749000703125:ℝ), (0:ℝ)]]
theorem admission07_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (27820977332489001183123/91629018218501120000000:ℝ) admission07_11_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission07_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission07_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_11_coefficients]

def admission07_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission07_12_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission07_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission07_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_12_coefficients]

def admission07_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission07_13_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission07_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission07_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_13_coefficients]

def admission07_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission07_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission07_14_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission07_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission07_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission07_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission07_14_coefficients]

theorem admission07_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission07_00_pos hδ hp
  · exact admission07_01_pos hδ hp
  · exact admission07_02_pos hδ hp
  · exact admission07_03_pos hδ hp
  · exact admission07_04_pos hδ hp
  · exact admission07_05_pos hδ hp
  · exact admission07_06_pos hδ hp
  · exact admission07_07_pos hδ hp
  · exact admission07_08_pos hδ hp
  · exact admission07_09_pos hδ hp
  · exact admission07_10_pos hδ hp
  · exact admission07_11_pos hδ hp
  · exact admission07_12_pos hδ hp
  · exact admission07_13_pos hδ hp
  · exact admission07_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
