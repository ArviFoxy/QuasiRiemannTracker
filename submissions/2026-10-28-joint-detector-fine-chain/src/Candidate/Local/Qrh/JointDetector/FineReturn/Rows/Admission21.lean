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

def admission21_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission21_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission21_00_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission21_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission21_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_00_coefficients]

def admission21_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission21_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission21_01_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission21_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission21_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_01_coefficients]

def admission21_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission21_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission21_02_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission21_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission21_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_02_coefficients]

def admission21_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(209731230464/13809603:ℝ), (269137431296/13809603:ℝ), (20090066944/4603201:ℝ)],
![(148832844224/13809603:ℝ), (147944844224/13809603:ℝ), (0:ℝ)]]
theorem admission21_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (2114548467/2356838912:ℝ) admission21_03_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission21_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission21_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_03_coefficients]

def admission21_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2686957744078017/1150800250000:ℝ), (2304:ℝ), (0:ℝ)],
![(16433037116777469/4603201000000:ℝ), (338651414500384/71925015625:ℝ), (84166488750192/71925015625:ℝ)]]
theorem admission21_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (142030949765949/1178419456000000:ℝ) admission21_04_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission21_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission21_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_04_coefficients]

def admission21_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(605471790067571/230160050000:ℝ), (352916929421584/71925015625:ℝ), (162611922020592/71925015625:ℝ)],
![(1351394087094019/4603201000000:ℝ), (889640972412/2877000625:ℝ), (0:ℝ)]]
theorem admission21_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (472946308102143/4713677824000000:ℝ) admission21_05_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission21_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission21_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_05_coefficients]

def admission21_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12375726717080437187750972/36750468727351734375:ℝ), (24440020920560575260310076/36750468727351734375:ℝ), (4022225402823046024186368/12250156242450578125:ℝ), (0:ℝ)],
![(15236507928062646808534259/36750468727351734375:ℝ), (32798433361363704696351347/36750468727351734375:ℝ), (6735866958792178839374976/12250156242450578125:ℝ), (176215151418748575353856/2450031248490115625:ℝ)]]
theorem admission21_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (7143209665364706402033/40141311975262054400000:ℝ) admission21_06_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission21_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission21_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_06_coefficients]

def admission21_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(167771831780769334882141/15892094584800750000:ℝ), (4731807281275064723544/331085303850015625:ℝ), (252768883181065364592/66217060770003125:ℝ)],
![(416227101821712528426313/63568378339203000000:ℝ), (2141342924004981648198/331085303850015625:ℝ), (0:ℝ)]]
theorem admission21_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (1616667648678897227703/4339601294622924800000:ℝ) admission21_07_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission21_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission21_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_07_coefficients]

def admission21_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1156599296275029445291853917/39730236462001875000000:ℝ), (283034023503902421805822200101/4966279557750234375000000:ℝ), (721651051681379573884739703/25866039363282470703125:ℝ), (0:ℝ)],
![(331665524283763229373298758241/3973023646200187500000000:ℝ), (4286312994448412872022005266353/19865118231000937500000000:ℝ), (18877154105458491667982628939/103464157453129882812500:ℝ), (259381712679217621682227596/5173207872656494140625:ℝ)]]
theorem admission21_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (410626683750033540118867473/21698006473114624000000000000:ℝ) admission21_08_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission21_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission21_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_08_coefficients]

def admission21_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2479781703482259548743421/15892094584800750000:ℝ), (1918082428685364105687904/4966279557750234375:ℝ), (505001246601120232306368/1655426519250078125:ℝ), (24793651611013380793344/331085303850015625:ℝ)],
![(4831852199503017227846729/63568378339203000000:ℝ), (751750576728131614725448/4966279557750234375:ℝ), (124736335785903479114736/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission21_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (1265468691492076010409/21698006473114624000000:ℝ) admission21_09_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission21_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission21_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_09_coefficients]

def admission21_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(671321674880834128/215775046875:ℝ), (531145014693444464/71925015625:ℝ), (393166577439429632/71925015625:ℝ), (257415523118789632/215775046875:ℝ)],
![(71916212196597368/14385003125:ℝ), (7235394981852320536/647325140625:ℝ), (4800726966619838464/647325140625:ℝ), (267247117871466496/215775046875:ℝ)],
![(396817312439030189/215775046875:ℝ), (2362011266275330567/647325140625:ℝ), (1874347074333184/1035720225:ℝ), (0:ℝ)]]
theorem admission21_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (10462821841319433/1206701522944000000:ℝ) admission21_10_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission21_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission21_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_10_coefficients]

def admission21_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(31186843629445010742407/3178418916960150000:ℝ), (876141462306778856516/66217060770003125:ℝ), (1159081734034332564592/331085303850015625:ℝ)],
![(389570437640147577415927/63568378339203000000:ℝ), (2002793562633234509257/331085303850015625:ℝ), (0:ℝ)]]
theorem admission21_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (7307228873353503638583/21698006473114624000000:ℝ) admission21_11_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission21_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission21_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_11_coefficients]

def admission21_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission21_12_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission21_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission21_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_12_coefficients]

def admission21_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission21_13_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission21_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission21_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_13_coefficients]

def admission21_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission21_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission21_14_coefficients
      (27/64:ℝ) (111/256:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission21_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission21_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission21_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission21_14_coefficients]

theorem admission21_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (111/256:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission21_00_pos hδ hp
  · exact admission21_01_pos hδ hp
  · exact admission21_02_pos hδ hp
  · exact admission21_03_pos hδ hp
  · exact admission21_04_pos hδ hp
  · exact admission21_05_pos hδ hp
  · exact admission21_06_pos hδ hp
  · exact admission21_07_pos hδ hp
  · exact admission21_08_pos hδ hp
  · exact admission21_09_pos hδ hp
  · exact admission21_10_pos hδ hp
  · exact admission21_11_pos hδ hp
  · exact admission21_12_pos hδ hp
  · exact admission21_13_pos hδ hp
  · exact admission21_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
