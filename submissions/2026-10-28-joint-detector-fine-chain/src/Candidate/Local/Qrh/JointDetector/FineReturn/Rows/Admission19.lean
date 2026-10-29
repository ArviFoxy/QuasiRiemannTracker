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

def admission19_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission19_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission19_00_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission19_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission19_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_00_coefficients]

def admission19_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission19_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission19_01_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission19_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission19_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_01_coefficients]

def admission19_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission19_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission19_02_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission19_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission19_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_02_coefficients]

def admission19_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13270201904/13809603:ℝ), (16821089456/13809603:ℝ), (1255629184/4603201:ℝ)],
![(9364268000/13809603:ℝ), (9124268000/13809603:ℝ), (0:ℝ)]]
theorem admission19_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (253282755/294604864:ℝ) admission19_03_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission19_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission19_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_03_coefficients]

def admission19_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(698374912078017/4603201000000:ℝ), (144:ℝ), (0:ℝ)],
![(556319039765949/2301600500000:ℝ), (22028813593774/71925015625:ℝ), (5260405546887/71925015625:ℝ)]]
theorem admission19_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (142030949765949/1178419456000000:ℝ) admission19_04_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission19_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission19_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_04_coefficients]

def admission19_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(743698861525951/4603201000000:ℝ), (22057308088849/71925015625:ℝ), (10163245126287/71925015625:ℝ)],
![(407139986887/460320100000:ℝ), (117696822/23016005:ℝ), (0:ℝ)]]
theorem admission19_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (9536927549139/117841945600000:ℝ) admission19_05_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission19_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission19_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_05_coefficients]

def admission19_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(833216393923895908332911/147001874909406937500:ℝ), (317000330392843407573571/29400374981881387500:ℝ), (62847271919110094127912/12250156242450578125:ℝ), (0:ℝ)],
![(105773839794791927222087/14700187490940693750:ℝ), (219247311119332211920487/14700187490940693750:ℝ), (21709718165174660606304/2450031248490115625:ℝ), (2753361740917946489904/2450031248490115625:ℝ)]]
theorem admission19_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (7143209665364706402033/40141311975262054400000:ℝ) admission19_06_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission19_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission19_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_06_coefficients]

def admission19_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(42925168627458770461117/63568378339203000000:ℝ), (591475910159383090443/662170607700031250:ℝ), (15798055198816585287/66217060770003125:ℝ)],
![(2459661385521062532901/6356837833920300000:ℝ), (24412704345333666999/66217060770003125:ℝ), (0:ℝ)]]
theorem admission19_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (36862128797238699003/108490032365573120000:ℝ) admission19_07_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission19_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission19_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_07_coefficients]

def admission19_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(40950831952163433146667909893/79460472924003750000000000:ℝ), (75198520619665104527017165637/79460472924003750000000000:ℝ), (721651051681379573884739703/1655426519250078125000000:ℝ), (0:ℝ)],
![(2513121637405477680552330313/1589209458480075000000000:ℝ), (30489054837870214656279145709/7946047292400375000000000:ℝ), (504002387984955997062816801/165542651925007812500000:ℝ), (64845428169804405420556899/82771325962503906250000:ℝ)]]
theorem admission19_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (410626683750033540118867473/21698006473114624000000000000:ℝ) admission19_08_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission19_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission19_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_08_coefficients]

def admission19_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(785524386425970476333233/317841891696015000000:ℝ), (30147660053251541380288/4966279557750234375:ℝ), (7890644478142503629787/1655426519250078125:ℝ), (387400806422084074896/331085303850015625:ℝ)],
![(30589874266003508350441/31784189169601500000:ℝ), (1893079026023643129476/993255911550046875:ℝ), (311424768237047985126/331085303850015625:ℝ), (0:ℝ)]]
theorem admission19_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26188893446991342957/542450161827865600000:ℝ) admission19_09_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission19_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission19_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_09_coefficients]

def admission19_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11256648524050597/863100187500:ℝ), (8864405433618743/287700062500:ℝ), (1651020944130704/71925015625:ℝ), (1120743388190704/215775046875:ℝ)],
![(878276402770597/43155009375:ℝ), (5925442652153327/129465028125:ℝ), (4052800677562304/129465028125:ℝ), (254872411240256/43155009375:ℝ)],
![(54908603410597/8631001875:ℝ), (320194446791791/25893005625:ℝ), (248317818496/41428809:ℝ), (0:ℝ)]]
theorem admission19_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (4909211698209/754188451840000:ℝ) admission19_10_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission19_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission19_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_10_coefficients]

def admission19_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(39955697357240831864467/63568378339203000000:ℝ), (219035365576694714129/264868243080012500:ℝ), (72442608377145785287/331085303850015625:ℝ)],
![(2302801497447528481483/6356837833920300000:ℝ), (45588568003431264421/132434121540006250:ℝ), (0:ℝ)]]
theorem admission19_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (6655245397959191571/21698006473114624000:ℝ) admission19_11_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission19_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission19_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_11_coefficients]

def admission19_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission19_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission19_12_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission19_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission19_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_12_coefficients]

def admission19_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission19_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission19_13_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission19_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission19_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_13_coefficients]

def admission19_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission19_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission19_14_coefficients
      (27/64:ℝ) (15/32:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission19_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission19_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission19_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission19_14_coefficients]

theorem admission19_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission19_00_pos hδ hp
  · exact admission19_01_pos hδ hp
  · exact admission19_02_pos hδ hp
  · exact admission19_03_pos hδ hp
  · exact admission19_04_pos hδ hp
  · exact admission19_05_pos hδ hp
  · exact admission19_06_pos hδ hp
  · exact admission19_07_pos hδ hp
  · exact admission19_08_pos hδ hp
  · exact admission19_09_pos hδ hp
  · exact admission19_10_pos hδ hp
  · exact admission19_11_pos hδ hp
  · exact admission19_12_pos hδ hp
  · exact admission19_13_pos hδ hp
  · exact admission19_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
