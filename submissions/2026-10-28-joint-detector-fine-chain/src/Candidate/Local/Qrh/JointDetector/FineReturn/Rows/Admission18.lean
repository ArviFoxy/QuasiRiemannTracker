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

def admission18_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission18_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission18_00_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission18_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission18_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_00_coefficients]

def admission18_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission18_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission18_01_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission18_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission18_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_01_coefficients]

def admission18_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission18_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission18_02_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission18_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission18_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_02_coefficients]

def admission18_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13409248256/13809603:ℝ), (16984135808/13809603:ℝ), (1255629184/4603201:ℝ)],
![(9503314352/13809603:ℝ), (9287314352/13809603:ℝ), (0:ℝ)]]
theorem admission18_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (535994319/589209728:ℝ) admission18_03_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission18_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission18_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_03_coefficients]

def admission18_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(77597212453113/575400125000:ℝ), (128:ℝ), (0:ℝ)],
![(207008173415757/920640200000:ℝ), (20878013343774/71925015625:ℝ), (5260405546887/71925015625:ℝ)]]
theorem admission18_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (15781216640661/147302432000000:ℝ) admission18_04_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission18_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission18_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_04_coefficients]

def admission18_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(104109829387583/575400125000:ℝ), (23420323356374/71925015625:ℝ), (10163245126287/71925015625:ℝ)],
![(93251173443583/4603201000000:ℝ), (69232713451/2877000625:ℝ), (0:ℝ)]]
theorem admission18_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (125859010870251/1178419456000000:ℝ) admission18_05_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission18_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission18_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_05_coefficients]

def admission18_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(193474023588737333459798/36750468727351734375:ℝ), (73656765305017116235678/7350093745470346875:ℝ), (58446379126116082572864/12250156242450578125:ℝ), (0:ℝ)],
![(998418098378972697727151/147001874909406937500:ℝ), (83224270613177896242023/5880074996376277500:ℝ), (104147698032879291476472/12250156242450578125:ℝ), (2753361740917946489904/2450031248490115625:ℝ)]]
theorem admission18_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (828369292367823929397/5017663996907756800000:ℝ) admission18_06_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission18_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission18_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_06_coefficients]

def admission18_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(5760948801105374214713/7946047292400375000:ℝ), (311431836444548902578/331085303850015625:ℝ), (15798055198816585287/66217060770003125:ℝ)],
![(27759035636594848585597/63568378339203000000:ℝ), (275514806183051384703/662170607700031250:ℝ), (0:ℝ)]]
theorem admission18_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (416015453568836745891/1084900323655731200000:ℝ) admission18_07_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission18_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission18_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_07_coefficients]

def admission18_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2312149134633151433681740897/9932559115500468750000000:ℝ), (4032665748708093762805842913/9932559115500468750000000:ℝ), (36750489212682937796840667/206928314906259765625000:ℝ), (0:ℝ)],
![(103202442995175662350402532933/79460472924003750000000000:ℝ), (261953353748701792138221034757/79460472924003750000000000:ℝ), (4612376741869643899118153643/1655426519250078125000000:ℝ), (64845428169804405420556899/82771325962503906250000:ℝ)]]
theorem admission18_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (27011299905077540482149597/2712250809139328000000000000:ℝ) admission18_08_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission18_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission18_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_08_coefficients]

def admission18_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(111655657003338144657737/39730236462001875000:ℝ), (33396888687391083742876/4966279557750234375:ℝ), (8413153018768506210504/1655426519250078125:ℝ), (387400806422084074896/331085303850015625:ℝ)],
![(413619612260769764433073/317841891696015000000:ℝ), (12714623764257758009968/4966279557750234375:ℝ), (2079632381811242506347/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission18_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (334526585674054193613/5424501618278656000000:ℝ) admission18_09_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission18_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission18_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_09_coefficients]

def admission18_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(908618731139616/71925015625:ℝ), (18443393057113856/647325140625:ℝ), (12702022633365968/647325140625:ℝ), (813506052169552/215775046875:ℝ)],
![(1541259911272068/71925015625:ℝ), (5995810930873876/129465028125:ℝ), (18999369613461152/647325140625:ℝ), (967124720180128/215775046875:ℝ)],
![(2257891657095927/287700062500:ℝ), (4381431880855927/287700062500:ℝ), (848444089504/115080025:ℝ), (0:ℝ)]]
theorem admission18_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (701060555106657/75418845184000000:ℝ) admission18_10_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission18_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission18_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_10_coefficients]

def admission18_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(42974398931594388139/63568378339203000:ℝ), (288731777178867053696/331085303850015625:ℝ), (72442608377145785287/331085303850015625:ℝ)],
![(26046716548828841089363/63568378339203000000:ℝ), (515635960866307288349/1324341215400062500:ℝ), (0:ℝ)]]
theorem admission18_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (1881139174621235248611/5424501618278656000000:ℝ) admission18_11_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission18_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission18_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_11_coefficients]

def admission18_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission18_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission18_12_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission18_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission18_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_12_coefficients]

def admission18_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission18_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission18_13_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission18_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission18_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_13_coefficients]

def admission18_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission18_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission18_14_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission18_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission18_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission18_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission18_14_coefficients]

theorem admission18_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission18_00_pos hδ hp
  · exact admission18_01_pos hδ hp
  · exact admission18_02_pos hδ hp
  · exact admission18_03_pos hδ hp
  · exact admission18_04_pos hδ hp
  · exact admission18_05_pos hδ hp
  · exact admission18_06_pos hδ hp
  · exact admission18_07_pos hδ hp
  · exact admission18_08_pos hδ hp
  · exact admission18_09_pos hδ hp
  · exact admission18_10_pos hδ hp
  · exact admission18_11_pos hδ hp
  · exact admission18_12_pos hδ hp
  · exact admission18_13_pos hδ hp
  · exact admission18_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
