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

def admission17_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission17_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission17_00_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission17_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission17_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_00_coefficients]

def admission17_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission17_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission17_01_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission17_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission17_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_01_coefficients]

def admission17_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission17_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission17_02_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission17_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission17_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_02_coefficients]

def admission17_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3400312064/13809603:ℝ), (4246033952/13809603:ℝ), (313907296/4603201:ℝ)],
![(2401067000/13809603:ℝ), (2281067000/13809603:ℝ), (0:ℝ)]]
theorem admission17_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (253282755/294604864:ℝ) admission17_03_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission17_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission17_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_03_coefficients]

def admission17_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(40771604453113/1150800250000:ℝ), (32:ℝ), (0:ℝ)],
![(288024511015757/4603201000000:ℝ), (11014406796887/143850031250:ℝ), (5260405546887/287700062500:ℝ)]]
theorem admission17_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (15781216640661/147302432000000:ℝ) admission17_04_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission17_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission17_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_04_coefficients]

def admission17_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(41635041406901/920640200000:ℝ), (191211728016557/2301600500000:ℝ), (166461063186157/4603201000000:ℝ)],
![(0:ℝ), (1358312343113/460320100000:ℝ), (769828233113/920640200000:ℝ)]]
theorem admission17_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (30056271217377/377094225920000:ℝ) admission17_05_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission17_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission17_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_05_coefficients]

def admission17_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(53166894670781604800251/73500937454703468750:ℝ), (96472344573368666729899/73500937454703468750:ℝ), (7305797390764510321608/12250156242450578125:ℝ), (0:ℝ)],
![(57429522965775624342599/58800749963762775000:ℝ), (3074844805312047748427/1589209458480075000:ℝ), (2713714770646832575788/2450031248490115625:ℝ), (344170217614743311238/2450031248490115625:ℝ)]]
theorem admission17_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (828369292367823929397/5017663996907756800000:ℝ) admission17_06_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission17_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission17_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_06_coefficients]

def admission17_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2971650075699782500997/15892094584800750000:ℝ), (155715918222274451289/662170607700031250:ℝ), (15798055198816585287/264868243080012500:ℝ)],
![(1287851576945046516949/12713675667840600000:ℝ), (24412704345333666999/264868243080012500:ℝ), (0:ℝ)]]
theorem admission17_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (36862128797238699003/108490032365573120000:ℝ) admission17_07_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission17_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission17_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_07_coefficients]

def admission17_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1473644261662599611681814889/39730236462001875000000000:ℝ), (2268642266499312748557490897/39730236462001875000000000:ℝ), (36750489212682937796840667/1655426519250078125000000:ℝ), (0:ℝ)],
![(1347643769564701215750352129/6356837833920300000000000:ℝ), (15634681871044161177824132717/31784189169601500000000000:ℝ), (504002387984955997062816801/1324341215400062500000000:ℝ), (64845428169804405420556899/662170607700031250000000:ℝ)]]
theorem admission17_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (27011299905077540482149597/2712250809139328000000000000:ℝ) admission17_08_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission17_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission17_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_08_coefficients]

def admission17_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(28547020366384846949257/79460472924003750000:ℝ), (4218486943895614199131/4966279557750234375:ℝ), (1051644127346063276313/1655426519250078125:ℝ), (48425100802760509362/331085303850015625:ℝ)],
![(7774804287314369921849/63568378339203000000:ℝ), (479402360656249587049/1986511823100093750:ℝ), (155712384118523992563/1324341215400062500:ℝ), (0:ℝ)]]
theorem admission17_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26188893446991342957/542450161827865600000:ℝ) admission17_09_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission17_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission17_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_09_coefficients]

def admission17_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(112329585552452/129465028125:ℝ), (420559652689936/215775046875:ℝ), (880286915341322/647325140625:ℝ), (60445295011258/215775046875:ℝ)],
![(12419655584371/8631001875:ℝ), (45031273575629/14385003125:ℝ), (29581689502516/14385003125:ℝ), (15929525702516/43155009375:ℝ)],
![(86856491951791/207144045000:ℝ), (54998603410597/69048015000:ℝ), (15519863656/41428809:ℝ), (0:ℝ)]]
theorem admission17_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (4909211698209/754188451840000:ℝ) admission17_10_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission17_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission17_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_10_coefficients]

def admission17_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2776329840828643296467/15892094584800750000:ℝ), (72182944294716763424/331085303850015625:ℝ), (72442608377145785287/1324341215400062500:ℝ)],
![(1208675865365178135379/12713675667840600000:ℝ), (45588568003431264421/529736486160025000:ℝ), (0:ℝ)]]
theorem admission17_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (6655245397959191571/21698006473114624000:ℝ) admission17_11_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission17_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission17_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_11_coefficients]

def admission17_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission17_12_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission17_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission17_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_12_coefficients]

def admission17_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission17_13_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission17_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission17_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_13_coefficients]

def admission17_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission17_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission17_14_coefficients
      (3/8:ℝ) (15/32:ℝ) (3/8:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission17_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission17_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission17_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission17_14_coefficients]

theorem admission17_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (3/8:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission17_00_pos hδ hp
  · exact admission17_01_pos hδ hp
  · exact admission17_02_pos hδ hp
  · exact admission17_03_pos hδ hp
  · exact admission17_04_pos hδ hp
  · exact admission17_05_pos hδ hp
  · exact admission17_06_pos hδ hp
  · exact admission17_07_pos hδ hp
  · exact admission17_08_pos hδ hp
  · exact admission17_09_pos hδ hp
  · exact admission17_10_pos hδ hp
  · exact admission17_11_pos hδ hp
  · exact admission17_12_pos hδ hp
  · exact admission17_13_pos hδ hp
  · exact admission17_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
