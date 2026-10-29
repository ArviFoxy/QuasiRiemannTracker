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

def admission28_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission28_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission28_00_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission28_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission28_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_00_coefficients]

def admission28_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission28_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission28_01_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission28_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission28_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_01_coefficients]

def admission28_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission28_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission28_02_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission28_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission28_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_02_coefficients]

def admission28_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13131155552/13809603:ℝ), (16658043104/13809603:ℝ), (1255629184/4603201:ℝ)],
![(9225221648/13809603:ℝ), (8961221648/13809603:ℝ), (0:ℝ)]]
theorem admission28_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (477136701/589209728:ℝ) admission28_03_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission28_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission28_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_03_coefficients]

def admission28_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(77597212453113/460320100000:ℝ), (160:ℝ), (0:ℝ)],
![(1190235291985011/4603201000000:ℝ), (23179613843774/71925015625:ℝ), (5260405546887/71925015625:ℝ)]]
theorem admission28_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (15781216640661/117841945600000:ℝ) admission28_04_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission28_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission28_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_04_coefficients]

def admission28_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(739627461657081/4603201000000:ℝ), (747325743988211/2301600500000:ℝ), (735556061788211/4603201000000:ℝ)],
![(0:ℝ), (53261567345043/2301600500000:ℝ), (85108373705843/4603201000000:ℝ)]]
theorem admission28_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (3896965446084327/75418845184000000:ℝ) admission28_05_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission28_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission28_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_05_coefficients]

def admission28_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(89253669349284248282663/14700187490940693750:ℝ), (917225944771941487039/79460472924003750:ℝ), (13449632942420821136592/2450031248490115625:ℝ), (0:ℝ)],
![(30190775608563941803097/3973023646200187500:ℝ), (460867891411439366471833/29400374981881387500:ℝ), (112949483618867314586568/12250156242450578125:ℝ), (2753361740917946489904/2450031248490115625:ℝ)]]
theorem admission28_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (765946499178682136889/4014131197526205440000:ℝ) admission28_06_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission28_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission28_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_06_coefficients]

def admission28_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3976274684607454720453/6356837833920300000:ℝ), (56008814742966837573/66217060770003125:ℝ), (15798055198816585287/66217060770003125:ℝ)],
![(21434192073826402072423/63568378339203000000:ℝ), (212739280723621955277/662170607700031250:ℝ), (0:ℝ)]]
theorem admission28_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (321227122375937234169/1084900323655731200000:ℝ) admission28_07_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission28_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission28_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_07_coefficients]

def admission28_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(6340447082726165482388189261/7946047292400375000000000:ℝ), (11813571524966545895158758797/7946047292400375000000000:ℝ), (114929818966129564539475407/165542651925007812500000:ℝ), (0:ℝ)],
![(148109720745372105704830498367/79460472924003750000000000:ℝ), (347827743008702500987361879423/79460472924003750000000000:ℝ), (5467671017829476042138182377/1655426519250078125000000:ℝ), (64845428169804405420556899/82771325962503906250000:ℝ)]]
theorem admission28_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (60516296825944675638053817/2169800647311462400000000000:ℝ) admission28_08_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission28_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission28_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_08_coefficients]

def admission28_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(67780351682523579540457/31784189169601500000:ℝ), (1075937256764479960708/198651182310009375:ℝ), (1473627187503300209814/331085303850015625:ℝ), (387400806422084074896/331085303850015625:ℝ)],
![(198177873059300402575747/317841891696015000000:ℝ), (6216166495978673284792/4966279557750234375:ℝ), (1034615300559237344913/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission28_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (189251283265772665527/5424501618278656000000:ℝ) admission28_09_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission28_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission28_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_09_coefficients]

def admission28_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2800695809476781/215775046875:ℝ), (20856687687701479/647325140625:ℝ), (16731792431906704/647325140625:ℝ), (1427980724211856/215775046875:ℝ)],
![(3955439775630427/215775046875:ℝ), (9365294818075291/215775046875:ℝ), (6986504434667296/215775046875:ℝ), (1581599392222432/215775046875:ℝ)],
![(3800956674312941/863100187500:ℝ), (22247027604778823/2589300562500:ℝ), (4324595032736/1035720225:ℝ), (0:ℝ)]]
theorem admission28_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (223174784031177/75418845184000000:ℝ) admission28_10_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission28_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission28_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_10_coefficients]

def admission28_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(18468497891443637794967/31784189169601500000:ℝ), (517713273525739463253/662170607700031250:ℝ), (72442608377145785287/331085303850015625:ℝ)],
![(20009313400121728540297/63568378339203000000:ℝ), (396135399202318000071/1324341215400062500:ℝ), (0:ℝ)]]
theorem admission28_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (1446483524358360536889/5424501618278656000000:ℝ) admission28_11_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission28_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission28_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_11_coefficients]

def admission28_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission28_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission28_12_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission28_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission28_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_12_coefficients]

def admission28_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission28_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission28_13_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission28_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission28_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_13_coefficients]

def admission28_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission28_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission28_14_coefficients
      (15/32:ℝ) (33/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission28_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission28_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission28_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission28_14_coefficients]

theorem admission28_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (15/32:ℝ) (33/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission28_00_pos hδ hp
  · exact admission28_01_pos hδ hp
  · exact admission28_02_pos hδ hp
  · exact admission28_03_pos hδ hp
  · exact admission28_04_pos hδ hp
  · exact admission28_05_pos hδ hp
  · exact admission28_06_pos hδ hp
  · exact admission28_07_pos hδ hp
  · exact admission28_08_pos hδ hp
  · exact admission28_09_pos hδ hp
  · exact admission28_10_pos hδ hp
  · exact admission28_11_pos hδ hp
  · exact admission28_12_pos hδ hp
  · exact admission28_13_pos hδ hp
  · exact admission28_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
