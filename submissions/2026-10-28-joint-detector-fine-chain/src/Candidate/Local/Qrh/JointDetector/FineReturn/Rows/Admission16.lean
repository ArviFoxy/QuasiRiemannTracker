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

def admission16_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission16_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission16_00_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission16_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission16_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_00_coefficients]

def admission16_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission16_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission16_01_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission16_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission16_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_01_coefficients]

def admission16_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission16_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission16_02_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission16_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission16_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_02_coefficients]

def admission16_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13548294608/13809603:ℝ), (17147182160/13809603:ℝ), (1255629184/4603201:ℝ)],
![(9642360704/13809603:ℝ), (9450360704/13809603:ℝ), (0:ℝ)]]
theorem admission16_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (70677891/73651216:ℝ) admission16_03_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission16_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission16_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_03_coefficients]

def admission16_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(543180487171791/4603201000000:ℝ), (112:ℝ), (0:ℝ)],
![(119680456828209/575400125000:ℝ), (19727213093774/71925015625:ℝ), (5260405546887/71925015625:ℝ)]]
theorem admission16_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (110468516484627/1178419456000000:ℝ) admission16_04_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission16_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission16_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_04_coefficients]

def admission16_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(922058408675377/4603201000000:ℝ), (24783338623899/71925015625:ℝ), (10163245126287/71925015625:ℝ)],
![(22803868377287/575400125000:ℝ), (123753324152/2877000625:ℝ), (0:ℝ)]]
theorem admission16_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (19543593281139/147302432000000:ℝ) admission16_05_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission16_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission16_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_05_coefficients]

def admission16_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(714575794786002759345473/147001874909406937500:ℝ), (272253792047293522311853/29400374981881387500:ℝ), (54045486333122071017816/12250156242450578125:ℝ), (0:ℝ)],
![(234774449702506530808358/36750468727351734375:ℝ), (98437020973278634644814/7350093745470346875:ℝ), (99746805239885279921424/12250156242450578125:ℝ), (2753361740917946489904/2450031248490115625:ℝ)]]
theorem admission16_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (6110699012520476468319/40141311975262054400000:ℝ) admission16_06_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission16_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission16_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_06_coefficients]

def admission16_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(49250012190227216974291/63568378339203000000:ℝ), (654251435618812519869/662170607700031250:ℝ), (15798055198816585287/66217060770003125:ℝ)],
![(3865182177247383980273/7946047292400375000:ℝ), (153451284456383049708/331085303850015625:ℝ), (0:ℝ)]]
theorem admission16_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (57926202395660812719/135612540456966400000:ℝ) admission16_07_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission16_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission16_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_07_coefficients]

def admission16_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (596734376881713150578243797/39730236462001875000000000:ℝ), (363630841915553820319086209/5297364861600250000000000:ℝ), (3956445798033010207760055541/79460472924003750000000000:ℝ)],
![(28235083306036816960316201919/26486824308001250000000000:ℝ), (230885496512800468336930779047/79460472924003750000000000:ℝ), (70912119460268655449490283957/26486824308001250000000000:ℝ), (66208056841045239411494678581/79460472924003750000000000:ℝ)]]
theorem admission16_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (2940870915953264222808289739/6943362071396679680000000000000:ℝ) admission16_08_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission16_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission16_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_08_coefficients]

def admission16_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1000966125627439838190559/317841891696015000000:ℝ), (36646117321530626105464/4966279557750234375:ℝ), (8935661559394508791221/1655426519250078125:ℝ), (387400806422084074896/331085303850015625:ℝ)],
![(65167560232688055670217/39730236462001875000:ℝ), (15963852398397300372556/4966279557750234375:ℝ), (2602140922437245087064/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission16_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (50895529609774369707/678062702284832000000:ℝ) admission16_09_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission16_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission16_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_09_coefficients]

def admission16_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10143111986781509/863100187500:ℝ), (65408520728466127/2589300562500:ℝ), (410411793619024/25893005625:ℝ), (20250748645936/8631001875:ℝ)],
![(4652632935520084/215775046875:ℝ), (9717136211678036/215775046875:ℝ), (5721870660316928/215775046875:ℝ), (659887384158976/215775046875:ℝ)],
![(1912350141249296/215775046875:ℝ), (11121838587587888/647325140625:ℝ), (8608749062144/1035720225:ℝ), (0:ℝ)]]
theorem admission16_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (13337389685757/1178419456000000:ℝ) admission16_10_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission16_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission16_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_10_coefficients]

def admission16_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(45993100505947944413533/63568378339203000000:ℝ), (1214677389547462858923/1324341215400062500:ℝ), (72442608377145785287/331085303850015625:ℝ)],
![(3633177265397799670487/7946047292400375000:ℝ), (143846560424575483122/331085303850015625:ℝ), (0:ℝ)]]
theorem admission16_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (262308374969084075559/678062702284832000000:ℝ) admission16_11_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission16_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission16_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_11_coefficients]

def admission16_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission16_12_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission16_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission16_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_12_coefficients]

def admission16_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission16_13_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission16_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission16_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_13_coefficients]

def admission16_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission16_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission16_14_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission16_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission16_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission16_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission16_14_coefficients]

theorem admission16_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission16_00_pos hδ hp
  · exact admission16_01_pos hδ hp
  · exact admission16_02_pos hδ hp
  · exact admission16_03_pos hδ hp
  · exact admission16_04_pos hδ hp
  · exact admission16_05_pos hδ hp
  · exact admission16_06_pos hδ hp
  · exact admission16_07_pos hδ hp
  · exact admission16_08_pos hδ hp
  · exact admission16_09_pos hδ hp
  · exact admission16_10_pos hδ hp
  · exact admission16_11_pos hδ hp
  · exact admission16_12_pos hδ hp
  · exact admission16_13_pos hδ hp
  · exact admission16_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
