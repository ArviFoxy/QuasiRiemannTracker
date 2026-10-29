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

def admission26_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission26_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission26_00_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission26_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission26_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_00_coefficients]

def admission26_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission26_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission26_01_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission26_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission26_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_01_coefficients]

def admission26_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission26_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission26_02_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission26_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission26_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_02_coefficients]

def admission26_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3327238496000/13809603:ℝ), (4287937709312/13809603:ℝ), (321441071104/4603201:ℝ)],
![(2360330541056/13809603:ℝ), (2356682541056/13809603:ℝ), (0:ℝ)]]
theorem admission26_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1042559829/1178419456:ℝ) admission26_03_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission26_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission26_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_03_coefficients]

def admission26_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(178537183320420063/4603201000000:ℝ), (38656:ℝ), (0:ℝ)],
![(33238254156633723/575400125000:ℝ), (5492073848006144/71925015625:ℝ), (1346663820003072/71925015625:ℝ)]]
theorem admission26_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (2382963712739811/18854711296000000:ℝ) admission26_04_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission26_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission26_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_04_coefficients]

def admission26_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(36961653575315309/920640200000:ℝ), (5494013160782544/71925015625:ℝ), (2601790752329472/71925015625:ℝ)],
![(2111998162136453/575400125000:ℝ), (10744936473728/2877000625:ℝ), (0:ℝ)]]
theorem admission26_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (221228286361641/2356838912000000:ℝ) admission26_05_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission26_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission26_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_05_coefficients]

def admission26_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(801018021970006694810118596/36750468727351734375:ℝ), (63877380311182983502953572/1470018749094069375:ℝ), (265308825665720214254573568/12250156242450578125:ℝ), (0:ℝ)],
![(973589498839158051767429792/36750468727351734375:ℝ), (422243778974187472016966176/7350093745470346875:ℝ), (435601999582725313552367616/12250156242450578125:ℝ), (11277769690799908822646784/2450031248490115625:ℝ)]]
theorem admission26_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (117905141930790107200527/642260991604192870400000:ℝ) admission26_06_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission26_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission26_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_06_coefficients]

def admission26_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(10336010149518971593956643/63568378339203000000:ℝ), (73951201787537011552776/331085303850015625:ℝ), (4044302130897045833472/66217060770003125:ℝ)],
![(800639912968204272672527/7946047292400375000:ℝ), (33257078376728835500352/331085303850015625:ℝ), (0:ℝ)]]
theorem admission26_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (784636741541223735921/2169800647311462400000:ℝ) admission26_07_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission26_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission26_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_07_coefficients]

def admission26_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5637495766564187817393478292461/2483139778875117187500000:ℝ), (22441260073901183536529615183003/4966279557750234375000000:ℝ), (58159787171045942730903743268/25866039363282470703125:ℝ), (0:ℝ)],
![(1721357671916954289396258776609/310392472359389648437500:ℝ), (8863655803531956882799599598567/620784944718779296875000:ℝ), (308876819895014523831882292896/25866039363282470703125:ℝ), (16600429611469927787662566144/5173207872656494140625:ℝ)]]
theorem admission26_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (7931780931566429155733574447/347168103569833984000000000000:ℝ) admission26_08_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission26_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission26_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_08_coefficients]

def admission26_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2982082946909838367742226607/317841891696015000000:ℝ), (116944590703765815323380192/4966279557750234375:ℝ), (31383744477669898242962688/1655426519250078125:ℝ), (1586793703104856370774016/331085303850015625:ℝ)],
![(179120205326969780620397963/39730236462001875000:ℝ), (44734474107399602244515584/4966279557750234375:ℝ), (7448076744696796020688896/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission26_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (596415520143967623183/10849003236557312000000:ℝ) admission26_09_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission26_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission26_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_09_coefficients]

def admission26_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(169701115047233318932/215775046875:ℝ), (1235498240436826465084/647325140625:ℝ), (944852806100510482432/647325140625:ℝ), (72819816624294658048/215775046875:ℝ)],
![(53202317911794475328/43155009375:ℝ), (604699349568948811328/215775046875:ℝ), (412135765858442412032/215775046875:ℝ), (73449038688465977344/215775046875:ℝ)],
![(31889685376610500352/71925015625:ℝ), (572863796879847143168/647325140625:ℝ), (457368110352564224/1035720225:ℝ), (0:ℝ)]]
theorem admission26_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (2412766950107097/301675380736000000:ℝ) admission26_10_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission26_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission26_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_10_coefficients]

def admission26_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9595300494500863157254621/63568378339203000000:ℝ), (68418309121246458485388/331085303850015625:ℝ), (18545307744549321033472/331085303850015625:ℝ)],
![(748570312971750477346673/7946047292400375000:ℝ), (31088692508819837841888/331085303850015625:ℝ), (0:ℝ)]]
theorem admission26_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3544950524111033141361/10849003236557312000000:ℝ) admission26_11_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission26_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission26_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_11_coefficients]

def admission26_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission26_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission26_12_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission26_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission26_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_12_coefficients]

def admission26_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission26_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission26_13_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission26_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission26_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_13_coefficients]

def admission26_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission26_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission26_14_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission26_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission26_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission26_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission26_14_coefficients]

theorem admission26_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission26_00_pos hδ hp
  · exact admission26_01_pos hδ hp
  · exact admission26_02_pos hδ hp
  · exact admission26_03_pos hδ hp
  · exact admission26_04_pos hδ hp
  · exact admission26_05_pos hδ hp
  · exact admission26_06_pos hδ hp
  · exact admission26_07_pos hδ hp
  · exact admission26_08_pos hδ hp
  · exact admission26_09_pos hδ hp
  · exact admission26_10_pos hδ hp
  · exact admission26_11_pos hδ hp
  · exact admission26_12_pos hδ hp
  · exact admission26_13_pos hδ hp
  · exact admission26_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
