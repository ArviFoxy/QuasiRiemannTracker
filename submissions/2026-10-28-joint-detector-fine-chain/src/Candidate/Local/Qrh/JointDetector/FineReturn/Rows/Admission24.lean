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

def admission24_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission24_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission24_00_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission24_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission24_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_00_coefficients]

def admission24_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission24_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission24_01_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission24_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission24_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_01_coefficients]

def admission24_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission24_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission24_02_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission24_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission24_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_02_coefficients]

def admission24_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(833355809408/13809603:ℝ), (1072636612736/13809603:ℝ), (80360267776/4603201:ℝ)],
![(590994635264/13809603:ℝ), (589170635264/13809603:ℝ), (0:ℝ)]]
theorem admission24_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1042559829/1178419456:ℝ) admission24_03_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission24_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission24_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_03_coefficients]

def admission24_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1779467173359339/184128040000:ℝ), (9600:ℝ), (0:ℝ)],
![(3331322808924287/230160050000:ℝ), (1373018462001536/71925015625:ℝ), (336665955000768/71925015625:ℝ)]]
theorem admission24_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (47343649921983/377094225920000:ℝ) admission24_04_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission24_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission24_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_04_coefficients]

def admission24_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(46478480709752077/4603201000000:ℝ), (1378955351265736/71925015625:ℝ), (650447688082368/71925015625:ℝ)],
![(1037504514763653/1150800250000:ℝ), (2686234118432/2877000625:ℝ), (0:ℝ)]]
theorem admission24_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (221228286361641/2356838912000000:ℝ) admission24_05_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission24_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission24_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_05_coefficients]

def admission24_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(20067485990878542462389362/7350093745470346875:ℝ), (1077842115462251986746634/198651182310009375:ℝ), (6604554927767843682412032/2450031248490115625:ℝ), (0:ℝ)],
![(122340775545366678444645032/36750468727351734375:ℝ), (264540678541439841984320168/36750468727351734375:ℝ), (54450249947840664194045952/12250156242450578125:ℝ), (1409721211349988602830848/2450031248490115625:ℝ)]]
theorem admission24_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (11738888660436799223367/64226099160419287040000:ℝ) admission24_06_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission24_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission24_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_06_coefficients]

def admission24_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(520221479908175299650043/12713675667840600000:ℝ), (3710115194468736463524/66217060770003125:ℝ), (1011075532724261458368/66217060770003125:ℝ)],
![(401554972447458246668303/15892094584800750000:ℝ), (8314269594182208875088/331085303850015625:ℝ), (0:ℝ)]]
theorem admission24_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (784636741541223735921/2169800647311462400000:ℝ) admission24_07_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission24_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission24_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_07_coefficients]

def admission24_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(552595755204924532235596224929/1986511823100093750000000:ℝ), (1094426486570785857771679639859/1986511823100093750000000:ℝ), (282245993095631392224318429/1034641574531298828125:ℝ), (0:ℝ)],
![(1728296722876034560768023022621/2483139778875117187500000:ℝ), (4438689456116195312613686474983/2483139778875117187500000:ℝ), (38609602486876815478985286612/25866039363282470703125:ℝ), (2075053701433740973457820768/5173207872656494140625:ℝ)]]
theorem admission24_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (6189795717645612751577523/277734482855867187200000000:ℝ) admission24_08_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission24_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission24_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_08_coefficients]

def admission24_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(75275491496539207499502311/63568378339203000000:ℝ), (2944966449403114767447536/993255911550046875:ℝ), (787937666601753872590656/331085303850015625:ℝ), (198349212888107046346752/331085303850015625:ℝ)],
![(44870769365552147766469003/79460472924003750000:ℝ), (5597560968327303545612224/4966279557750234375:ℝ), (931009593087099502586112/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission24_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (596415520143967623183/10849003236557312000000:ℝ) admission24_09_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission24_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission24_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_09_coefficients]

def admission24_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(10665888302589376922/215775046875:ℝ), (8598147757114931422/71925015625:ℝ), (19640340566263126016/215775046875:ℝ), (4511912160007708672/215775046875:ℝ)],
![(50252571008495944432/647325140625:ℝ), (12665065563085365104/71925015625:ℝ), (77503944313359712256/647325140625:ℝ), (4590564918029123584/215775046875:ℝ)],
![(18009759298039772896/647325140625:ℝ), (3986232332076312544/71925015625:ℝ), (28585506897035264/1035720225:ℝ), (0:ℝ)]]
theorem admission24_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (2412766950107097/301675380736000000:ℝ) admission24_10_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission24_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission24_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_10_coefficients]

def admission24_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2415293579135920859287961/63568378339203000000:ℝ), (17164327561143609265486/331085303850015625:ℝ), (4636326936137330258368/331085303850015625:ℝ)],
![(375506002865912423244017/15892094584800750000:ℝ), (7772173127204959460472/331085303850015625:ℝ), (0:ℝ)]]
theorem admission24_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3544950524111033141361/10849003236557312000000:ℝ) admission24_11_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission24_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission24_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_11_coefficients]

def admission24_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission24_12_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission24_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission24_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_12_coefficients]

def admission24_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission24_13_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission24_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission24_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_13_coefficients]

def admission24_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission24_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission24_14_coefficients
      (225/512:ℝ) (57/128:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission24_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission24_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission24_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission24_14_coefficients]

theorem admission24_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission24_00_pos hδ hp
  · exact admission24_01_pos hδ hp
  · exact admission24_02_pos hδ hp
  · exact admission24_03_pos hδ hp
  · exact admission24_04_pos hδ hp
  · exact admission24_05_pos hδ hp
  · exact admission24_06_pos hδ hp
  · exact admission24_07_pos hδ hp
  · exact admission24_08_pos hδ hp
  · exact admission24_09_pos hδ hp
  · exact admission24_10_pos hδ hp
  · exact admission24_11_pos hδ hp
  · exact admission24_12_pos hδ hp
  · exact admission24_13_pos hδ hp
  · exact admission24_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
