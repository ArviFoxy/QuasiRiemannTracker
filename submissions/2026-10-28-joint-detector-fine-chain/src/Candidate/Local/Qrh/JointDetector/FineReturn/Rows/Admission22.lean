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

def admission22_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission22_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission22_00_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission22_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission22_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_00_coefficients]

def admission22_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission22_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission22_01_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission22_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission22_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_01_coefficients]

def admission22_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission22_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission22_02_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission22_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission22_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_02_coefficients]

def admission22_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(209103045056/13809603:ℝ), (268485245888/13809603:ℝ), (20090066944/4603201:ℝ)],
![(148204658816/13809603:ℝ), (147292658816/13809603:ℝ), (0:ℝ)]]
theorem admission22_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1042559829/1178419456:ℝ) admission22_03_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission22_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission22_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_03_coefficients]

def admission22_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11046381836765181/4603201000000:ℝ), (2368:ℝ), (0:ℝ)],
![(8365793988615291/2301600500000:ℝ), (343254615500384/71925015625:ℝ), (84166488750192/71925015625:ℝ)]]
theorem admission22_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (583905015704457/4713677824000000:ℝ) admission22_04_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission22_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission22_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_04_coefficients]

def admission22_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(11758557096411907/4603201000000:ℝ), (347464868351484/71925015625:ℝ), (162611922020592/71925015625:ℝ)],
![(500257691077253/2301600500000:ℝ), (671558529608/2877000625:ℝ), (0:ℝ)]]
theorem admission22_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (221228286361641/2356838912000000:ℝ) admission22_05_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission22_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission22_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_05_coefficients]

def admission22_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12593280656781418178226419/36750468727351734375:ℝ), (24868751547520018805427827/36750468727351734375:ℝ), (4092639687510950209067136/12250156242450578125:ℝ), (0:ℝ)],
![(15454061867763627799009706/36750468727351734375:ℝ), (33227163988323148241469098/36750468727351734375:ℝ), (6806281243480083024255744/12250156242450578125:ℝ), (176215151418748575353856/2450031248490115625:ℝ)]]
theorem admission22_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (29089093987880940574989/160565247901048217600000:ℝ) admission22_06_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission22_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission22_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_06_coefficients]

def admission22_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(658885229675535278434633/63568378339203000000:ℝ), (4669031755815635294118/331085303850015625:ℝ), (252768883181065364592/66217060770003125:ℝ)],
![(202012502187085233666191/31784189169601500000:ℝ), (2078567398545552218772/331085303850015625:ℝ), (0:ℝ)]]
theorem admission22_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (784636741541223735921/2169800647311462400000:ℝ) admission22_07_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission22_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission22_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_07_coefficients]

def admission22_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(132460368946124095921347964513/3973023646200187500000000:ℝ), (1298235664383825870242743360433/19865118231000937500000000:ℝ), (3314251344705434367048973179/103464157453129882812500:ℝ), (0:ℝ)],
![(174232981801192190382730665527/1986511823100093750000000:ℝ), (2226206282408314527520729913191/9932559115500468750000000:ℝ), (9652400621719203869746321653/51732078726564941406250:ℝ), (259381712679217621682227596/5173207872656494140625:ℝ)]]
theorem admission22_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1837043019509547376737140589/86792025892458496000000000000:ℝ) admission22_08_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission22_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission22_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_08_coefficients]

def admission22_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9592233308817586340168777/63568378339203000000:ℝ), (1867464899223733750425928/4966279557750234375:ℝ), (496641109951104191014896/1655426519250078125:ℝ), (24793651611013380793344/331085303850015625:ℝ)],
![(2252479347195782686520911/31784189169601500000:ℝ), (701133047266501259463472/4966279557750234375:ℝ), (116376199135887437823264/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission22_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (596415520143967623183/10849003236557312000000:ℝ) admission22_09_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission22_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission22_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_09_coefficients]

def admission22_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(224632008354391183/71925015625:ℝ), (4855719679892620807/647325140625:ℝ), (733035067015106048/129465028125:ℝ), (55415742524828672/43155009375:ℝ)],
![(1062683492055446956/215775046875:ℝ), (2400022303494527404/215775046875:ℝ), (1624185848815900672/215775046875:ℝ), (286910307376820224/215775046875:ℝ)],
![(378183271363177204/215775046875:ℝ), (2251268647254971612/647325140625:ℝ), (1786594181064704/1035720225:ℝ), (0:ℝ)]]
theorem admission22_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (2412766950107097/301675380736000000:ℝ) admission22_10_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission22_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission22_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_10_coefficients]

def admission22_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(612114130574739429817591/63568378339203000000:ℝ), (4320957030701899638441/331085303850015625:ℝ), (1159081734034332564592/331085303850015625:ℝ)],
![(188973847812993396192689/31784189169601500000:ℝ), (1943043281801239865118/331085303850015625:ℝ), (0:ℝ)]]
theorem admission22_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3544950524111033141361/10849003236557312000000:ℝ) admission22_11_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission22_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission22_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_11_coefficients]

def admission22_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission22_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission22_12_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission22_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission22_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_12_coefficients]

def admission22_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission22_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission22_13_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission22_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission22_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_13_coefficients]

def admission22_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission22_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission22_14_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission22_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission22_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission22_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission22_14_coefficients]

theorem admission22_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission22_00_pos hδ hp
  · exact admission22_01_pos hδ hp
  · exact admission22_02_pos hδ hp
  · exact admission22_03_pos hδ hp
  · exact admission22_04_pos hδ hp
  · exact admission22_05_pos hδ hp
  · exact admission22_06_pos hδ hp
  · exact admission22_07_pos hδ hp
  · exact admission22_08_pos hδ hp
  · exact admission22_09_pos hδ hp
  · exact admission22_10_pos hδ hp
  · exact admission22_11_pos hδ hp
  · exact admission22_12_pos hδ hp
  · exact admission22_13_pos hδ hp
  · exact admission22_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
