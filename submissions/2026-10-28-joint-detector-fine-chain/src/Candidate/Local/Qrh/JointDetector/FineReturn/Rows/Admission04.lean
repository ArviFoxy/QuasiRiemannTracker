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

def admission04_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission04_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission04_00_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission04_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission04_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_00_coefficients]

def admission04_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission04_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission04_01_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission04_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission04_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_01_coefficients]

def admission04_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission04_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission04_02_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission04_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission04_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_02_coefficients]

def admission04_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(37555514368/38073609:ℝ), (46991780224/38073609:ℝ), (1112473984/4230401:ℝ)],
![(27072426256/38073609:ℝ), (26424426256/38073609:ℝ), (0:ℝ)]]
theorem admission04_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1400333357/1624473984:ℝ) admission04_03_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission04_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission04_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_03_coefficients]

def admission04_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(357884178647453/2644000625000:ℝ), (128:ℝ), (0:ℝ)],
![(936695986878017/4230401000000:ℝ), (93295833955094/330500078125:ℝ), (22851911352547/330500078125:ℝ)]]
theorem admission04_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (68555734057641/676864160000000:ℝ) admission04_04_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission04_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission04_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_04_coefficients]

def admission04_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1430027303302769/7932001875000:ℝ), (316013132854282/991500234375:ℝ), (44571227649547/330500078125:ℝ)],
![(1612792712142769/63456015000000:ℝ), (33359060279/1133143125:ℝ), (0:ℝ)]]
theorem admission04_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (549476079862231/5414913280000000:ℝ) admission04_05_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission04_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission04_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_05_coefficients]

def admission04_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(64597669045646167657922/12583330749000703125:ℝ), (906289291402357862213954/93116647542605203125:ℝ), (2149037854952881107726656/465583237713026015625:ℝ), (0:ℝ)],
![(12084558752716980938886593/1862332950852104062500:ℝ), (995176322094113333361289/74493318034084162500:ℝ), (3656490783090664041870488/465583237713026015625:ℝ), (9980225810510020957424/10346294171400578125:ℝ)]]
theorem admission04_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (9565772013517160591771/63567631389085152000000:ℝ) admission04_06_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission04_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission04_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_06_coefficients]

def admission04_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(71364813360194299455959/100666645992005625000:ℝ), (1255379518006384260218/1398147861000078125:ℝ), (60109690473650981347/279629572200015625:ℝ)],
![(357118241671337795228371/805333167936045000000:ℝ), (1174734692007274574843/2796295722000156250:ℝ), (0:ℝ)]]
theorem admission04_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (4748665547418427526413/13744352732775168000000:ℝ) admission04_07_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission04_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission04_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_07_coefficients]

def admission04_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3737606501023371339590986979/25166661498001406250000000:ℝ), (674621554329006544021612299/2796295722000156250000000:ℝ), (153149343528710295598517107/1572916343625087890625000:ℝ), (0:ℝ)],
![(241422458955237783049475602831/201333291984011250000000000:ℝ), (69040123788737195002017401111/22370365776001250000000000:ℝ), (33492009745703475246097246403/12583330749000703125000000:ℝ), (53779820385820672712541731/69907393050003906250000:ℝ)]]
theorem admission04_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (8896983988637214224939293/2290725455462528000000000000:ℝ) admission04_08_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission04_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission04_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_08_coefficients]

def admission04_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(276869024112799174083163/100666645992005625000:ℝ), (5482202382816159252716/838888716600046875:ℝ), (12310084040907199296872/2516666149800140625:ℝ), (99239990681325904/89481463104005:ℝ)],
![(1049081660302366507305107/805333167936045000000:ℝ), (2143620349416422402864/838888716600046875:ℝ), (3145818336841582944167/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission04_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (52155025968142729897/916290182185011200000:ℝ) admission04_09_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission04_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission04_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_09_coefficients]

def admission04_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12130193259755488/991500234375:ℝ), (9052241021455104/330500078125:ℝ), (55511296591144208/2974500703125:ℝ), (1493329596759248/424928671875:ℝ)],
![(20664046918324924/991500234375:ℝ), (2957240082025284/66100015625:ℝ), (83464935454644512/2974500703125:ℝ), (12429872518481504/2974500703125:ℝ)],
![(10191418279648787/1322000312500:ℝ), (19706078758448787/1322000312500:ℝ), (760200838304/105760025:ℝ), (0:ℝ)]]
theorem admission04_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (3014558748010917/346554449920000000:ℝ) admission04_10_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission04_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission04_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_10_coefficients]

def admission04_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(179212512962056383959/268444389312015000:ℝ), (10612451379254552787584/12583330749000703125:ℝ), (281530196441380181347/1398147861000078125:ℝ)],
![(111928537680984450710303/268444389312015000000:ℝ), (19835403321457790989721/50333322996002812500:ℝ), (0:ℝ)]]
theorem admission04_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (7166391980453285431791/22907254554625280000000:ℝ) admission04_11_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission04_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission04_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_11_coefficients]

def admission04_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission04_12_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission04_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission04_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_12_coefficients]

def admission04_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission04_13_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission04_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission04_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_13_coefficients]

def admission04_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission04_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission04_14_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission04_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission04_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission04_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission04_14_coefficients]

theorem admission04_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ)) (hp : p ∈ Set.Icc (7/16:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission04_00_pos hδ hp
  · exact admission04_01_pos hδ hp
  · exact admission04_02_pos hδ hp
  · exact admission04_03_pos hδ hp
  · exact admission04_04_pos hδ hp
  · exact admission04_05_pos hδ hp
  · exact admission04_06_pos hδ hp
  · exact admission04_07_pos hδ hp
  · exact admission04_08_pos hδ hp
  · exact admission04_09_pos hδ hp
  · exact admission04_10_pos hδ hp
  · exact admission04_11_pos hδ hp
  · exact admission04_12_pos hδ hp
  · exact admission04_13_pos hδ hp
  · exact admission04_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
