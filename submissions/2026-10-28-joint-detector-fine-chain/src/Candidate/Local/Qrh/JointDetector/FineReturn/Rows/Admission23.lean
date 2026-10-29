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

def admission23_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission23_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission23_00_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission23_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission23_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_00_coefficients]

def admission23_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission23_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission23_01_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission23_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission23_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_01_coefficients]

def admission23_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission23_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission23_02_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission23_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission23_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_02_coefficients]

def admission23_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(834636180224/13809603:ℝ), (1073940983552/13809603:ℝ), (80360267776/4603201:ℝ)],
![(592275006080/13809603:ℝ), (590475006080/13809603:ℝ), (0:ℝ)]]
theorem admission23_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (4199668125/4713677824:ℝ) admission23_03_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission23_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission23_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_03_coefficients]

def admission23_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(21946761804765181/2301600500000:ℝ), (9472:ℝ), (0:ℝ)],
![(66033300454032627/4603201000000:ℝ), (1363812060001536/71925015625:ℝ), (336665955000768/71925015625:ℝ)]]
theorem admission23_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (583905015704457/4713677824000000:ℝ) admission23_04_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission23_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission23_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_04_coefficients]

def admission23_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4717829132317799/460320100000:ℝ), (1389859473405936/71925015625:ℝ), (650447688082368/71925015625:ℝ)],
![(193993146899221/184128040000:ℝ), (624479800808/575400125:ℝ), (0:ℝ)]]
theorem admission23_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (36616115233017/377094225920000:ℝ) admission23_05_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission23_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission23_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_05_coefficients]

def admission23_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(99479902533668575221711308/36750468727351734375:ℝ), (197698358690342880239322572/36750468727351734375:ℝ), (32741117500087601672537088/12250156242450578125:ℝ), (0:ℝ)],
![(24296649624928508270881906/7350093745470346875:ℝ), (10513529834850644187020618/1470018749094069375:ℝ), (10833718561817809490904576/2450031248490115625:ℝ), (1409721211349988602830848/2450031248490115625:ℝ)]]
theorem admission23_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (29089093987880940574989/160565247901048217600000:ℝ) admission23_06_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission23_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission23_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_06_coefficients]

def admission23_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1312681198938314504896969/31784189169601500000:ℝ), (18676127023262541176472/331085303850015625:ℝ), (1011075532724261458368/66217060770003125:ℝ)],
![(326094977625117099643387/12713675667840600000:ℝ), (1687964129020213546788/66217060770003125:ℝ), (0:ℝ)]]
theorem admission23_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (637188226352268939909/1735840517849169920000:ℝ) admission23_07_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission23_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission23_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_07_coefficients]

def admission23_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(1298436883648944874161443016683/4966279557750234375000000:ℝ), (2570908180750712667189549061169/4966279557750234375000000:ℝ), (6628502689410868734097946358/25866039363282470703125:ℝ), (0:ℝ)],
![(1349416376555481066043399399841/1986511823100093750000000:ℝ), (696977670124491091839017832919/397302364620018750000000:ℝ), (7636391069779379881495054449/5173207872656494140625:ℝ), (2075053701433740973457820768/5173207872656494140625:ℝ)]]
theorem admission23_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1837043019509547376737140589/86792025892458496000000000000:ℝ) admission23_08_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission23_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission23_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_08_coefficients]

def admission23_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(191428296565300359718132589/158920945848007500000:ℝ), (14926388945739027043259296/4966279557750234375:ℝ), (3973128879608833528119168/1655426519250078125:ℝ), (198349212888107046346752/331085303850015625:ℝ)],
![(37192442622022654600925927/63568378339203000000:ℝ), (1159823533410151350326768/993255911550046875:ℝ), (7715601117497309342016/13243412154000625:ℝ), (0:ℝ)]]
theorem admission23_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (98331989271200450271/1735840517849169920000:ℝ) admission23_09_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission23_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission23_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_09_coefficients]

def admission23_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(6391908086419456216/129465028125:ℝ), (8536780074357599352/71925015625:ℝ), (57934930539015749632/647325140625:ℝ), (4354606643964878848/215775046875:ℝ)],
![(2026664626501213064/25893005625:ℝ), (2540740229071788648/14385003125:ℝ), (15393144720331808768/129465028125:ℝ), (886651880397258752/43155009375:ℝ)],
![(49231809140653346/1726200375:ℝ), (32689884776857782/575400125:ℝ), (390694661519360/13809603:ℝ), (0:ℝ)]]
theorem admission23_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (322052662269981/38614448734208000:ℝ) admission23_10_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission23_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission23_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_10_coefficients]

def admission23_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1219194187534912307996599/31784189169601500000:ℝ), (17283828122807598553764/331085303850015625:ℝ), (4636326936137330258368/331085303850015625:ℝ)],
![(305023761479510689936261/12713675667840600000:ℝ), (12626677902190317998/529736486160025:ℝ), (0:ℝ)]]
theorem admission23_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (2879425984315113984261/8679202589245849600000:ℝ) admission23_11_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission23_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission23_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_11_coefficients]

def admission23_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission23_12_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission23_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission23_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_12_coefficients]

def admission23_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission23_13_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission23_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission23_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_13_coefficients]

def admission23_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission23_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission23_14_coefficients
      (111/256:ℝ) (225/512:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission23_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission23_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission23_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission23_14_coefficients]

theorem admission23_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (225/512:ℝ)) (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission23_00_pos hδ hp
  · exact admission23_01_pos hδ hp
  · exact admission23_02_pos hδ hp
  · exact admission23_03_pos hδ hp
  · exact admission23_04_pos hδ hp
  · exact admission23_05_pos hδ hp
  · exact admission23_06_pos hδ hp
  · exact admission23_07_pos hδ hp
  · exact admission23_08_pos hδ hp
  · exact admission23_09_pos hδ hp
  · exact admission23_10_pos hδ hp
  · exact admission23_11_pos hδ hp
  · exact admission23_12_pos hδ hp
  · exact admission23_13_pos hδ hp
  · exact admission23_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
