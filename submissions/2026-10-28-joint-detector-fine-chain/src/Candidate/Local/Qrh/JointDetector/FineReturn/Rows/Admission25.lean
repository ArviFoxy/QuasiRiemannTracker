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

def admission25_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission25_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission25_00_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission25_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission25_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_00_coefficients]

def admission25_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission25_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission25_01_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission25_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission25_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_01_coefficients]

def admission25_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission25_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission25_02_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission25_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission25_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_02_coefficients]

def admission25_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3329823237632/13809603:ℝ), (4290546450944/13809603:ℝ), (321441071104/4603201:ℝ)],
![(2362915282688/13809603:ℝ), (2359291282688/13809603:ℝ), (0:ℝ)]]
theorem admission25_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (8369907441/9427355648:ℝ) admission25_03_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission25_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission25_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_03_coefficients]

def admission25_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(3547096357359339/92064020000:ℝ), (38400:ℝ), (0:ℝ)],
![(264723667800616671/4603201000000:ℝ), (5473661044006144/71925015625:ℝ), (1346663820003072/71925015625:ℝ)]]
theorem admission25_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (47343649921983/377094225920000:ℝ) admission25_04_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission25_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission25_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_04_coefficients]

def admission25_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(93102971153487629/2301600500000:ℝ), (5515821405062944/71925015625:ℝ), (2601790752329472/71925015625:ℝ)],
![(18293659727490337/4603201000000:ℝ), (11617266244944/2877000625:ℝ), (0:ℝ)]]
theorem admission25_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (1800316026271989/18854711296000000:ℝ) admission25_05_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission25_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission25_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_05_coefficients]

def admission25_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(159522618092570794038501832/7350093745470346875:ℝ), (12721198054193661696655624/294003749818813875:ℝ), (52836439422142749459296256/2450031248490115625:ℝ), (0:ℝ)],
![(970184567332005327149820356/36750468727351734375:ℝ), (420886828773114096918588916/7350093745470346875:ℝ), (434475371027718846594275328/12250156242450578125:ℝ), (11277769690799908822646784/2450031248490115625:ℝ)]]
theorem admission25_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (11738888660436799223367/64226099160419287040000:ℝ) admission25_06_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission25_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission25_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_06_coefficients]

def admission25_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(207687418992622900127999/1271367566784060000:ℝ), (14840460777874945854096/66217060770003125:ℝ), (4044302130897045833472/66217060770003125:ℝ)],
![(6453480103857807593823523/63568378339203000000:ℝ), (33508180478566553218056/331085303850015625:ℝ), (0:ℝ)]]
theorem admission25_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (6324488097926239643229/17358405178491699200000:ℝ) admission25_07_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission25_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission25_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_07_coefficients]

def admission25_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(547233637129830665769491812117/248313977887511718750000:ℝ), (2178251100058010403913062407219/496627955775023437500000:ℝ), (2257967944765051137794547432/1034641574531298828125:ℝ), (0:ℝ)],
![(13605701980069753155471510041581/2483139778875117187500000:ℝ), (70250497354934575564997805677723/4966279557750234375000000:ℝ), (307166231343094859545842235428/25866039363282470703125:ℝ), (16600429611469927787662566144/5173207872656494140625:ℝ)]]
theorem admission25_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (6189795717645612751577523/277734482855867187200000000:ℝ) admission25_08_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission25_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission25_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_08_coefficients]

def admission25_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(60157645924465127491564283/6356837833920300000:ℝ), (23549798132082698343482816/993255911550046875:ℝ), (6303501332814030980725248/331085303850015625:ℝ), (1586793703104856370774016/331085303850015625:ℝ)],
![(1458760991929176251799171247/317841891696015000000:ℝ), (45538874064047278638549472/4966279557750234375:ℝ), (7581838931097052681352448/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission25_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (4843961812355881749507/86792025892458496000000:ℝ) admission25_09_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission25_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission25_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_09_coefficients]

def admission25_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(169630520576525365456/215775046875:ℝ), (410427437198269404368/215775046875:ℝ), (312357782867696058368/215775046875:ℝ), (71561372495952019456/215775046875:ℝ)],
![(267153237381371582992/215775046875:ℝ), (1817138213803155581488/647325140625:ℝ), (1232247227589410848768/647325140625:ℝ), (72190594560123338752/215775046875:ℝ)],
![(32293766140979553628/71925015625:ℝ), (580119890818174542652/647325140625:ℝ), (463159130370973696/1035720225:ℝ), (0:ℝ)]]
theorem admission25_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (157750511471174337/19307224367104000000:ℝ) admission25_10_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission25_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission25_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_10_coefficients]

def admission25_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4820669699137126428654617/31784189169601500000:ℝ), (68657310244574437061944/331085303850015625:ℝ), (18545307744549321033472/331085303850015625:ℝ)],
![(6034601407547393518827997/63568378339203000000:ℝ), (31327693632147816418444/331085303850015625:ℝ), (0:ℝ)]]
theorem admission25_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (28576932018019702486749/86792025892458496000000:ℝ) admission25_11_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission25_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission25_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_11_coefficients]

def admission25_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission25_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission25_12_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission25_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission25_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_12_coefficients]

def admission25_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission25_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission25_13_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission25_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission25_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_13_coefficients]

def admission25_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission25_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission25_14_coefficients
      (225/512:ℝ) (453/1024:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission25_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission25_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission25_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission25_14_coefficients]

theorem admission25_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (225/512:ℝ) (453/1024:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission25_00_pos hδ hp
  · exact admission25_01_pos hδ hp
  · exact admission25_02_pos hδ hp
  · exact admission25_03_pos hδ hp
  · exact admission25_04_pos hδ hp
  · exact admission25_05_pos hδ hp
  · exact admission25_06_pos hδ hp
  · exact admission25_07_pos hδ hp
  · exact admission25_08_pos hδ hp
  · exact admission25_09_pos hδ hp
  · exact admission25_10_pos hδ hp
  · exact admission25_11_pos hδ hp
  · exact admission25_12_pos hδ hp
  · exact admission25_13_pos hδ hp
  · exact admission25_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
