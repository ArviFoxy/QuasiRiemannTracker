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

def admission27_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission27_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission27_00_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission27_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission27_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_00_coefficients]

def admission27_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission27_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission27_01_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission27_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission27_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_01_coefficients]

def admission27_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission27_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission27_02_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission27_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission27_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_02_coefficients]

def admission27_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(52346714912/13809603:ℝ), (66958265120/13809603:ℝ), (5022516736/4603201:ℝ)],
![(36977072000/13809603:ℝ), (36497072000/13809603:ℝ), (0:ℝ)]]
theorem admission27_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (253282755/294604864:ℝ) admission27_03_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission27_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission27_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_03_coefficients]

def admission27_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2873720140609147/4603201000000:ℝ), (608:ℝ), (0:ℝ)],
![(1092908097266333/1150800250000:ℝ), (88115254375096/71925015625:ℝ), (21041622187548/71925015625:ℝ)]]
theorem admission27_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (299843116172559/2356838912000000:ℝ) admission27_04_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission27_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission27_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_04_coefficients]

def admission27_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(113337001262541/184128040000:ℝ), (85503201820346/71925015625:ℝ), (40652980505148/71925015625:ℝ)],
![(2761076426887/230160050000:ℝ), (470787288/23016005:ℝ), (0:ℝ)]]
theorem admission27_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (9536927549139/117841945600000:ℝ) admission27_05_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission27_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission27_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_05_coefficients]

def admission27_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(656876797678361757778001/14700187490940693750:ℝ), (6404160128941449584350933/73500937454703468750:ℝ), (520381746524856799243488/12250156242450578125:ℝ), (0:ℝ)],
![(405718948568649065962126/7350093745470346875:ℝ), (860406835529810204755726/7350093745470346875:ℝ), (173677745321397284850432/2450031248490115625:ℝ), (22026893927343571919232/2450031248490115625:ℝ)]]
theorem admission27_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (14802674657151527770923/80282623950524108800000:ℝ) admission27_06_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission27_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission27_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_06_coefficients]

def admission27_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(32581159804070882933443/12713675667840600000:ℝ), (1151564057589051466173/331085303850015625:ℝ), (63192220795266341148/66217060770003125:ℝ)],
![(960656200534618912961/635683783392030000:ℝ), (97650817381334667996/66217060770003125:ℝ), (0:ℝ)]]
theorem admission27_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (36862128797238699003/108490032365573120000:ℝ) admission27_07_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission27_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission27_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_07_coefficients]

def admission27_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(193747551116602030987285128607/39730236462001875000000000:ℝ), (74589072607645476905887231163/7946047292400375000000000:ℝ), (1870949241342675219279493773/413856629812519531250000:ℝ), (0:ℝ)],
![(4857129433527182215693561681/397302364620018750000000:ℝ), (60197800771522321613189171693/1986511823100093750000000:ℝ), (504002387984955997062816801/20692831490625976562500:ℝ), (64845428169804405420556899/10346415745312988281250:ℝ)]]
theorem admission27_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1015789652009480296499405643/43396012946229248000000000000:ℝ) admission27_08_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission27_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission27_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_08_coefficients]

def admission27_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(5812534952297797484148619/317841891696015000000:ℝ), (45493080555332000692196/993255911550046875:ℝ), (61035121662636018715428/1655426519250078125:ℝ), (3099206451376672599168/331085303850015625:ℝ)],
![(121065180849516695065769/15892094584800750000:ℝ), (15046510541783724160928/993255911550046875:ℝ), (2491398145896383881008/331085303850015625:ℝ), (0:ℝ)]]
theorem admission27_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (26188893446991342957/542450161827865600000:ℝ) admission27_09_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission27_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission27_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_09_coefficients]

def admission27_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(51800095391503627/258930056250:ℝ), (209519001671609533/431550093750:ℝ), (242236427194062848/647325140625:ℝ), (19160843555135872/215775046875:ℝ)],
![(2637183827677868/8631001875:ℝ), (10058139070025844/14385003125:ℝ), (21063036651532288/43155009375:ℝ), (4077958579844096/43155009375:ℝ)],
![(2560475574334328/25893005625:ℝ), (1681577919764776/8631001875:ℝ), (3973085095936/41428809:ℝ), (0:ℝ)]]
theorem admission27_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (4909211698209/754188451840000:ℝ) admission27_10_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission27_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission27_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_10_coefficients]

def admission27_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(151343693520181845767441/63568378339203000000:ℝ), (2130603374934952497151/662170607700031250:ℝ), (289770433508583141148/331085303850015625:ℝ)],
![(4491052761612229173691/3178418916960150000:ℝ), (91177136006862528842/66217060770003125:ℝ), (0:ℝ)]]
theorem admission27_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (6655245397959191571/21698006473114624000:ℝ) admission27_11_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission27_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission27_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_11_coefficients]

def admission27_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission27_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission27_12_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission27_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission27_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_12_coefficients]

def admission27_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission27_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission27_13_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission27_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission27_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_13_coefficients]

def admission27_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission27_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission27_14_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission27_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission27_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission27_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission27_14_coefficients]

theorem admission27_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission27_00_pos hδ hp
  · exact admission27_01_pos hδ hp
  · exact admission27_02_pos hδ hp
  · exact admission27_03_pos hδ hp
  · exact admission27_04_pos hδ hp
  · exact admission27_05_pos hδ hp
  · exact admission27_06_pos hδ hp
  · exact admission27_07_pos hδ hp
  · exact admission27_08_pos hδ hp
  · exact admission27_09_pos hδ hp
  · exact admission27_10_pos hδ hp
  · exact admission27_11_pos hδ hp
  · exact admission27_12_pos hδ hp
  · exact admission27_13_pos hδ hp
  · exact admission27_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
