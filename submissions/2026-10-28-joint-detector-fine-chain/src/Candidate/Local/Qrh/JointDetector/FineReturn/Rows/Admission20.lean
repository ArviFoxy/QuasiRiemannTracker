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

def admission20_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12603201/4603201:ℝ), (0:ℝ)]]
theorem admission20_00_identity (δ p : ℝ) : admissionGuard .Cphys δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (15016005/9206402:ℝ) admission20_00_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_00_coefficients, Fin.sum_univ_succ, admission_power_Cphys_00] <;> ring
theorem admission20_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 0 := by
  rw [admission20_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_00_coefficients]

def admission20_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4603201:ℝ), (0:ℝ)]]
theorem admission20_01_identity (δ p : ℝ) : admissionGuard .Cphys δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (5206402/4603201:ℝ) admission20_01_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_01_coefficients, Fin.sum_univ_succ, admission_power_Cphys_01] <;> ring
theorem admission20_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 1 := by
  rw [admission20_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_01_coefficients]

def admission20_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(3945996453113/4603201000000:ℝ), (0:ℝ)]]
theorem admission20_02_identity (δ p : ℝ) : admissionGuard .Cphys δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (5260405546887/9206402000000:ℝ) admission20_02_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_02_coefficients, Fin.sum_univ_succ, admission_power_Cphys_02] <;> ring
theorem admission20_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 2 := by
  rw [admission20_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_02_coefficients]

def admission20_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(52648807616/13809603:ℝ), (67284357824/13809603:ℝ), (5022516736/4603201:ℝ)],
![(37279164704/13809603:ℝ), (36823164704/13809603:ℝ), (0:ℝ)]]
theorem admission20_03_identity (δ p : ℝ) : admissionGuard .Cphys δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (1042559829/1178419456:ℝ) admission20_03_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_03_coefficients, Fin.sum_univ_succ, admission_power_Cphys_03] <;> ring
theorem admission20_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 3 := by
  rw [admission20_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_03_coefficients]

def admission20_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1361235856078017/2301600500000:ℝ), (576:ℝ), (0:ℝ)],
![(4220383960612219/4603201000000:ℝ), (85813653875096/71925015625:ℝ), (21041622187548/71925015625:ℝ)]]
theorem admission20_04_identity (δ p : ℝ) : admissionGuard .Cphys δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (142030949765949/1178419456000000:ℝ) admission20_04_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_04_coefficients, Fin.sum_univ_succ, admission_power_Cphys_04] <;> ring
theorem admission20_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 4 := by
  rw [admission20_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_04_coefficients]

def admission20_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1504918891129919/2301600500000:ℝ), (88229232355396/71925015625:ℝ), (40652980505148/71925015625:ℝ)],
![(231634279234053/4603201000000:ℝ), (167889632402/2877000625:ℝ), (0:ℝ)]]
theorem admission20_05_identity (δ p : ℝ) : admissionGuard .Cphys δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (221228286361641/2356838912000000:ℝ) admission20_05_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_05_coefficients, Fin.sum_univ_succ, admission_power_Cphys_05] <;> ring
theorem admission20_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 5 := by
  rw [admission20_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_05_coefficients]

def admission20_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(317238530891743407573571/7350093745470346875:ℝ), (3093336178022859296937743/36750468727351734375:ℝ), (502778175352880753023296/12250156242450578125:ℝ), (0:ℝ)],
![(789038161242423189293393/14700187490940693750:ℝ), (8386580582402371057081813/73500937454703468750:ℝ), (850785155435010378031968/12250156242450578125:ℝ), (22026893927343571919232/2450031248490115625:ℝ)]]
theorem admission20_06_identity (δ p : ℝ) : admissionGuard .Cphys δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (7143209665364706402033/40141311975262054400000:ℝ) admission20_06_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_06_coefficients, Fin.sum_univ_succ, admission_power_Cphys_06] <;> ring
theorem admission20_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 6 := by
  rw [admission20_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_06_coefficients]

def admission20_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(135265156819033000429/50854702671362400:ℝ), (1182951820318766180886/331085303850015625:ℝ), (63192220795266341148/66217060770003125:ℝ)],
![(20448253411379745433027/12713675667840600000:ℝ), (519641849636388054693/331085303850015625:ℝ), (0:ℝ)]]
theorem admission20_07_identity (δ p : ℝ) : admissionGuard .Cphys δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (784636741541223735921/2169800647311462400000:ℝ) admission20_07_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_07_coefficients, Fin.sum_univ_succ, admission_power_Cphys_07] <;> ring
theorem admission20_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 7 := by
  rw [admission20_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_07_coefficients]

def admission20_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(75394301526267378610076290637/19865118231000937500000000:ℝ), (1155816172648620348959617417/158920945848007500000000:ℝ), (721651051681379573884739703/206928314906259765625000:ℝ), (0:ℝ)],
![(442753995288650947802223620767/39730236462001875000000000:ℝ), (223992939110874826994850326459/7946047292400375000000000:ℝ), (9652400621719203869746321653/413856629812519531250000:ℝ), (64845428169804405420556899/10346415745312988281250:ℝ)]]
theorem admission20_08_identity (δ p : ℝ) : admissionGuard .Cphys δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (410626683750033540118867473/21698006473114624000000000000:ℝ) admission20_08_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_08_coefficients, Fin.sum_univ_succ, admission_power_Cphys_08] <;> ring
theorem admission20_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 8 := by
  rw [admission20_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_08_coefficients]

def admission20_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3114264047141827685890289/158920945848007500000:ℝ), (48046792506490223830952/993255911550046875:ℝ), (63125155825140029038296/1655426519250078125:ℝ), (3099206451376672599168/331085303850015625:ℝ)],
![(2837296758976191788947339/317841891696015000000:ℝ), (17600222492941947299684/993255911550046875:ℝ), (14547024891985929727908/1655426519250078125:ℝ), (0:ℝ)]]
theorem admission20_09_identity (δ p : ℝ) : admissionGuard .Cphys δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (596415520143967623183/10849003236557312000000:ℝ) admission20_09_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_09_coefficients, Fin.sum_univ_succ, admission_power_Cphys_09] <;> ring
theorem admission20_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 9 := by
  rw [admission20_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_09_coefficients]

def admission20_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(42984246152102218/215775046875:ℝ), (6790049904743702/14385003125:ℝ), (25187385762006656/71925015625:ℝ), (16702944866966656/215775046875:ℝ)],
![(205247105508380938/647325140625:ℝ), (153200855962016174/215775046875:ℝ), (308104975010821376/647325140625:ℝ), (17931894211051264/215775046875:ℝ)],
![(144035415626702903/1294650281250:ℝ), (94553940340794301/431550093750:ℝ), (111662136316544/1035720225:ℝ), (0:ℝ)]]
theorem admission20_10_identity (δ p : ℝ) : admissionGuard .Cphys δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (2412766950107097/301675380736000000:ℝ) admission20_10_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_10_coefficients, Fin.sum_univ_succ, admission_power_Cphys_10] <;> ring
theorem admission20_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 10 := by
  rw [admission20_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_10_coefficients]

def admission20_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(78615204287235572480323/31784189169601500000:ℝ), (219035365576694714129/66217060770003125:ℝ), (289770433508583141148/331085303850015625:ℝ)],
![(3828310811461355306681/2542735133568120000:ℝ), (971521640900619932559/662170607700031250:ℝ), (0:ℝ)]]
theorem admission20_11_identity (δ p : ℝ) : admissionGuard .Cphys δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3544950524111033141361/10849003236557312000000:ℝ) admission20_11_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_11_coefficients, Fin.sum_univ_succ, admission_power_Cphys_11] <;> ring
theorem admission20_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 11 := by
  rw [admission20_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_11_coefficients]

def admission20_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission20_12_identity (δ p : ℝ) : admissionGuard .Cphys δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission20_12_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_12_coefficients, Fin.sum_univ_succ, admission_power_Cphys_12] <;> ring
theorem admission20_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 12 := by
  rw [admission20_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_12_coefficients]

def admission20_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission20_13_identity (δ p : ℝ) : admissionGuard .Cphys δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (262253340591/5000000000000:ℝ) admission20_13_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_13_coefficients, Fin.sum_univ_succ, admission_power_Cphys_13] <;> ring
theorem admission20_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 13 := by
  rw [admission20_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_13_coefficients]

def admission20_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission20_14_identity (δ p : ℝ) : admissionGuard .Cphys δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission20_14_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_Cphys_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission20_14_coefficients, Fin.sum_univ_succ, admission_power_Cphys_14] <;> ring
theorem admission20_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .Cphys δ p 14 := by
  rw [admission20_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission20_14_coefficients]

theorem admission20_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .Cphys δ p j := by
  fin_cases j
  · exact admission20_00_pos hδ hp
  · exact admission20_01_pos hδ hp
  · exact admission20_02_pos hδ hp
  · exact admission20_03_pos hδ hp
  · exact admission20_04_pos hδ hp
  · exact admission20_05_pos hδ hp
  · exact admission20_06_pos hδ hp
  · exact admission20_07_pos hδ hp
  · exact admission20_08_pos hδ hp
  · exact admission20_09_pos hδ hp
  · exact admission20_10_pos hδ hp
  · exact admission20_11_pos hδ hp
  · exact admission20_12_pos hδ hp
  · exact admission20_13_pos hδ hp
  · exact admission20_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
