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

def admission13_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission13_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission13_00_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission13_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission13_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_00_coefficients]

def admission13_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission13_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission13_01_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission13_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission13_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_01_coefficients]

def admission13_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission13_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission13_02_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission13_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission13_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_02_coefficients]

def admission13_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(146029123936/38073609:ℝ), (184710187360/38073609:ℝ), (4449895936/4230401:ℝ)],
![(104966416000/38073609:ℝ), (14789488000/5439087:ℝ), (0:ℝ)]]
theorem admission13_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (661056265/812236992:ℝ) admission13_03_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission13_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission13_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_03_coefficients]

def admission13_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13230008914301607/21152005000000:ℝ), (608:ℝ), (0:ℝ)],
![(4944103619800273/5288001250000:ℝ), (394335340820376/330500078125:ℝ), (91407645410188/330500078125:ℝ)]]
theorem admission13_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (1302558947095179/10829826560000000:ℝ) admission13_04_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission13_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission13_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_04_coefficients]

def admission13_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1547254851807811/2538240600000:ℝ), (1147672996139878/991500234375:ℝ), (178284910598188/330500078125:ℝ)],
![(96976837257641/3172800750000:ℝ), (358128952/9065145:ℝ), (0:ℝ)]]
theorem admission13_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (41576239691359/541491328000000:ℝ) admission13_05_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission13_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission13_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_05_coefficients]

def admission13_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(8076214398195521761358143/186233295085210406250:ℝ), (11224573834926504149687917/133023782203721718750:ℝ), (19113772164250210120512352/465583237713026015625:ℝ), (0:ℝ)],
![(4893306114933258866888018/93116647542605203125:ℝ), (10277458443156887992772818/93116647542605203125:ℝ), (6106581162895350634819328/93116647542605203125:ℝ), (79841806484080167659392/10346294171400578125:ℝ)]]
theorem admission13_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (169893983271510229833989/1017082102225362432000000:ℝ) admission13_06_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission13_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission13_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_06_coefficients]

def admission13_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(400823949920774134554349/161066633587209000000:ℝ), (4620026468428114084913/1398147861000078125:ℝ), (240438761894603925388/279629572200015625:ℝ)],
![(1760612235365652842489/1150475954194350000:ℝ), (59480237569988586068/39947081742859375:ℝ), (0:ℝ)]]
theorem admission13_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (60109690473650981347/196347896182502400000:ℝ) admission13_07_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission13_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission13_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_07_coefficients]

def admission13_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(46960385007188876702119244661/11185182888000625000000000:ℝ), (161923692165396814341956803441/20133329198401125000000000:ℝ), (12127525463851253579185998133/3145832687250175781250000:ℝ), (0:ℝ)],
![(1278195456630078389073644763/111851828880006250000000:ℝ), (20568589650475588142833118593/719047471371468750000000:ℝ), (3671772173483410486263382121/157291634362508789062500:ℝ), (53779820385820672712541731/8738424131250488281250:ℝ)]]
theorem admission13_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (89481446755797354573129181/5235943898200064000000000000:ℝ) admission13_08_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission13_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission13_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_08_coefficients]

def admission13_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(4773720853025700886097419/268444389312015000000:ℝ), (111428674863385069977772/2516666149800140625:ℝ), (88989974443312675942516/2516666149800140625:ℝ), (793919925450607232/89481463104005:ℝ)],
![(102075472216339967136809/13422219465600750000:ℝ), (7598674283850087433568/503333229960028125:ℝ), (18839414772102717931696/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission13_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (20262669780087425261/458145091092505600000:ℝ) admission13_09_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission13_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission13_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_09_coefficients]

def admission13_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(227917303683610487/1189800281250:ℝ), (2749502375811278419/5949001406250:ℝ), (1051151619680319488/2974500703125:ℝ), (246315528483706496/2974500703125:ℝ)],
![(35011452628034324/118980028125:ℝ), (132783364435129292/198300046875:ℝ), (91889046802608128/198300046875:ℝ), (52425610242608128/594900140625:ℝ)],
![(3826742316352456/39660009375:ℝ), (22572560433857368/118980028125:ℝ), (3547818715136/38073609:ℝ), (0:ℝ)]]
theorem admission13_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (3020223402547/495077785600000:ℝ) admission13_10_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission13_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission13_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_10_coefficients]

def admission13_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1877751523452018384808063/805333167936045000000:ℝ), (77866926878693280989779/25166661498001406250:ℝ), (1126120785765520725388/1398147861000078125:ℝ)],
![(8227912638068577700259/5752379770971750000:ℝ), (71392552121129566882/51360533669390625:ℝ), (0:ℝ)]]
theorem admission13_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (3612457937788082793/13089859745500160000:ℝ) admission13_11_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission13_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission13_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_11_coefficients]

def admission13_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission13_12_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission13_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission13_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_12_coefficients]

def admission13_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission13_13_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission13_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission13_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_13_coefficients]

def admission13_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission13_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission13_14_coefficients
      (57/128:ℝ) (15/32:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission13_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission13_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission13_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission13_14_coefficients]

theorem admission13_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (57/128:ℝ) (15/32:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission13_00_pos hδ hp
  · exact admission13_01_pos hδ hp
  · exact admission13_02_pos hδ hp
  · exact admission13_03_pos hδ hp
  · exact admission13_04_pos hδ hp
  · exact admission13_05_pos hδ hp
  · exact admission13_06_pos hδ hp
  · exact admission13_07_pos hδ hp
  · exact admission13_08_pos hδ hp
  · exact admission13_09_pos hδ hp
  · exact admission13_10_pos hδ hp
  · exact admission13_11_pos hδ hp
  · exact admission13_12_pos hδ hp
  · exact admission13_13_pos hδ hp
  · exact admission13_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
