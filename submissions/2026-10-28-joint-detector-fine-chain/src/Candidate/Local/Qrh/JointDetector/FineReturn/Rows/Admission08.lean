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

def admission08_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission08_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission08_00_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission08_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission08_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_00_coefficients]

def admission08_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission08_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission08_01_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission08_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission08_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_01_coefficients]

def admission08_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission08_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission08_02_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission08_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission08_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_02_coefficients]

def admission08_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(583479784768/38073609:ℝ), (741012038464/38073609:ℝ), (17799583744/4230401:ℝ)],
![(421184242048/38073609:ℝ), (418448242048/38073609:ℝ), (0:ℝ)]]
theorem admission08_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (388920841/464135424:ℝ) admission08_03_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission08_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission08_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_03_coefficients]

def admission08_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(50807675489955761/21152005000000:ℝ), (2368:ℝ), (0:ℝ)],
![(37790606566805671/10576002500000:ℝ), (1535037353281504/330500078125:ℝ), (365630581640752/330500078125:ℝ)]]
theorem admission08_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (2536562160132717/21659653120000000:ℝ) admission08_04_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission08_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission08_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_04_coefficients]

def admission08_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(160797375561029101/63456015000000:ℝ), (4668278341411012/991500234375:ℝ), (713139642392752/330500078125:ℝ)],
![(9440334543591179/31728007500000:ℝ), (356404720232/1133143125:ℝ), (0:ℝ)]]
theorem admission08_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (965238476775821/10829826560000000:ℝ) admission08_05_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission08_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission08_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_05_coefficients]

def admission08_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(22076341454786157497679131/66511891101860859375:ℝ), (304846972067088151769587261/465583237713026015625:ℝ), (150348218214498799285833344/465583237713026015625:ℝ), (0:ℝ)],
![(185923683498232418453011958/465583237713026015625:ℝ), (396283362005779320131873014/465583237713026015625:ℝ), (239139328316808262036242176/465583237713026015625:ℝ), (638734451872641341275136/10346294171400578125:ℝ)]]
theorem admission08_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (334174089524608572879427/2034164204450724864000000:ℝ) admission08_06_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission08_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission08_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_06_coefficients]

def admission08_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(8101896660806169746584519/805333167936045000000:ℝ), (18747766942777404976958/1398147861000078125:ℝ), (961755047578415701552/279629572200015625:ℝ)],
![(369694870378440924332759/57523797709717500000:ℝ), (8862555397928299324132/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission08_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (8956343880573996220703/27488705465550336000000:ℝ) admission08_07_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission08_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission08_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_07_coefficients]

def admission08_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(281792028505431567585631121891/10066664599200562500000000:ℝ), (917920372005644162251874881777/16777774332000937500000000:ℝ), (3004191276938839648833631637/112351167401791992187500:ℝ), (0:ℝ)],
![(409851686411354067515673212389/5033332299600281250000000:ℝ), (1767680425193796399556190781479/8388887166000468750000000:ℝ), (70209731480537580108731067613/393229085906271972656250:ℝ), (215119281543282690850166924/4369212065625244140625:ℝ)]]
theorem admission08_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (1091400793423700945886183341/73303214574800896000000000000:ℝ) admission08_08_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission08_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission08_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_08_coefficients]

def admission08_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(118165739819726690254293191/805333167936045000000:ℝ), (20338608966093354069208/55925914440003125:ℝ), (724574059391761298783408/2516666149800140625:ℝ), (6351359403604857856/89481463104005:ℝ)],
![(28438175033832125736784417/402666583968022500000:ℝ), (39310063386811318339024/279629572200015625:ℝ), (176023845867341525940128/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission08_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (13240052218331082917/261797194910003200000:ℝ) admission08_09_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission08_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission08_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_09_coefficients]

def admission08_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(8901998861282603107/2974500703125:ℝ), (2363356968798263563/330500078125:ℝ), (3185859946127410688/594900140625:ℝ), (101758511721008128/84985734375:ℝ)],
![(2017849178489594444/424928671875:ℝ), (10584072913122892124/991500234375:ℝ), (2368263725779052544/330500078125:ℝ), (3688048092069957632/2974500703125:ℝ)],
![(5085949469636157772/2974500703125:ℝ), (3360572455767785924/991500234375:ℝ), (228355682179072/135977175:ℝ), (0:ℝ)]]
theorem admission08_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (10380965593410557/1386217799680000000:ℝ) admission08_10_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission08_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission08_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_10_coefficients]

def admission08_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(2531302900372332651193171/268444389312015000000:ℝ), (158078081809167609083189/12583330749000703125:ℝ), (4504483143062082901552/1398147861000078125:ℝ)],
![(115407450750827788714787/19174599236572500000:ℝ), (74653157182269069751622/12583330749000703125:ℝ), (0:ℝ)]]
theorem admission08_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (13488193371582430319541/45814509109250560000000:ℝ) admission08_11_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission08_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission08_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_11_coefficients]

def admission08_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission08_12_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission08_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission08_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_12_coefficients]

def admission08_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission08_13_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission08_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission08_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_13_coefficients]

def admission08_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission08_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission08_14_coefficients
      (111/256:ℝ) (57/128:ℝ) (31/64:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission08_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission08_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission08_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission08_14_coefficients]

theorem admission08_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (111/256:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (31/64:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission08_00_pos hδ hp
  · exact admission08_01_pos hδ hp
  · exact admission08_02_pos hδ hp
  · exact admission08_03_pos hδ hp
  · exact admission08_04_pos hδ hp
  · exact admission08_05_pos hδ hp
  · exact admission08_06_pos hδ hp
  · exact admission08_07_pos hδ hp
  · exact admission08_08_pos hδ hp
  · exact admission08_09_pos hδ hp
  · exact admission08_10_pos hδ hp
  · exact admission08_11_pos hδ hp
  · exact admission08_12_pos hδ hp
  · exact admission08_13_pos hδ hp
  · exact admission08_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
