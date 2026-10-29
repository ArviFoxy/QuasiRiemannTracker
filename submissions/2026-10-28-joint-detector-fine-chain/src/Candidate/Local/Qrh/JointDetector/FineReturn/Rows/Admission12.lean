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

def admission12_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission12_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission12_00_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission12_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission12_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_00_coefficients]

def admission12_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission12_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission12_01_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission12_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission12_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_01_coefficients]

def admission12_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission12_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission12_02_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission12_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission12_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_02_coefficients]

def admission12_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(9277869088000/38073609:ℝ), (1690019592448/5439087:ℝ), (284793339904/4230401:ℝ)],
![(6706115872768/38073609:ℝ), (6695171872768/38073609:ℝ), (0:ℝ)]]
theorem admission12_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (388920841/464135424:ℝ) admission12_03_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission12_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission12_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_03_coefficients]

def admission12_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(820589172175765403/21152005000000:ℝ), (38656:ℝ), (0:ℝ)],
![(150053656644317863/2644000625000:ℝ), (24560597652504064/330500078125:ℝ), (5850089306252032/330500078125:ℝ)]]
theorem admission12_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (10351915842703791/86638612480000000:ℝ) admission12_04_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission12_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission12_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_04_coefficients]

def admission12_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(505136421085018787/12691203000000:ℝ), (73761417180358192/991500234375:ℝ), (11410234278284032/330500078125:ℝ)],
![(39378331043079179/7932001875000:ℝ), (5702475523712/1133143125:ℝ), (0:ℝ)]]
theorem admission12_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (965238476775821/10829826560000000:ℝ) admission12_05_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission12_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission12_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_05_coefficients]

def admission12_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(9812813856311947463220143228/465583237713026015625:ℝ), (111759590994629243931829828/2660475644074434375:ℝ), (9745260002504061474850076672/465583237713026015625:ℝ), (0:ℝ)],
![(1670527809912684954097032608/66511891101860859375:ℝ), (5031782012474269277225267168/93116647542605203125:ℝ), (15304917012275728770319499264/465583237713026015625:ℝ), (40879004919849045841608704/10346294171400578125:ℝ)]]
theorem admission12_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (1353537989153669951883361/8136656817802899456000000:ℝ) admission12_06_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission12_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission12_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_06_coefficients]

def admission12_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(126897400509912883049271949/805333167936045000000:ℝ), (6056170168482838693544/28533629816328125:ℝ), (15388080761254651224832/279629572200015625:ℝ)],
![(10245111956459137086379361/100666645992005625000:ℝ), (141800886366852789186112/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission12_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (8956343880573996220703/27488705465550336000000:ℝ) admission12_07_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission12_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission12_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_07_coefficients]

def admission12_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(12137617571714052346955731436327/6291665374500351562500000:ℝ), (16095175493407535837977031190107/4194443583000234375000000:ℝ), (375177966886717596067805641028/196614542953135986328125:ℝ), (0:ℝ)],
![(4047294912014388723872123364163/786458171812543945312500:ℝ), (7037264869634681755582882989223/524305447875029296875000:ℝ), (2246711407377202563479394163616/196614542953135986328125:ℝ), (13767634018770092214410683136/4369212065625244140625:ℝ)]]
theorem admission12_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (4849621557167189837957608943/293212858299203584000000000000:ℝ) admission12_08_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission12_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission12_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_08_coefficients]

def admission12_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(7337339194762185495439208333/805333167936045000000:ℝ), (3817478998398202859277536/167777743320009375:ℝ), (45765335136500248342460672/2516666149800140625:ℝ), (406487001830710902784/89481463104005:ℝ)],
![(451731986913828818315152417/100666645992005625000:ℝ), (7519646110321872110357248/838888716600046875:ℝ), (11265526135509857660168192/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission12_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (13240052218331082917/261797194910003200000:ℝ) admission12_09_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission12_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission12_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_09_coefficients]

def admission12_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2237200548900457068076/2974500703125:ℝ), (257359178249732857724/141642890625:ℝ), (4103378798938923016192/2974500703125:ℝ), (936044299932490072064/2974500703125:ℝ)],
![(706016015795865191104/594900140625:ℝ), (2664192865798217154368/991500234375:ℝ), (1802207779128411553792/991500234375:ℝ), (944140311569909153792/2974500703125:ℝ)],
![(1284618024008816497408/2974500703125:ℝ), (284824182423513299712/330500078125:ℝ), (58459054637842432/135977175:ℝ), (0:ℝ)]]
theorem admission12_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (10380965593410557/1386217799680000000:ℝ) admission12_10_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission12_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission12_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_10_coefficients]

def admission12_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(13204188705966922468243867/89481463104005000000:ℝ), (357302653189329882869636/1797618678428671875:ℝ), (72071730288993326424832/1398147861000078125:ℝ)],
![(1065584395029468251018471/11185182888000625000:ℝ), (1194450514916305116025952/12583330749000703125:ℝ), (0:ℝ)]]
theorem admission12_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (13488193371582430319541/45814509109250560000000:ℝ) admission12_11_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission12_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission12_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_11_coefficients]

def admission12_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission12_12_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission12_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission12_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_12_coefficients]

def admission12_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission12_13_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission12_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission12_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_13_coefficients]

def admission12_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission12_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission12_14_coefficients
      (453/1024:ℝ) (57/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission12_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission12_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission12_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission12_14_coefficients]

theorem admission12_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (453/1024:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission12_00_pos hδ hp
  · exact admission12_01_pos hδ hp
  · exact admission12_02_pos hδ hp
  · exact admission12_03_pos hδ hp
  · exact admission12_04_pos hδ hp
  · exact admission12_05_pos hδ hp
  · exact admission12_06_pos hδ hp
  · exact admission12_07_pos hδ hp
  · exact admission12_08_pos hδ hp
  · exact admission12_09_pos hδ hp
  · exact admission12_10_pos hδ hp
  · exact admission12_11_pos hδ hp
  · exact admission12_12_pos hδ hp
  · exact admission12_13_pos hδ hp
  · exact admission12_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
