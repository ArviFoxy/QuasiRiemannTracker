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

def admission06_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(12230401/4230401:ℝ), (0:ℝ)]]
theorem admission06_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
    Record12518109.Bernstein.bsum 0 1 (13152005/8460802:ℝ) admission06_00_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_00_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_00_coefficients, Fin.sum_univ_succ, admission_power_C_00] <;> ring
theorem admission06_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
  rw [admission06_00_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_00_coefficients]

def admission06_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(8000000/4230401:ℝ), (0:ℝ)]]
theorem admission06_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
    Record12518109.Bernstein.bsum 0 1 (4460802/4230401:ℝ) admission06_01_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_01_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_01_coefficients, Fin.sum_univ_succ, admission_power_C_01] <;> ring
theorem admission06_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
  rw [admission06_01_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_01_coefficients]

def admission06_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(19452098647453/21152005000000:ℝ), (0:ℝ)]]
theorem admission06_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
    Record12518109.Bernstein.bsum 0 1 (22851911352547/42304010000000:ℝ) admission06_02_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_02_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_02_coefficients, Fin.sum_univ_succ, admission_power_C_02] <;> ring
theorem admission06_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
  rw [admission06_02_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_02_coefficients]

def admission06_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(147042768448/38073609:ℝ), (26542261696/5439087:ℝ), (4449895936/4230401:ℝ)],
![(105980060512/38073609:ℝ), (104612060512/38073609:ℝ), (0:ℝ)]]
theorem admission06_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
    Record12518109.Bernstein.bsum 1 2 (388920841/464135424:ℝ) admission06_03_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_03_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_03_coefficients, Fin.sum_univ_succ, admission_power_C_03] <;> ring
theorem admission06_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
  rw [admission06_03_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_03_coefficients]

def admission06_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(6266846327827077/10576002500000:ℝ), (576:ℝ), (0:ℝ)],
![(19080098220553639/21152005000000:ℝ), (383759338320376/330500078125:ℝ), (91407645410188/330500078125:ℝ)]]
theorem admission06_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
    Record12518109.Bernstein.bsum 1 2 (617001606518769/5414913280000000:ℝ) admission06_04_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_04_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_04_coefficients, Fin.sum_univ_succ, admission_power_C_04] <;> ring
theorem admission06_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
  rw [admission06_04_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_04_coefficients]

def admission06_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(20596251505192817/31728007500000:ℝ), (1186466174565628/991500234375:ℝ), (178284910598188/330500078125:ℝ)],
![(4450668460343179/63456015000000:ℝ), (89101180058/1133143125:ℝ), (0:ℝ)]]
theorem admission06_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
    Record12518109.Bernstein.bsum 1 2 (965238476775821/10829826560000000:ℝ) admission06_05_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_05_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_05_coefficients, Fin.sum_univ_succ, admission_power_C_05] <;> ring
theorem admission06_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
  rw [admission06_05_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_05_coefficients]

def admission06_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(3901484541618984403404653/93116647542605203125:ℝ), (5423338357721701673995607/66511891101860859375:ℝ), (18473282389374489700945984/465583237713026015625:ℝ), (0:ℝ)],
![(1359052416415566397032457/26604756440744343750:ℝ), (100129304595187174315851259/931166475426052031250:ℝ), (29892416039601032754530272/465583237713026015625:ℝ), (79841806484080167659392/10346294171400578125:ℝ)]]
theorem admission06_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
    Record12518109.Bernstein.bsum 1 3 (82140053126549171522719/508541051112681216000000:ℝ) admission06_06_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_06_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_06_coefficients, Fin.sum_univ_succ, admission_power_C_06] <;> ring
theorem admission06_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
  rw [admission06_06_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_06_coefficients]

def admission06_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(1666677840156260040547/644266534348836000:ℝ), (679122428994369771938/199735408714296875:ℝ), (240438761894603925388/279629572200015625:ℝ)],
![(262331223069482273530861/161066633587209000000:ℝ), (2215638849482074831033/1398147861000078125:ℝ), (0:ℝ)]]
theorem admission06_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
    Record12518109.Bernstein.bsum 1 2 (8956343880573996220703/27488705465550336000000:ℝ) admission06_07_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_07_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_07_coefficients, Fin.sum_univ_succ, admission_power_C_07] <;> ring
theorem admission06_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
  rw [admission06_07_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_07_coefficients]

def admission06_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(17469697222610187784463714351/5592591444000312500000000:ℝ), (2393059852485393009473494619/402666583968022500000000:ℝ), (4450906737360311981324711663/1572916343625087890625000:ℝ), (0:ℝ)],
![(115798555101039337774172660341/11185182888000625000000000:ℝ), (533649810672189304131045248113/20133329198401125000000000:ℝ), (70209731480537580108731067613/3145832687250175781250000:ℝ), (53779820385820672712541731/8738424131250488281250:ℝ)]]
theorem admission06_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
    Record12518109.Bernstein.bsum 1 3 (232515333066559731937139537/18325803643700224000000000000:ℝ) admission06_08_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_08_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_08_coefficients, Fin.sum_univ_succ, admission_power_C_08] <;> ring
theorem admission06_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
  rw [admission06_08_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_08_coefficients]

def admission06_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(2562086242686390366729329/134222194656007500000:ℝ), (117876984597624717587704/2516666149800140625:ℝ), (92153540404627648753336/2516666149800140625:ℝ), (793919925450607232/89481463104005:ℝ)],
![(2391961076673879190097419/268444389312015000000:ℝ), (44441681153490084777772/2516666149800140625:ℝ), (22002980733417690742516/2516666149800140625:ℝ), (0:ℝ)]]
theorem admission06_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
    Record12518109.Bernstein.bsum 1 3 (13240052218331082917/261797194910003200000:ℝ) admission06_09_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_09_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_09_coefficients, Fin.sum_univ_succ, admission_power_C_09] <;> ring
theorem admission06_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
  rw [admission06_09_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_09_coefficients]

def admission06_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(569290550677116374/2974500703125:ℝ), (12770202323466598/28328578125:ℝ), (328720608770638208/991500234375:ℝ), (214690483025038208/2974500703125:ℝ)],
![(911255664167833778/2974500703125:ℝ), (2029361114193378482/2974500703125:ℝ), (1348377605779917056/2974500703125:ℝ), (230503005754372352/2974500703125:ℝ)],
![(215651820483546481/1983000468750:ℝ), (1271609204909039443/5949001406250:ℝ), (14272230136192/135977175:ℝ), (0:ℝ)]]
theorem admission06_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
    Record12518109.Bernstein.bsum 2 3 (10380965593410557/1386217799680000000:ℝ) admission06_10_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_10_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_10_coefficients, Fin.sum_univ_succ, admission_power_C_10] <;> ring
theorem admission06_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
  rw [admission06_10_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_10_coefficients]

def admission06_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(977474852486747976878189/402666583968022500000:ℝ), (1145873641863918972763/359523735685734375:ℝ), (1126120785765520725388/1398147861000078125:ℝ)],
![(49164238034043137879383/32213326717441800000:ℝ), (37326578591134534875811/25166661498001406250:ℝ), (0:ℝ)]]
theorem admission06_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
    Record12518109.Bernstein.bsum 1 2 (13488193371582430319541/45814509109250560000000:ℝ) admission06_11_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_11_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_11_coefficients, Fin.sum_univ_succ, admission_power_C_11] <;> ring
theorem admission06_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
  rw [admission06_11_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_11_coefficients]

def admission06_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
    Record12518109.Bernstein.bsum 0 0 (74999/10000000:ℝ) admission06_12_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_12_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_12_coefficients, Fin.sum_univ_succ, admission_power_C_12] <;> ring
theorem admission06_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
  rw [admission06_12_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_12_coefficients]

def admission06_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
    Record12518109.Bernstein.bsum 0 0 (220742529263/5000000000000:ℝ) admission06_13_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_13_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_13_coefficients, Fin.sum_univ_succ, admission_power_C_13] <;> ring
theorem admission06_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
  rw [admission06_13_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_13_coefficients]

def admission06_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission06_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
    Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission06_14_coefficients
      (27/64:ℝ) (57/128:ℝ) (15/32:ℝ) (1/2:ℝ) δ p := by
  rw [admission_power_C_14_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    admission06_14_coefficients, Fin.sum_univ_succ, admission_power_C_14] <;> ring
theorem admission06_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
  rw [admission06_14_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [admission06_14_coefficients]

theorem admission06_all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (27/64:ℝ) (57/128:ℝ)) (hp : p ∈ Set.Icc (15/32:ℝ) (1/2:ℝ))
    (j : Fin 15) : 0 < admissionGuard .C δ p j := by
  fin_cases j
  · exact admission06_00_pos hδ hp
  · exact admission06_01_pos hδ hp
  · exact admission06_02_pos hδ hp
  · exact admission06_03_pos hδ hp
  · exact admission06_04_pos hδ hp
  · exact admission06_05_pos hδ hp
  · exact admission06_06_pos hδ hp
  · exact admission06_07_pos hδ hp
  · exact admission06_08_pos hδ hp
  · exact admission06_09_pos hδ hp
  · exact admission06_10_pos hδ hp
  · exact admission06_11_pos hδ hp
  · exact admission06_12_pos hδ hp
  · exact admission06_13_pos hδ hp
  · exact admission06_14_pos hδ hp

end
end Qrh.JointDetector.FineReturn
