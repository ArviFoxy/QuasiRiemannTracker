/- Mixed source step, N3 (families, full): new in this submission; uses the transfer's contracts
(`Residual/CollisionColumn.lean`) and Collet's definitions by import.

The first MAIN label transfer without (S) and without (Col), at the node of its piece:
* `coll_piece_radius`: at the plain node `δ`, the collision family with side products of norm `N(D)`
  runs at the MAIN radius of the shortened parent, `firstMainRadius (V / (Π_J P · N(D))) (3(a+δ))`; the
  window `Σ_J w ≤ δ − mesh` pays its radius condition when `N(D) ≤ 2^|Q| Π_Q P` (active assignments).
* `piece_label_transfer_full`: both node cases; at node 0 there is no collision pattern. -/
import Submissions.arvi_mixed_step.Downstream.Families
import Submissions.arvi_mixed_step.Residual.CollisionColumn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Downstream
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass Cycle61Moment ActualEisensteinCubic
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer QRH.MixedStep.Residual QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

theorem one_le_prod_real {β : Type*} (S : Finset β) (f : β → ℝ) (h : ∀ j ∈ S, 1 ≤ f j) :
    1 ≤ ∏ j ∈ S, f j := by
  calc (1 : ℝ) = ∏ _j ∈ S, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ j ∈ S, f j := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

/-- The MAIN radius does not increase when the volume is divided by `W ≥ 1`. -/
theorem firstMainRadius_div_le (reflected : Bool) (K V Z ξ σ reserve W : ℝ) (l : FirstSourceLabel)
    (hZ : 1 < Z) (hW : 1 ≤ W) :
    firstMainRadius reflected K (V / W) Z ξ σ reserve l ≤
      firstMainRadius reflected K V Z ξ σ reserve l := by
  unfold firstMainRadius mainCommonRadius
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have h := nominalLog_div_le l.1.1 l.1.2
    (Ideal.span {primeSubsetGenerator (fun p : CenteredMomentCanonicalFirst.CommonIndex l.1.1 l.1.2 =>
      p.val) l.2.val}) K V Z W hZ hW
  linarith

section Radius
variable {α : Type*} [DecidableEq α]

/-- **The radius of a collision family at the plain node.** -/
theorem coll_piece_radius (reflected : Bool) (K V Z ξ a δ reserve mesh : ℝ) (l : FirstSourceLabel)
    (hZ : 1 < Z) (N : ℕ) (J : Finset α) (hJ : J.card ≤ N) (w P hi : α → ℝ)
    (hP : ∀ j, P j = Z ^ w j) (hw : ∀ j, 0 ≤ w j) (hhi : ∀ j ∈ J, 0 ≤ hi j ∧ hi j ≤ 2)
    (hmesh : Real.logb Z (2 * 16 ^ N) ≤ 6 * mesh) (hact : ∑ j ∈ J, w j ≤ δ - mesh)
    (Q : Finset α) (hQJ : Q ⊆ J) (hQ : Q.Nonempty) (ND : ℝ) (hND1 : 1 ≤ ND)
    (hND : ND ≤ 2 ^ Q.card * ∏ j ∈ Q, P j) :
    2 * (2 * firstMainRadius reflected K V Z ξ (3 * a) reserve l / ND) *
        (∏ j ∈ J \ Q, hi j * P j) ^ 4 ≤
      firstMainRadius reflected K (V / ((∏ j ∈ J, P j) * ND)) Z ξ (3 * (a + δ)) reserve l := by
  have hZ0 : 0 < Z := by linarith
  have hPpos : ∀ j, 0 < P j := fun j => by rw [hP j]; exact Real.rpow_pos_of_pos hZ0 _
  have hP1 : ∀ j, 1 ≤ P j := fun j => by rw [hP j]; exact Real.one_le_rpow hZ.le (hw j)
  have hWJ : ∏ j ∈ J, P j = Z ^ (∑ j ∈ J, w j) := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_congr rfl (fun j _ => hP j)
  have hPJ1 : 1 ≤ ∏ j ∈ J, P j := one_le_prod_real J P (fun j _ => hP1 j)
  have hPQ1 : 1 ≤ ∏ j ∈ Q, P j := one_le_prod_real Q P (fun j _ => hP1 j)
  have hPR1 : 1 ≤ ∏ j ∈ J \ Q, P j := one_le_prod_real (J \ Q) P (fun j _ => hP1 j)
  have hsplit : ∏ j ∈ J, P j = (∏ j ∈ J \ Q, P j) * ∏ j ∈ Q, P j :=
    (Finset.prod_sdiff hQJ).symm
  have hW1 : 1 ≤ (∏ j ∈ J, P j) * ND := one_le_mul_of_one_le_of_one_le hPJ1 hND1
  have hH := firstMainRadius_restrict reflected K V Z ξ a δ reserve ((∏ j ∈ J, P j) * ND) l hZ hW1
  have hHpos := first_main_radius_pos reflected K V Z ξ (3 * a) reserve hZ0 l
  set H := firstMainRadius reflected K V Z ξ (3 * a) reserve l with hHdef
  set Hc := firstMainRadius reflected K (V / ((∏ j ∈ J, P j) * ND)) Z ξ (3 * (a + δ)) reserve l
    with hHcdef
  have h16 : (2 : ℝ) * 16 ^ J.card ≤ Z ^ (6 * mesh) := by
    calc (2 : ℝ) * 16 ^ J.card ≤ 2 * 16 ^ N := by
          gcongr
          norm_num
      _ = Z ^ (Real.logb Z (2 * 16 ^ N)) := (Real.rpow_logb hZ0 hZ.ne' (by positivity)).symm
      _ ≤ Z ^ (6 * mesh) := Real.rpow_le_rpow_of_exponent_le hZ.le hmesh
  have hW6 : (∏ j ∈ J, P j) ^ 6 ≤ Z ^ (6 * (δ - mesh)) := by
    rw [hWJ, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    push_cast
    linarith
  -- the window factor of the remaining block
  have hwin : (∏ j ∈ J \ Q, hi j * P j) ^ 4 ≤ 16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4 := by
    have h0 : 0 ≤ ∏ j ∈ J \ Q, hi j * P j :=
      Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j (Finset.mem_sdiff.mp hj).1).1 (hPpos j).le)
    have h1 : ∏ j ∈ J \ Q, hi j * P j ≤ ∏ j ∈ J \ Q, 2 * P j :=
      Finset.prod_le_prod₀ (fun j hj => mul_nonneg (hhi j (Finset.mem_sdiff.mp hj).1).1 (hPpos j).le)
        (fun j hj => mul_le_mul_of_nonneg_right (hhi j (Finset.mem_sdiff.mp hj).1).2 (hPpos j).le)
    calc _ ≤ (∏ j ∈ J \ Q, 2 * P j) ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = ((2:ℝ) ^ (J \ Q).card) ^ 4 * (∏ j ∈ J \ Q, P j) ^ 4 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
      _ = 16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4 := by
          rw [← pow_mul, mul_comm (J \ Q).card 4, pow_mul]
          norm_num
  -- the numerical factor
  have hcard : (J \ Q).card + Q.card = J.card := Finset.card_sdiff_add_card_eq_card hQJ
  have hq1 : 1 ≤ Q.card := Finset.card_pos.mpr hQ
  have hnum : (4 : ℝ) * 16 ^ (J \ Q).card * 2 ^ Q.card ≤ 2 * 16 ^ J.card := by
    have h2q : (2 : ℝ) * 2 ^ Q.card ≤ 16 ^ Q.card := by
      have : (16 : ℝ) ^ Q.card = 2 ^ (4 * Q.card) := by
        rw [pow_mul]
        norm_num
      rw [this, ← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc (4 : ℝ) * 16 ^ (J \ Q).card * 2 ^ Q.card = 2 * 16 ^ (J \ Q).card * (2 * 2 ^ Q.card) := by
          ring
      _ ≤ 2 * 16 ^ (J \ Q).card * 16 ^ Q.card := by gcongr
      _ = 2 * 16 ^ J.card := by rw [mul_assoc, ← pow_add, hcard]
  -- the powers of the scales
  have hpow : (∏ j ∈ J \ Q, P j) ^ 4 * (∏ j ∈ J, P j) ^ 2 * (∏ j ∈ Q, P j) ≤ (∏ j ∈ J, P j) ^ 6 := by
    rw [hsplit]
    have hQ3 : (∏ j ∈ Q, P j) ^ 3 ≤ (∏ j ∈ Q, P j) ^ 6 :=
      pow_le_pow_right₀ hPQ1 (by norm_num)
    have hR : 0 ≤ (∏ j ∈ J \ Q, P j) ^ 6 := by positivity
    calc (∏ j ∈ J \ Q, P j) ^ 4 * ((∏ j ∈ J \ Q, P j) * ∏ j ∈ Q, P j) ^ 2 * (∏ j ∈ Q, P j)
        = (∏ j ∈ J \ Q, P j) ^ 6 * (∏ j ∈ Q, P j) ^ 3 := by ring
      _ ≤ (∏ j ∈ J \ Q, P j) ^ 6 * (∏ j ∈ Q, P j) ^ 6 := mul_le_mul_of_nonneg_left hQ3 hR
      _ = ((∏ j ∈ J \ Q, P j) * ∏ j ∈ Q, P j) ^ 6 := by ring
  have hND0 : 0 < ND := lt_of_lt_of_le one_pos hND1
  -- the main inequality, multiplied by `W² = (Π_J P · ND)²`
  have key : 2 * (2 * H / ND) * (∏ j ∈ J \ Q, hi j * P j) ^ 4 * ((∏ j ∈ J, P j) * ND) ^ 2 ≤
      Hc * ((∏ j ∈ J, P j) * ND) ^ 2 := by
    have hA : 2 * (2 * H / ND) * (∏ j ∈ J \ Q, hi j * P j) ^ 4 * ((∏ j ∈ J, P j) * ND) ^ 2 ≤
        H * (4 * (16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4) * (∏ j ∈ J, P j) ^ 2 * ND) := by
      have e : 2 * (2 * H / ND) * (∏ j ∈ J \ Q, hi j * P j) ^ 4 * ((∏ j ∈ J, P j) * ND) ^ 2 =
          H * (4 * (∏ j ∈ J \ Q, hi j * P j) ^ 4 * (∏ j ∈ J, P j) ^ 2 * ND) := by
        field_simp
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hHpos.le
      gcongr
    have hB : 4 * (16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4) * (∏ j ∈ J, P j) ^ 2 * ND ≤
        Z ^ (6 * δ) := by
      calc 4 * (16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4) * (∏ j ∈ J, P j) ^ 2 * ND
          ≤ 4 * (16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4) * (∏ j ∈ J, P j) ^ 2 *
              (2 ^ Q.card * ∏ j ∈ Q, P j) := by gcongr
        _ = (4 * 16 ^ (J \ Q).card * 2 ^ Q.card) *
              ((∏ j ∈ J \ Q, P j) ^ 4 * (∏ j ∈ J, P j) ^ 2 * (∏ j ∈ Q, P j)) := by ring
        _ ≤ (2 * 16 ^ J.card) * (∏ j ∈ J, P j) ^ 6 := by
            apply mul_le_mul hnum hpow (by positivity) (by positivity)
        _ ≤ Z ^ (6 * mesh) * Z ^ (6 * (δ - mesh)) := by
            apply mul_le_mul h16 hW6 (by positivity) (by positivity)
        _ = Z ^ (6 * δ) := by
            rw [← Real.rpow_add hZ0]
            ring_nf
    calc _ ≤ H * (4 * (16 ^ (J \ Q).card * (∏ j ∈ J \ Q, P j) ^ 4) * (∏ j ∈ J, P j) ^ 2 * ND) := hA
      _ ≤ H * Z ^ (6 * δ) := mul_le_mul_of_nonneg_left hB hHpos.le
      _ ≤ _ := hH
  exact le_of_mul_le_mul_right key (by positivity)

end Radius

end
end QRH.MixedStep.Downstream

#print axioms QRH.MixedStep.Downstream.coll_piece_radius
#print axioms QRH.MixedStep.Downstream.firstMainRadius_div_le
