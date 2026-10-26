/- Mixed source step, L3: new in this submission; uses the transfer's and the collision lemmas by
import.

`transfer_full_column`: the full transfer of one label (`transfer_full_label`) for a first-layer
column character, with the residual characters read as shifted column characters
(`rayShift_energy`) and the radius losses `(max 1 ·)^ε` paid by `Z^(Aε)`. -/
import Submissions.arvi_mixed_step.Residual.CollisionLabel
import Submissions.arvi_mixed_step.Residual.SupplierWaist

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u v

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open RayFourExpansion CanonicalQuadraticSieve CompletedGauss Cycle61InitialMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer QRH.MixedStep.Collision
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

theorem collWeight_nonneg {α : Type*} [Fintype α] [DecidableEq α] (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (J : Finset α) (τ : HeckeFamily.Character) (t : ℝ)
    (hhi : ∀ j ∈ J, 0 ≤ s.hi j) (D : Ideal O × Ideal O) :
    0 ≤ collWeight s C R B J τ t D := by
  unfold collWeight
  apply Finset.sum_nonneg
  intro q hq
  unfold collAssignWeight
  split_ifs
  · apply mul_nonneg (div_nonneg (sq_nonneg _) (Finset.prod_pos (fun j _ => s.P_pos _)).le)
    exact Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j.val.val
      ((mem_liveBlock B J _).mp (Finset.mem_subtype.mp hj))) (sq_nonneg _))
  · exact le_refl 0

/-- **The full transfer of one label at a column character.** -/
theorem transfer_full_column (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s → Squarefree L →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ {ι₀ : Type v} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t T H H' Z A : ℝ) (Hc : Ideal O × Ideal O → ℝ), 0 < T → 0 < H →
      2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 ≤ H' → 1 ≤ Z → 0 ≤ A → H' ≤ Z ^ A → H ≤ Z ^ A →
      (∀ D, 0 < Hc D) → (∀ D, Hc D ≤ Z ^ A) →
      (∀ q ∈ collAssign s C R B J (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t,
        Supported (selProduct q.1.1 q.2.1) →
        selWeight (child s C R B (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t)
          q.1.1 (1 * markedProduct B.val) (R * C) q.2.1 ≠ 0 →
        2 * (2 * H / (Ideal.absNorm (selProduct q.1.1 q.2.1) : ℝ)) *
          (∏ j ∈ restBlock (liveBlock B J) q.1.1, s.hi j.val.val * s.P j.val.val) ^ 4 ≤
            Hc (collSides q)) →
      ∃ seeds : Finset (Ideal O), ∃ seedsD : Ideal O × Ideal O → Finset (Ideal O),
        (∀ L' ∈ seeds, L' ∣ L) ∧ (∀ D, ∀ L' ∈ seedsD D, L' ∣ L) ∧
        correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H ≤
          K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
            ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
              correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
                (allocRestrict s C B J hJ)
                (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
                t (T / ∏ j ∈ J, s.P j) H' +
          K * Z ^ (A * ε) *
            ∑ D ∈ (collAssign s C R B J
                (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t).image collSides,
              collWeight s C R B J (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t D *
                ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D,
                  collE s C R L' P B J (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c)
                    t T Hc D ξ := by
  obtain ⟨K₁, hK₁, hfull⟩ := transfer_full_label.{u} (ε / 2) (by positivity) N
  refine ⟨K₁ * 2 ^ N * 2 ^ ε, by positivity, ?_⟩
  intro α _ _ hcard s C R L P hp hPA hLsq B J hJ hhi ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀
    ξ₀ hK key c t T H H' Z A Hc hT hH hrad hZ hA hHZ hHZA hHcpos hHcZ hcoll
  have hPpos : 0 < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hH' : 0 < H' := lt_of_lt_of_le (by positivity) hrad
  have hrad' : 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' := by
    calc
      _ ≤ 2 * H * (16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4) :=
        mul_le_mul_of_nonneg_left (window_le s J hhi) (by positivity)
      _ = 2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 := by ring
      _ ≤ H' := hrad
  obtain ⟨seeds, seedsD, hseeds, hseedsD, hb⟩ := hfull hcard s C R L P hp hPA hLsq B J hJ
    (fun j hj => (hhi j hj).1) (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H
    H' Hc hT hH hH' hrad' hHcpos hcoll
  refine ⟨seeds, seedsD, hseeds, hseedsD, hb.trans ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hε2 : 0 ≤ ε / 2 := by positivity
  have hZA1 : 1 ≤ Z ^ A := Real.one_le_rpow hZ hA
  have hZhalf : Z ^ (A * (ε / 2)) ≤ Z ^ (A * ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hZsq : Z ^ (A * (ε / 2)) * Z ^ (A * (ε / 2)) = Z ^ (A * ε) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  have h2half : (2 : ℝ) ^ (ε / 2) ≤ 2 ^ N * 2 ^ ε := by
    have h1 : (2 : ℝ) ^ (ε / 2) ≤ 2 ^ ε :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ε]
  have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
  apply add_le_add
  · -- the plain families
    have hE : ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (childCharacter (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ξ) t
            (T / ∏ j ∈ J, s.P j) H' =
        ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (T / ∏ j ∈ J, s.P j) H' :=
      Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun L' _ =>
        rayShift_energy reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c ξ (s.restrict J) 1 1 1 1 C R
          L' (fun _ => 1) P (allocRestrict s C B J hJ) t (T / ∏ j ∈ J, s.P j) H'))
    rw [hE]
    have hsum : 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seeds,
          correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L' (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (T / ∏ j ∈ J, s.P j) H' :=
      Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
        corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH'))
    have hM : 0 ≤ ∏ j ∈ J, s.M j ^ 2 := Finset.prod_nonneg (fun j _ => sq_nonneg _)
    have hmax := max_rpow_le H' Z A (ε / 2) hZ hA hε2 hHZ
    have h2e : (1 : ℝ) ≤ 2 ^ ε := Real.one_le_rpow (by norm_num) hε.le
    calc K₁ * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ (ε / 2) * _
        ≤ K₁ * (2 ^ N * ∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) * _ := by
          apply mul_le_mul_of_nonneg_right _ hsum
          apply mul_le_mul (mul_le_mul_of_nonneg_left (slot_factor_le s J N hJN hhi) hK₁.le)
            (hmax.trans hZhalf) (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
            (mul_nonneg hK₁.le (mul_nonneg (by positivity) hM))
      _ ≤ K₁ * 2 ^ N * 2 ^ ε * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) * _ := by
          apply mul_le_mul_of_nonneg_right _ hsum
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
          have : K₁ * (2 ^ N * ∏ j ∈ J, s.M j ^ 2) = K₁ * 2 ^ N * 1 * ∏ j ∈ J, s.M j ^ 2 := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_left h2e (by positivity)
  · -- the collision families
    set τ := columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c with hτ
    have hS : ∀ D, 0 ≤ ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ :=
      fun D => Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun L' _ =>
        collE_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ (hHcpos D)))
    have hW : ∀ D, 0 ≤ collWeight s C R B J τ t D :=
      collWeight_nonneg s C R B J τ t (fun j hj => (hhi j hj).1)
    have h2H : (max 1 (2 * H)) ^ (ε / 2) ≤ 2 ^ (ε / 2) * Z ^ (A * (ε / 2)) := by
      have hle : max 1 (2 * H) ≤ 2 * Z ^ A := max_le (by linarith) (by linarith)
      calc (max 1 (2 * H)) ^ (ε / 2) ≤ (2 * Z ^ A) ^ (ε / 2) :=
            Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hle hε2
        _ = 2 ^ (ε / 2) * Z ^ (A * (ε / 2)) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
    have hterm : ∀ D, collWeight s C R B J τ t D * ((max 1 (Hc D)) ^ (ε / 2) *
          ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ) ≤
        Z ^ (A * (ε / 2)) * (collWeight s C R B J τ t D *
          ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ) := by
      intro D
      have h := mul_le_mul_of_nonneg_right (max_rpow_le (Hc D) Z A (ε / 2) hZ hA hε2 (hHcZ D)) (hS D)
      calc _ ≤ collWeight s C R B J τ t D * (Z ^ (A * (ε / 2)) *
            ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ) :=
            mul_le_mul_of_nonneg_left h (hW D)
        _ = _ := by ring
    have hsum0 : 0 ≤ ∑ D ∈ (collAssign s C R B J τ t).image collSides, collWeight s C R B J τ t D *
        ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ :=
      Finset.sum_nonneg (fun D _ => mul_nonneg (hW D) (hS D))
    calc K₁ * (max 1 (2 * H)) ^ (ε / 2) * ∑ D ∈ (collAssign s C R B J τ t).image collSides,
          collWeight s C R B J τ t D * ((max 1 (Hc D)) ^ (ε / 2) *
            ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ)
        ≤ K₁ * (2 ^ (ε / 2) * Z ^ (A * (ε / 2))) * ∑ D ∈ (collAssign s C R B J τ t).image collSides,
            Z ^ (A * (ε / 2)) * (collWeight s C R B J τ t D *
              ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2H hK₁.le) (Finset.sum_le_sum (fun D _ => hterm D))
            (Finset.sum_nonneg (fun D _ => mul_nonneg (hW D) (mul_nonneg
              (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (hS D))))
            (mul_nonneg hK₁.le (by positivity))
      _ = K₁ * 2 ^ (ε / 2) * (Z ^ (A * (ε / 2)) * Z ^ (A * (ε / 2))) *
            ∑ D ∈ (collAssign s C R B J τ t).image collSides, collWeight s C R B J τ t D *
              ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ K₁ * 2 ^ N * 2 ^ ε * Z ^ (A * ε) *
            ∑ D ∈ (collAssign s C R B J τ t).image collSides, collWeight s C R B J τ t D *
              ∑ ξ : RayCharacter, ∑ L' ∈ seedsD D, collE s C R L' P B J τ t T Hc D ξ := by
          rw [hZsq]
          apply mul_le_mul_of_nonneg_right _ hsum0
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
          rw [mul_assoc K₁ (2 ^ N) (2 ^ ε)]
          exact mul_le_mul_of_nonneg_left h2half hK₁.le

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_full_column
