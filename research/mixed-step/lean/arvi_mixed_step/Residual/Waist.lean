/- Mixed source step: new in this submission; uses Collet's definitions by import.

The transfer contract in the form written in L45_DESIGN.md §4, and its column
version for L4/L5:

* `transfer_waist_design`: the radius condition is the design's
  `2·16^|J|·H·(∏_J P)⁴ ≤ H'` (slot windows `hi ≤ 2`, as in Collet's inputs); the
  constant absorbs `2^|J|`, and the remaining slot factor is `∏_J M_j²`.
* `transfer_waist_column`: the parent character is a first-layer column
  character `columnCharacter c`; the residual energies are read at the shifted
  columns `rayShift c ξ` (N2), and `H' ≤ Z^A` turns `(max 1 H')^ε` into `Z^(Aε)`.

Normalization: the residual carries `T/∏_J P`; no factor `∏_J P` appears. -/
import Submissions.arvi_mixed_step.Residual.RayShift

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u v

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- No collision in the child: on nonzero child tuples the selected product is
coprime to the ordinary pair (the hypothesis (Col) of the transfer). -/
def NoCollision {α : Type*} [Fintype α] [DecidableEq α] (s : Input α) (C R L : Ideal O)
    (B : actualAllocations s.pools C) (J : Finset α) (τ : HeckeFamily.Character) (t : ℝ) : Prop :=
  ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
    CoupledFirst.tupleCoefficient (child s C R B τ t)
      (markedSourceModifier (1 * B.val (Sum.inr 0)) (1 * B.val (Sum.inr 1)) 1
        (1 * markedProduct B.val) (fun _ => 1)) (R * C) L v ≠ 0 →
      IsCoprime (∏ j ∈ liveBlock B J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))

theorem corrected_energy_nonneg {α : Type*} [Fintype α] [DecidableEq α] (s : Input α)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O → ℂ) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t T H : ℝ) (hH : 0 < H) :
    0 ≤ correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ t T H := by
  unfold correctedChildGaussEnergy
  dsimp only
  exact ball_energy_nonneg _ _ _ _ H hH

theorem window_le {α : Type*} [Fintype α] (s : Input α) (J : Finset α)
    (hhi : ∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) :
    (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ 16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4 := by
  have h0 : 0 ≤ ∏ j ∈ J, s.hi j * s.P j :=
    Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj).1 (s.P_pos j).le)
  have h1 : ∏ j ∈ J, s.hi j * s.P j ≤ ∏ j ∈ J, 2 * s.P j :=
    Finset.prod_le_prod₀ (fun j hj => mul_nonneg (hhi j hj).1 (s.P_pos j).le)
      (fun j hj => mul_le_mul_of_nonneg_right (hhi j hj).2 (s.P_pos j).le)
  calc
    _ ≤ (∏ j ∈ J, 2 * s.P j) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = ((2:ℝ) ^ J.card) ^ 4 * (∏ j ∈ J, s.P j) ^ 4 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
    _ = 16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4 := by
      rw [← pow_mul, mul_comm J.card 4, pow_mul]
      norm_num

theorem slot_factor_le {α : Type*} [Fintype α] (s : Input α) (J : Finset α) (N : ℕ)
    (hJ : J.card ≤ N) (hhi : ∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) :
    ∏ j ∈ J, s.hi j * s.M j ^ 2 ≤ 2 ^ N * ∏ j ∈ J, s.M j ^ 2 := by
  calc
    _ ≤ ∏ j ∈ J, 2 * s.M j ^ 2 :=
      Finset.prod_le_prod₀ (fun j hj => mul_nonneg (hhi j hj).1 (sq_nonneg _))
        (fun j hj => mul_le_mul_of_nonneg_right (hhi j hj).2 (sq_nonneg _))
    _ = 2 ^ J.card * ∏ j ∈ J, s.M j ^ 2 := by rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ 2 ^ N * ∏ j ∈ J, s.M j ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hJ)
        (Finset.prod_nonneg (fun j _ => sq_nonneg _))

/-- **Transfer contract, design form** (L45_DESIGN.md §4, with the slot factor
`∏_J M²` and `(max 1 H')^ε` in place of `Z^ε`). -/
theorem transfer_waist_design (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      SeedFree s J L → (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ (τ : HeckeFamily.Character) (t T H H' : ℝ), 0 < H →
      2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 ≤ H' →
      NoCollision s C R L B J τ t →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B τ t T H ≤
        K * (∏ j ∈ J, s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' := by
  obtain ⟨Kw, hKw, hw⟩ := transfer_waist.{u} ε hε N
  refine ⟨Kw * 2 ^ N, by positivity, ?_⟩
  intro α _ _ hcard s C R L P hp hPA B J hJ hSF hhi τ t T H H' hH hrad hNC
  have hPpos : 0 < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hH' : 0 < H' := lt_of_lt_of_le (by positivity) hrad
  have hrad' : 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' := by
    calc
      _ ≤ 2 * H * (16 ^ J.card * (∏ j ∈ J, s.P j) ^ 4) :=
        mul_le_mul_of_nonneg_left (window_le s J hhi) (by positivity)
      _ = 2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 := by ring
      _ ≤ H' := hrad
  have hmain := hw hcard s C R L P hp hPA B J hJ hSF (fun j hj => (hhi j hj).1) τ t T H H'
    hH hH' hrad' hNC
  refine hmain.trans ?_
  have hJN : J.card ≤ N := (Finset.card_le_univ J).trans hcard
  have hsum : 0 ≤ ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
      (fun _ => 1) P (allocRestrict s C B J hJ) (childCharacter τ ξ) t (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_nonneg (fun ξ _ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH')
  have hX : 0 ≤ (max 1 H') ^ ε := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) ε
  calc
    _ ≤ Kw * (2 ^ N * ∏ j ∈ J, s.M j ^ 2) * (max 1 H') ^ ε *
        ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
          (fun _ => 1) P (allocRestrict s C B J hJ) (childCharacter τ ξ) t
          (T / ∏ j ∈ J, s.P j) H' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (slot_factor_le s J N hJN hhi) hKw.le) hX) hsum
    _ = _ := by ring

theorem max_rpow_le (H' Z A ε : ℝ) (hZ : 1 ≤ Z) (hA : 0 ≤ A) (hε : 0 ≤ ε) (hH : H' ≤ Z ^ A) :
    (max 1 H') ^ ε ≤ Z ^ (A * ε) := by
  have h1 : 1 ≤ Z ^ A := Real.one_le_rpow hZ hA
  rw [Real.rpow_mul (zero_le_one.trans hZ)]
  exact Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) (max_le h1 hH) hε

/-- **Transfer contract for a first-layer column** (consumed by L4/L5): the
parent child energy at `columnCharacter c` is bounded by the residual child
energies at the shifted columns `rayShift c ξ`. -/
theorem transfer_waist_column (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α ≤ N →
    ∀ (s : Input α) (C R L : Ideal O) (P : Finset (Ideal O)), (∀ Q ∈ P, Prime Q) →
      PoolAvoids P s →
    ∀ (B : actualAllocations s.pools C) (J : Finset α) (hJ : J ⊆ liveIndices B.val),
      SeedFree s J L → (∀ j ∈ J, 0 ≤ s.hi j ∧ s.hi j ≤ 2) →
    ∀ {ι₀ : Type v} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
      (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
      (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
      (t T H H' Z A : ℝ), 0 < H → 2 * 16 ^ J.card * H * (∏ j ∈ J, s.P j) ^ 4 ≤ H' →
      1 ≤ Z → 0 ≤ A → H' ≤ Z ^ A →
      NoCollision s C R L B J (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t →
      correctedChildGaussEnergy s 1 1 1 1 C R L (fun _ => 1) P B
          (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H ≤
        K * (∏ j ∈ J, s.M j ^ 2) * Z ^ (A * ε) *
          ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P
            (allocRestrict s C B J hJ)
            (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
            t (T / ∏ j ∈ J, s.P j) H' := by
  obtain ⟨K, hK0, hd⟩ := transfer_waist_design.{u} ε hε N
  refine ⟨K, hK0, ?_⟩
  intro α _ _ hcard s C R L P hp hPA B J hJ hSF hhi ι₀ _ _ reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀
    hK key c t T H H' Z A hH hrad hZ hA hHZ hNC
  have h := hd hcard s C R L P hp hPA B J hJ hSF hhi
    (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) t T H H' hH hrad hNC
  have hPpos : 0 < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  have hH' : 0 < H' := lt_of_lt_of_le (by positivity) hrad
  have hE : ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
        (fun _ => 1) P (allocRestrict s C B J hJ)
        (childCharacter (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ξ) t
        (T / ∏ j ∈ J, s.P j) H' =
      ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
        (fun _ => 1) P (allocRestrict s C B J hJ)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ)) t
        (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_congr rfl (fun ξ _ => rayShift_energy reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
      c ξ (s.restrict J) 1 1 1 1 C R L (fun _ => 1) P (allocRestrict s C B J hJ) t
      (T / ∏ j ∈ J, s.P j) H')
  have hsum : 0 ≤ ∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L
        (fun _ => 1) P (allocRestrict s C B J hJ)
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ)) t
        (T / ∏ j ∈ J, s.P j) H' :=
    Finset.sum_nonneg (fun ξ _ => corrected_energy_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH')
  have hKM : 0 ≤ K * ∏ j ∈ J, s.M j ^ 2 :=
    mul_nonneg hK0.le (Finset.prod_nonneg (fun j _ => sq_nonneg _))
  refine h.trans ?_
  rw [hE]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (max_rpow_le H' Z A ε hZ hA hε.le hHZ) hKM) hsum

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.transfer_waist_design
#print axioms QRH.MixedStep.Residual.transfer_waist_column
