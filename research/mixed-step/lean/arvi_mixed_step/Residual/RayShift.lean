/- Mixed source step, N2: new in this submission; uses Collet's and the baseline's
definitions by import.

The ray label `ξ` returned by the transfer (design §5, T1). The residual of a
first-layer column `c` carries the twist `childCharacter (columnCharacter c) ξ`.
On supported ideals its row weight is that of `columnCharacter (rayShift c ξ)`,
where `rayShift` multiplies the left ray by `ξ` (reflected: the right ray by
`ξ⁻¹`, so that the pair's second ray `ξ₂⁻¹` becomes `ξ₂⁻¹·ξ`). Since `fixedPair`
is a classical choice, only the energies are identified (`rayShift_energy`),
never the characters. The shifted column has the same source label, divisor,
ideal, scalar, rows and liveness (all `rfl`). -/
import Submissions.arvi_mixed_step.Residual.Contract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyLabels
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBalancedColumns

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondChildProfile
open RayFourExpansion CanonicalQuadraticSieve Cycle61InitialMass
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
open QRH.Record1252270103Source.Admission.FirstFamily
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O
local notation "source" => QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource

/-- The ray shift of a first-layer column by the transfer label `ξ`. -/
def rayShift {Label : Type*} {src : Label → FirstBlockSource} (reflected : Bool)
    (c : FirstColumnIndex src) (ξ : RayCharacter) : FirstColumnIndex src :=
  ⟨c.1, c.2.1, if reflected then c.2.2.1 else c.2.2.1 * ξ,
    if reflected then c.2.2.2 * ξ⁻¹ else c.2.2.2⟩

section Same
variable {Label : Type*} {src : Label → FirstBlockSource} (reflected : Bool)
  (c : FirstColumnIndex src) (ξ : RayCharacter)

@[simp] theorem rayShift_fst : (rayShift reflected c ξ).1 = c.1 := rfl

theorem rayShift_divisor : (rayShift reflected c ξ).2.1 = c.2.1 := rfl

theorem firstColumnRows_rayShift (V : Fin 4 → ℝ → ℂ) :
    firstColumnRows src V (rayShift reflected c ξ) = firstColumnRows src V c := rfl

theorem rayShift_mem_firstLiveColumns [Fintype Label] (V : Fin 4 → ℝ → ℂ) :
    rayShift reflected c ξ ∈ firstLiveColumns src V ↔ c ∈ firstLiveColumns src V := by
  simp only [firstLiveColumns, Finset.mem_filter, Finset.mem_univ, true_and,
    firstColumnRows_rayShift]

end Same

section Labels
variable {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool) (s₀ : Input ι₀)
  (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
  (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
  (ξ : RayCharacter)

theorem firstLabel_rayShift :
    firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ) =
      firstLabel s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c := rfl

theorem columnIdeal_rayShift (reflected' : Bool) :
    columnIdeal reflected' s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ) =
      columnIdeal reflected' s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c := rfl

theorem balancedColumnScalar_rayShift (reflected' : Bool) (M A : ℝ)
    (weight : CoupledFirst.SourceCoordinate s₀ modifier R₀ seed K₀ Z₀ ξ₀ → ℂ) :
    CoupledFirst.balancedColumnScalar reflected' s₀ modifier R₀ seed K₀ Z₀ ξ₀ M A hK key weight
        (rayShift reflected c ξ) =
      CoupledFirst.balancedColumnScalar reflected' s₀ modifier R₀ seed K₀ Z₀ ξ₀ M A hK key weight c :=
  rfl

end Labels

/-- On supported ideals the child twist multiplies the row weight by the ray
character of the primary generator. -/
theorem rowWeight_child (τ : HeckeFamily.Character) (ξ : RayCharacter) (t : ℝ) (I : Ideal O)
    (hI : Supported I) :
    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I =
      rowWeight τ fixedBadMask 1 1 t I * rayCharacter ξ (CompletedGauss.primaryGenerator I) := by
  rw [← heightCoeff_eq_fixed_rowWeight _ t I hI, ← heightCoeff_eq_fixed_rowWeight _ t I hI]
  unfold heightCoeff
  rw [child_ideal_primary τ ξ I hI]
  ring

theorem fixedPair_left_shift (η : HeckeFamily.Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) (ξ₁ ξ₂ ξ : RayCharacter) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight (childCharacter (fixedPair η C D hC E ξ₁ ξ₂).left ξ) fixedBadMask 1 1 t I =
      rowWeight (fixedPair η C D hC E (ξ₁ * ξ) ξ₂).left fixedBadMask 1 1 t I := by
  rw [rowWeight_child _ ξ t I hI, ← heightCoeff_eq_fixed_rowWeight _ t I hI,
    ← heightCoeff_eq_fixed_rowWeight _ t I hI,
    (fixedPair η C D hC E ξ₁ ξ₂).left_height I hI t,
    (fixedPair η C D hC E (ξ₁ * ξ) ξ₂).left_height I hI t]
  simp only [rayCharacter, MulChar.mul_apply]
  ring

theorem fixedPair_right_shift (η : HeckeFamily.Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D)) (ξ₁ ξ₂ ξ ξ₂' : RayCharacter)
    (h : ξ₂' = ξ₂ * ξ) (t : ℝ) (I : Ideal O) (hI : Supported I) :
    rowWeight (childCharacter (fixedPair η C D hC E ξ₁ ξ₂).right ξ) fixedBadMask 1 1 t I =
      rowWeight (fixedPair η C D hC E ξ₁ ξ₂').right fixedBadMask 1 1 t I := by
  subst h
  rw [rowWeight_child _ ξ t I hI, ← heightCoeff_eq_fixed_rowWeight _ t I hI,
    ← heightCoeff_eq_fixed_rowWeight _ t I hI,
    (fixedPair η C D hC E ξ₁ ξ₂).right_height I hI t,
    (fixedPair η C D hC E ξ₁ (ξ₂ * ξ)).right_height I hI t]
  simp only [rayCharacter, MulChar.mul_apply]
  ring

/-- **Row weights of the shifted column.** -/
theorem column_rayShift_rowWeight {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool)
    (s₀ : Input ι₀) (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
    (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
    (ξ : RayCharacter) (t : ℝ) (I : Ideal O) (hI : Supported I) :
    rowWeight (childCharacter (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ξ)
        fixedBadMask 1 1 t I =
      rowWeight (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key
        (rayShift reflected c ξ)) fixedBadMask 1 1 t I := by
  cases reflected
  · exact fixedPair_left_shift _ _ _ _ _ _ _ ξ t I hI
  · exact fixedPair_right_shift _ _ _ _ _ _ _ ξ _
      (by show (c.2.2.2 * ξ⁻¹)⁻¹ = c.2.2.2⁻¹ * ξ; rw [mul_inv_rev, inv_inv, mul_comm]) t I hI

/-- The corrected child energy depends on the character only through its row
weights on supported ideals (the child input uses the character only in its
`η` field, which the coefficient does not read). -/
theorem corrected_energy_congr {α : Type*} [Fintype α] [DecidableEq α] (s : Input α)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O → ℂ) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (τ₁ τ₂ : HeckeFamily.Character) (t T H : ℝ)
    (h : ∀ I : Ideal O, Supported I →
      rowWeight τ₁ fixedBadMask 1 1 t I = rowWeight τ₂ fixedBadMask 1 1 t I) :
    correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ₁ t T H =
      correctedChildGaussEnergy s A₁ A₂ D K C R L F P B τ₂ t T H := by
  have key : ∀ (S : Finset (Ideal O)) (c : Ideal O → ℂ),
      gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S =>
          c I * ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ₁ fixedBadMask 1 1 t I)) ballProfile H =
      gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
        (fun I : supportedColumns S =>
          c I * ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ₂ fixedBadMask 1 1 t I)) ballProfile H := by
    intro S c
    congr 1
    funext I
    rw [h I.val (Finset.mem_filter.mp I.property).2]
  unfold correctedChildGaussEnergy
  dsimp only
  exact congrArg Complex.re (key _ _)

/-- **N2: the energy equality.** The residual energy with the transfer twist
equals the energy at the shifted column character. -/
theorem rayShift_energy {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀] (reflected : Bool)
    (s₀ : Input ι₀) (modifier : Tuple ι₀ → ℂ) (R₀ seed : Ideal O) (K₀ Z₀ ξ₀ : ℝ) (hK : 0 < K₀)
    (key : ℤ × (Fin 5 → ℤ)) (c : FirstColumnIndex (source s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key))
    (ξ : RayCharacter) {α : Type*} [Fintype α] [DecidableEq α] (s : Input α)
    (A₁ A₂ D K C R L : Ideal O) (F : Ideal O → ℂ) (P : Finset (Ideal O))
    (B : actualAllocations s.pools C) (t T H : ℝ) :
    correctedChildGaussEnergy s A₁ A₂ D K C R L F P B
        (childCharacter (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c) ξ) t T H =
      correctedChildGaussEnergy s A₁ A₂ D K C R L F P B
        (columnCharacter reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key (rayShift reflected c ξ))
        t T H :=
  corrected_energy_congr s A₁ A₂ D K C R L F P B _ _ t T H
    (fun I hI => column_rayShift_rowWeight reflected s₀ modifier R₀ seed K₀ Z₀ ξ₀ hK key c ξ t I hI)

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.rayShift_energy
#print axioms QRH.MixedStep.Residual.rayShift_mem_firstLiveColumns
