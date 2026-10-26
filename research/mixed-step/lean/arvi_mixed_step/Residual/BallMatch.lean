/- Mixed source step: the ball-energy transfer with the residual given by any
input whose slot data match the residual along an equivalence (so that the
residual can be taken to be the child of the restricted parent). -/
import Submissions.arvi_mixed_step.Transfer.Ball
import Submissions.arvi_mixed_step.Residual.Restrict

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Residual
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeExpansion
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentFirstAmplificationChoice
open RayFourExpansion
open Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.MixedStep.Transfer
local notation "O" => ActualEisensteinCubic.O

/-- **Ball transfer, matched residual.** -/
theorem collet_main_selected_transfer_ball_match (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) {κ' : Type u} [Fintype κ'] [DecidableEq κ']
      (e : {i // i ∉ J} ≃ κ') (s₂ : RayCharacter → Input κ'),
      (∀ ξ, SlotMatch e (residualInput s J) (s₂ ξ)) →
    ∀ (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T H H' : ℝ),
      0 < H → 0 < H' → 2 * H * (∏ j ∈ J, s.hi j * s.P j) ^ 4 ≤ H' →
      (∀ j ∈ J, 0 ≤ s.hi j) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime L (∏ j ∈ J, v (Sum.inl j))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      (gaussEnergy Finset.univ
          (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
              ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) ballProfile H).re ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (max 1 H') ^ ε *
          ∑ ξ : RayCharacter,
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (s₂ ξ).pools)))
              (sourceGenerator_supported (finiteColumns (Fintype.piFinset (s₂ ξ).pools)))
              (fun I : supportedColumns (finiteColumns (Fintype.piFinset (s₂ ξ).pools)) =>
                CoupledFirst.coefficient (s₂ ξ) (markedSourceModifier A₁ A₂ Dc K F) R L I *
                  ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) ballProfile H').re := by
  obtain ⟨C, hC, hball⟩ := collet_main_selected_transfer_ball.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J κ' _ _ e s₂ hm A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hS hF hCol
  refine (hball hcard s J A₁ A₂ Dc K R L F τ t T H H' hH hH' hrad hhi hS hF hCol).trans
    (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro ξ _
  apply congrArg Complex.re
  exact energy_transport e (hm ξ) A₁ A₂ Dc K F R L
    (fun I => (Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
      rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I) ballProfile H'

end
end QRH.MixedStep.Residual

#print axioms QRH.MixedStep.Residual.collet_main_selected_transfer_ball_match
