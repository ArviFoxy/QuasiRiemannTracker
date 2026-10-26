/- Adapted from Collet's `actual_marked_allocation_main`
(Record1252270103Source/High/GlobalPhysicalAllocationMain.lean): the allocation split,
the per-allocation step and the decidable-instance transport are kept. Change: the
per-child pool bound is replaced by the selected transfer
`collet_main_selected_transfer_pool`.

Mixed source step, L2 transfer: the transfer at Collet's MAIN waist.

`allocation_selected_transfer_pool` is the mixed twin of Collet's
`actual_marked_allocation_main` (S/High/GlobalPhysicalAllocationMain.lean):
the first-common allocation energy is split over actual allocations `B`
(Collet's `actual_allocation_dyadic_energy`), and in each child
`child s C R B τ t` a selected block `Jsel B` of live slots is transferred
(`collet_main_selected_transfer_pool`). The child energy normalized by the
parent volume `√T` is replaced by the pool-corrected energies of the residual
children normalized by `√(T/∏_{Jsel B} P)`, at radius `Z^(M'+6·upper)`. -/
import Submissions.arvi_mixed_step.Transfer.Pool
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllocationMain

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open RayFourExpansion
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

/-- **Transfer at Collet's MAIN waist** (mixed twin of
`actual_marked_allocation_main`). -/
theorem allocation_selected_transfer_pool (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (A₁ A₂ D K C R seed L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W M' : ℝ)
      (P : Finset (Ideal O)) (ell upper Bcap : ℝ)
      (Jsel : ∀ B : actualAllocations s.pools C, Finset (liveIndices B.val)),
      dyadicScale n ≤ Z ^ M → Z ^ M * W ^ 4 ≤ Z ^ M' →
      (∀ B, (∏ j ∈ Jsel B, (child s C R B τ t).hi j * (child s C R B τ t).P j) ≤ W) →
      (∀ B, ∀ j ∈ Jsel B, 0 ≤ (child s C R B τ t).hi j) →
      (∀ B, ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
        CoupledFirst.tupleCoefficient (child s C R B τ t)
          (markedSourceModifier (A₁ * B.val (Sum.inr 0)) (A₂ * B.val (Sum.inr 1)) (D * C)
            (K * markedProduct B.val) F) (R * C) L v ≠ 0 →
          IsCoprime L (∏ j ∈ Jsel B, v (Sum.inl j))) →
      (∀ B, ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
        F ((D * C) * finiteTupleProduct v) =
          F ((D * C) * finiteTupleProduct (restPart (Jsel B) v))) →
      (∀ B, ∀ v ∈ Fintype.piFinset (child s C R B τ t).pools,
        CoupledFirst.tupleCoefficient (child s C R B τ t)
          (markedSourceModifier (A₁ * B.val (Sum.inr 0)) (A₂ * B.val (Sum.inr 1)) (D * C)
            (K * markedProduct B.val) F) (R * C) L v ≠ 0 →
          IsCoprime (∏ j ∈ Jsel B, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      P.Nonempty → (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, ∀ i, ∀ J ∈ s.pools (Sum.inl i), ¬Q ∣ J) →
      1 < Z → 0 < ell → 0 ≤ M' + 6 * upper →
      (∀ Q ∈ P, Z ^ ell ≤ (Q.absNorm : ℝ)) → (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z ^ upper) →
      2 * (Bcap / ell) ≤ (P.card : ℝ) → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ B, sourceRadius (residualInput (child s C R B τ t) (Jsel B)) ≤ Z ^ Bcap) →
      (∑' z : O, dyadicWeight n (normValue z) *
        ‖CoupledFirst.allocatedPolynomial (original s R seed) (markedSourceModifier A₁ A₂ D K F)
          C L τ t T z‖ ^ 2) ≤
      ((actualAllocations s.pools C).card : ℝ) *
        ∑ B : actualAllocations s.pools C, ‖frozenCoefficient B.val C R s.ν s.W s.P‖ ^ 2 *
          (Cc * (∏ j ∈ Jsel B, (child s C R B τ t).hi j * (child s C R B τ t).M j ^ 2) *
            (Z ^ M * W ^ 4) ^ ε *
            ∑ ξ : RayCharacter, (P.card : ℝ)⁻¹ * ((M' + 6 * upper) / ell) *
              (gaussEnergy Finset.univ
                (sourceGenerator (finiteColumns
                  (Fintype.piFinset (residualInput (child s C R B τ t) (Jsel B)).pools)))
                (sourceGenerator_supported (finiteColumns
                  (Fintype.piFinset (residualInput (child s C R B τ t) (Jsel B)).pools)))
                (fun I : supportedColumns (finiteColumns
                    (Fintype.piFinset (residualInput (child s C R B τ t) (Jsel B)).pools)) =>
                  CoupledFirst.coefficient (residualInput (child s C R B τ t) (Jsel B))
                    (markedSourceModifier (A₁ * B.val (Sum.inr 0)) (A₂ * B.val (Sum.inr 1)) 1
                      (K * markedProduct B.val)
                      (fun J' => (((P.card : ℝ) /
                        ((P.card : ℝ) - (idealDividingPool P J').card)) : ℂ) * F ((D * C) * J')))
                    (R * C) L I *
                  ((Real.sqrt (T / ∏ j ∈ Jsel B, (child s C R B τ t).P j) : ℂ)⁻¹ *
                    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I))
                ballProfile (Z ^ (M' + 6 * upper))).re) := by
  obtain ⟨Cc, hCc, hpool⟩ := collet_main_selected_transfer_pool.{u} ε hε N
  refine ⟨Cc, hCc, ?_⟩
  intro ι _ _ hcard s A₁ A₂ D K C R seed L F τ t T n Z M W M' P ell upper Bcap Jsel hdyad hWM hW
    hhi hS hF hCol hP hp hbad hmarked hZ hell hscale hlower hupper hsize hz₁ hz₂ hsource
  apply (actual_allocation_dyadic_energy s (markedSourceModifier A₁ A₂ D K F)
    C R seed L τ t T n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hcardB : Fintype.card (liveIndices B.val) ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans hcard
  have hh := hpool hcardB (child s C R B τ t) (Jsel B) (A₁ * B.val (Sum.inr 0))
    (A₂ * B.val (Sum.inr 1)) (D * C) (K * markedProduct B.val) (R * C) L F τ t T n Z M W M'
    P ell upper Bcap hdyad (hW B) hWM (hhi B) (hS B) (hF B) (hCol B) hP hp hbad
    (fun Q hQ i J hJ => hmarked Q hQ i.val J hJ) hZ hell hscale hlower hupper hsize hz₁ hz₂
    (hsource B)
  simp_rw [actual_marked_child_polynomial]
  refine le_trans (le_of_eq ?_) hh
  exact source_gauss_dyadic_pool_decEq (ι := liveIndices B.val) _ _ (child s C R B τ t).pools
    (fun I => CoupledFirst.coefficient (child s C R B τ t)
      (markedSourceModifier (A₁ * B.val (Sum.inr 0)) (A₂ * B.val (Sum.inr 1)) (D * C)
        (K * markedProduct B.val) F) (R * C) L I *
      ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) n

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.allocation_selected_transfer_pool
