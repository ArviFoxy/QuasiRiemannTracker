/- Mixed source step, L2 transfer: new in this submission; uses Collet's pool chain
(through PoolRows.lean) by import.

`collet_main_selected_transfer_pool` composes the transfer with
`actual_marked_corrected_rows`: the original first-MAIN dyadic energy is bounded by
the corrected energies of the residual sources (normalized by `√(T/∏_J P)`) at radius
`Z^(M'+6L)`, where `Z^M · W⁴ ≤ Z^M'`. -/
import Submissions.arvi_mixed_step.Transfer.Main
import Submissions.arvi_mixed_step.Transfer.PoolRows

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentAmplificationSlotGap
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceProfileMass
open RayFourExpansion CompletedGauss
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open QRH.Record1252270103Source.High.GlobalPhysical QRH.Record1252270103Low
local notation "O" => ActualEisensteinCubic.O

/-- The residual has the same pools on its marked slots, so a pool avoiding
the original slots avoids the residual ones. -/
theorem residual_marked {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Input ι) (J : Finset ι)
    (P : Finset (Ideal O)) (hmarked : ∀ Q ∈ P, ∀ i, ∀ I ∈ s.pools (Sum.inl i), ¬Q ∣ I) :
    ∀ Q ∈ P, ∀ i, ∀ I ∈ (residualInput s J).pools (Sum.inl i), ¬Q ∣ I :=
  fun Q hQ i I hI => hmarked Q hQ i.val I hI

/-- **Transfer chained into Collet's pool.** The original first-MAIN dyadic
energy (normalized by `√T`) is bounded by the pool-corrected ball energies of
the residual sources (normalized by `√(T/∏_J P)`, Hecke character
`childCharacter τ ξ`) at radius `Z^(M'+6L)`, where `Z^M W⁴ ≤ Z^M'`. The seed
condition is the tuple-level (S'); the pool-level (S) implies it
(`seed_free_of_slots`). -/
theorem collet_main_selected_transfer_pool (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
    ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
      (τ : HeckeFamily.Character) (t T : ℝ) (n : ℤ) (Z M W M' : ℝ)
      (P : Finset (Ideal O)) (ell upper B : ℝ),
      dyadicScale n ≤ Z ^ M → (∏ j ∈ J, s.hi j * s.P j) ≤ W → Z ^ M * W ^ 4 ≤ Z ^ M' →
      (∀ j ∈ J, 0 ≤ s.hi j) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime L (∏ j ∈ J, v (Sum.inl j))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v))) →
      (∀ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
          IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1))) →
      P.Nonempty → (∀ Q ∈ P, Prime Q) → (∀ Q ∈ P, Q ∉ fixedBadPrimes) →
      (∀ Q ∈ P, ∀ i, ∀ I ∈ s.pools (Sum.inl i), ¬Q ∣ I) →
      1 < Z → 0 < ell → 0 ≤ M' + 6 * upper →
      (∀ Q ∈ P, Z ^ ell ≤ (Q.absNorm : ℝ)) → (∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z ^ upper) →
      2 * (B / ell) ≤ (P.card : ℝ) → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      sourceRadius (residualInput s J) ≤ Z ^ B →
      (∑' h : O, dyadicWeight n (normValue h) *
          ‖gaussPolynomial Finset.univ
            (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
            (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
            (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
              CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
                ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) h‖ ^ 2) ≤
        C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε *
          ∑ ξ : RayCharacter, (P.card : ℝ)⁻¹ * ((M' + 6 * upper) / ell) *
            (gaussEnergy Finset.univ
              (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (sourceGenerator_supported
                (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
              (fun I : supportedColumns
                  (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
                CoupledFirst.coefficient (residualInput s J)
                  (markedSourceModifier A₁ A₂ 1 K
                    (fun J' => (((P.card : ℝ) / ((P.card : ℝ) - (idealDividingPool P J').card)) : ℂ) *
                      F (Dc * J')))
                  R L I *
                ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
                  rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I))
              ballProfile (Z ^ (M' + 6 * upper))).re := by
  obtain ⟨C, hC, htr⟩ := collet_main_selected_transfer_gen.{u} ε hε N
  refine ⟨C, hC, ?_⟩
  intro ι _ _ hcard s J A₁ A₂ Dc K R L F τ t T n Z M W M' P ell upper B hdyad hW hWM hhi hS hF
    hCol hP hp hbad hmarked hZ hell hscale hlower hupper hsize hz₁ hz₂ hsource
  obtain ⟨rows, hrows, hbound⟩ :=
    htr hcard s J A₁ A₂ Dc K R L F τ t T n Z M W hdyad hW hS hF hCol
  refine hbound.trans ?_
  have hZM : 0 < Z ^ M := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
  have hpos : 0 ≤ C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z ^ M * W ^ 4) ^ ε :=
    mul_nonneg (mul_nonneg hC.le (Finset.prod_nonneg (fun j hj => mul_nonneg (hhi j hj)
      (sq_nonneg _)))) (Real.rpow_nonneg (mul_nonneg hZM.le (by positivity)) ε)
  apply mul_le_mul_of_nonneg_left _ hpos
  apply Finset.sum_le_sum
  intro ξ _
  have h := actual_marked_corrected_rows (residualInput s J) A₁ A₂ Dc K R L F
    (fun I => (Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
      rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)
    P hP hp hbad (residual_marked s J P hmarked) rows (fun r hr => (hrows r hr).1)
    Z ell upper M' B hZ hell hscale hlower hupper hsize hz₁ hz₂ hsource
    (fun r hr => (hrows r hr).2.trans hWM)
  exact h

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.collet_main_selected_transfer_pool
