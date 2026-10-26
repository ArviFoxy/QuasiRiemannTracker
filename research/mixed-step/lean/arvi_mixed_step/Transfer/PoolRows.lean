/- Adapted from Collet's tree: `column_no_prime_square` from `source_column_no_prime_square`
(Record1252270103Source/Coefficient/AmplifierSupport.lean), `corrected_source_rows_main`
from `corrected_source_dyadic_main` (Coefficient/SourceAmplifier.lean),
`corrected_coefficient_generic` from `actual_marked_corrected_coefficient`
(High/GlobalPhysicalCorrection.lean) and `actual_marked_corrected_rows` from
`actual_marked_main_ideal_coefficient` (High/GlobalPhysicalCorrectedMain.lean).
Changes: a finite set of nonzero rows replaces the dyadic weight; any `Input`,
column set and column multiplier `Γ`; the ambient decidable-equality instance on
the slot type.

Mixed source step, L2 transfer: Collet's pool chain on finitely many rows.
`actual_marked_corrected_rows` (rows 3-5 of the MAIN chain): for any `Input`, the
energy of the marked source polynomial over a finite set of nonzero rows of norm
`≤ Z^M` is bounded by the pool-corrected ball energy at radius `Z^(M+6L)`. The pool
premises are discharged from the source structure as in Collet's
`corrected_source_dyadic_main`. -/
import Submissions.arvi_mixed_step.Transfer.Rays
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalCorrectedMain

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

/-- Collet's `source_column_no_prime_square`, for the tuple box built with the
ambient decidable-equality instance on the slot type. -/
theorem column_no_prime_square {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : (κ ⊕ Fin 2) → Finset (Ideal O)) (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ)
    (β : Tuple κ → ℂ) (I Q : Ideal O) (hQ : Prime Q)
    (hmarked : ∀ i, ∀ J ∈ S (Sum.inl i), ¬Q ∣ J)
    (hne : finiteColumnCoefficient (Fintype.piFinset S)
      (fun v => sourceModifier A₁ A₂ D F v * β v) I ≠ 0) : ¬Q ^ 2 ∣ I := by
  obtain ⟨v, hv, hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv, he⟩ := Finset.mem_filter.mp hv
  have hsf := (sourceModifier_nonzero A₁ A₂ D F v (mul_ne_zero_iff.mp hvn).1).2.1
  have heq : A₁ * v (Sum.inr 0) * A₂ * v (Sum.inr 1) =
      (A₁ * A₂) * (v (Sum.inr 0) * v (Sum.inr 1)) := by ring
  rw [heq] at hsf
  have hslot : ¬Q ∣ ∏ i, v (Sum.inl i) := by
    apply hQ.not_dvd_finsetProd
    intro i _
    exact hmarked i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))
  rw [← he]
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  simpa only [mul_assoc] using
    QRH.Record1252270103TwoIdeal.no_prime_square_dvd_column hQ hsf.of_mul_right hslot

/-- Finite-row version of Collet's `corrected_source_dyadic_main`. -/
theorem corrected_source_rows_main {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : (κ ⊕ Fin 2) → Finset (Ideal O)) (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ)
    (β : Tuple κ → ℂ) (Γ : Ideal O → ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (hmarked : ∀ Q ∈ P, ∀ i, ∀ J ∈ S (Sum.inl i), ¬Q ∣ J)
    (rows : Finset O) (hrows : ∀ h ∈ rows, h ≠ 0)
    (Z ell L M B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hscale : 0 ≤ M + 6 * L)
    (hlower : ∀ Q ∈ P, Z ^ ell ≤ (Ideal.absNorm Q : ℝ))
    (hupper : ∀ Q ∈ P, (Ideal.absNorm Q : ℝ) ≤ Z ^ L)
    (hsize : 2 * (B / ell) ≤ (P.card : ℝ))
    (hcolumn : ∀ I ∈ finiteColumns (Fintype.piFinset S),
      finiteColumnCoefficient (Fintype.piFinset S) (fun v => sourceModifier A₁ A₂ D F v * β v) I ≠ 0 →
      (Ideal.absNorm I : ℝ) ≤ Z ^ B)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z ^ M) :
    let T := finiteColumns (Fintype.piFinset S)
    let c := fun I : supportedColumns T =>
      finiteColumnCoefficient (Fintype.piFinset S) (fun v => sourceModifier A₁ A₂ D F v * β v) I * Γ I
    (∑ h ∈ rows, ‖gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T) c h‖ ^ 2) ≤
      (P.card : ℝ)⁻¹ * ((M + 6 * L) / ell) *
        (gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
          (correctedCoefficient (elementPool P) (sourceGenerator T) c)
          ballProfile (Z ^ (M + 6 * L))).re := by
  dsimp only
  let T := finiteColumns (Fintype.piFinset S)
  let c := fun I : supportedColumns T =>
    finiteColumnCoefficient (Fintype.piFinset S) (fun v => sourceModifier A₁ A₂ D F v * β v) I * Γ I
  have hdata := elementPool_data P hp hbad
  have hcard := elementPool_card P hp hbad
  have hcap (I : supportedColumns T) (hci : c I ≠ 0) : (Ideal.absNorm I.val : ℝ) ≤ Z ^ B :=
    hcolumn I (Finset.mem_filter.mp I.property).1 (mul_ne_zero_iff.mp hci).1
  have he := corrected_gauss_energy_ball Finset.univ (sourceGenerator T)
    (sourceGenerator_supported T) c rows (elementPool P) (Finset.Nonempty.image hP _) hrows
    (fun p hpm => (hdata p hpm).1)
    (fun p hpm => (hdata p hpm).2.2.2.1)
    (fun p hpm => (hdata p hpm).2.2.2.2.1)
    (fun p hpm => (hdata p hpm).2.2.2.2.2)
    (fun p hpm => (hdata p hpm).2.2.1) ?_ ?_ Z ell M L hZ hell hscale
    (fun p hpm => hlower _ (hdata p hpm).2.1)
    (fun p hpm => hupper _ (hdata p hpm).2.1) hhu
  · simpa only [hcard] using he
  · intro I _ hci p hpm
    apply source_generator_no_prime_square T I p
    exact column_no_prime_square S A₁ A₂ D F β I (Ideal.span {p})
      (hp _ (hdata p hpm).2.1) (hmarked _ (hdata p hpm).2.1) (mul_ne_zero_iff.mp hci).1
  · intro I _ hci
    apply dividingPool_card_lt_of_geometry (elementPool P) (Finset.Nonempty.image hP _)
      (sourceGenerator T I) ?_ (fun p hpm => (hdata p hpm).1)
      (fun p hpm => (hdata p hpm).2.2.1) Z ell B hZ hell
      (fun p hpm => hlower _ (hdata p hpm).2.1) ?_ ?_
    · exact Ideal.span_singleton_eq_bot.not.mp (sourceGenerator_supported T I).1
    · simpa only [sourceGenerator, primary_span_supported I (Finset.mem_filter.mp I.property).2]
        using hcap I hci
    · simpa only [hcard] using hsize

/-- Collet's `actual_marked_corrected_coefficient`, for an arbitrary column set. -/
theorem corrected_coefficient_generic {κ : Type*} [Fintype κ]
    (s : Input κ) (A₁ A₂ D K R seed : Ideal O) (F Γ : Ideal O → ℂ)
    (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (S : Finset (Ideal O)) (I : supportedColumns S) :
    correctedCoefficient (elementPool P) (sourceGenerator S)
      (fun J => CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed J * Γ J) I =
      CoupledFirst.coefficient s
        (markedSourceModifier A₁ A₂ 1 K
          (fun J => (((P.card : ℝ) / ((P.card : ℝ) - (idealDividingPool P J).card)) : ℂ) * F (D * J)))
        R seed I * Γ I := by
  rw [corrected_generator_coefficient P _ hp hbad]
  rw [← mul_assoc]
  unfold CoupledFirst.coefficient CoupledFirst.tupleCoefficient
  apply congrArg (fun x : ℂ => x * Γ I)
  exact marked_column_multiplier _ A₁ A₂ D K F
    (fun J => (((P.card : ℝ) / ((P.card : ℝ) - (idealDividingPool P J).card)) : ℂ))
    (fun v => profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v) I

/-- Finite-row version of Collet's `actual_marked_main_ideal_coefficient`
(rows 3–5 of the MAIN chain), for an arbitrary `Input`. -/
theorem actual_marked_corrected_rows {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Input κ) (A₁ A₂ D K R seed : Ideal O) (F Γ : Ideal O → ℂ)
    (P : Finset (Ideal O)) (hP : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (hmarked : ∀ Q ∈ P, ∀ i, ∀ J ∈ s.pools (Sum.inl i), ¬Q ∣ J)
    (rows : Finset O) (hrows : ∀ h ∈ rows, h ≠ 0)
    (Z ell L M B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hscale : 0 ≤ M + 6 * L)
    (hlower : ∀ Q ∈ P, Z ^ ell ≤ (Q.absNorm : ℝ))
    (hupper : ∀ Q ∈ P, (Q.absNorm : ℝ) ≤ Z ^ L)
    (hsize : 2 * (B / ell) ≤ (P.card : ℝ))
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0) (hsource : sourceRadius s ≤ Z ^ B)
    (hhu : ∀ h ∈ rows, normValue h ≤ Z ^ M) :
    (∑ h ∈ rows,
      ‖gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
          CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed I * Γ I) h‖ ^ 2) ≤
      (P.card : ℝ)⁻¹ * ((M + 6 * L) / ell) *
        (gaussEnergy Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
          (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
          (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
            CoupledFirst.coefficient s
              (markedSourceModifier A₁ A₂ 1 K
                (fun J => (((P.card : ℝ) / ((P.card : ℝ) - (idealDividingPool P J).card)) : ℂ) *
                  F (D * J)))
              R seed I * Γ I)
          ballProfile (Z ^ (M + 6 * L))).re := by
  let β := fun v =>
    QRH.Record1252270103TwoIdeal.squarefreeIndicator (K * markedProduct v) *
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  have he : (fun v => sourceModifier A₁ A₂ D F v * β v) =
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ D K F) R seed := by
    funext v
    simp only [β, CoupledFirst.tupleCoefficient, markedSourceModifier]
    ring
  have hec : finiteColumnCoefficient (Fintype.piFinset s.pools)
      (fun v => sourceModifier A₁ A₂ D F v * β v) =
      CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ D K F) R seed := by
    rw [he]
    unfold CoupledFirst.coefficient
    congr
    exact Subsingleton.elim _ _
  have hcolumn (I : Ideal O) (_hI : I ∈ finiteColumns (Fintype.piFinset s.pools))
      (hne : finiteColumnCoefficient (Fintype.piFinset s.pools)
        (fun v => sourceModifier A₁ A₂ D F v * β v) I ≠ 0) : (I.absNorm : ℝ) ≤ Z ^ B := by
    rw [hec] at hne
    exact (CoupledFirst.original_column_norm s (markedSourceModifier A₁ A₂ D K F)
      R seed I hz₁ hz₂ hne).2.trans hsource
  have hh := corrected_source_rows_main s.pools A₁ A₂ D F β Γ P hP hp hbad hmarked
    rows hrows Z ell L M B hZ hell hscale hlower hupper hsize hcolumn hhu
  dsimp only at hh
  simp only [hec] at hh
  have hcoef := funext (corrected_coefficient_generic s A₁ A₂ D K R seed F Γ P hp hbad
    (finiteColumns (Fintype.piFinset s.pools)))
  rw [hcoef] at hh
  exact hh

end
end QRH.MixedStep.Transfer
