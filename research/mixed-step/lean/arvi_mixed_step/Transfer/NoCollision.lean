/- Mixed source step, L2 transfer: new in this submission; uses Sil's, Collet's and
the baseline's lemmas by import. `ball_from_identity` is the body of
`collet_main_selected_transfer_ball` (Ball.lean) with the identity (T) taken as a
hypothesis; `term_identity_abstract` is `term_identity_of_factor`
(SupplierIdentity.lean) with an abstract left coefficient.

The transfer without (Col). Split the tuple coefficient `tc` of a source as
`tc = tc·m + tc·(1 - m)`, where `m(v) = [∏_J v_j ⊥ v₀ v₁]` is the no-collision mask.
On the no-collision part the factorization

  tc(u ⊔ w) · m(u ⊔ w) = selWeight(u) · tc'(w) · [D_u ⊥ n_w]

holds for every pair of parts with no collision hypothesis, so the identity (T)
holds with the full residual, and the ball-energy transfer follows with the same
constant. The collision part `tc·(1 - m)` is left explicit (for L3). -/
import Submissions.arvi_mixed_step.Transfer.Ball
import Submissions.arvi_mixed_step.Transfer.SupplierIdentity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

universe u

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical SchwartzMap
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentSmoothedWindowEnergy CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstColumns RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source.Collision QRH.Record1252270103Source.High QRH.Record1252270103TwoIdeal
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

section Masks
variable {κ : Type*} [Fintype κ]

/-- The no-collision mask: the selected product is coprime to the ordinary pair. -/
def noColMask (J : Finset κ) (v : Tuple κ) : ℂ :=
  if IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)) then 1 else 0

/-- The no-collision part of a tuple coefficient. -/
def noColPart (J : Finset κ) (β : Tuple κ → ℂ) (v : Tuple κ) : ℂ := β v * noColMask J v

/-- The collision part of a tuple coefficient. -/
def colPart (J : Finset κ) (β : Tuple κ → ℂ) (v : Tuple κ) : ℂ := β v * (1 - noColMask J v)

theorem column_split (S : Finset (Tuple κ)) (J : Finset κ) (β : Tuple κ → ℂ) (I : Ideal O) :
    finiteColumnCoefficient S β I =
      finiteColumnCoefficient S (noColPart J β) I + finiteColumnCoefficient S (colPart J β) I := by
  unfold finiteColumnCoefficient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  unfold noColPart colPart
  ring

end Masks

/-- The ball energy is subadditive up to the factor 2. -/
theorem ball_energy_add_le {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c₁ c₂ : α → ℂ) (H : ℝ) (hH : 0 < H) :
    (gaussEnergy S a ha (fun i => c₁ i + c₂ i) ballProfile H).re ≤
      2 * (gaussEnergy S a ha c₁ ballProfile H).re + 2 * (gaussEnergy S a ha c₂ ballProfile H).re := by
  have h0 := gaussEnergy_hasSum_re S a ha (fun i => c₁ i + c₂ i) ballProfile H hH
  have h1 := (gaussEnergy_hasSum_re S a ha c₁ ballProfile H hH).mul_left 2
  have h2 := (gaussEnergy_hasSum_re S a ha c₂ ballProfile H hH).mul_left 2
  refine hasSum_le (fun z => ?_) h0 (h1.add h2)
  have hadd : gaussPolynomial S a ha (fun i => c₁ i + c₂ i) z =
      gaussPolynomial S a ha c₁ z + gaussPolynomial S a ha c₂ z := by
    unfold gaussPolynomial
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hw := ballProfile_nonneg (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / H)
  have hsq : ‖gaussPolynomial S a ha c₁ z + gaussPolynomial S a ha c₂ z‖ ^ 2 ≤
      2 * ‖gaussPolynomial S a ha c₁ z‖ ^ 2 + 2 * ‖gaussPolynomial S a ha c₂ z‖ ^ 2 := by
    have hn := norm_add_le (gaussPolynomial S a ha c₁ z) (gaussPolynomial S a ha c₂ z)
    nlinarith [sq_nonneg (‖gaussPolynomial S a ha c₁ z‖ - ‖gaussPolynomial S a ha c₂ z‖),
      norm_nonneg (gaussPolynomial S a ha c₁ z + gaussPolynomial S a ha c₂ z),
      norm_nonneg (gaussPolynomial S a ha c₁ z), norm_nonneg (gaussPolynomial S a ha c₂ z)]
  rw [hadd]
  calc
    _ ≤ (2 * ‖gaussPolynomial S a ha c₁ z‖ ^ 2 + 2 * ‖gaussPolynomial S a ha c₂ z‖ ^ 2) *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / H)).re :=
      mul_le_mul_of_nonneg_right hsq hw
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Factorization of the no-collision part**, with no collision hypothesis. -/
theorem tuple_factor_nocol (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (u : J → Ideal O) (w : Tuple {i // i ∉ J})
    (hL : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime L (selProduct J u))
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w)) :
    noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)
        (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0) := by
  unfold noColPart noColMask
  rw [sel_prod_join, joinTuple_inr, joinTuple_inr]
  by_cases hc0 : IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1))
  · simp only [hc0, ↓reduceIte, mul_one]
    exact tuple_factor_masked_gen s J A₁ A₂ Dc K R L F u w hL hF (fun _ => hc0)
  · have hn : ¬IsCoprime (selProduct J u) (finiteTupleProduct w) := by
      intro h
      apply hc0
      apply h.of_isCoprime_of_dvd_right
      rw [finiteTupleProduct_split w]
      exact dvd_mul_left _ _
    simp only [hc0, hn, ↓reduceIte, mul_zero]

/-- One term of the tuple sum, for any left coefficient with an exact factorization. -/
theorem term_identity_abstract (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L' : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (u : J → Ideal O)
    (w : Tuple {i // i ∉ J}) (a : ℂ)
    (hfac : a = selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L' w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0))
    (k : O) :
    a * (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct (joinTuple J u w))) *
          primaryGaussRow (finiteTupleProduct (joinTuple J u w)) k) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (selScalar s J K R τ t u χ k *
          (CoupledFirst.tupleCoefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L' w *
            ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
              (rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct w) *
                rayCharacter ξ (primaryGenerator (finiteTupleProduct w)) *
                primaryGaussRow (finiteTupleProduct w)
                  ((primaryGenerator (selProduct J u))^4 * k))))) := by
  have hWP : (0:ℝ) < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  set tc' := CoupledFirst.tupleCoefficient (residualInput s J)
    (markedSourceModifier A₁ A₂ Dc K F) R L' w with htc'
  by_cases hz : tc' = 0
  · have hz0 : a = 0 := by
      rw [hfac, hz]
      ring
    rw [hz0, hz]
    simp only [zero_mul, mul_zero, Finset.sum_const_zero]
  · have hfree : Supported (finiteTupleProduct w) →
        SexticSieve.PowerFree 5 (finiteTupleProduct w) :=
      fun _ => residual_power_free s J A₁ A₂ Dc K R L' F w hz
    have hrow := row_rays_fourth (selProduct J u) (finiteTupleProduct w) hfree k
    rw [hfac, finiteTupleProduct_join, map_mul, sqrt_split T _ hWP]
    have hmask : (if IsCoprime (selProduct J u) (finiteTupleProduct w) then (1:ℂ) else 0) *
        primaryGaussRow (selProduct J u * finiteTupleProduct w) k =
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then
          primaryGaussRow (selProduct J u * finiteTupleProduct w) k else 0) := by
      split_ifs <;> ring
    calc
      _ = (((Real.sqrt (∏ j ∈ J, s.P j) : ℂ))⁻¹ * selWeight s J K R u *
            rowWeight τ fixedBadMask 1 1 t (selProduct J u)) *
          (tc' * ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
            rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct w))) *
          ((if IsCoprime (selProduct J u) (finiteTupleProduct w) then (1:ℂ) else 0) *
            primaryGaussRow (selProduct J u * finiteTupleProduct w) k) := by ring
      _ = _ := by
        rw [hmask, hrow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ _
        unfold selScalar
        ring

/-- **The identity (T) for any original coefficient with the factorization.** -/
theorem transfer_identity_beta (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (β : Tuple ι → ℂ)
    (hβ : ∀ u ∈ selBox s J, ∀ w ∈ Fintype.piFinset (residualInput s J).pools,
      β (joinTuple J u w) = selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0))
    (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
          finiteColumnCoefficient (Fintype.piFinset s.pools) β I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k) := by
  rw [gauss_tuple_sum _ β (fun I => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) k,
    box_sum]
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw =>
    term_identity_abstract s J A₁ A₂ Dc K R L F τ t T u w (β (joinTuple J u w)) (hβ u hu w hw) k))]
  simp only [Finset.sum_comm (s := Fintype.piFinset (residualInput s J).pools)
    (t := (Finset.univ : Finset RayCharacter))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [residual_tuple_form, Finset.mul_sum, Finset.mul_sum]

/-- The no-collision part satisfies the identity (T) under (S') and (F) alone. -/
theorem transfer_identity_nocol (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ)
    (hS : ∀ v ∈ Fintype.piFinset s.pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
        IsCoprime L (∏ j ∈ J, v (Sum.inl j)))
    (hF : ∀ v ∈ Fintype.piFinset s.pools,
      F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v)))
    (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
          finiteColumnCoefficient (Fintype.piFinset s.pools)
            (noColPart J (CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L)) I *
            ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k) := by
  apply transfer_identity_beta
  intro u hu w hw
  have hv : joinTuple J u w ∈ Fintype.piFinset s.pools := by
    apply Fintype.mem_piFinset.mpr
    apply (mem_pools_iff s _).mpr
    have hu' := Fintype.mem_piFinset.mp hu
    have hw' := (mem_pools_iff (residualInput s J) _).mp (Fintype.mem_piFinset.mp hw)
    refine ⟨?_, hw'.2.1, hw'.2.2⟩
    intro i
    by_cases h : i ∈ J
    · rw [joinTuple_inl_mem J _ _ i h]; exact hu' ⟨i, h⟩
    · rw [joinTuple_inl_not_mem J _ _ i h]; exact hw'.1 ⟨i, h⟩
  apply tuple_factor_nocol s J A₁ A₂ Dc K R L F u w
  · intro hne
    have h := hS _ hv hne
    rwa [sel_prod_join] at h
  · have h := hF _ hv
    rwa [restPart_join] at h

end
end QRH.MixedStep.Transfer

#print axioms QRH.MixedStep.Transfer.transfer_identity_nocol
#print axioms QRH.MixedStep.Transfer.ball_energy_add_le
