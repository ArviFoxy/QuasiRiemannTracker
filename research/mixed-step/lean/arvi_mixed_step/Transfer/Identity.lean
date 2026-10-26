/- Mixed source step, L2 transfer: the exact fourth-power transfer identity (T)
at Collet's first MAIN layer.

  G(k) = Σ_{χ,ξ} π_{χξ} Σ_{u ∈ selBox} α_χ(u,k) · G'_ξ(d(u)⁴ k)

where `G` is Collet's child-source polynomial (normalized by `√T`), `G'_ξ` is
the residual source polynomial on `{i // i ∉ J}` normalized by
`√(T/∏_J P)` with the Hecke character `childCharacter τ ξ`, `d(u)` is the
primary generator of the selected product and `α_χ(u,k)` carries the
remaining `(√∏_J P)⁻¹`. Hypotheses: (S), (F-invariance), (Col). -/
import Submissions.arvi_mixed_step.Transfer.Rays

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace QRH.MixedStep.Transfer
noncomputable section
open OAI OAI.SevenEighths
open scoped BigOperators Classical
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentLiveDomain
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentFirstColumns CenteredMomentChildRows
open RayFourExpansion CanonicalQuadraticSieve CompletedGauss
open Record1252270103Source Record1252270103Source.Collision QRH.Record1252270103Source.High
open Candidate.FourthPower
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Collet's child-source polynomial with the original normalization `√T`. -/
def originalPolynomial (s : Input ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (k : O) : ℂ :=
  gaussPolynomial Finset.univ (sourceGenerator (finiteColumns (Fintype.piFinset s.pools)))
    (sourceGenerator_supported (finiteColumns (Fintype.piFinset s.pools)))
    (fun I : supportedColumns (finiteColumns (Fintype.piFinset s.pools)) =>
      CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I *
        ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)) k

/-- The residual source polynomial with ray label `ξ`, normalized by the
residual volume `√(T/∏_J P)`. -/
def residualPolynomial (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (ξ : RayCharacter) (k : O) : ℂ :=
  gaussPolynomial Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
    (sourceGenerator_supported (finiteColumns (Fintype.piFinset (residualInput s J).pools)))
    (fun I : supportedColumns (finiteColumns (Fintype.piFinset (residualInput s J).pools)) =>
      CoupledFirst.coefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L I *
        ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
          rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)) k

/-- The selected scalar: the selected weight, the remaining volume factor
`(√∏_J P)⁻¹`, the selected row weight, the first ray character and the
selected Gauss sum. -/
def selScalar (s : Input ι) (J : Finset ι) (K R : Ideal O) (τ : HeckeFamily.Character) (t : ℝ)
    (u : J → Ideal O) (χ : RayCharacter) (k : O) : ℂ :=
  ((Real.sqrt (∏ j ∈ J, s.P j) : ℂ))⁻¹ * selWeight s J K R u *
    rowWeight τ fixedBadMask 1 1 t (selProduct J u) *
    (rayCharacter χ (primaryGenerator (selProduct J u)) * primaryGaussRow (selProduct J u) k)

theorem coefficient_eq_box {κ : Type*} [Fintype κ] [DecidableEq κ] (s : Input κ)
    (modifier : Tuple κ → ℂ) (R L : Ideal O) :
    CoupledFirst.coefficient s modifier R L =
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (CoupledFirst.tupleCoefficient s modifier R L) := by
  unfold CoupledFirst.coefficient
  congr
  exact Subsingleton.elim _ _

theorem original_tuple_form (s : Input ι) (A₁ A₂ Dc K R L : Ideal O) (F : Ideal O → ℂ)
    (τ : HeckeFamily.Character) (t T : ℝ) (k : O) :
    originalPolynomial s A₁ A₂ Dc K R L F τ t T k =
      ∑ v ∈ Fintype.piFinset s.pools,
        CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v *
          (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct v)) *
            primaryGaussRow (finiteTupleProduct v) k) := by
  unfold originalPolynomial
  rw [coefficient_eq_box]
  exact gauss_tuple_sum _ _ (fun I => (Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I) k

theorem residual_tuple_form (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (ξ : RayCharacter) (k : O) :
    residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ k =
      ∑ w ∈ Fintype.piFinset (residualInput s J).pools,
        CoupledFirst.tupleCoefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L w *
          ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
            (rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct w) *
              rayCharacter ξ (primaryGenerator (finiteTupleProduct w)) *
              primaryGaussRow (finiteTupleProduct w) k)) := by
  unfold residualPolynomial
  rw [coefficient_eq_box]
  rw [gauss_tuple_sum _ _ (fun I => (Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
    rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I) k]
  apply Finset.sum_congr rfl
  intro w _
  rw [mul_assoc (Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹, rowWeight_child_gauss]

/-- One term of the original tuple sum, split by the selected part. -/
theorem term_identity (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (u : J → Ideal O)
    (w : Tuple {i // i ∉ J}) (hL : IsCoprime L (selProduct J u))
    (hF : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w))
    (hCol : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
      (joinTuple J u w) ≠ 0 → IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1)))
    (k : O) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) *
        (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct (joinTuple J u w))) *
          primaryGaussRow (finiteTupleProduct (joinTuple J u w)) k) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (selScalar s J K R τ t u χ k *
          (CoupledFirst.tupleCoefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L w *
            ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
              (rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct w) *
                rayCharacter ξ (primaryGenerator (finiteTupleProduct w)) *
                primaryGaussRow (finiteTupleProduct w)
                  ((primaryGenerator (selProduct J u))^4 * k))))) := by
  have hWP : (0:ℝ) < ∏ j ∈ J, s.P j := Finset.prod_pos (fun j _ => s.P_pos j)
  set tc' := CoupledFirst.tupleCoefficient (residualInput s J)
    (markedSourceModifier A₁ A₂ Dc K F) R L w with htc'
  by_cases hz : tc' = 0
  · have hz0 : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
        (joinTuple J u w) = 0 := by
      rw [tuple_factor_masked s J A₁ A₂ Dc K R L F u w hL hF hCol, ← htc', hz]
      ring
    rw [hz0, hz]
    simp only [zero_mul, mul_zero, Finset.sum_const_zero]
  · have hfree : Supported (finiteTupleProduct w) →
        SexticSieve.PowerFree 5 (finiteTupleProduct w) :=
      fun _ => residual_power_free s J A₁ A₂ Dc K R L F w hz
    have hrow := row_rays_fourth (selProduct J u) (finiteTupleProduct w) hfree k
    rw [tuple_factor_masked s J A₁ A₂ Dc K R L F u w hL hF hCol, finiteTupleProduct_join,
      map_mul, sqrt_split T _ hWP, ← htc']
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

/-- **The transfer identity (T)** at Collet's first MAIN layer, under (S), the
`F`-invariance and (Col). -/
theorem transfer_identity (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ)
    (hS : ∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L)
    (hF : ∀ v ∈ Fintype.piFinset s.pools,
      F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v)))
    (hCol : ∀ v ∈ Fintype.piFinset s.pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
        IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)))
    (k : O) :
    originalPolynomial s A₁ A₂ Dc K R L F τ t T k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R L F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k) := by
  rw [original_tuple_form, box_sum]
  have hterm : ∀ u ∈ selBox s J, ∀ w ∈ Fintype.piFinset (residualInput s J).pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) *
        (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct (joinTuple J u w))) *
          primaryGaussRow (finiteTupleProduct (joinTuple J u w)) k) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (selScalar s J K R τ t u χ k *
          (CoupledFirst.tupleCoefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R L w *
            ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
              (rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct w) *
                rayCharacter ξ (primaryGenerator (finiteTupleProduct w)) *
                primaryGaussRow (finiteTupleProduct w)
                  ((primaryGenerator (selProduct J u))^4 * k))))) := by
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
    apply term_identity s J A₁ A₂ Dc K R L F τ t T u w (seed_coprime s J L hS u hu)
    · have h := hF _ hv
      rwa [restPart_join] at h
    · intro hne
      have h := hCol _ hv hne
      rwa [sel_prod_join] at h
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw => hterm u hu w hw))]
  -- exchange the four sums
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

end
end QRH.MixedStep.Transfer
