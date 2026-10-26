/- Mixed source step, L2 transfer: the identity (T) without (S).

With a squarefree seed `L`, the residual polynomial of each selected
assignment `u` carries the residual seed `residualSeed J L u = L/gcd(L,D_u)`:

  G(k) = Σ_{χ,ξ} π_{χξ} Σ_{u} α_χ(u,k) · G'_{ξ, L/gcd(L,D_u)}(d(u)⁴ k). -/
import Submissions.arvi_mixed_step.Transfer.Identity
import Submissions.arvi_mixed_step.Transfer.SupplierFactor

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

/-- One term of the original tuple sum, given any exact factorization with a
residual seed `L'`. -/
theorem term_identity_of_factor (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L L' : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (u : J → Ideal O)
    (w : Tuple {i // i ∉ J})
    (hfac : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
        (joinTuple J u w) =
      selWeight s J K R u *
        CoupledFirst.tupleCoefficient (residualInput s J)
          (markedSourceModifier A₁ A₂ Dc K F) R L' w *
        (if IsCoprime (selProduct J u) (finiteTupleProduct w) then 1 else 0))
    (k : O) :
    CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) *
        (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct (joinTuple J u w))) *
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
  · have hz0 : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
        (joinTuple J u w) = 0 := by
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

/-- **The transfer identity (T) without (S)**: squarefree seed, residual seeds
`L/gcd(L, D_u)`, under the `F`-invariance and (Col). -/
theorem transfer_identity_supplier (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O)
    (F : Ideal O → ℂ) (τ : HeckeFamily.Character) (t T : ℝ) (hLsq : Squarefree L)
    (hF : ∀ v ∈ Fintype.piFinset s.pools,
      F (Dc * finiteTupleProduct v) = F (Dc * finiteTupleProduct (restPart J v)))
    (hCol : ∀ v ∈ Fintype.piFinset s.pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 →
        IsCoprime (∏ j ∈ J, v (Sum.inl j)) (v (Sum.inr 0) * v (Sum.inr 1)))
    (k : O) :
    originalPolynomial s A₁ A₂ Dc K R L F τ t T k =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        ∑ u ∈ selBox s J, selScalar s J K R τ t u χ k *
          residualPolynomial s J A₁ A₂ Dc K R (residualSeed J L u) F τ t T ξ
            ((primaryGenerator (selProduct J u))^4 * k) := by
  rw [original_tuple_form, box_sum]
  have hterm : ∀ u ∈ selBox s J, ∀ w ∈ Fintype.piFinset (residualInput s J).pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L (joinTuple J u w) *
        (((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t (finiteTupleProduct (joinTuple J u w))) *
          primaryGaussRow (finiteTupleProduct (joinTuple J u w)) k) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (selScalar s J K R τ t u χ k *
          (CoupledFirst.tupleCoefficient (residualInput s J) (markedSourceModifier A₁ A₂ Dc K F) R
              (residualSeed J L u) w *
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
    have hFv : F (Dc * finiteTupleProduct (joinTuple J u w)) = F (Dc * finiteTupleProduct w) := by
      have h := hF _ hv
      rwa [restPart_join] at h
    have hColv : CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L
        (joinTuple J u w) ≠ 0 → IsCoprime (selProduct J u) (w (Sum.inr 0) * w (Sum.inr 1)) := by
      intro hne
      have h := hCol _ hv hne
      rwa [sel_prod_join] at h
    exact term_identity_of_factor s J A₁ A₂ Dc K R L (residualSeed J L u) F τ t T u w
      (tuple_factor_masked_supplier s J A₁ A₂ Dc K R L F hLsq u hu w hFv hColv) k
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw => hterm u hu w hw))]
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
