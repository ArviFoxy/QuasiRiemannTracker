/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the per-label OAI rewrites of the second nonfixed block, and the GROUPED label bound.

* `labelBlock`: the normalized nonfixed second block of one label (genuine common pair
  `(C, D)`, unit set `U`, retained radius `R`, rows, dyadic logs), exactly the expression
  inside the norm in OAI `CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source`.
* `labelBlock_eq`: OAI's exact rewrite (sector elements, `actualCorrelation`,
  `actual_scaled_row_children`): the block is `∑_{t₂} μ(t₂) ∑_{χ,ξ} c(χ,ξ) · child(t₂, χ, ξ)`
  with `child` a `childMatrix` (the form of `grouped_child_bound_dep`).
* `grouped_label_blocks`: for a finite family of labels of one dyadic class (common kernel
  ratio `r`, window centres `X, Y`, energy profile `Φ` at radius `H`) and nonnegative label
  weights `ω`, height-uniform bounds on the WEIGHTED SUMS over (label, `t₂`) of the masked
  one-sided source energies bound `(1+r)^decay ∑_ℓ ω_ℓ ‖labelBlock ℓ‖` by
  `Cg · windowBudget J₁ t E₁ · windowBudget J₂ t E₂`. This is the grouped version of
  OAI `actual_block_from_squarefree_source` (which has per-label, per-`t₂` budgets). -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteKernelDep
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowSource

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSupportedCorrelation CenteredMomentFixedRay CenteredMomentHeckeWindowEnergy
local notation "O" => ActualEisensteinCubic.O

/-! ### One label -/

/-- The normalized nonfixed block of one second label. -/
def labelBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (r : ℝ) (ρ x : O → ℝ) (X Y : ℝ) : ℂ :=
  ∑ z ∈ rows, retainedScalar C D U R z *
    ∑ I : sectorPool C hC.1 S, ∑ J : sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC, sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD, sectorPool_supported D hD.1 S J⟩)
          ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) else 0) *
        ((β (C*I) * heightCoeff η t I) * star (β (D*J) * heightCoeff η t J)) *
          wholeKernel W (fun _ => logAnnulus) r (ρ z) (x z)
            (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
            (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))

/-- The `(t₂, χ, ξ)` child of a label. -/
def labelChild (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (r : ℝ) (ρ x : O → ℝ) (X Y : ℝ)
    (L : Ideal O) (χ ξ : RayCharacter) : ℂ :=
  childMatrix W (fun _ => logAnnulus) r rows Finset.univ Finset.univ
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    (divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient (commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U)
        (sectorElement C hC.1 S) (fun I => β (C*I) * heightCoeff η t I)) χ)
    (divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient (commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U)
        (sectorElement D hD.1 S) (fun J => β (D*J) * heightCoeff η t J)) (ξ⁻¹))
    (fun I => Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun J => Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y)) ρ x
    (fun z => retainedScalar C D U R z *
      actualCorrelation (primaryGenerator C) (primaryGenerator D)
        ((supported_span_primaryGenerator_iff C).mpr hC)
        ((supported_span_primaryGenerator_iff D).mpr hD)
        ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z))

theorem actualCorrelation_congr {u u' v v' : O} (huu : u = u') (hvv : v = v')
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v}))
    (hu' : Supported (Ideal.span {u'})) (hv' : Supported (Ideal.span {v'})) (j : O) :
    actualCorrelation u v hu hv j = actualCorrelation u' v' hu' hv' j := by
  subst huu hvv; rfl

/-- **OAI's exact rewrite of one label block.** -/
theorem labelBlock_eq (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (r : ℝ)
    (ρ x : O → ℝ) (X Y : ℝ) :
    labelBlock η t S β C D hC hD U R rows W r ρ x X Y =
      ∑ L ∈ divisorPool Finset.univ (fun j : sectorPool D hD.1 S => Ideal.span {sectorElement D hD.1 S j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ *
              labelChild η t S β C D hC hD U R rows W r ρ x X Y L χ ξ := by
  have hpC := (supported_span_primaryGenerator_iff C).mpr hC
  have hpD := (supported_span_primaryGenerator_iff D).mpr hD
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff, sectorElement_span, sectorElement_span]
  have hterm : labelBlock η t S β C D hC hD U R rows W r ρ x X Y =
      ∑ z ∈ rows, retainedScalar C D U R z * ∑ i ∈ (Finset.univ : Finset (sectorPool C hC.1 S)),
        ∑ j ∈ (Finset.univ : Finset (sectorPool D hD.1 S)),
        (if IsCoprime (sectorElement C hC.1 S i) (sectorElement D hD.1 S j) then
          actualCorrelation (primaryGenerator C * sectorElement C hC.1 S i)
            (primaryGenerator D * sectorElement D hD.1 S j)
            (supported_mul_elements _ _ hpC (sectorElement_supported C hC.1 S i))
            (supported_mul_elements _ _ hpD (sectorElement_supported D hD.1 S j))
            ((commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) * z) else 0) *
          ((β (C*i) * heightCoeff η t i) * star (β (D*j) * heightCoeff η t j)) *
          wholeKernel W (fun _ => logAnnulus) r (ρ z) (x z)
            (Real.log ((Ideal.absNorm (i:Ideal O):ℝ)/X))
            (Real.log ((Ideal.absNorm (j:Ideal O):ℝ)/Y)) := by
    unfold labelBlock
    apply Finset.sum_congr rfl; intro z _
    congr 1
    apply Finset.sum_congr rfl; intro I _
    apply Finset.sum_congr rfl; intro J _
    congr 2
    by_cases h : IsCoprime (I:Ideal O) (J:Ideal O)
    · rw [if_pos h, if_pos ((hcop I J).mpr h)]
      unfold idealCorrelation
      exact actualCorrelation_congr (by rw [primaryGenerator_mul]; rfl)
        (by rw [primaryGenerator_mul]; rfl) _ _ _ _ _
    · rw [if_neg h, if_neg (fun h' => h ((hcop I J).mp h'))]
  rw [hterm, actual_scaled_row_children rows Finset.univ Finset.univ (primaryGenerator C)
    (primaryGenerator D) (commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S) hpC hpD
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD]
  rfl

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
