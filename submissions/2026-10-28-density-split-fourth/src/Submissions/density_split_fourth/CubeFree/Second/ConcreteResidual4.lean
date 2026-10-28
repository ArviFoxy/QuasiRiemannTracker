/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M (a), part 4: the D⁴ transfer of one selected assignment onto the residual source.

`residual_transfer`: for a supported selected product `D` and a squarefree seed `u'` coprime
to `D`,
  `∑_{I ∈ rest} c^{rest}_{u'}(I) [(D, I) = 1] h_τ(I) g(D I; k)
     = ∑_{χ,ξ} c(χ,ξ) · χ(D) g(D; k) · P^{rest}_{u', childCharacter τ ξ}(D⁴ k)`,
where `P^{rest}_{u',ψ}` is the Gauss polynomial of `restSource` with seed `u'` and character
`ψ` (the residual ray character `ξ` is absorbed into `childCharacter τ ξ`, whose modulus is
`τ.modulus ⊓ (12)`). Combined with `selected_expansion` this is the f = 1 replacement of FP's
supplier lane (`selected_transfer_expansion`). -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteResidual3
import Submissions.density_split_fourth.CubeFree.FP.MixedSelectedCommon
import Submissions.density_split_fourth.CubeFree.FP.MixedFirstAveragedWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondChildProfile

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSourceEnergy CenteredMomentLiveDomain CenteredMomentChildRows
open CenteredMomentFirstColumns RayFourExpansion
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedOriginalSecondZero
open MixedTupleRows MixedFirstLiveSource MixedRestrictedDictionary MixedSelectedCommon
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The seed mask of any source coefficient. -/
theorem sourceCoefficient_seed (s : Source ι a b) (ha : 0 < a) (u I : Id) :
    sourceCoefficient s ha u I = if u ∣ I then sourceCoefficient s ha 1 I else 0 :=
  column_seed_mask (Fintype.piFinset (tuplePools s)) (punctureProduct s.S s.H) s.R u I s.ν s.Wslot
    s.P (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d

theorem seedRest_coprime (u D : Id) : IsCoprime (seedRest u D) D := by
  unfold seedRest
  rw [IsCoprime.prod_left_iff]
  intro P hP
  obtain ⟨hPu, hDP⟩ := Finset.mem_filter.mp hP
  have hpr := IdealMobiusDivisorSum.support_prime hPu
  rw [prime_coprime ⟨P, hpr⟩ D]
  intro h
  exact hDP (Ideal.le_of_dvd h)

theorem primaryGaussRow_supported (I : Id) (hI : Supported I) (k : O) :
    primaryGaussRow I k = idealGauss I hI k := by
  rw [primaryGaussRow, dif_pos hI]
  rfl

theorem heightCoeff_child (τ : Character) (ξ : RayCharacter) (t : ℝ) (I : Id) (hI : Supported I) :
    heightCoeff (childCharacter τ ξ) t I =
      heightCoeff τ t I * rayCharacter ξ (primaryGenerator I) := by
  unfold heightCoeff
  rw [CenteredMomentSecondChildProfile.child_ideal_primary τ ξ I hI]
  ring

/-- **The D⁴ transfer onto the residual source.** -/
theorem residual_transfer (r : Source ι a b) (ha : 0 < a) (u D : Id) (hD : Supported D)
    (hu : IsCoprime u D) (τ : Character) (t : ℝ) (k : O) :
    (∑ I ∈ sourceColumns r, sourceCoefficient r ha u I *
        ((if IsCoprime D I then 1 else 0) * heightCoeff τ t I * primaryGaussRow (D * I) k)) =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ *
        (rayCharacter χ (primaryGenerator D) * idealGauss D hD k) *
          gaussPolynomial Finset.univ (sourceGenerator (sourceColumns r))
            (sourceGenerator_supported (sourceColumns r))
            (fun I : supportedColumns (sourceColumns r) =>
              sourceCoefficient r ha u I * heightCoeff (childCharacter τ ξ) t I)
            ((primaryGenerator D)^4 * k) := by
  have hn : ∀ v : supportedColumns (sourceColumns r), Supported (v : Id) :=
    fun v => (Finset.mem_filter.mp v.property).2
  have h := ideal_seeded_selected_row_fourth (Finset.univ : Finset (supportedColumns (sourceColumns r)))
    (fun v => (v : Id)) hn 1 (fun v => sourceCoefficient r ha 1 v * heightCoeff τ t v) 1 u D
    one_ne_zero hD hu (by
      intro v _ hb
      have hc : sourceCoefficient r ha u v ≠ 0 := by
        rw [sourceCoefficient_seed]
        intro hz
        apply hb
        by_cases hs : u ∣ (v : Id)
        · rw [if_pos hs] at hz ⊢
          rw [hz, zero_mul]
        · rw [if_neg hs]
      exact MixedFirstAveragedWindow.source_fifth_free r ha u v hc) k
  -- the left side as a sum over supported columns
  have hL : (∑ I ∈ sourceColumns r, sourceCoefficient r ha u I *
        ((if IsCoprime D I then 1 else 0) * heightCoeff τ t I * primaryGaussRow (D * I) k)) =
      ∑ v : supportedColumns (sourceColumns r),
        (if 1 * u ∣ 1 * D * (v : Id) then 1 * (sourceCoefficient r ha 1 v * heightCoeff τ t v) else 0) *
          (if IsCoprime D (v : Id) then
            idealGauss (D * v) ((supported_mul_iff D v).mpr ⟨hD, hn v⟩) k else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not (sourceColumns r) Supported]
    have hzero : (∑ I ∈ (sourceColumns r).filter (fun I => ¬ Supported I),
        sourceCoefficient r ha u I *
          ((if IsCoprime D I then 1 else 0) * heightCoeff τ t I * primaryGaussRow (D * I) k)) = 0 := by
      apply Finset.sum_eq_zero
      intro I hI
      have hns : ¬ Supported (D * I) := by
        intro hs
        exact (Finset.mem_filter.mp hI).2 ((supported_mul_iff D I).mp hs).2
      rw [primaryGaussRow, dif_neg hns, mul_zero, mul_zero]
    rw [hzero, add_zero]
    change (∑ I ∈ supportedColumns (sourceColumns r), _) = _
    rw [← Finset.sum_coe_sort (supportedColumns (sourceColumns r))]
    apply Finset.sum_congr rfl
    intro v _
    rw [surviving_seed_iff 1 u D v one_ne_zero hu, sourceCoefficient_seed]
    by_cases hs : u ∣ (v : Id)
    · by_cases hc : IsCoprime D (v : Id)
      · rw [if_pos hs, if_pos hs, if_pos hc, if_pos hc,
          primaryGaussRow_supported _ ((supported_mul_iff D v).mpr ⟨hD, hn v⟩)]
        ring
      · rw [if_pos hs, if_pos hs, if_neg hc, if_neg hc]
        ring
    · rw [if_neg hs, if_neg hs]
      ring
  rw [hL, h]
  apply Finset.sum_congr rfl; intro χ _
  apply Finset.sum_congr rfl; intro ξ _
  rw [one_mul]
  congr 1
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  unfold commonCoefficient
  beta_reduce
  rw [heightCoeff_child τ ξ t v (hn v), sourceCoefficient_seed r ha u]
  by_cases hs : u ∣ (v : Id)
  · simp only [hs, ite_true]; ring
  · simp only [hs, ite_false, zero_mul]

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
