/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1 (htotal), part 3: the decomposition of the u'-summed residual energy consumed by
the window step.

`residual_poisson`: for a source `r`, a finite set `V` of squarefree seeds containing every
squarefree divisor of every common label of the (unmasked) active source `S0`, at Gauss scale
`K` (WP-J: `K = 16·K₀·W⁴`):
  `∑_{v∈V} E_v ≤ Z0 + Zf + Zt + ∑_{p : labels S0} ρ(p.1) ∑_U ∑_n ‖B_{p,U,n}‖`,
* `Z0 = ∑_v ‖K·Ŵ(0)·sourceSecondZero(β_v)‖` (WP-J `residual_second_zero`, `= W·‖zeroDensity‖`),
* `Zf = ∑_v ‖partEnergy true (β_v)‖` (WP-J `residual_fixed_inducing`),
* `Zt = ∑_v ‖secondDiscardedEnergy (β_v)‖` (WP-J `original_tail_arbitrary_saving`),
* `B_{p,U,n}` the nonfixed physical block of the UNMASKED coefficient, which is
  `outerScalar·normalizer·labelBlock` (`nonfixed_block_eq`): the input of `grouped_label_blocks`.
Here `β_v = sourceCoefficient r v` (seed `v`), `β = sourceCoefficient r 1`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteTotalPoisson
import Submissions.density_split_fourth.CubeFree.Second.ConcreteLabel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedEnergy RayFourExpansion
open CenteredMomentSecondWholeKernel CenteredMomentSecondLocalization CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The unmasked active residual source. -/
def S0 (r : Source ι a b) (ha : 0 < a) : Finset Id :=
  activeSource (sourceColumns r) (sourceCoefficient r ha 1)

theorem seed_fun (r : Source ι a b) (ha : 0 < a) (v : Id) :
    sourceCoefficient r ha v = fun I => if v ∣ I then sourceCoefficient r ha 1 I else 0 :=
  funext (sourceCoefficient_seed r ha v)

theorem active_seed_subset (r : Source ι a b) (ha : 0 < a) (v : Id) :
    activeSource (sourceColumns r) (sourceCoefficient r ha v) ⊆ S0 r ha := by
  intro I hI
  rw [mem_activeSource] at hI
  unfold S0
  rw [mem_activeSource]
  refine ⟨hI.1, fun h0 => hI.2 ?_⟩
  rw [sourceCoefficient_seed, h0, ite_self]

theorem active_seed_zero (r : Source ι a b) (ha : 0 < a) (v : Id) :
    ∀ I ∈ S0 r ha, I ∉ activeSource (sourceColumns r) (sourceCoefficient r ha v) →
      sourceCoefficient r ha v I = 0 := by
  intro I hI hn
  unfold S0 at hI
  rw [mem_activeSource] at hI hn
  by_contra h
  exact hn ⟨hI.1, h⟩

/-- **The u'-summed nonfixed part regroups.** -/
theorem nonfixed_regroup (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (hV : ∀ v ∈ V, Squarefree v)
    (hVdiv : ∀ q ∈ commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
      ∀ u, Squarefree u → u ∣ q.1 → u ∈ V)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t : ℝ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) :
    (∑ v ∈ V, partEnergy false ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
        W K Tsec Z ξ H) =
      ∑ p : commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)), rhoC p.val.1 *
        (heightCoeff ψ t p.val.1 * star (heightCoeff ψ t p.val.2) *
        ∑ U : Finset (CommonIndex p.val.1 p.val.2),
          ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock ψ t (S0 r ha) (sourceCoefficient r ha 1) p.val.1 p.val.2
              (commonLabels_supported (S0 r ha) _ _ p.property).1
              (commonLabels_supported (S0 r ha) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (partRows false ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
              W K (fun i => (n i : ℤ))) := by
  have h1 : ∀ v ∈ V, partEnergy false ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
      W K Tsec Z ξ H = labelSum false ψ χ₀ Q m t (S0 r ha)
        (fun I => if v ∣ I then sourceCoefficient r ha 1 I else 0) W K Tsec Z ξ H := by
    intro v _
    rw [partEnergy_eq_labelSum, labelSum_mono false ψ χ₀ Q m t (active_seed_subset r ha v)
      (sourceCoefficient r ha v) (active_seed_zero r ha v), seed_fun]
  rw [Finset.sum_congr rfl h1]
  exact labelSum_regroup false ψ χ₀ Q m t (S0 r ha) (sourceCoefficient r ha 1) W K Tsec Z ξ H V
    hV hVdiv

/-- **The residual Poisson decomposition.** -/
theorem residual_poisson (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (hV : ∀ v ∈ V, Squarefree v)
    (hVdiv : ∀ q ∈ commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
      ∀ u, Squarefree u → u ∣ q.1 → u ∈ V)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ v ∈ V, Qenergy r ha v ψ t K) ≤
      (∑ v ∈ V, ‖((K:ℂ) * paperRadialFourier ballProfile 0) *
          sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t‖) +
      (∑ v ∈ V, ‖partEnergy true ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
          ballProfile K Tsec Z ξ H‖) +
      (∑ v ∈ V, ‖secondDiscardedEnergy ψ t (sourceColumns r) (sourceCoefficient r ha v)
          ballProfile K Tsec Z ξ‖) +
      ∑ p : commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
        ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
          ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            ‖physicalBlock ψ t (S0 r ha) (sourceCoefficient r ha 1) p.val.1 p.val.2
              (commonLabels_supported (S0 r ha) _ _ p.property).1
              (commonLabels_supported (S0 r ha) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (partRows false ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
              ballProfile K (fun i => (n i : ℤ))‖ := by
  have hper : ∀ v ∈ V, Qenergy r ha v ψ t K ≤
      ‖((K:ℂ) * paperRadialFourier ballProfile 0) *
          sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t‖ +
        ‖partEnergy true ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
          ballProfile K Tsec Z ξ H‖ +
        ‖secondDiscardedEnergy ψ t (sourceColumns r) (sourceCoefficient r ha v)
          ballProfile K Tsec Z ξ‖ +
        (partEnergy false ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
          ballProfile K Tsec Z ξ H).re := by
    intro v _
    have hH' : ∀ I ∈ sourceColumns r, sourceCoefficient r ha v I ≠ 0 →
        (Ideal.absNorm I : ℝ) ≤ H := by
      intro I hI hv
      apply hH I hI
      intro h0
      apply hv
      rw [sourceCoefficient_seed, h0, ite_self]
    have hloc := sourceGaussEnergy_localized ψ t (sourceColumns r) (sourceCoefficient r ha v)
      ballProfile K Tsec Z ξ hK
    rw [original_energy_split ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v) ballProfile
      K Tsec Z ξ H hK hH'] at hloc
    have hq : Qenergy r ha v ψ t K = (CenteredMomentOriginalChildEnergy.sourceGaussEnergy
        (sourceColumns r) (sourceCoefficient r ha v) (heightCoeff ψ t) ballProfile K).re := rfl
    rw [hq, hloc]
    simp only [Complex.add_re]
    have h1 := Complex.re_le_norm (((K:ℂ) * paperRadialFourier ballProfile 0) *
      sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t)
    have h2 := Complex.re_le_norm (partEnergy true ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile K Tsec Z ξ H)
    have h3 := Complex.re_le_norm (secondDiscardedEnergy ψ t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile K Tsec Z ξ)
    linarith
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rw [← Complex.re_sum, nonfixed_regroup r ha V hV hVdiv ψ χ₀ Q m t ballProfile K Tsec Z ξ H]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_))
  have hdata := commonLabels_data _ _ p.val.1 p.val.2 p.property
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hc := common_height_norm_le_one ψ t _ _ hdata.1 hdata.2.1
  refine (mul_le_of_le_one_left (norm_nonneg _) hc).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun U _ => ?_)
  exact norm_sum_le _ _

/-- **The nonfixed block in label form** (input of `grouped_label_blocks`). -/
theorem nonfixed_block_eq (η : Character) (t : ℝ) (S : Finset Id) (β : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (χ₀ : RayCharacter) (Q : Id) (m : O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ) :
    ‖physicalBlock η t S β C D hC hD U R (partRows false η χ₀ Q m C D U R) W K n‖ =
      outerScalar C D K n * normalizer C D U *
        ‖labelBlock η t S β C D hC hD U R (partRows false η χ₀ Q m C D U R) W
          (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
          (fun _ => Real.log (secondEffectiveScale C D
            (commonFrequencyGenerator C D * nonunitFrequencyGenerator C D U) K / dyadicScale (n 0)))
          (fun z => Real.log (normValue z / dyadicScale (n 1)))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ := by
  have hrows : ∀ z ∈ partRows false η χ₀ Q m C D U R, z ≠ 0 := by
    intro z hz
    rw [partRows_false] at hz
    exact sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1
  rw [physicalBlock_eq η t S β C D hC hD U R _ hrows W K hK n, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real]
  have h1 : 0 ≤ outerScalar C D K n := by unfold outerScalar; positivity
  have h2 : 0 < normalizer C D U := normalizer_pos C D hC U
  rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2.le]
  rfl

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
