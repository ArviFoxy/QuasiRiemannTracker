/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the corrected assembly with an allocation-dependent second-step frequency `Tsec_B`.

The residual Poisson split (`residual_poisson`) is per (allocation, ray), so its second-step
frequency may depend on the allocation `B`: `diagAvgT`/`labelAvgT` are `diagAvg`/`labelAvg` at
`Tsec B`. This is needed because the label rows of a residual must lie below its own Poisson
cutoff (`hdyad`), whose scale `vol_B²/Kc_B` varies with `B` by powers of `Z`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteAssemblyAvg

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson CenteredMomentCompleteCommon
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource RepairedFirstRawSides
open MixedOriginalTail MixedOriginalNormCap CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) instDecEqSubtypeAsmAvgT {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) :=
  Classical.decEq _

/-- `diagAvg` at the allocation-dependent second-step frequency `T B`. -/
def diagAvgT (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ)
    (B : actualAllocations (tuplePools s) G) (ξ : RayCharacter) : ℝ :=
  diagAvg s ha hb cover G J Us τ χ₀ Q m t K (T B) Z ξr W B ξ

/-- `labelAvg` at the allocation-dependent second-step frequency `T B`. -/
def labelAvgT (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ)
    (B : actualAllocations (tuplePools s) G) (ξ : RayCharacter) : ℝ :=
  labelAvg s ha hb cover G J τ χ₀ Q m t K (T B) Z ξr W B ξ

theorem side_decomposition_avgT (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (W M : actualAllocations (tuplePools s) G → ℝ)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ) (hK : 0 < K)
    (hW : WidthBound s hb cover G J W) (hM : MultBound s hb cover G J K W M) :
    (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K) ≤
      outerAvg s hb cover G J τ t M (diagAvgT s ha hb cover G J Us τ χ₀ Q m t K T Z ξr W) +
      outerAvg s hb cover G J τ t M (labelAvgT s ha hb cover G J τ χ₀ Q m t K T Z ξr W) := by
  rw [← outerAvg_add]
  refine (summed_raw_reduction_avg s ha hb cover opposite G hO hG hOG Us hUs J
    (fun B => Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us)
    (fun B => Vset_img _ _ _ Us) τ t K hK W M (fun B => (hW B).1) (fun B => (hW B).2)
    (fun B => (hM B).1) (fun B => (hM B).2)).trans ?_
  unfold outerAvg
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum; intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Atot_nonneg _ _ _ _) (mul_nonneg (by positivity) (hM B).1))
  apply Finset.sum_le_sum; intro χ _
  apply Finset.sum_le_sum; intro ξ _
  have hKc : 0 < 16 * K * W B^4 := by have := (hW B).1; positivity
  have h := residual_poisson (restOf s hb cover G B (J B)) ha
    (Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us)
    (Vset_squarefree _ _ _ Us) (Vset_div _ _ _ Us ha) (childCharacter τ ξ) χ₀ Q m t
    (16 * K * W B^4) (T B) Z ξr (sourceNormCap (restOf s hb cover G B (J B)).P b
      (restOf s hb cover G B (J B)).T (restOf s hb cover G B (J B)).d) hKc
    (rest_hH (restOf s hb cover G B (J B)) ha)
  refine h.trans (le_of_eq ?_)
  unfold diagAvgT labelAvgT diagAvg labelAvg
  ring

theorem balanced_side_of_parts_avgT (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (W M : actualAllocations (tuplePools s) G → ℝ)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (K : ℝ)
    (T : actualAllocations (tuplePools s) G → ℝ) (Z ξr : ℝ) (hK : 0 < K)
    (hW : WidthBound s hb cover G J W) (hM : MultBound s hb cover G J K W M)
    (Jd : ℕ) (Ed El : ℝ)
    (hdiag : ∀ v : ℝ, outerAvg s hb cover G J τ v M
      (diagAvgT s ha hb cover G J Us τ χ₀ Q m v K T Z ξr W) ≤ Ed * (1+‖v‖)^(2*Jd))
    (hlabel : ∀ v : ℝ, outerAvg s hb cover G J τ v M
      (labelAvgT s ha hb cover G J τ χ₀ Q m v K T Z ξr W) ≤ El * (1+‖v‖)^(2*Jd)) :
    ∀ v : ℝ, (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ v K) ≤ (Ed + El) * (1+‖v‖)^(2*Jd) := by
  intro v
  refine (side_decomposition_avgT s ha hb cover opposite G hO hG hOG Us hUs J W M τ χ₀ Q m v
    K T Z ξr hK hW hM).trans ?_
  rw [add_mul]
  exact add_le_add (hdiag v) (hlabel v)

/-- **The balanced Seam 0 skeleton with allocation-dependent second-step frequencies.** -/
theorem balanced_summed_raw_side_bounds_avgT (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport D)
    (E : Finset (CommonIndex C D)) (KL KR A Z loss : ℝ) (hKL : 0 < KL) (hKR : 0 < KR) (Jd : ℕ)
    (JL : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val))
    (JR : (B : actualAllocations (tuplePools s) D) → Finset (liveIndices B.val))
    (WL ML : actualAllocations (tuplePools s) C → ℝ) (WR MR : actualAllocations (tuplePools s) D → ℝ)
    (hWL : WidthBound s hb cover C JL WL) (hML : MultBound s hb cover C JL KL WL ML)
    (hWR : WidthBound s hb cover D JR WR) (hMR : MultBound s hb cover D JR KR WR MR)
    (χ₀ : RayCharacter) (Q : Id) (m : O)
    (TL : actualAllocations (tuplePools s) C → ℝ) (TR : actualAllocations (tuplePools s) D → ℝ)
    (Zs ξr : ℝ)
    (EdL ElL EdR ElR : RayCharacter → RayCharacter → ℝ)
    (hdiagL : ∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (diagAvgT s ha hb cover C JL (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).left
        χ₀ Q m v KL TL Zs ξr WL) ≤ EdL χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelL : ∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (labelAvgT s ha hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left χ₀ Q m v KL TL Zs ξr WL)
        ≤ ElL χ ξ * (1+‖v‖)^(2*Jd))
    (hdiagR : ∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (diagAvgT s ha hb cover D JR (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).right
        χ₀ Q m v KR TR Zs ξr WR) ≤ EdR χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelR : ∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (labelAvgT s ha hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right χ₀ Q m v KR TR Zs ξr WR)
        ≤ ElR χ ξ * (1+‖v‖)^(2*Jd))
    (hbudL : ∀ χ ξ, EdL χ ξ + ElL χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)
    (hbudR : ∀ χ ξ, EdR χ ξ + ElR χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss) :
    BalancedSummedRawSideBounds s ha η C D hC hD E KL KR A Z loss Jd := by
  intro χ ξ
  have hp : ∀ v : ℝ, 0 ≤ (1+‖v‖)^(2*Jd) := fun v => by positivity
  refine ⟨fun v => ?_, fun v => ?_⟩
  · refine (balanced_side_of_parts_avgT s ha hb cover D C hD hC hCD.symm
      (concreteArtificial s C D hD.1) (concreteArtificial_squarefree s C D hD.1) JL WL ML
      _ χ₀ Q m KL TL Zs ξr hKL hWL hML Jd (EdL χ ξ) (ElL χ ξ) (hdiagL χ ξ) (hlabelL χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudL χ ξ) (hp v)
  · refine (balanced_side_of_parts_avgT s ha hb cover C D hC hD hCD
      (concreteArtificial s C D hD.1) (concreteArtificial_squarefree s C D hD.1) JR WR MR
      _ χ₀ Q m KR TR Zs ξr hKR hWR hMR Jd (EdR χ ξ) (ElR χ ξ) (hdiagR χ ξ) (hlabelR χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudR χ ξ) (hp v)

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete

