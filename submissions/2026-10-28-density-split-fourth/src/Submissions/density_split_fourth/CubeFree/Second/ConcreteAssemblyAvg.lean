/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M assembly of the concrete Seam 0, CORRECTED normalization (supersedes `outerSum`,
`diagPart`, `labelPart`, `side_decomposition`, `balanced_side_of_parts`,
`balanced_summed_raw_side_bounds` of `ConcreteAssembly`, which lose a factor `#selY ≍ Z^u`).

* `outerAvg`: outer weights `#B·Σ_B ‖w_B‖²·Atot_B·2^{|J_B|}·M_B·Σ_χ Σ_ξ F B ξ`. There is no `Σ_y`:
  all selected assignments share the radius `16·K·W_B⁴` (`selWidth y ≤ W_B`) and their transferred
  rows are absorbed by the row multiplicity `M_B` (`summed_raw_reduction_avg`).
* `diagAvg`, `labelAvg`: `Z0 + Zf + Zt` and the regrouped nonfixed blocks of ONE residual per
  `(B, ξ)` at Gauss scale `16·K·W_B⁴` (the per-split `residual_poisson` is unchanged).
* `side_decomposition_avg`, `balanced_side_of_parts_avg`, `balanced_summed_raw_side_bounds_avg`. -/
import Submissions.density_split_fourth.CubeFree.Second.ConcreteAssembly
import Submissions.density_split_fourth.CubeFree.Second.ConcreteTotalMult

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
local instance (priority := 2000) instDecEqSubtypeAsmAvg {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) :=
  Classical.decEq _

/-- The selected-row multiplicity hypothesis of one allocation. -/
def MultBound (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (K : ℝ) (W M : actualAllocations (tuplePools s) G → ℝ) : Prop :=
  ∀ B, 0 ≤ M B ∧ ∀ z : O, (z ≠ 0 ∨ J B = ∅) →
    ‖ConcreteTraceCRT.eisEmbedding z‖^2 ≤ 16 * K * W B^4 →
    (((selY (allocatedLiveSource s hb cover G B) (J B)).filter
      (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ) ≤ M B

/-- The common-width hypothesis of one allocation. -/
def WidthBound (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (W : actualAllocations (tuplePools s) G → ℝ) : Prop :=
  ∀ B, 0 < W B ∧ ∀ y ∈ selY (allocatedLiveSource s hb cover G B) (J B), selWidth y ≤ W B

/-- **The corrected outer weights** (no `Σ_y`). -/
def outerAvg (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (τ : Character)
    (t : ℝ) (M : actualAllocations (tuplePools s) G → ℝ)
    (F : actualAllocations (tuplePools s) G → RayCharacter → ℝ) : ℝ :=
  ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
    ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
      (Atot (allocatedLiveSource s hb cover G B) (J B) τ t *
        ((2:ℝ)^(Fintype.card (J B)) * M B) * ∑ _χ : RayCharacter, ∑ ξ : RayCharacter, F B ξ)

/-- **The diagonal part** `Z0 + Zf + Zt` of one (allocation, ray), at scale `16·K·W_B⁴`. -/
def diagAvg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ)
    (B : actualAllocations (tuplePools s) G) (ξ : RayCharacter) : ℝ :=
  let r := restOf s hb cover G B (J B)
  let Kc : ℝ := 16 * K * W B^4
  let V := Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us
  (∑ v ∈ V, ‖((Kc:ℂ) * paperRadialFourier ballProfile 0) *
      sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) (childCharacter τ ξ) t‖) +
  (∑ v ∈ V, ‖partEnergy true (childCharacter τ ξ) χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr (sourceNormCap r.P b r.T r.d)‖) +
  (∑ v ∈ V, ‖secondDiscardedEnergy (childCharacter τ ξ) t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr‖)

/-- **The label part** of one (allocation, ray), at scale `16·K·W_B⁴`. -/
def labelAvg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ)
    (B : actualAllocations (tuplePools s) G) (ξ : RayCharacter) : ℝ :=
  let r := restOf s hb cover G B (J B)
  let Kc : ℝ := 16 * K * W B^4
  ∑ p : commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
    ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U Kc (frequencyRadius Tsec Z ξr)
          (sourceNormCap r.P b r.T r.d),
        ‖physicalBlock (childCharacter τ ξ) t (S0 r ha) (sourceCoefficient r ha 1) p.val.1 p.val.2
          (commonLabels_supported (S0 r ha) _ _ p.property).1
          (commonLabels_supported (S0 r ha) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξr)
          (partRows false (childCharacter τ ξ) χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξr))
          ballProfile Kc (fun i => (n i : ℤ))‖

theorem outerAvg_add (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (τ : Character)
    (t : ℝ) (M : actualAllocations (tuplePools s) G → ℝ)
    (F₁ F₂ : actualAllocations (tuplePools s) G → RayCharacter → ℝ) :
    outerAvg s hb cover G J τ t M (fun B ξ => F₁ B ξ + F₂ B ξ) =
      outerAvg s hb cover G J τ t M F₁ + outerAvg s hb cover G J τ t M F₂ := by
  unfold outerAvg
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro B _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl; intro χ _
  rw [← Finset.sum_add_distrib]

/-- **The corrected side decomposition.** -/
theorem side_decomposition_avg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (W M : actualAllocations (tuplePools s) G → ℝ)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ) (hK : 0 < K)
    (hW : WidthBound s hb cover G J W) (hM : MultBound s hb cover G J K W M) :
    (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K) ≤
      outerAvg s hb cover G J τ t M (diagAvg s ha hb cover G J Us τ χ₀ Q m t K Tsec Z ξr W) +
      outerAvg s hb cover G J τ t M (labelAvg s ha hb cover G J τ χ₀ Q m t K Tsec Z ξr W) := by
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
    (16 * K * W B^4) Tsec Z ξr (sourceNormCap (restOf s hb cover G B (J B)).P b
      (restOf s hb cover G B (J B)).T (restOf s hb cover G B (J B)).d) hKc
    (rest_hH (restOf s hb cover G B (J B)) ha)
  refine h.trans (le_of_eq ?_)
  unfold diagAvg labelAvg
  ring

/-- One side of the balanced Seam 0 from the two corrected parts. -/
theorem balanced_side_of_parts_avg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (W M : actualAllocations (tuplePools s) G → ℝ)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (K Tsec Z ξr : ℝ) (hK : 0 < K)
    (hW : WidthBound s hb cover G J W) (hM : MultBound s hb cover G J K W M)
    (Jd : ℕ) (Ed El : ℝ)
    (hdiag : ∀ v : ℝ, outerAvg s hb cover G J τ v M
      (diagAvg s ha hb cover G J Us τ χ₀ Q m v K Tsec Z ξr W) ≤ Ed * (1+‖v‖)^(2*Jd))
    (hlabel : ∀ v : ℝ, outerAvg s hb cover G J τ v M
      (labelAvg s ha hb cover G J τ χ₀ Q m v K Tsec Z ξr W) ≤ El * (1+‖v‖)^(2*Jd)) :
    ∀ v : ℝ, (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ v K) ≤ (Ed + El) * (1+‖v‖)^(2*Jd) := by
  intro v
  refine (side_decomposition_avg s ha hb cover opposite G hO hG hOG Us hUs J W M τ χ₀ Q m v
    K Tsec Z ξr hK hW hM).trans ?_
  rw [add_mul]
  exact add_le_add (hdiag v) (hlabel v)

/-- **Corrected skeleton of `balanced_summed_raw_side_bounds`.** -/
theorem balanced_summed_raw_side_bounds_avg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport D)
    (E : Finset (CommonIndex C D)) (KL KR A Z loss : ℝ) (hKL : 0 < KL) (hKR : 0 < KR) (Jd : ℕ)
    (JL : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val))
    (JR : (B : actualAllocations (tuplePools s) D) → Finset (liveIndices B.val))
    (WL ML : actualAllocations (tuplePools s) C → ℝ) (WR MR : actualAllocations (tuplePools s) D → ℝ)
    (hWL : WidthBound s hb cover C JL WL) (hML : MultBound s hb cover C JL KL WL ML)
    (hWR : WidthBound s hb cover D JR WR) (hMR : MultBound s hb cover D JR KR WR MR)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (Tsec Zs ξr : ℝ)
    (EdL ElL EdR ElR : RayCharacter → RayCharacter → ℝ)
    (hdiagL : ∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (diagAvg s ha hb cover C JL (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).left
        χ₀ Q m v KL Tsec Zs ξr WL) ≤ EdL χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelL : ∀ χ ξ v, outerAvg s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v ML
      (labelAvg s ha hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left χ₀ Q m v KL Tsec Zs ξr WL)
        ≤ ElL χ ξ * (1+‖v‖)^(2*Jd))
    (hdiagR : ∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (diagAvg s ha hb cover D JR (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).right
        χ₀ Q m v KR Tsec Zs ξr WR) ≤ EdR χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelR : ∀ χ ξ v, outerAvg s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v MR
      (labelAvg s ha hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right χ₀ Q m v KR Tsec Zs ξr WR)
        ≤ ElR χ ξ * (1+‖v‖)^(2*Jd))
    (hbudL : ∀ χ ξ, EdL χ ξ + ElL χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)
    (hbudR : ∀ χ ξ, EdR χ ξ + ElR χ ξ ≤
      balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss) :
    BalancedSummedRawSideBounds s ha η C D hC hD E KL KR A Z loss Jd := by
  intro χ ξ
  have hp : ∀ v : ℝ, 0 ≤ (1+‖v‖)^(2*Jd) := fun v => by positivity
  refine ⟨fun v => ?_, fun v => ?_⟩
  · refine (balanced_side_of_parts_avg s ha hb cover D C hD hC hCD.symm
      (concreteArtificial s C D hD.1) (concreteArtificial_squarefree s C D hD.1) JL WL ML
      _ χ₀ Q m KL Tsec Zs ξr hKL hWL hML Jd (EdL χ ξ) (ElL χ ξ) (hdiagL χ ξ) (hlabelL χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudL χ ξ) (hp v)
  · refine (balanced_side_of_parts_avg s ha hb cover C D hC hD hCD
      (concreteArtificial s C D hD.1) (concreteArtificial_squarefree s C D hD.1) JR WR MR
      _ χ₀ Q m KR Tsec Zs ξr hKR hWR hMR Jd (EdR χ ξ) (ElR χ ξ) (hdiagR χ ξ) (hlabelR χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudR χ ξ) (hp v)

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
