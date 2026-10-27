/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M assembly of the concrete Seam 0 (parts independent of the frame/grouping of WP-M2).

* `Vset`: the residual seed set `= seedRest images ∪ squarefree divisors of residual columns`,
  with `Vset_squarefree`, `Vset_img`, `Vset_div` (the hypotheses of `summed_raw_reduction` and
  `residual_poisson`).
* `rest_hH`: the column-norm cap `H = sourceNormCap` (FP `original_coefficient_cap`).
* `outerSum`: the outer D-Cauchy weights `#B·Σ_B ‖w_B‖²·Atot_B·Σ_{y,χ,ξ} 2^{ω(D_y)}` of a family
  of per-(allocation, selected assignment, residual ray) quantities.
* `diagPart` (`Z0 + Zf + Zt`, WP-J's per-seed forms at Gauss scale `16·K·W_y⁴`, `W_y = selWidth y`)
  and `labelPart` (the regrouped nonfixed blocks, input of `grouped_label_blocks`).
* `side_decomposition`: `∑_{u ∈ Us} rawEnergy ≤ outerSum diagPart + outerSum labelPart`.
* `balanced_side_of_parts`, `balanced_summed_raw_side_bounds`: the skeleton of the final
  theorem: height-uniform bounds of `outerSum diagPart` and `outerSum labelPart` on both sides,
  summing to the balanced budget, give `BalancedSummedRawSideBounds`. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteTotalFirst
import Submissions.sil_density_split_20261026.CubeFree.Second.Concrete
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedOriginalTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.SilDensitySplit.CubeFree.Second.Concrete
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
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource RepairedFirstRawSides
open MixedOriginalTail MixedOriginalNormCap CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) :=
  Classical.decEq _

/-! ### (1) The residual seed set -/

/-- Squarefree divisors of the columns of a source. -/
def divSqfree (r : Source ι a b) : Finset Id :=
  (sourceColumns r).biUnion (fun I => (IdealMobiusDivisorSum.idealDivisors I).filter Squarefree)

/-- The residual seed set of a selected block. -/
def Vset (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (Us : Finset Id) : Finset Id :=
  (Us ×ˢ selY s J).image (fun p => seedRest p.1 (∏ j, p.2 j)) ∪ divSqfree (restSource s hB1 J)

theorem Vset_squarefree (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (Us : Finset Id) :
    ∀ v ∈ Vset s hB1 J Us, Squarefree v := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    exact seedRest_squarefree _ _
  · obtain ⟨I, _, hI⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp hI).2

theorem Vset_img (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (Us : Finset Id) :
    ∀ u ∈ Us, ∀ y ∈ selY s J, seedRest u (∏ j, y j) ∈ Vset s hB1 J Us := by
  intro u hu y hy
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, y), Finset.mem_product.mpr ⟨hu, hy⟩, rfl⟩)

theorem Vset_div (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (Us : Finset Id)
    (ha : 0 < a) :
    ∀ q ∈ commonLabels (supportedColumns (S0 (restSource s hB1 J) ha))
        (supportedColumns (S0 (restSource s hB1 J) ha)),
      ∀ u, Squarefree u → u ∣ q.1 → u ∈ Vset s hB1 J Us := by
  intro q hq u hu hdvd
  apply Finset.mem_union_right
  unfold commonLabels at hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hp1 : p.1 ∈ supportedColumns (S0 (restSource s hB1 J) ha) := (Finset.mem_product.mp hp).1
  have hsupp := (Finset.mem_filter.mp hp1).2
  have hmem := (Finset.mem_filter.mp hp1).1
  unfold S0 at hmem
  rw [mem_activeSource] at hmem
  apply Finset.mem_biUnion.mpr
  refine ⟨p.1, hmem.1, Finset.mem_filter.mpr ⟨?_, hu⟩⟩
  rw [IdealMobiusDivisorSum.mem_idealDivisors hsupp.1]
  exact hdvd.trans (commonPart_dvd p.1 p.2 hsupp.1)

/-! ### (2) The column-norm cap -/

theorem rest_hH (r : Source ι a b) (ha : 0 < a) :
    ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 →
      (Ideal.absNorm I : ℝ) ≤ sourceNormCap r.P b r.T r.d :=
  fun I _ hi => (original_coefficient_cap r ha 1 I hi).2

/-! ### (3) The outer weights, the diagonal part and the label part -/

/-- The outer D-Cauchy weights. -/
def outerSum (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (τ : Character)
    (t : ℝ)
    (F : (B : actualAllocations (tuplePools s) G) → (J B → Id) → RayCharacter → ℝ) : ℝ :=
  ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
    ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
      (Atot (allocatedLiveSource s hb cover G B) (J B) τ t *
        ∑ y ∈ selY (allocatedLiveSource s hb cover G B) (J B), ∑ χ : RayCharacter,
          ∑ ξ : RayCharacter, 2^(IdealMobiusDivisorSum.primeSupport (∏ j, y j)).card * F B y ξ)

/-- The residual of an allocation and a selected block. -/
abbrev restOf (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :=
  restSource (allocatedLiveSource s hb cover G B) (fun _ => rfl) J

/-- **The diagonal part** `Z0 + Zf + Zt` of one (allocation, selected assignment, ray). -/
def diagPart (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (B : actualAllocations (tuplePools s) G) (y : J B → Id) (ξ : RayCharacter) : ℝ :=
  let r := restOf s hb cover G B (J B)
  let Kc : ℝ := 16 * K * selWidth y^4
  let V := Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us
  (∑ v ∈ V, ‖((Kc:ℂ) * paperRadialFourier ballProfile 0) *
      sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) (childCharacter τ ξ) t‖) +
  (∑ v ∈ V, ‖partEnergy true (childCharacter τ ξ) χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr (sourceNormCap r.P b r.T r.d)‖) +
  (∑ v ∈ V, ‖secondDiscardedEnergy (childCharacter τ ξ) t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile Kc Tsec Z ξr‖)

/-- **The label part** (regrouped nonfixed blocks of the unmasked residual). -/
def labelPart (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (B : actualAllocations (tuplePools s) G) (y : J B → Id) (ξ : RayCharacter) : ℝ :=
  let r := restOf s hb cover G B (J B)
  let Kc : ℝ := 16 * K * selWidth y^4
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

theorem outerSum_add (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (τ : Character)
    (t : ℝ) (F₁ F₂ : (B : actualAllocations (tuplePools s) G) → (J B → Id) → RayCharacter → ℝ) :
    outerSum s hb cover G J τ t (fun B y ξ => F₁ B y ξ + F₂ B y ξ) =
      outerSum s hb cover G J τ t F₁ + outerSum s hb cover G J τ t F₂ := by
  unfold outerSum
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro B _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl; intro y _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro χ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ξ _
  ring

theorem Atot_nonneg (s : Source ι a b) (J : Finset ι) (τ : Character) (t : ℝ) :
    0 ≤ Atot s J τ t := by unfold Atot; positivity

/-- **The side decomposition.** -/
theorem side_decomposition (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ) (hK : 0 < K) :
    (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K) ≤
      outerSum s hb cover G J τ t (diagPart s ha hb cover G J Us τ χ₀ Q m t K Tsec Z ξr) +
      outerSum s hb cover G J τ t (labelPart s ha hb cover G J τ χ₀ Q m t K Tsec Z ξr) := by
  rw [← outerSum_add]
  refine (summed_raw_reduction s ha hb cover opposite G hO hG hOG Us hUs J
    (fun B => Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us)
    (fun B => Vset_img _ _ _ Us) τ t K hK).trans ?_
  unfold outerSum
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum; intro B _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Atot_nonneg _ _ _ _)
  apply Finset.sum_le_sum; intro y hy
  apply Finset.sum_le_sum; intro χ _
  apply Finset.sum_le_sum; intro ξ _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hKc : 0 < 16 * K * selWidth y^4 := by
    have := selWidth_pos _ _ y hy; positivity
  have h := residual_poisson (restOf s hb cover G B (J B)) ha
    (Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) Us)
    (Vset_squarefree _ _ _ Us) (Vset_div _ _ _ Us ha) (childCharacter τ ξ) χ₀ Q m t
    (16 * K * selWidth y^4) Tsec Z ξr (sourceNormCap (restOf s hb cover G B (J B)).P b
      (restOf s hb cover G B (J B)).T (restOf s hb cover G B (J B)).d) hKc
    (rest_hH (restOf s hb cover G B (J B)) ha)
  refine h.trans (le_of_eq ?_)
  unfold diagPart labelPart
  ring

/-! ### (4) The skeleton of the final theorem -/

/-- One side of the balanced Seam 0 from the two parts. -/
theorem balanced_side_of_parts (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (K Tsec Z ξr : ℝ) (hK : 0 < K)
    (Jd : ℕ) (Ed El : ℝ)
    (hdiag : ∀ v : ℝ, outerSum s hb cover G J τ v (diagPart s ha hb cover G J Us τ χ₀ Q m v K Tsec Z ξr)
      ≤ Ed * (1+‖v‖)^(2*Jd))
    (hlabel : ∀ v : ℝ, outerSum s hb cover G J τ v (labelPart s ha hb cover G J τ χ₀ Q m v K Tsec Z ξr)
      ≤ El * (1+‖v‖)^(2*Jd)) :
    ∀ v : ℝ, (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ v K) ≤ (Ed + El) * (1+‖v‖)^(2*Jd) := by
  intro v
  refine (side_decomposition s ha hb cover opposite G hO hG hOG Us hUs J τ χ₀ Q m v K Tsec Z ξr hK).trans ?_
  rw [add_mul]
  exact add_le_add (hdiag v) (hlabel v)

theorem concreteArtificial_squarefree (s : Source ι a b) (C D : Id) (hD : D ≠ 0) :
    ∀ u ∈ concreteArtificial s C D hD, Squarefree u := by
  intro u hu
  exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero u (Finset.mem_filter.mp hu).2

/-- **Skeleton of `balanced_summed_raw_side_bounds`.** The diagonal parts (WP-J, item 3) and the
label parts (Seam B through WP-M2's frame, item 4) of both sides, height-uniformly bounded so that
their sums are the balanced budgets, give the balanced Seam 0. -/
theorem balanced_summed_raw_side_bounds (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (η : Character) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport D)
    (E : Finset (CommonIndex C D)) (KL KR A Z loss : ℝ) (hKL : 0 < KL) (hKR : 0 < KR) (Jd : ℕ)
    (JL : (B : actualAllocations (tuplePools s) C) → Finset (liveIndices B.val))
    (JR : (B : actualAllocations (tuplePools s) D) → Finset (liveIndices B.val))
    (χ₀ : RayCharacter) (Q : Id) (m : O) (Tsec Zs ξr : ℝ)
    (EdL ElL EdR ElR : RayCharacter → RayCharacter → ℝ)
    (hdiagL : ∀ χ ξ v, outerSum s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v
      (diagPart s ha hb cover C JL (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).left
        χ₀ Q m v KL Tsec Zs ξr) ≤ EdL χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelL : ∀ χ ξ v, outerSum s hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left v
      (labelPart s ha hb cover C JL (fixedPair η C D hC E χ (ξ⁻¹)).left χ₀ Q m v KL Tsec Zs ξr)
        ≤ ElL χ ξ * (1+‖v‖)^(2*Jd))
    (hdiagR : ∀ χ ξ v, outerSum s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v
      (diagPart s ha hb cover D JR (concreteArtificial s C D hD.1) (fixedPair η C D hC E χ (ξ⁻¹)).right
        χ₀ Q m v KR Tsec Zs ξr) ≤ EdR χ ξ * (1+‖v‖)^(2*Jd))
    (hlabelR : ∀ χ ξ v, outerSum s hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right v
      (labelPart s ha hb cover D JR (fixedPair η C D hC E χ (ξ⁻¹)).right χ₀ Q m v KR Tsec Zs ξr)
        ≤ ElR χ ξ * (1+‖v‖)^(2*Jd))
    (hbudL : ∀ χ ξ, EdL χ ξ + ElL χ ξ ≤ balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)
    (hbudR : ∀ χ ξ, EdR χ ξ + ElR χ ξ ≤ balancedBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss) :
    BalancedSummedRawSideBounds s ha η C D hC hD E KL KR A Z loss Jd := by
  intro χ ξ
  have hp : ∀ v : ℝ, 0 ≤ (1+‖v‖)^(2*Jd) := fun v => by positivity
  refine ⟨fun v => ?_, fun v => ?_⟩
  · refine (balanced_side_of_parts s ha hb cover D C hD hC hCD.symm (concreteArtificial s C D hD.1)
      (concreteArtificial_squarefree s C D hD.1) JL _ χ₀ Q m KL Tsec Zs ξr hKL Jd (EdL χ ξ) (ElL χ ξ)
      (hdiagL χ ξ) (hlabelL χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudL χ ξ) (hp v)
  · refine (balanced_side_of_parts s ha hb cover C D hC hD hCD (concreteArtificial s C D hD.1)
      (concreteArtificial_squarefree s C D hD.1) JR _ χ₀ Q m KR Tsec Zs ξr hKR Jd (EdR χ ξ) (ElR χ ξ)
      (hdiagR χ ξ) (hlabelR χ ξ) v).trans ?_
    exact mul_le_mul_of_nonneg_right (hbudR χ ξ) (hp v)

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
