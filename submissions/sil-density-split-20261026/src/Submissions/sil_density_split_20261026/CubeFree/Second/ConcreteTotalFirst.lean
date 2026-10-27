/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1 (htotal), part 4: from the first-step raw side energy to the live sources, and the
assembled reduction.

* `raw_first_allocation_le`: the (forked) first raw side energy of artificial divisor `u` is at
  most `#B · ∑_B |w_B|² · E_u(live_B)` (Cauchy over the genuine first allocations `B`, FP
  `first_gauss_live_sources`).
* `summed_raw_reduction`: for every first allocation `B` with selected slots `J B`, residual
  seed set `V B` and Gauss scales `16·K·W_y⁴` (`selWidth`), the u-summed first raw side energy is
  at most
    `#B ∑_B |w_B|² Atot_B ∑_{y,χ,ξ} 2^{ω(D_y)} ∑_{v ∈ V_B} E^{rest_B}_v(childCharacter τ ξ; 16 K W_y⁴)`,
  and each inner `∑_v E_v` is decomposed by `residual_poisson`. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteTotalSplit
import Submissions.sil_density_split_20261026.CubeFree.FP.RepairedFirstRawSides

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
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource RepairedFirstRawSides
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) :=
  Classical.decEq _

/-- The weight of a genuine first allocation. -/
def allocWeight (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G) : ℂ :=
  MixedCommonCoefficient.frozenWeight (punctureProduct s.S s.H) B.val *
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P

/-- **The first allocation Cauchy.** -/
theorem raw_first_allocation_le (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (u : Id) (τ : Character) (t K : ℝ) (hK : 0 < K) :
    rawEnergy s ha opposite G hG u τ t K ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          Qenergy (allocatedLiveSource s hb cover G B) ha u τ t K := by
  have hs := gaussEnergy_hasSum_re Finset.univ (element opposite G hG.1 (sourceColumns s))
    (element_supported opposite G hG.1 (sourceColumns s))
    (fun I : columns opposite G hG.1 (sourceColumns s) => originalResidual s ha 1 G u I * heightCoeff τ t I)
    ballProfile K hK
  unfold rawEnergy
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  intro rows
  have hpt : ∀ k : O, ‖gaussPolynomial Finset.univ (element opposite G hG.1 (sourceColumns s))
      (element_supported opposite G hG.1 (sourceColumns s))
      (fun I : columns opposite G hG.1 (sourceColumns s) =>
        originalResidual s ha 1 G u I * heightCoeff τ t I) k‖^2 ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          ‖Qpoly (allocatedLiveSource s hb cover G B) ha u τ t k‖^2 := by
    intro k
    rw [first_gauss_live_sources s ha hb cover opposite G 1 u hO hG hOG (one_dvd G) τ t k]
    have hc := FourthTransfer.d_cauchy (Finset.univ : Finset (actualAllocations (tuplePools s) G))
      (fun _ => (1 : ℂ)) (fun B => allocWeight s G B *
        Qpoly (allocatedLiveSource s hb cover G B) ha u τ t k)
    simp only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
    refine hc.trans (le_of_eq ?_)
    simp only [norm_mul, mul_pow]
  calc (∑ k ∈ rows, ‖gaussPolynomial Finset.univ (element opposite G hG.1 (sourceColumns s))
        (element_supported opposite G hG.1 (sourceColumns s))
        (fun I : columns opposite G hG.1 (sourceColumns s) =>
          originalResidual s ha 1 G u I * heightCoeff τ t I) k‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re)
      ≤ ∑ k ∈ rows, (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            ‖Qpoly (allocatedLiveSource s hb cover G B) ha u τ t k‖^2) *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hpt k) (ballProfile_nonneg _)
    _ = ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            ∑ k ∈ rows, ‖Qpoly (allocatedLiveSource s hb cover G B) ha u τ t k‖^2 *
              (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro B _
        apply Finset.sum_congr rfl; intro k _
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro B _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact finite_weighted_le_gaussEnergy _ _ _ _ ballProfile K hK
          (fun z => ballProfile_nonneg _) rows

/-- **The assembled energy reduction (htotal, first half).** -/
theorem summed_raw_reduction (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (V : actualAllocations (tuplePools s) G → Finset Id)
    (himg : ∀ B, ∀ u ∈ Us, ∀ y ∈ selY (allocatedLiveSource s hb cover G B) (J B),
      seedRest u (∏ j, y j) ∈ V B)
    (τ : Character) (t K : ℝ) (hK : 0 < K) :
    (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K) ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (Atot (allocatedLiveSource s hb cover G B) (J B) τ t *
            ∑ y ∈ selY (allocatedLiveSource s hb cover G B) (J B), ∑ χ : RayCharacter,
              ∑ ξ : RayCharacter, 2^(IdealMobiusDivisorSum.primeSupport (∏ j, y j)).card *
                ∑ v ∈ V B, Qenergy (restSource (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B))
                  ha v (childCharacter τ ξ) t (16 * K * selWidth y^4)) := by
  calc (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K)
      ≤ ∑ u ∈ Us, ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            Qenergy (allocatedLiveSource s hb cover G B) ha u τ t K :=
        Finset.sum_le_sum fun u _ =>
          raw_first_allocation_le s ha hb cover opposite G hO hG hOG u τ t K hK
    _ = ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            ∑ u ∈ Us, Qenergy (allocatedLiveSource s hb cover G B) ha u τ t K := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl; intro B _
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro B _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact summed_live_energy_le (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B) ha
          Us (V B) hUs (himg B) τ t K (fun y => 16 * K * selWidth y^4) hK
          (fun y hy => by have := selWidth_pos _ _ y hy; positivity)
          (fun y _ => selWidth_scale K hK y)

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
