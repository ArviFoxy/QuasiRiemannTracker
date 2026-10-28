/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1 (htotal), part 1: the energy reduction of a live source onto the residual source.

For a live source `s` (`s.B = 1`), a selected slot set `J` and a squarefree first artificial
divisor `u`:
* `expansion_transfer`: `P_u(k) = ∑_{y,χ,ξ} coefT(y,χ,ξ,k) · Q^{rest}_{seedRest u D_y, childCharacter τ ξ}(D_y⁴ k)`
  (`selected_expansion` + `residual_transfer`), `|coefT| ≤ |pc(χ,ξ)|·|sel(y)|`;
* `live_energy_le` (D-Cauchy and the substitution `z = D_y⁴ k`):
  `E_u(s; K) ≤ Atot · ∑_{y,χ,ξ} E^{rest}(seedRest u D_y, childCharacter τ ξ; K')`
  for `K'_y ≥ 2K‖D_y‖⁸` (`selWidth`: `K'_y = 16 K W_y⁴`, `W_y = ‖D_y‖²`, WP-J's scale) (`Atot = ∑_{y,χ,ξ} |pc|²|sel(y)|²`);
* `fiber_sum_le`: `∑_{u ∈ Us} F(seedRest u D) ≤ 2^{ω(D)} ∑_{v ∈ V} F(v)`;
* `summed_live_energy_le`: the u-summed form, with the residual seeds ranging over `V`. -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteTotalGauss
import Submissions.density_split_third_20261026.CubeFree.Second.FourthTransfer

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
open CenteredMomentFirstColumns RayFourExpansion CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstAmplificationChoice
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedCommonRestriction MixedCommonCoefficient MixedCommonAllocation MixedOriginalSecondZero
open MixedTupleRows MixedFirstLiveSource MixedRestrictedDictionary MixedSelectedCommon
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The Gauss polynomial of a source with seed `u` and character `ψ`. -/
def Qpoly (r : Source ι a b) (ha : 0 < a) (u : Id) (ψ : Character) (t : ℝ) (z : O) : ℂ :=
  gaussPolynomial Finset.univ (sourceGenerator (sourceColumns r))
    (sourceGenerator_supported (sourceColumns r))
    (fun I : supportedColumns (sourceColumns r) => sourceCoefficient r ha u I * heightCoeff ψ t I) z

/-- Its (real) Gauss energy. -/
def Qenergy (r : Source ι a b) (ha : 0 < a) (u : Id) (ψ : Character) (t K : ℝ) : ℝ :=
  (gaussEnergy Finset.univ (sourceGenerator (sourceColumns r))
    (sourceGenerator_supported (sourceColumns r))
    (fun I : supportedColumns (sourceColumns r) => sourceCoefficient r ha u I * heightCoeff ψ t I)
    ballProfile K).re

/-- The selected assignments. -/
abbrev selY (s : Source ι a b) (J : Finset ι) : Finset (J → Id) :=
  Fintype.piFinset (fun j : J => s.pool j.val)

def coefT (s : Source ι a b) (J : Finset ι) (y : J → Id) (τ : Character) (t : ℝ)
    (χ ξ : RayCharacter) (k : O) : ℂ :=
  selScalar s J y τ t * (pairCoeff firstPhaseTable χ ξ *
    (rayCharacter χ (primaryGenerator (∏ j, y j)) * primaryGaussRow (∏ j, y j) k))

theorem selY_supported (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J) :
    Supported (∏ j, y j) :=
  Finset.prod_induction _ Supported (fun x z hx hz => (supported_mul_iff x z).mpr ⟨hx, hz⟩)
    CenteredMomentAddedZero.supported_one_ideal
    (fun j _ => (s.hpn j.val _ ((Fintype.mem_piFinset.mp hy) j)).1)

theorem selY_prime (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J) (j : J) :
    Prime (y j) := s.hp j.val _ ((Fintype.mem_piFinset.mp hy) j)

/-- **Selected expansion and transfer.** -/
theorem expansion_transfer (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (hu : Squarefree u) (τ : Character) (t : ℝ) (k : O) :
    Qpoly s ha u τ t k =
      ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter, coefT s J y τ t χ ξ k *
        Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
          ((primaryGenerator (∏ j, y j))^4 * k) := by
  unfold Qpoly
  rw [selected_expansion s hB1 J ha u hu τ t k]
  apply Finset.sum_congr rfl
  intro y hy
  have hD := selY_supported s J y hy
  rw [residual_transfer (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (∏ j, y j) hD
    (seedRest_coprime u _) τ t k, ← primaryGaussRow_supported _ hD, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ξ _
  unfold coefT
  ring

theorem coefT_norm_sq (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J)
    (τ : Character) (t : ℝ) (χ ξ : RayCharacter) (k : O) :
    ‖coefT s J y τ t χ ξ k‖^2 ≤ ‖pairCoeff firstPhaseTable χ ξ‖^2 * ‖selScalar s J y τ t‖^2 := by
  unfold coefT
  by_cases hinj : Function.Injective y
  · have hG := prime_product_gauss_norm y (selY_prime s J y hy) hinj Finset.univ k
    have hχ := rayCharacter_norm_le χ (primaryGenerator (∏ j, y j))
    have h1 : ‖rayCharacter χ (primaryGenerator (∏ j, y j)) * primaryGaussRow (∏ j, y j) k‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul hχ hG (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul, norm_mul]
    have h2 : ‖selScalar s J y τ t‖ * (‖pairCoeff firstPhaseTable χ ξ‖ *
        ‖rayCharacter χ (primaryGenerator (∏ j, y j)) * primaryGaussRow (∏ j, y j) k‖) ≤
        ‖selScalar s J y τ t‖ * ‖pairCoeff firstPhaseTable χ ξ‖ := by
      rw [← mul_one (‖selScalar s J y τ t‖ * ‖pairCoeff firstPhaseTable χ ξ‖), mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (norm_nonneg _)
    calc _ ≤ (‖selScalar s J y τ t‖ * ‖pairCoeff firstPhaseTable χ ξ‖)^2 :=
          pow_le_pow_left₀ (by positivity) h2 2
      _ = _ := by ring
  · have h0 : selScalar s J y τ t = 0 := by simp [selScalar, hinj]
    rw [h0]
    simp

/-- The Cauchy mass of the selected block. -/
def Atot (s : Source ι a b) (J : Finset ι) (τ : Character) (t : ℝ) : ℝ :=
  ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
    ‖pairCoeff firstPhaseTable χ ξ‖^2 * ‖selScalar s J y τ t‖^2

theorem triple_sum_eq {M : Type*} [AddCommMonoid M] {Y : Type*} (Ys : Finset Y)
    (f : Y → RayCharacter → RayCharacter → M) :
    (∑ y ∈ Ys, ∑ χ : RayCharacter, ∑ ξ : RayCharacter, f y χ ξ) =
      ∑ p ∈ Ys ×ˢ (Finset.univ ×ˢ Finset.univ), f p.1 p.2.1 p.2.2 := by
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_product]

/-- Pointwise D-Cauchy. -/
theorem pointwise_cauchy (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (hu : Squarefree u) (τ : Character) (t : ℝ) (k : O) :
    ‖Qpoly s ha u τ t k‖^2 ≤ Atot s J τ t *
      ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
          ((primaryGenerator (∏ j, y j))^4 * k)‖^2 := by
  let T := selY s J ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ (Finset.univ : Finset RayCharacter))
  let c : (J → Id) × (RayCharacter × RayCharacter) → ℂ := fun p => coefT s J p.1 τ t p.2.1 p.2.2 k
  let X : (J → Id) × (RayCharacter × RayCharacter) → ℂ := fun p =>
    Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, p.1 j)) (childCharacter τ p.2.2) t
      ((primaryGenerator (∏ j, p.1 j))^4 * k)
  have e1 : Qpoly s ha u τ t k = ∑ p ∈ T, c p * X p := by
    rw [expansion_transfer s hB1 J ha u hu τ t k]
    exact triple_sum_eq (selY s J) (fun y χ ξ => coefT s J y τ t χ ξ k *
      Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
        ((primaryGenerator (∏ j, y j))^4 * k))
  have e2 : (∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
          ((primaryGenerator (∏ j, y j))^4 * k)‖^2) = ∑ p ∈ T, ‖X p‖^2 :=
    triple_sum_eq (selY s J) (fun y χ ξ =>
      ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
        ((primaryGenerator (∏ j, y j))^4 * k)‖^2)
  have e3 : Atot s J τ t = ∑ p ∈ T, ‖pairCoeff firstPhaseTable p.2.1 p.2.2‖^2 *
      ‖selScalar s J p.1 τ t‖^2 :=
    triple_sum_eq (selY s J) (fun y χ ξ =>
      ‖pairCoeff firstPhaseTable χ ξ‖^2 * ‖selScalar s J y τ t‖^2)
  rw [e1, e2, e3]
  refine (FourthTransfer.d_cauchy T c X).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  exact coefT_norm_sq s J p.1 (Finset.mem_product.mp hp).1 τ t p.2.1 p.2.2 k

/-- **The live energy is dominated by the residual energies** (D-Cauchy, `z = D⁴k`). -/
theorem live_energy_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (hu : Squarefree u) (τ : Character) (t K : ℝ) (Kp : (J → Id) → ℝ) (hK : 0 < K) (hK' : ∀ y ∈ selY s J, 0 < Kp y)
    (hKK : ∀ y ∈ selY s J,
      2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, y j))^4)‖^2 ≤ Kp y) :
    Qenergy s ha u τ t K ≤ Atot s J τ t *
      ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        Qenergy (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t (Kp y) := by
  have hA : 0 ≤ Atot s J τ t := by unfold Atot; positivity
  have hs := gaussEnergy_hasSum_re Finset.univ (sourceGenerator (sourceColumns s))
    (sourceGenerator_supported (sourceColumns s))
    (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha u I * heightCoeff τ t I)
    ballProfile K hK
  unfold Qenergy
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  intro rows
  calc (∑ z ∈ rows, ‖gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha u I * heightCoeff τ t I) z‖^2 *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / K)).re)
      ≤ ∑ z ∈ rows, (Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
            ((primaryGenerator (∏ j, y j))^4 * z)‖^2) *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / K)).re :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
          (pointwise_cauchy s hB1 J ha u hu τ t z) (ballProfile_nonneg _)
    _ = Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ∑ z ∈ rows, ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
            ((primaryGenerator (∏ j, y j))^4 * z)‖^2 *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / K)).re := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro χ _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ξ _
        apply Finset.sum_congr rfl; intro z _
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Finset.sum_le_sum; intro y hy
        apply Finset.sum_le_sum; intro χ _
        apply Finset.sum_le_sum; intro ξ _
        have hd : (primaryGenerator (∏ j, y j))^4 ≠ 0 :=
          pow_ne_zero 4 (supported_primaryGenerator_ne_zero _ (selY_supported s J y hy))
        exact sublattice_energy_le _ _ _ _ _ hd K (Kp y) hK (hK' y hy) (hKK y hy) rows

/-! ### The fibre bound for the artificial divisors -/

theorem fiber_card_le (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u) (D v : Id) (hD : D ≠ 0) :
    (Us.filter (fun u => seedRest u D = v)).card ≤ 2^(IdealMobiusDivisorSum.primeSupport D).card := by
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun u => (IdealMobiusDivisorSum.primeSupport u).filter
    (fun P => D ≤ P))
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro P hP
    obtain ⟨hPu, hDP⟩ := Finset.mem_filter.mp hP
    have hu0 := (hUs u (Finset.mem_filter.mp hu).1).ne_zero
    rw [mem_support_iff hD]
    exact ⟨((mem_support_iff hu0).mp hPu).1, hDP⟩
  · intro u₁ hu₁ u₂ hu₂ he
    obtain ⟨hm₁, hv₁⟩ := Finset.mem_filter.mp hu₁
    obtain ⟨hm₂, hv₂⟩ := Finset.mem_filter.mp hu₂
    have hs₁ : IdealMobiusDivisorSum.primeSupport u₁ =
        (IdealMobiusDivisorSum.primeSupport (seedRest u₁ D)) ∪
          (IdealMobiusDivisorSum.primeSupport u₁).filter (fun P => D ≤ P) := by
      rw [seedRest_support]
      ext P
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    have hs₂ : IdealMobiusDivisorSum.primeSupport u₂ =
        (IdealMobiusDivisorSum.primeSupport (seedRest u₂ D)) ∪
          (IdealMobiusDivisorSum.primeSupport u₂).filter (fun P => D ≤ P) := by
      rw [seedRest_support]
      ext P
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    have hsupp : IdealMobiusDivisorSum.primeSupport u₁ = IdealMobiusDivisorSum.primeSupport u₂ := by
      rw [hs₁, hs₂, hv₁, hv₂]
      exact congrArg _ he
    rw [← IdealMobiusDivisorSum.squarefree_support_product_self (hUs u₁ hm₁),
      ← IdealMobiusDivisorSum.squarefree_support_product_self (hUs u₂ hm₂), hsupp]

theorem fiber_sum_le (Us V : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u) (D : Id) (hD : D ≠ 0)
    (himg : ∀ u ∈ Us, seedRest u D ∈ V) (F : Id → ℝ) (hF : ∀ v, 0 ≤ F v) :
    (∑ u ∈ Us, F (seedRest u D)) ≤
      2^(IdealMobiusDivisorSum.primeSupport D).card * ∑ v ∈ V, F v := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => seedRest u D) himg]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hc : (∑ u ∈ Us.filter (fun u => seedRest u D = v), F (seedRest u D)) =
      (Us.filter (fun u => seedRest u D = v)).card * F v := by
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]), Finset.sum_const,
      nsmul_eq_mul]
  rw [hc]
  apply mul_le_mul_of_nonneg_right _ (hF v)
  exact_mod_cast fiber_card_le Us hUs D v hD

/-- **The u-summed live energy reduction.** `V` is any finite set of residual seeds containing the
images `seedRest u D_y`. -/
theorem summed_live_energy_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (Us V : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (himg : ∀ u ∈ Us, ∀ y ∈ selY s J, seedRest u (∏ j, y j) ∈ V)
    (τ : Character) (t K : ℝ) (Kp : (J → Id) → ℝ) (hK : 0 < K) (hK' : ∀ y ∈ selY s J, 0 < Kp y)
    (hKK : ∀ y ∈ selY s J,
      2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, y j))^4)‖^2 ≤ Kp y) :
    (∑ u ∈ Us, Qenergy s ha u τ t K) ≤ Atot s J τ t *
      ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        2^(IdealMobiusDivisorSum.primeSupport (∏ j, y j)).card *
          ∑ v ∈ V, Qenergy (restSource s hB1 J) ha v (childCharacter τ ξ) t (Kp y) := by
  have hA : 0 ≤ Atot s J τ t := by unfold Atot; positivity
  have hE : ∀ y ∈ selY s J, ∀ v ψ, 0 ≤ Qenergy (restSource s hB1 J) ha v ψ t (Kp y) := by
    intro y hy v ψ
    unfold Qenergy
    rw [← (gaussEnergy_hasSum_re _ _ _ _ ballProfile (Kp y) (hK' y hy)).tsum_eq]
    exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  calc (∑ u ∈ Us, Qenergy s ha u τ t K)
      ≤ ∑ u ∈ Us, Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          Qenergy (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t (Kp y) :=
        Finset.sum_le_sum fun u hu =>
          live_energy_le s hB1 J ha u (hUs u hu) τ t K Kp hK hK' hKK
    _ = Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ∑ u ∈ Us, Qenergy (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t (Kp y) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro χ _
        rw [Finset.sum_comm]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Finset.sum_le_sum; intro y hy
        apply Finset.sum_le_sum; intro χ _
        apply Finset.sum_le_sum; intro ξ _
        exact fiber_sum_le Us V hUs _ (selY_supported s J y hy).1 (fun u hu => himg u hu y hy)
          (fun v => Qenergy (restSource s hB1 J) ha v (childCharacter τ ξ) t (Kp y)) (fun v => hE y hy v _)

/-- The selected width `W_y = ‖D_y‖²` and WP-J's Gauss scale `16·K·W_y⁴`. -/
def selWidth {J : Finset ι} (y : J → Id) : ℝ :=
  ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator (∏ j, y j))‖^2

theorem selWidth_scale (K : ℝ) (hK : 0 < K) {J : Finset ι} (y : J → Id) :
    2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, y j))^4)‖^2 ≤
      16 * K * selWidth y^4 := by
  unfold selWidth
  rw [map_pow, norm_pow, ← pow_mul, show ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator (∏ j, y j))‖^(4*2) =
    (‖ConcreteTraceCRT.eisEmbedding (primaryGenerator (∏ j, y j))‖^2)^4 by ring]
  have : 0 ≤ (‖ConcreteTraceCRT.eisEmbedding (primaryGenerator (∏ j, y j))‖^2)^4 := by positivity
  nlinarith

theorem selWidth_pos (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J) :
    0 < selWidth y := by
  unfold selWidth
  have hn : primaryGenerator (∏ j, y j) ≠ 0 :=
    supported_primaryGenerator_ne_zero _ (selY_supported s J y hy)
  have : ConcreteTraceCRT.eisEmbedding (primaryGenerator (∏ j, y j)) ≠ 0 :=
    ConcreteTraceCRT.eisEmbedding_ne_zero hn
  positivity

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
