/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: discharge of the two hypotheses of the corrected assembly (`ConcreteAssemblyAvg`).

* **MultBound.** For `z ≠ 0` every selected `y` with `D_y⁴ ∣ z` has all its primes dividing
  `(z)`, so `y` is a `|J|`-tuple of divisors of `(z)`: `#{y : D_y⁴ ∣ z} ≤ τ((z))^{|J|}`
  (`selected_mult_card_le`). On the radius ball `N((z)) = ‖z‖² ≤ 16·K·W⁴ ≤ Z^C`, and the divisor bound
  (`Packet.Fibre.divisor_power_subpower`, OAI `ideal_divisor_small_power`) gives
  `M = max Cδ 1 · Z^δ` for every `δ > 0`, uniformly in `|J| ≤ N` (`multBound_subpower`). The zero row
  (`z = 0`, only for `J = ∅`) has multiplicity `#selY = 1`.
* **WidthBound and comparability.** `selWidth y = N(D_y) = ∏ N(y_j)` (`selWidth_eq_prod`). The slot
  width `W_B := ∏_{j∈J} 2 P_j` dominates every selected width (pools: `N(y_j) ≤ 2 P_j`,
  `widthBound_slot`), and on every LIVE `y` (`selAmp ≠ 0`, i.e. `N(y_j)/P_j ∈ [1,2]` by the support
  of `Wslot`) `W_B ≤ 2^{|J|}·selWidth y` (`slotWidth_le_of_live`), so the Gauss scales satisfy
  `16 K W_y⁴ ≤ 16 K W_B⁴ ≤ 2^{4|J|}·16 K W_y⁴` (`scale_comparable`). Non-live `y` have `coefT = 0`. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteAssemblyAvg
import Submissions.sil_density_split_20261026.CubeFree.Packet.Fibre
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

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

/-! ### MultBound -/

theorem selected_dvd_span {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) (y : J → Id)
    (hy : y ∈ selY s J) (z : O) (hdz : (primaryGenerator (∏ j, y j))^4 ∣ z) (j : J) :
    y j ∣ Ideal.span {z} := by
  have hD := selY_supported s J y hy
  have h1 : primaryGenerator (∏ j, y j) ∣ z := (dvd_pow_self _ (by norm_num)).trans hdz
  have h2 : Ideal.span {primaryGenerator (∏ j, y j)} ∣ Ideal.span {z} :=
    (Ideal.span_singleton_dvd_span_singleton_iff_dvd).mpr h1
  rw [primary_span_supported _ hD] at h2
  exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans h2

/-- `#{y ∈ selY : D_y⁴ ∣ z} ≤ τ((z))^{|J|}` for `z ≠ 0`. -/
theorem selected_mult_card_le {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) (z : O)
    (hz : z ≠ 0) :
    ((selY s J).filter (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card ≤
      (IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card ^ Fintype.card J := by
  have hr : Ideal.span {z} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hz
  let e := Fintype.equivFin J
  let f : (J → Id) → (Fin (Fintype.card J) → Id) := fun y i => y (e.symm i)
  have hinj : Function.Injective f := by
    intro y y' h
    funext j
    have := congrFun h (e j)
    simpa [f] using this
  rw [← Finset.card_image_of_injective _ hinj]
  apply Packet.Fibre.card_le_of_components_dvd hr
  intro g hg i
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨hyY, hyd⟩ := Finset.mem_filter.mp hy
  exact selected_dvd_span s J y hyY z hyd (e.symm i)

/-- The multiplicity at one selected block, from a divisor bound at exponent `N ≥ |J|`. -/
theorem selected_mult_le {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) (N : ℕ)
    (hJ : Fintype.card J ≤ N) (Cexp δ Cδ Z : ℝ) (hZ : 1 ≤ Z) (hδ : 0 ≤ δ)
    (hC : ∀ r : Id, r ≠ ⊥ → (Ideal.absNorm r : ℝ) ≤ Z ^ Cexp →
      ((IdealMobiusDivisorSum.idealDivisors r).card : ℝ) ^ N ≤ Cδ * Z ^ δ)
    (z : O) (hz : z ≠ 0 ∨ J = ∅) (hzn : ‖ConcreteTraceCRT.eisEmbedding z‖^2 ≤ Z ^ Cexp) :
    (((selY s J).filter (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ) ≤
      max Cδ 1 * Z ^ δ := by
  have hZδ : 1 ≤ Z ^ δ := Real.one_le_rpow hZ hδ
  by_cases hz0 : z = 0
  · have hJ0 : J = ∅ := hz.resolve_left (fun h => h hz0)
    subst hJ0
    have hc : ((selY s (∅ : Finset κ)).filter
        (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card ≤ 1 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Fintype.card_piFinset]
      simp
    calc (((selY s (∅ : Finset κ)).filter
          (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ) ≤ 1 := by exact_mod_cast hc
      _ ≤ max Cδ 1 * Z ^ δ := by
          have := le_max_right Cδ 1
          nlinarith
  · have hr : Ideal.span {z} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hz0
    have hN : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z ^ Cexp := by
      rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]; exact hzn
    have hτ1 : (1 : ℝ) ≤ (IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card := by
      have : 0 < (IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card :=
        Finset.card_pos.mpr ⟨_, (IdealMobiusDivisorSum.mem_idealDivisors hr).mpr dvd_rfl⟩
      exact_mod_cast this
    calc (((selY s J).filter (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ)
        ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card : ℝ) ^ Fintype.card J := by
          exact_mod_cast selected_mult_card_le s J z hz0
      _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {z})).card : ℝ) ^ N :=
          pow_le_pow_right₀ hτ1 hJ
      _ ≤ Cδ * Z ^ δ := hC _ hr hN
      _ ≤ max Cδ 1 * Z ^ δ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)

/-- **MultBound discharged.** For every `N`, `Cexp ≥ 0`, `δ > 0` there is `Cδ` such that, for
`Z ≥ 1`, blocks with `|J_B| ≤ N` and scales `16·K·W_B⁴ ≤ Z^Cexp`, the multiplicity is
`M_B = Cδ · Z^δ`. -/
theorem multBound_subpower (N : ℕ) (Cexp δ : ℝ) (hCexp : 0 ≤ Cexp) (hδ : 0 < δ) :
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
        (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
        (K : ℝ) (W : actualAllocations (tuplePools s) G → ℝ),
        (∀ B, Fintype.card (J B) ≤ N) → (∀ B, 16 * K * W B^4 ≤ Z ^ Cexp) →
          MultBound s hb cover G J K W (fun _ => Cδ * Z ^ δ) := by
  obtain ⟨Cδ, hCδ, hC⟩ := Packet.Fibre.divisor_power_subpower N Cexp δ hCexp hδ
  refine ⟨max Cδ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Z hZ s hb cover G J K W hJ hrad B
  refine ⟨by have := Real.rpow_nonneg (zero_le_one.trans hZ) δ; positivity, ?_⟩
  intro z hz hzn
  exact selected_mult_le (allocatedLiveSource s hb cover G B) (J B) N (hJ B) Cexp δ Cδ Z hZ hδ.le
    (fun r hr hN => hC Z hZ r hr hN) z hz (hzn.trans (hrad B))

/-! ### WidthBound and comparability -/

theorem selWidth_eq_prod {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) (y : J → Id)
    (hy : y ∈ selY s J) : selWidth y = ∏ j, (Ideal.absNorm (y j) : ℝ) := by
  unfold selWidth
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    primary_span_supported _ (selY_supported s J y hy), map_prod, Nat.cast_prod]

/-- The slot width `∏_{j∈J} 2 P_j`. -/
def slotWidth {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) : ℝ :=
  ∏ j : J, 2 * s.P j.val

theorem slotWidth_pos {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) :
    0 < slotWidth s J :=
  Finset.prod_pos fun j _ => by have := s.hP j.val; linarith

theorem selWidth_le_slotWidth {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ)
    (y : J → Id) (hy : y ∈ selY s J) : selWidth y ≤ slotWidth s J := by
  rw [selWidth_eq_prod s J y hy]
  exact Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
    (fun j _ => (s.hpn j.val _ ((Fintype.mem_piFinset.mp hy) j)).2)

/-- **Comparability on live assignments.** -/
theorem slotWidth_le_of_live {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ)
    (y : J → Id) (hy : y ∈ selY s J) (hlive : selAmp s J y ≠ 0) :
    slotWidth s J ≤ 2 ^ Fintype.card J * selWidth y := by
  rw [selWidth_eq_prod s J y hy, slotWidth, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀ (fun j _ => by have := s.hP j.val; linarith)
  intro j _
  have hfac : s.Wslot j.val ((Ideal.absNorm (y j) : ℝ) / s.P j.val) ≠ 0 := by
    intro h0
    apply hlive
    unfold selAmp
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h0, mul_zero])
  have hmem := s.hW j.val (Function.mem_support.mpr hfac)
  have hP0 : 0 < s.P j.val := lt_of_lt_of_le one_pos (s.hP j.val)
  have h1 := hmem.1
  rw [le_div_iff₀ hP0, one_mul] at h1
  exact h1

/-- The live/dead dichotomy: a selected scalar vanishes off the live assignments. -/
theorem selAmp_ne_zero_of_selScalar (s : Source ι a b) (J : Finset ι) (y : J → Id) (τ : Character)
    (t : ℝ) (h : selScalar s J y τ t ≠ 0) : selAmp s J y ≠ 0 := by
  intro h0; apply h; unfold selScalar; rw [h0]; ring

/-- **WidthBound discharged** by the slot widths. -/
theorem widthBound_slot (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) :
    WidthBound s hb cover G J (fun B => slotWidth (allocatedLiveSource s hb cover G B) (J B)) :=
  fun B => ⟨slotWidth_pos _ _, fun y hy => selWidth_le_slotWidth _ _ y hy⟩

/-- **Gauss-scale comparability**: `16KW_y⁴ ≤ 16KW_B⁴ ≤ 2^{4|J|}·16KW_y⁴` on live `y`. -/
theorem scale_comparable {κ : Type*} [Fintype κ] (s : Source κ a b) (J : Finset κ) (K : ℝ)
    (hK : 0 ≤ K) (y : J → Id) (hy : y ∈ selY s J) (hlive : selAmp s J y ≠ 0) :
    16 * K * selWidth y^4 ≤ 16 * K * slotWidth s J^4 ∧
      16 * K * slotWidth s J^4 ≤ (2:ℝ)^(4 * Fintype.card J) * (16 * K * selWidth y^4) := by
  have hy0 : 0 ≤ selWidth y := by unfold selWidth; positivity
  have hle := selWidth_le_slotWidth s J y hy
  have hge := slotWidth_le_of_live s J y hy hlive
  have hW0 := (slotWidth_pos s J).le
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hle 4) (by positivity)
  · have h4 : slotWidth s J^4 ≤ (2 ^ Fintype.card J * selWidth y)^4 := pow_le_pow_left₀ hW0 hge 4
    rw [mul_pow, ← pow_mul, mul_comm (Fintype.card J) 4] at h4
    calc 16 * K * slotWidth s J^4 ≤ 16 * K * ((2:ℝ)^(4 * Fintype.card J) * selWidth y^4) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
