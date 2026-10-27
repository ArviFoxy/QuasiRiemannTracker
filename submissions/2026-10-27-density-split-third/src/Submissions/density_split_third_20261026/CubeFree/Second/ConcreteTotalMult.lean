/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M item 1, CORRECTED energy reduction (selected-divisor average, CF §4, FP
`MixedFirstAveragedWindow.actual_selected_window_average`).

`live_energy_le` / `summed_raw_reduction` bounded each selected assignment `y` by a full residual
energy at its own radius and then summed over `y`: total `Atot·∑_y E_y ≍ Z^{2u}·Ē`. CF and FP pay
only `Z^u·Ē`: the rows `z = D_y⁴ k` of DIFFERENT selected assignments are different rows of ONE
residual energy (a row `z` is hit by at most `M = #{y : D_y⁴ ∣ z}` pairs, `M ≤ |J|!·2^{ω(z)} =
Z^{o(1)}`). This file implements that: all `y` share the radius `Kmax = 16 K W⁴` (`selWidth y ≤ W`),
the residual energy depends on `y` only through the seed `seedRest u D_y`, and after the
seed fibre bound the `y`-sum is absorbed by the multiplicity `M`:
  `∑_{u∈Us} E_u(s; K) ≤ Atot · 2^{|J|} · M · ∑_χ ∑_ξ ∑_{v∈V} E^{rest}_v(childCharacter τ ξ; Kmax)`
(`summed_live_energy_avg_le`). The zero row `k = 0` contributes nothing for `J ≠ ∅`
(`selected_zero_row`: a nonempty product of distinct primes is not a sixth power).
`summed_raw_reduction_avg` is the corrected first-allocation assembly. -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteTotalFirst
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows RayFourExpansion CenteredMomentLiveDomain
open CenteredMomentFirstColumns
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource RepairedFirstRawSides
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) instDecEqSubtypeMult {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) :=
  Classical.decEq _

/-! ### The zero row -/

theorem selected_zero_row {κ : Type*} [Fintype κ] (y : κ → Id) (hy : ∀ j, Prime (y j))
    (hinj : Function.Injective y) (j₀ : κ) : primaryGaussRow (∏ j, y j) 0 = 0 := by
  by_contra hne
  have hs : Supported (∏ j, y j) := by
    by_contra hs
    exact hne (by rw [primaryGaussRow, dif_neg hs])
  rw [primaryGaussRow_supported _ hs] at hne
  have h6 := CenteredMomentAddedZero.gaussRow_zero_ideal_sixth_power _
    (MixedSelectedCommon.primary_supported _ hs) hne
  rw [primary_span_supported _ hs] at h6
  set Q := CenteredExceptionalCount.sixthQuotient (∏ j, y j)
  have hP := hy j₀
  have hPD : y j₀ ∣ ∏ j, y j := Finset.dvd_prod_of_mem _ (Finset.mem_univ j₀)
  rw [← h6] at hPD
  have hPQ : y j₀ ∣ Q := hP.dvd_of_dvd_pow hPD
  have hP2 : y j₀ * y j₀ ∣ ∏ j, y j := by
    rw [← h6]
    exact (mul_dvd_mul hPQ hPQ).trans (by
      rw [show Q^6 = (Q * Q) * Q^4 by ring]; exact dvd_mul_right _ _)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)] at hP2
  have hP' : y j₀ ∣ ∏ j ∈ Finset.univ.erase j₀, y j :=
    (mul_dvd_mul_iff_left hP.ne_zero).mp hP2
  obtain ⟨j, hj, hdj⟩ := (Prime.dvd_finset_prod_iff hP _).mp hP'
  exact (Finset.mem_erase.mp hj).1 (hinj (prime_dvd_prime_eq hP (hy j) hdj)).symm

theorem coefT_zero (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J)
    (j₀ : J) (τ : Character) (t : ℝ) (χ ξ : RayCharacter) : coefT s J y τ t χ ξ 0 = 0 := by
  unfold coefT
  by_cases hinj : Function.Injective y
  · rw [selected_zero_row y (selY_prime s J y hy) hinj j₀]; ring
  · have h0 : selScalar s J y τ t = 0 := by simp [selScalar, hinj]
    rw [h0, zero_mul]

theorem live_zero_row (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι) (ha : 0 < a)
    (u : Id) (hu : Squarefree u) (τ : Character) (t : ℝ) (j₀ : J) :
    Qpoly s ha u τ t 0 = 0 := by
  rw [expansion_transfer s hB1 J ha u hu τ t 0]
  apply Finset.sum_eq_zero; intro y hy
  apply Finset.sum_eq_zero; intro χ _
  apply Finset.sum_eq_zero; intro ξ _
  rw [coefT_zero s J y hy j₀, zero_mul]

/-! ### Multiplicity of the transferred rows -/

/-- Rows of ONE Gauss polynomial hit by several multipliers. -/
theorem mult_energy_le {α κ : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (Y : Finset κ) (d : κ → O)
    (hd : ∀ y ∈ Y, d y ≠ 0) (K Kmax : ℝ) (hK : 0 < K) (hKmax : 0 < Kmax)
    (hKK : ∀ y ∈ Y, 2 * K * ‖ConcreteTraceCRT.eisEmbedding (d y)‖^2 ≤ Kmax)
    (rows : Finset O) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ (Y ×ˢ rows).image (fun p => d p.1 * p.2),
      (((Y ×ˢ rows).filter (fun p => d p.1 * p.2 = z)).card : ℝ) ≤ M) :
    (∑ y ∈ Y, ∑ k ∈ rows, ‖gaussPolynomial S a ha c (d y * k)‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re) ≤
      M * (gaussEnergy S a ha c ballProfile Kmax).re := by
  let g : O → ℝ := fun z => ‖gaussPolynomial S a ha c z‖^2 *
    (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / Kmax)).re
  have hg : ∀ z, 0 ≤ g z := fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  calc (∑ y ∈ Y, ∑ k ∈ rows, ‖gaussPolynomial S a ha c (d y * k)‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re)
      ≤ ∑ p ∈ Y ×ˢ rows, g (d p.1 * p.2) := by
        rw [Finset.sum_product]
        apply Finset.sum_le_sum; intro y hy
        apply Finset.sum_le_sum; intro k _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [emb_mul_sq]
        exact ball_le_scaled K Kmax _ _ hK hKmax (sq_nonneg _) (sq_nonneg _) (hKK y hy)
    _ = ∑ z ∈ (Y ×ˢ rows).image (fun p => d p.1 * p.2),
          ((Y ×ˢ rows).filter (fun p => d p.1 * p.2 = z)).card * g z := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => d p.1 * p.2)
          (fun p hp => Finset.mem_image_of_mem _ hp)]
        apply Finset.sum_congr rfl; intro z _
        rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ (Y ×ˢ rows).image (fun p => d p.1 * p.2), M * g z :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hM z hz) (hg z)
    _ = M * ∑ z ∈ (Y ×ˢ rows).image (fun p => d p.1 * p.2), g z := by rw [Finset.mul_sum]
    _ ≤ M * (gaussEnergy S a ha c ballProfile Kmax).re :=
        mul_le_mul_of_nonneg_left (finite_weighted_le_gaussEnergy S a ha c ballProfile
          Kmax hKmax (fun z => ballProfile_nonneg _) _) hM0

/-! ### The averaged reduction -/

theorem omega_le_card (s : Source ι a b) (J : Finset ι) (y : J → Id) (hy : y ∈ selY s J) :
    (IdealMobiusDivisorSum.primeSupport (∏ j, y j)).card ≤ Fintype.card J := by
  have hD : (∏ j, y j) ≠ 0 := (selY_supported s J y hy).1
  have hsub : IdealMobiusDivisorSum.primeSupport (∏ j, y j) ⊆ Finset.univ.image y := by
    intro P hP
    obtain ⟨hPi, hDP⟩ := (mem_support_iff hD).mp hP
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      exact hD (le_bot_iff.mp hDP)
    have hPp : Prime P := Ideal.prime_of_isPrime hP0 hPi
    have hdvd : P ∣ ∏ j, y j := Ideal.dvd_iff_le.mpr hDP
    obtain ⟨j, _, hj⟩ := (Prime.dvd_finset_prod_iff hPp _).mp hdvd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j,
      (prime_dvd_prime_eq hPp (selY_prime s J y hy j) hj).symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem pair_fiber_card {κ : Type*} (Y : Finset κ) (d : κ → O) (hd : ∀ y ∈ Y, d y ≠ 0)
    (rows : Finset O) (z : O) :
    ((Y ×ˢ rows).filter (fun p => d p.1 * p.2 = z)).card ≤ (Y.filter (fun y => d y ∣ z)).card := by
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hm).1, ⟨p.2, he.symm⟩⟩
  · intro p hp q hq he
    obtain ⟨hpm, hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hqe⟩ := Finset.mem_filter.mp hq
    have h1 : p.1 = q.1 := he
    have h2 : d p.1 * p.2 = d p.1 * q.2 := by rw [hpe, h1, hqe]
    exact Prod.ext h1 (mul_left_cancel₀ (hd p.1 (Finset.mem_product.mp hpm).1) h2)

/-- **The averaged u-summed live energy reduction** (`Z^u·Ē`, not `Z^{2u}·Ē`). -/
theorem summed_live_energy_avg_le (s : Source ι a b) (hB1 : ∀ k, s.B k = 1) (J : Finset ι)
    (ha : 0 < a) (Us V : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (himg : ∀ u ∈ Us, ∀ y ∈ selY s J, seedRest u (∏ j, y j) ∈ V)
    (τ : Character) (t K Kmax : ℝ) (hK : 0 < K) (hKmax : 0 < Kmax)
    (hKK : ∀ y ∈ selY s J,
      2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, y j))^4)‖^2 ≤ Kmax)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hmult : ∀ z : O, (z ≠ 0 ∨ J = ∅) → ‖ConcreteTraceCRT.eisEmbedding z‖^2 ≤ Kmax →
      (((selY s J).filter (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ) ≤ M) :
    (∑ u ∈ Us, Qenergy s ha u τ t K) ≤
      Atot s J τ t * ((2:ℝ)^(Fintype.card J) * M) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ∑ v ∈ V, Qenergy (restSource s hB1 J) ha v (childCharacter τ ξ) t Kmax := by
  have hA : 0 ≤ Atot s J τ t := by unfold Atot; positivity
  let d : (J → Id) → O := fun y => (primaryGenerator (∏ j, y j))^4
  have hd : ∀ y ∈ selY s J, d y ≠ 0 := fun y hy =>
    pow_ne_zero 4 (supported_primaryGenerator_ne_zero _ (selY_supported s J y hy))
  have hs : HasSum (fun k : O => ∑ u ∈ Us, ‖Qpoly s ha u τ t k‖^2 *
      (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re)
      (∑ u ∈ Us, Qenergy s ha u τ t K) :=
    hasSum_sum (fun u _ => gaussEnergy_hasSum_re _ _ _ _ ballProfile K hK)
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le
    (fun k => Finset.sum_nonneg fun u _ => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))
  intro rows
  let rows' := rows.filter (fun k => (k ≠ 0 ∨ J = ∅) ∧ ‖ConcreteTraceCRT.eisEmbedding k‖^2 < 2 * K)
  let Hf : RayCharacter → (J → Id) → Id → ℝ := fun ξ y v =>
    ∑ k ∈ rows', ‖Qpoly (restSource s hB1 J) ha v (childCharacter τ ξ) t (d y * k)‖^2 *
      (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re
  have hHf : ∀ ξ y v, 0 ≤ Hf ξ y v := fun ξ y v =>
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  -- step 1: drop the zero row, then pointwise Cauchy
  have hstep1 : (∑ k ∈ rows, ∑ u ∈ Us, ‖Qpoly s ha u τ t k‖^2 *
      (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re) ≤
      ∑ u ∈ Us, Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        Hf ξ y (seedRest u (∏ j, y j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro u hu
    have hdrop : (∑ k ∈ rows, ‖Qpoly s ha u τ t k‖^2 *
        (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re) =
        ∑ k ∈ rows', ‖Qpoly s ha u τ t k‖^2 *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hk'
      by_cases hrad : ‖ConcreteTraceCRT.eisEmbedding k‖^2 < 2 * K
      swap
      · have hb0 : ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K) = 0 := by
          by_contra hne
          have := CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper _
            (div_nonneg (sq_nonneg _) hK.le) hne
          rw [div_lt_iff₀ hK] at this
          exact hrad (by linarith)
        rw [hb0]; simp
      have h0 : k = 0 ∧ J ≠ ∅ := by
        by_contra hc
        apply hk'
        refine Finset.mem_filter.mpr ⟨hk, ?_, hrad⟩
        by_cases hk0 : k = 0
        · right; by_contra hJ; exact hc ⟨hk0, hJ⟩
        · left; exact hk0
      obtain ⟨hk0, hJ⟩ := h0
      obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
      rw [hk0, live_zero_row s hB1 J ha u (hUs u hu) τ t ⟨j₀, hj₀⟩]
      simp
    rw [hdrop]
    calc (∑ k ∈ rows', ‖Qpoly s ha u τ t k‖^2 *
          (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re)
        ≤ ∑ k ∈ rows', (Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            ‖Qpoly (restSource s hB1 J) ha (seedRest u (∏ j, y j)) (childCharacter τ ξ) t
              (d y * k)‖^2) * (ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2 / K)).re :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (pointwise_cauchy s hB1 J ha u (hUs u hu) τ t k) (ballProfile_nonneg _)
      _ = _ := by
          simp only [Hf, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro χ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro ξ _
          apply Finset.sum_congr rfl; intro k _
          ring
  refine hstep1.trans ?_
  -- step 2: the seed fibres (`ω(D_y) ≤ |J|`)
  have hstep2 : (∑ u ∈ Us, Atot s J τ t * ∑ y ∈ selY s J, ∑ χ : RayCharacter,
        ∑ ξ : RayCharacter, Hf ξ y (seedRest u (∏ j, y j))) ≤
      Atot s J τ t * ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        (2:ℝ)^(Fintype.card J) * ∑ v ∈ V, ∑ y ∈ selY s J, Hf ξ y v := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [Finset.sum_comm]
    calc (∑ y ∈ selY s J, ∑ u ∈ Us, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          Hf ξ y (seedRest u (∏ j, y j)))
        ≤ ∑ y ∈ selY s J, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            (2:ℝ)^(Fintype.card J) * ∑ v ∈ V, Hf ξ y v := by
          apply Finset.sum_le_sum; intro y hy
          rw [Finset.sum_comm]
          apply Finset.sum_le_sum; intro χ _
          rw [Finset.sum_comm]
          apply Finset.sum_le_sum; intro ξ _
          refine (fiber_sum_le Us V hUs _ (selY_supported s J y hy).1
            (fun u hu => himg u hu y hy) (Hf ξ y) (hHf ξ y)).trans ?_
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun v _ => hHf ξ y v)
          exact pow_le_pow_right₀ (by norm_num) (omega_le_card s J y hy)
      _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro χ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro ξ _
          rw [← Finset.mul_sum, Finset.sum_comm]
  refine hstep2.trans ?_
  -- step 3: the multiplicity of the transferred rows
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hA
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro ξ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro v _
  apply mult_energy_le _ _ _ _ (selY s J) d hd K Kmax hK hKmax hKK rows' M hM0
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hpY, hpk⟩ := Finset.mem_product.mp hp
  obtain ⟨_, hpc, hpr⟩ := Finset.mem_filter.mp hpk
  have hcond : d p.1 * p.2 ≠ 0 ∨ J = ∅ := by
    rcases hpc with h | h
    · exact Or.inl (mul_ne_zero (hd p.1 hpY) h)
    · exact Or.inr h
  have hrad : ‖ConcreteTraceCRT.eisEmbedding (d p.1 * p.2)‖^2 ≤ Kmax := by
    rw [emb_mul_sq]
    have h1 := hKK p.1 hpY
    have h2 : ‖ConcreteTraceCRT.eisEmbedding (d p.1)‖^2 * ‖ConcreteTraceCRT.eisEmbedding p.2‖^2 ≤
        ‖ConcreteTraceCRT.eisEmbedding (d p.1)‖^2 * (2 * K) :=
      mul_le_mul_of_nonneg_left hpr.le (sq_nonneg _)
    change ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, p.1 j))^4)‖^2 *
      ‖ConcreteTraceCRT.eisEmbedding p.2‖^2 ≤ Kmax
    change 2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, p.1 j))^4)‖^2 ≤ Kmax at h1
    change ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, p.1 j))^4)‖^2 *
      ‖ConcreteTraceCRT.eisEmbedding p.2‖^2 ≤
        ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, p.1 j))^4)‖^2 * (2 * K) at h2
    linarith
  exact (Nat.cast_le.mpr (pair_fiber_card (selY s J) d hd rows' _)).trans (hmult _ hcond hrad)

/-- The common Gauss scale `16·K·W⁴` dominates every selected transfer. -/
theorem common_scale (K W : ℝ) (hK : 0 < K) (s : Source ι a b) (J : Finset ι)
    (hW : ∀ y ∈ selY s J, selWidth y ≤ W) :
    ∀ y ∈ selY s J,
      2 * K * ‖ConcreteTraceCRT.eisEmbedding ((primaryGenerator (∏ j, y j))^4)‖^2 ≤
        16 * K * W^4 := by
  intro y hy
  refine (selWidth_scale K hK y).trans ?_
  have h0 := (selWidth_pos s J y hy).le
  have : selWidth y^4 ≤ W^4 := pow_le_pow_left₀ h0 (hW y hy) 4
  nlinarith

/-- **The corrected assembled energy reduction (htotal, first half).** Outer weight
`#B·∑_B |w_B|²·Atot_B·2^{|J_B|}·M_B`, and ONE residual energy per `(B, χ, ξ)` at the common radius
`16·K·W_B⁴`: no `∑_y`. -/
theorem summed_raw_reduction_avg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (opposite G : Id) (hO : Supported opposite) (hG : Supported G)
    (hOG : QRH.Record1252270103KernelMass.primeSupport opposite =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u)
    (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (V : actualAllocations (tuplePools s) G → Finset Id)
    (himg : ∀ B, ∀ u ∈ Us, ∀ y ∈ selY (allocatedLiveSource s hb cover G B) (J B),
      seedRest u (∏ j, y j) ∈ V B)
    (τ : Character) (t K : ℝ) (hK : 0 < K)
    (W M : actualAllocations (tuplePools s) G → ℝ) (hW0 : ∀ B, 0 < W B)
    (hW : ∀ B, ∀ y ∈ selY (allocatedLiveSource s hb cover G B) (J B), selWidth y ≤ W B)
    (hM0 : ∀ B, 0 ≤ M B)
    (hmult : ∀ B, ∀ z : O, (z ≠ 0 ∨ J B = ∅) →
      ‖ConcreteTraceCRT.eisEmbedding z‖^2 ≤ 16 * K * W B^4 →
      (((selY (allocatedLiveSource s hb cover G B) (J B)).filter
        (fun y => (primaryGenerator (∏ j, y j))^4 ∣ z)).card : ℝ) ≤ M B) :
    (∑ u ∈ Us, rawEnergy s ha opposite G hG u τ t K) ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (Atot (allocatedLiveSource s hb cover G B) (J B) τ t *
            ((2:ℝ)^(Fintype.card (J B)) * M B) *
            ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
              ∑ v ∈ V B, Qenergy (restSource (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B))
                ha v (childCharacter τ ξ) t (16 * K * W B^4)) := by
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
        have hW4 : 0 < 16 * K * W B^4 := by have := hW0 B; positivity
        exact summed_live_energy_avg_le (allocatedLiveSource s hb cover G B) (fun _ => rfl) (J B)
          ha Us (V B) hUs (himg B) τ t K (16 * K * W B^4) hK hW4
          (common_scale K (W B) hK _ (J B) (hW B)) (M B) (hM0 B) (hmult B)

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
