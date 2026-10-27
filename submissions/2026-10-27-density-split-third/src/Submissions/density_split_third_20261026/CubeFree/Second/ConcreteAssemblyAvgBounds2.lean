/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the per-allocation counting hypotheses of WP-J's `ConcreteDiagAssembly.diag_budget`, with
explicit uniform constants. Throughout `r_B = allocatedLiveSource s hb cover G B`,
`W_B = slotWidth r_B J_B = ∏_{J_B} 2P_j` (`widthBound_slot`), `M_B ≤ Mc` (e.g. `Mc = Cδ Z^δ`,
`multBound_subpower`), `|J_B| ≤ N`, `W_B ≤ Wmax`, and

  `pcMass = Σ_χ Σ_ξ ‖pairCoeff firstPhaseTable χ ξ‖²`, `Mall = ∏_i M_i`.

* `AtotP_le`: `AtotP r J ≤ pcMass · (∏_J M_j)² · ∏_J 256 P_j` (`|selAmp| ≤ ∏ M_j`; `#pool_j ≤ 256 P_j`
  by the baseline ideal count).
* `hV_bound`: `Σ_{w∈Vset} 1/N w ≤ Hv := 2304 · log X` when the artificial divisors and `poolCap s`
  are `≤ X`, `X ≥ 3`.
* `hself_bound`: `Selmax := pcMass · Mall² · 1024^N · Mc · Wmax^{2/3}` (CF size `Wmax^{2/3}`).
* `hsel0_bound`: `S0 := pcMass·Mall²·256^N·Wmax·(2^N·Mc)·(Wmax⁴·profileCap(s)²·Ymax^{1+ε})`.
* `hselT_bound`: `St := pcMass·Mall²·256^N·Wmax·(2^N·Mc)·(128 X·Wmax·profileCap(s)²)`. -/
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteAssemblyAvgBounds
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteDiagAssembly2
import Submissions.density_split_third_20261026.Analysis.PrimeHarmonic
import Submissions.density_split_third_20261026.CubeFree.FP.MixedPrincipalPoolCaps

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
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedCommonCoefficient
open MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource RepairedFirstRawSides
open MixedOriginalTail MixedFirstAllocatedRemainders MixedPrincipalPoolCaps
open QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
open CenteredMomentAddedZeroUniform GammaDetectorExpansion CenteredMomentFirstColumns
open MixedOriginalNormCap
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-! ### Generic facts -/

theorem prod_comp_le {κ κ' : Type*} [Fintype κ] [Fintype κ'] (f : κ' → κ)
    (hf : Function.Injective f) (g : κ → ℝ) (hg : ∀ i, 1 ≤ g i) :
    (∏ k, g (f k)) ≤ ∏ i, g i := by
  have he : (∏ k, g (f k)) = ∏ i ∈ Finset.univ.map ⟨f, hf⟩, g i := by
    rw [Finset.prod_map]; rfl
  rw [he]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _ => zero_le_one.trans (hg i)) (fun i _ _ => hg i)

theorem norm_le_of_dvd {w I : Id} (hI : I ≠ 0) (h : w ∣ I) :
    (Ideal.absNorm w : ℝ) ≤ Ideal.absNorm I := by
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := right_ne_zero_of_mul hI
  have h1 : (1:ℝ) ≤ Ideal.absNorm c := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hc)
  have h0 : (0:ℝ) ≤ Ideal.absNorm w := Nat.cast_nonneg _
  rw [map_mul, Nat.cast_mul]
  nlinarith

/-- `Σ 1/N I ≤ 2304·log X` over nonzero ideals of norm `≤ X`, `X ≥ 3`. -/
theorem recip_sum_le (X : ℝ) (hX : 3 ≤ X) (F : Finset Id) (hF : ∀ I ∈ F, I ≠ ⊥)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ X) :
    ∑ I ∈ F, 1 / (Ideal.absNorm I : ℝ) ≤ 2304 * Real.log X := by
  have hL := PrimeHarmonic.one_le_log_of_three_le hX
  have ht : 0 ≤ 1 / Real.log X := by positivity
  have hXt : X ^ (1 / Real.log X) ≤ 3 := by
    rw [Real.rpow_def_of_pos (by linarith), show Real.log X * (1 / Real.log X) = 1 by
      field_simp]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hpt : ∀ I ∈ F, 1 / (Ideal.absNorm I : ℝ) ≤
      3 * (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) := by
    intro I hI
    have hn1 : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun h => hF I hI (Ideal.absNorm_eq_zero_iff.mp h))
    have hn0 : 0 < (Ideal.absNorm I : ℝ) := by linarith
    have he : 1 / (Ideal.absNorm I : ℝ) = (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) *
        (Ideal.absNorm I : ℝ) ^ (1 / Real.log X) := by
      rw [← Real.rpow_add hn0, show -(1 + 1 / Real.log X) + 1 / Real.log X = (-1:ℝ) by ring,
        Real.rpow_neg_one, one_div]
    rw [he]
    have h1 : (Ideal.absNorm I : ℝ) ^ (1 / Real.log X) ≤ 3 :=
      (Real.rpow_le_rpow hn0.le (hN I hI) ht).trans hXt
    have h2 : 0 ≤ (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) := Real.rpow_nonneg hn0.le _
    nlinarith
  calc ∑ I ∈ F, 1 / (Ideal.absNorm I : ℝ)
      ≤ ∑ I ∈ F, 3 * (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) := Finset.sum_le_sum hpt
    _ = 3 * ∑ I ∈ F, (Ideal.absNorm I : ℝ) ^ (-(1 + 1 / Real.log X)) := by rw [Finset.mul_sum]
    _ ≤ 3 * (768 * Real.log X) :=
        mul_le_mul_of_nonneg_left (PrimeHarmonic.mass_le_log X hX F hF) (by norm_num)
    _ = 2304 * Real.log X := by ring

/-! ### The selected mass `AtotP` -/

/-- The phase-table mass `Σ_χ Σ_ξ ‖pairCoeff‖²`. -/
def pcMass : ℝ := ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff firstPhaseTable χ ξ‖^2

theorem pcMass_nonneg : 0 ≤ pcMass := by unfold pcMass; positivity

theorem selAmp_norm_le {κ : Type*} [Fintype κ] (r : Source κ a b) (J : Finset κ) (y : J → Id) :
    ‖selAmp r J y‖ ≤ ∏ j : J, r.M j.val := by
  unfold selAmp
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
  intro j _
  rw [norm_mul]
  calc ‖r.ν j.val (y j)‖ * ‖r.Wslot j.val ((Ideal.absNorm (y j) : ℝ) / r.P j.val)‖
      ≤ 1 * r.M j.val := mul_le_mul (r.hν _ _) (r.hWnorm _ _) (norm_nonneg _) zero_le_one
    _ = r.M j.val := one_mul _

theorem selY_card_le {κ : Type*} [Fintype κ] (r : Source κ a b) (J : Finset κ) :
    ((selY r J).card : ℝ) ≤ ∏ j : J, 256 * r.P j.val := by
  rw [Fintype.card_piFinset, Nat.cast_prod]
  apply Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
  intro j _
  have h := PrimeHarmonic.ideal_count (r.pool j.val) (2 * r.P j.val) (by linarith [r.hP j.val])
    (fun I hI => by simpa using (r.hp _ I hI).ne_zero) (fun I hI => (r.hpn _ I hI).2)
  linarith

/-- **`AtotP ≲ ∏_J P_j`.** -/
theorem AtotP_le {κ : Type*} [Fintype κ] (r : Source κ a b) (J : Finset κ) :
    AtotP r J ≤ pcMass * (∏ j : J, r.M j.val)^2 * ∏ j : J, 256 * r.P j.val := by
  have hpc := pcMass_nonneg
  calc AtotP r J = ∑ y ∈ selY r J, pcMass * ‖selAmp r J y‖^2 := by
        unfold AtotP pcMass
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro χ _
        rw [Finset.sum_mul]
    _ ≤ ∑ y ∈ selY r J, pcMass * (∏ j : J, r.M j.val)^2 :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (selAmp_norm_le r J y) 2) hpc
    _ = (selY r J).card * (pcMass * (∏ j : J, r.M j.val)^2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j : J, 256 * r.P j.val) * (pcMass * (∏ j : J, r.M j.val)^2) :=
        mul_le_mul_of_nonneg_right (selY_card_le r J) (by positivity)
    _ = _ := by ring

/-! ### Caps of the residual -/

theorem rest_profile_cap_le {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) : profileCap (restSource r hB1 J) ≤ profileCap r := by
  change 2 * supControl r.W₁ * supControl r.W₂ * (∏ i : Rest J, r.M i.val) ≤
    2 * supControl r.W₁ * supControl r.W₂ * (∏ i, r.M i)
  have h1 := supControl_nonneg r.W₁
  have h2 := supControl_nonneg r.W₂
  exact mul_le_mul_of_nonneg_left (prod_comp_le Subtype.val Subtype.val_injective r.M r.hM)
    (by positivity)

theorem rest_pool_cap_le {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) : poolCap (restSource r hB1 J) ≤ poolCap r := by
  unfold poolCap
  have hV : 0 ≤ (128*b)^2*(r.X₁+r.Y₁)*(r.X₂+r.Y₂) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg
      (r.hL.trans_le r.hX₁).le (r.hL.trans_le r.hY₁).le))
      (add_nonneg (r.hL.trans_le r.hX₂).le (r.hL.trans_le r.hY₂).le)
  apply mul_le_mul_of_nonneg_left
  · exact prod_comp_le Subtype.val Subtype.val_injective (fun i => 256 * r.P i)
      (fun i => by linarith [r.hP i])
  · exact div_nonneg hV (by unfold QRH.Record1252270103KernelMass.pairNorm; positivity)

local instance (priority := 2000) instDecEqSubtypeBounds2 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

theorem restOf_profile_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    profileCap (restOf s hb cover G B J) ≤ profileCap s :=
  (rest_profile_cap_le _ _ _).trans (live_profile_cap_le (allocationSource s hb cover G B))

theorem restOf_pool_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val)) :
    poolCap (restOf s hb cover G B J) ≤ poolCap s :=
  (rest_pool_cap_le _ _ _).trans (live_pool_cap_le (allocationSource s hb cover G B))

/-! ### The seed set: norms, count, reciprocal mass -/

theorem Vset_norm_le {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) (Us : Finset Id) (hb : 0 ≤ b) (hUs : ∀ u ∈ Us, Squarefree u) (X : ℝ)
    (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X) (hPX : poolCap (restSource r hB1 J) ≤ X) :
    ∀ w ∈ Vset r hB1 J Us, (Ideal.absNorm w : ℝ) ≤ X := by
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    have hu := (Finset.mem_product.mp hp).1
    have hd : seedRest p.1 (∏ j, p.2 j) ∣ p.1 := by
      unfold seedRest
      conv_rhs => rw [← IdealMobiusDivisorSum.squarefree_support_product_self (hUs p.1 hu)]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact (norm_le_of_dvd (hUs p.1 hu).ne_zero hd).trans (hUX p.1 hu)
  · obtain ⟨I, hI, hwI⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hne : finiteTupleProduct v ≠ 0 := finiteTupleProduct_ne_zero_of_mem _ v hv
    have hne' : finiteTupleProduct v ≠ ⊥ := hne
    have hdvd : w ∣ finiteTupleProduct v :=
      (IdealMobiusDivisorSum.mem_idealDivisors hne').mp (Finset.mem_filter.mp hwI).1
    exact (norm_le_of_dvd hne hdvd).trans
      ((source_column_pool_norm (restSource r hB1 J) hb _ hI).trans hPX)

theorem Vset_ne_bot {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) (Us : Finset Id) : ∀ w ∈ Vset r hB1 J Us, w ≠ ⊥ :=
  fun w hw => (Vset_squarefree r hB1 J Us w hw).ne_zero

theorem Vset_alloc_norm_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (hUs : ∀ u ∈ Us, Squarefree u) (X : ℝ) (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X)
    (hPX : poolCap s ≤ X) (B : actualAllocations (tuplePools s) G) :
    ∀ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
      (Ideal.absNorm w : ℝ) ≤ X :=
  Vset_norm_le _ _ _ Us hb hUs X hUX ((restOf_pool_le s hb cover G B (JB B)).trans hPX)

/-- **`hV`** with `Hv = 2304·log X`. -/
theorem hV_bound (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (hUs : ∀ u ∈ Us, Squarefree u) (X : ℝ) (hX : 3 ≤ X)
    (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X) (hPX : poolCap s ≤ X) :
    ∀ B, ∑ w ∈ Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us,
      1 / (w.absNorm : ℝ) ≤ 2304 * Real.log X :=
  fun B => recip_sum_le X hX _ (Vset_ne_bot _ _ _ Us)
    (Vset_alloc_norm_le s hb cover G JB Us hUs X hUX hPX B)

theorem Vset_card_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val)) (Us : Finset Id)
    (hUs : ∀ u ∈ Us, Squarefree u) (X : ℝ) (hX : 1 ≤ X)
    (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X) (hPX : poolCap s ≤ X)
    (B : actualAllocations (tuplePools s) G) :
    ((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card : ℝ) ≤ 128 * X :=
  PrimeHarmonic.ideal_count _ X hX (Vset_ne_bot _ _ _ Us)
    (Vset_alloc_norm_le s hb cover G JB Us hUs X hUX hPX B)

/-! ### Per-allocation uniform bounds -/

/-! ### The residual norm cap: exact relation -/

theorem normCap_nonneg {κ : Type*} [Fintype κ] (r : Source κ a b) :
    0 ≤ sourceNormCap r.P b r.T r.d := by
  unfold sourceNormCap
  rw [← r.hpX]
  have h1 := r.hL.trans_le r.hX₁
  have h2 := r.hL.trans_le r.hX₂
  have hpn : (0:ℝ) ≤ QRH.Record1252270103KernelMass.pairNorm r.d := by
    unfold QRH.Record1252270103KernelMass.pairNorm; positivity
  exact mul_nonneg (mul_nonneg (sq_nonneg b) (div_nonneg (mul_nonneg h1.le h2.le) hpn))
    (Finset.prod_nonneg fun i _ => by linarith [r.hP i])

/-- **Exact relation**: removing the selected slots divides the norm cap by `∏_J 2P_j`:
`sourceNormCap(rest) · slotWidth r J = sourceNormCap(r)`. -/
theorem rest_normCap_mul {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) :
    sourceNormCap (restSource r hB1 J).P b (restSource r hB1 J).T (restSource r hB1 J).d *
      slotWidth r J = sourceNormCap r.P b r.T r.d := by
  have h1 : (∏ i, 2 * (restSource r hB1 J).P i) =
      ∏ i ∈ Finset.univ.filter (fun i => i ∉ J), 2 * r.P i := by
    rw [Finset.prod_subtype (Finset.univ.filter (fun i => i ∉ J)) (p := fun i => i ∉ J)
      (fun x => by simp)]
    rfl
  have h2 : (∏ j : J, 2 * r.P j.val) = ∏ i ∈ Finset.univ.filter (fun i => i ∈ J), 2 * r.P i := by
    rw [Finset.prod_coe_sort J (fun i => 2 * r.P i)]
    apply Finset.prod_congr (by ext; simp); intro i _; rfl
  have h3 := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ J)
    (fun i => 2 * r.P i)
  unfold sourceNormCap slotWidth
  change b^2*(r.T/QRH.Record1252270103KernelMass.pairNorm r.d)*(∏ i, 2 * (restSource r hB1 J).P i) *
    (∏ j : J, 2 * r.P j.val) = b^2*(r.T/QRH.Record1252270103KernelMass.pairNorm r.d)*∏ i, 2 * r.P i
  rw [h1, h2, ← h3]
  ring

section alloc
variable (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
  (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))

theorem alloc_M_le (B : actualAllocations (tuplePools s) G) :
    (∏ j : JB B, (allocatedLiveSource s hb cover G B).M j.val) ≤ ∏ i, s.M i :=
  prod_comp_le (fun j : JB B => j.val.val)
    (Subtype.val_injective.comp Subtype.val_injective) s.M s.hM

theorem alloc_M_nonneg (B : actualAllocations (tuplePools s) G) :
    0 ≤ ∏ j : JB B, (allocatedLiveSource s hb cover G B).M j.val :=
  Finset.prod_nonneg fun j _ => zero_le_one.trans (s.hM j.val.val)

theorem alloc_P_ge (B : actualAllocations (tuplePools s) G) :
    1 ≤ ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val := by
  have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (JB B))) (f := fun _ => (1:ℝ))
    (g := fun j => (allocatedLiveSource s hb cover G B).P j.val) (fun _ _ => zero_le_one)
    (fun j _ => show (1:ℝ) ≤ (allocatedLiveSource s hb cover G B).P j.val from s.hP j.val.val)
  simpa using h

theorem alloc_slotWidth_eq (B : actualAllocations (tuplePools s) G) :
    slotWidth (allocatedLiveSource s hb cover G B) (JB B) =
      (2:ℝ)^(Fintype.card (JB B)) * ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val := by
  unfold slotWidth
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rfl

theorem alloc_P_le_W (B : actualAllocations (tuplePools s) G) :
    (∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) ≤
      slotWidth (allocatedLiveSource s hb cover G B) (JB B) := by
  rw [alloc_slotWidth_eq]
  have := alloc_P_ge s hb cover G JB B
  exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))

theorem alloc_AtotP_le (B : actualAllocations (tuplePools s) G) :
    AtotP (allocatedLiveSource s hb cover G B) (JB B) ≤
      pcMass * (∏ i, s.M i)^2 * ((256:ℝ)^(Fintype.card (JB B)) *
        ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) := by
  refine (AtotP_le _ _).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hm0 := alloc_M_nonneg s hb cover G JB B
  have hm := alloc_M_le s hb cover G JB B
  have hp := alloc_P_ge s hb cover G JB B
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hm 2) pcMass_nonneg

/-- The uniform selected weight `AtotP·2^{|J|}·M ≤ pcMass·Mall²·256^N·Wmax·(2^N·Mc)`. -/
theorem alloc_weight_le (M : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Wmax : ℝ)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hW : ∀ B, slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ Wmax)
    (B : actualAllocations (tuplePools s) G) :
    AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax * ((2:ℝ)^N * Mc) := by
  have hp := alloc_P_ge s hb cover G JB B
  have hpW := (alloc_P_le_W s hb cover G JB B).trans (hW B)
  have hpc := pcMass_nonneg
  have h256 : (256:ℝ)^(Fintype.card (JB B)) ≤ 256^N := pow_le_pow_right₀ (by norm_num) (hJ B)
  have h2 : (2:ℝ)^(Fintype.card (JB B)) ≤ 2^N := pow_le_pow_right₀ (by norm_num) (hJ B)
  have hA : AtotP (allocatedLiveSource s hb cover G B) (JB B) ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax := by
    refine (alloc_AtotP_le s hb cover G JB B).trans ?_
    rw [mul_assoc (pcMass * (∏ i, s.M i)^2)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h256 hpW (by linarith) (by positivity))
      (by positivity)
  have hMc : 0 ≤ Mc := (hM B).1.trans (hM B).2
  exact mul_le_mul hA (mul_le_mul h2 (hM B).2 (hM B).1 (by positivity))
    (mul_nonneg (by positivity) (hM B).1)
    (by have : 0 ≤ Wmax := (by linarith : (0:ℝ) ≤ 1).trans (hp.trans hpW); positivity)

/-- **`hself`** with `Selmax = pcMass·Mall²·1024^N·Mc·Wmax^{2/3}`. -/
theorem hself_bound (M : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Wmax : ℝ)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hW : ∀ B, slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ Wmax) :
    ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        slotWidth (allocatedLiveSource s hb cover G B) (JB B) *
        ((∏ j ∈ JB B, s.P j.val)^(4/3:ℝ))⁻¹ ≤
      pcMass * (∏ i, s.M i)^2 * (1024:ℝ)^N * Mc * Wmax^(2/3:ℝ) := by
  intro B
  set c := Fintype.card (JB B)
  set p := ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val with hpdef
  have hpE : (∏ j ∈ JB B, s.P j.val) = p :=
    (Finset.prod_coe_sort (JB B) (fun j => s.P j.val)).symm
  have hp := alloc_P_ge s hb cover G JB B
  have hp0 : 0 < p := by linarith
  have hpW := (alloc_P_le_W s hb cover G JB B).trans (hW B)
  have hpc := pcMass_nonneg
  have hMc : 0 ≤ Mc := (hM B).1.trans (hM B).2
  have hA := alloc_AtotP_le s hb cover G JB B
  have hm : 0 ≤ (∏ i, s.M i) := Finset.prod_nonneg fun i _ => zero_le_one.trans (s.hM i)
  rw [hpE, alloc_slotWidth_eq]
  have hq : 0 ≤ (2:ℝ)^c * p * (p^(4/3:ℝ))⁻¹ := by
    have := Real.rpow_nonneg hp0.le (4/3:ℝ); positivity
  have hpp : p * p * (p^(4/3:ℝ))⁻¹ = p^(2/3:ℝ) := by
    rw [← Real.rpow_neg hp0.le, show p * p = p^(2:ℝ) by rw [Real.rpow_two, sq],
      ← Real.rpow_add hp0]
    norm_num
  calc AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^c * M B) * ((2:ℝ)^c * p) *
        (p^(4/3:ℝ))⁻¹
      = (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^c * M B)) *
          ((2:ℝ)^c * p * (p^(4/3:ℝ))⁻¹) := by ring
    _ ≤ ((pcMass * (∏ i, s.M i)^2 * ((256:ℝ)^c * p)) * ((2:ℝ)^c * Mc)) *
          ((2:ℝ)^c * p * (p^(4/3:ℝ))⁻¹) := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul hA (mul_le_mul_of_nonneg_left (hM B).2 (by positivity))
          (mul_nonneg (by positivity) (hM B).1) (by positivity)
    _ = pcMass * (∏ i, s.M i)^2 * ((256:ℝ)^c * 2^c * 2^c) * Mc * (p * p * (p^(4/3:ℝ))⁻¹) := by
        ring
    _ = pcMass * (∏ i, s.M i)^2 * (1024:ℝ)^c * Mc * p^(2/3:ℝ) := by
        rw [hpp, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ pcMass * (∏ i, s.M i)^2 * (1024:ℝ)^N * Mc * Wmax^(2/3:ℝ) := by
        apply mul_le_mul _ (Real.rpow_le_rpow hp0.le hpW (by norm_num))
          (Real.rpow_nonneg hp0.le _) (by positivity)
        apply mul_le_mul_of_nonneg_right _ hMc
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hJ B)) (by positivity)

/-- **`hsel0`** with `S0 = pcMass·Mall²·256^N·Wmax·(2^N·Mc)·(Wmax⁴·profileCap(s)²·Ymax^{1+ε})`. -/
theorem hsel0_bound (M Y : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Wmax Ymax ε : ℝ)
    (hε : 0 ≤ 1 + ε) (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hW : ∀ B, slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ Wmax)
    (hY : ∀ B, 0 ≤ Y B ∧ Y B ≤ Ymax) :
    ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
          (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B)^(1+ε)) ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax * ((2:ℝ)^N * Mc) *
        (Wmax^4 * (profileCap s)^2 * Ymax^(1+ε)) := by
  intro B
  have hW0 := (slotWidth_pos (allocatedLiveSource s hb cover G B) (JB B)).le
  have hpr0 := profileCap_nonneg (restOf s hb cover G B (JB B))
  have hpr := restOf_profile_le s hb cover G B (JB B)
  have hY0 := (hY B).1
  have hf : slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
        (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B)^(1+ε) ≤
      Wmax^4 * (profileCap s)^2 * Ymax^(1+ε) :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ hW0 (hW B) 4) (pow_le_pow_left₀ hpr0 hpr 2)
      (sq_nonneg _) (by positivity)) (Real.rpow_le_rpow hY0 (hY B).2 hε)
      (Real.rpow_nonneg hY0 _) (by positivity)
  have hw := alloc_weight_le s hb cover G JB M N Mc Wmax hJ hM hW B
  have hMc : 0 ≤ Mc := (hM B).1.trans (hM B).2
  have hWm : 0 ≤ Wmax := hW0.trans (hW B)
  exact mul_le_mul hw hf (by have := Real.rpow_nonneg hY0 (1+ε); positivity)
    (by have := pcMass_nonneg; positivity)

/-- **`hselT`** with `St = pcMass·Mall²·256^N·Wmax·(2^N·Mc)·(128 X·Wmax·profileCap(s)²)`. -/
theorem hselT_bound (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u) (X : ℝ) (hX : 1 ≤ X)
    (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ X) (hPX : poolCap s ≤ X)
    (M : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Wmax : ℝ)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hW : ∀ B, slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ Wmax) :
    ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card : ℝ) *
          slotWidth (allocatedLiveSource s hb cover G B) (JB B) *
          (profileCap (restOf s hb cover G B (JB B)))^2) ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax * ((2:ℝ)^N * Mc) *
        (128 * X * Wmax * (profileCap s)^2) := by
  intro B
  have hW0 := (slotWidth_pos (allocatedLiveSource s hb cover G B) (JB B)).le
  have hWm : 0 ≤ Wmax := hW0.trans (hW B)
  have hpr0 := profileCap_nonneg (restOf s hb cover G B (JB B))
  have hpr := restOf_profile_le s hb cover G B (JB B)
  have hc := Vset_card_le s hb cover G JB Us hUs X hX hUX hPX B
  have hf : ((Vset (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B) Us).card : ℝ) *
        slotWidth (allocatedLiveSource s hb cover G B) (JB B) *
        (profileCap (restOf s hb cover G B (JB B)))^2 ≤
      128 * X * Wmax * (profileCap s)^2 :=
    mul_le_mul (mul_le_mul hc (hW B) hW0 (by linarith)) (pow_le_pow_left₀ hpr0 hpr 2)
      (sq_nonneg _) (mul_nonneg (by linarith) hWm)
  have hw := alloc_weight_le s hb cover G JB M N Mc Wmax hJ hM hW B
  have hMc : 0 ≤ Mc := (hM B).1.trans (hM B).2
  exact mul_le_mul hw hf (by positivity) (by have := pcMass_nonneg; positivity)

/-- The full slot width `∏_i 2P_i` is an admissible `Wmax`. -/
theorem slotWidth_le_full (B : actualAllocations (tuplePools s) G) :
    slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ ∏ i, 2 * s.P i :=
  prod_comp_le (fun j : JB B => j.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    (fun i => 2 * s.P i) (fun i => by linarith [s.hP i])

/-- **`hsel0` with the residual cap.** WP-J needs `sourceNormCap(rest_B) ≤ Y_B` and `1 ≤ Y_B`;
take `Y_B = max 1 (sourceNormCap rest_B)`, so `Y_B ≤ 1 + sourceNormCap(r_B)/W_B` and
`AtotP_B·Y_B ≲ Wmax + Yr`, with `Yr ≥ sourceNormCap(r_B)` the live (allocated) cap:
`S0 = pcMass·Mall²·256^N·(Wmax + Yr)·(2^N·Mc)·(Wmax⁴·profileCap(s)²·Yup^ε)`. -/
theorem hsel0_bound_rest (M Y : actualAllocations (tuplePools s) G → ℝ) (N : ℕ)
    (Mc Wmax Yr Yup ε : ℝ) (hε : 0 ≤ ε) (hJ : ∀ B, Fintype.card (JB B) ≤ N)
    (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc)
    (hW : ∀ B, slotWidth (allocatedLiveSource s hb cover G B) (JB B) ≤ Wmax)
    (hYr : ∀ B, sourceNormCap (allocatedLiveSource s hb cover G B).P b
      (allocatedLiveSource s hb cover G B).T (allocatedLiveSource s hb cover G B).d ≤ Yr)
    (hY : ∀ B, 1 ≤ Y B ∧ Y B ≤ Yup ∧
      Y B ≤ 1 + sourceNormCap (restOf s hb cover G B (JB B)).P b
        (restOf s hb cover G B (JB B)).T (restOf s hb cover G B (JB B)).d) :
    ∀ B, AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
          (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B)^(1+ε)) ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * (Wmax + Yr) * ((2:ℝ)^N * Mc) *
        (Wmax^4 * (profileCap s)^2 * Yup^ε) := by
  intro B
  have hY1 := (hY B).1
  have hY0 : 0 < Y B := by linarith
  have hp := alloc_P_ge s hb cover G JB B
  have hp0 : 0 < ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val := by linarith
  have hW0 := (slotWidth_pos (allocatedLiveSource s hb cover G B) (JB B)).le
  have hWm : 0 ≤ Wmax := hW0.trans (hW B)
  have hpW := (alloc_P_le_W s hb cover G JB B).trans (hW B)
  have hpc := pcMass_nonneg
  have hm : 0 ≤ (∏ i, s.M i) := Finset.prod_nonneg fun i _ => zero_le_one.trans (s.hM i)
  have hMc : 0 ≤ Mc := (hM B).1.trans (hM B).2
  have hA := alloc_AtotP_le s hb cover G JB B
  have hA0 := AtotP_nonneg (allocatedLiveSource s hb cover G B) (JB B)
  have hrel : sourceNormCap (restOf s hb cover G B (JB B)).P b
        (restOf s hb cover G B (JB B)).T (restOf s hb cover G B (JB B)).d *
        ((2:ℝ)^(Fintype.card (JB B)) * ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) =
      sourceNormCap (allocatedLiveSource s hb cover G B).P b
        (allocatedLiveSource s hb cover G B).T (allocatedLiveSource s hb cover G B).d := by
    rw [← alloc_slotWidth_eq]
    exact rest_normCap_mul (allocatedLiveSource s hb cover G B) (fun _ => rfl) (JB B)
  have hYr0 := normCap_nonneg (allocatedLiveSource s hb cover G B)
  have hYrest0 := normCap_nonneg (restOf s hb cover G B (JB B))
  have h256 : (256:ℝ)^(Fintype.card (JB B)) ≤ 256^N := pow_le_pow_right₀ (by norm_num) (hJ B)
  have h128 : (128:ℝ)^(Fintype.card (JB B)) ≤ 256^N :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num : (128:ℝ) ≤ 256) _).trans h256
  have hAY : AtotP (allocatedLiveSource s hb cover G B) (JB B) * Y B ≤
      pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * (Wmax + Yr) := by
    have e1 := mul_le_mul_of_nonneg_left (hY B).2.2 hA0
    have e2 : AtotP (allocatedLiveSource s hb cover G B) (JB B) ≤
        pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Wmax := by
      refine hA.trans ?_
      rw [mul_assoc (pcMass * (∏ i, s.M i)^2)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h256 hpW hp0.le (by positivity)) (by positivity)
    have e3 : AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        sourceNormCap (restOf s hb cover G B (JB B)).P b
          (restOf s hb cover G B (JB B)).T (restOf s hb cover G B (JB B)).d ≤
        pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Yr := by
      refine (mul_le_mul_of_nonneg_right hA hYrest0).trans ?_
      rw [show (256:ℝ)^(Fintype.card (JB B)) = 128^(Fintype.card (JB B)) * 2^(Fintype.card (JB B)) by
        rw [← mul_pow]; norm_num]
      calc pcMass * (∏ i, s.M i)^2 * ((128:ℝ)^(Fintype.card (JB B)) * 2^(Fintype.card (JB B)) *
            ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) *
            sourceNormCap (restOf s hb cover G B (JB B)).P b
              (restOf s hb cover G B (JB B)).T (restOf s hb cover G B (JB B)).d
          = pcMass * (∏ i, s.M i)^2 * (128:ℝ)^(Fintype.card (JB B)) *
              (sourceNormCap (restOf s hb cover G B (JB B)).P b
                (restOf s hb cover G B (JB B)).T (restOf s hb cover G B (JB B)).d *
              ((2:ℝ)^(Fintype.card (JB B)) *
                ∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val)) := by ring
        _ = pcMass * (∏ i, s.M i)^2 * (128:ℝ)^(Fintype.card (JB B)) *
              sourceNormCap (allocatedLiveSource s hb cover G B).P b
                (allocatedLiveSource s hb cover G B).T (allocatedLiveSource s hb cover G B).d := by
            rw [hrel]
        _ ≤ pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * Yr :=
            mul_le_mul (mul_le_mul_of_nonneg_left h128 (by positivity)) (hYr B) hYr0
              (by positivity)
    nlinarith
  have hYe : (Y B)^(1+ε) = Y B * (Y B)^ε := by
    rw [Real.rpow_add hY0, Real.rpow_one]
  have hYε := Real.rpow_nonneg hY0.le ε
  have hpr0 := profileCap_nonneg (restOf s hb cover G B (JB B))
  have hf : slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
        (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B)^ε ≤
      Wmax^4 * (profileCap s)^2 * Yup^ε :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ hW0 (hW B) 4)
      (pow_le_pow_left₀ hpr0 (restOf_profile_le s hb cover G B (JB B)) 2)
      (sq_nonneg _) (by positivity)) (Real.rpow_le_rpow hY0.le (hY B).2.1 hε)
      hYε (by positivity)
  have h2M : (2:ℝ)^(Fintype.card (JB B)) * M B ≤ 2^N * Mc :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) (hJ B)) (hM B).2 (hM B).1 (by positivity)
  rw [hYe]
  calc AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
          (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B * (Y B)^ε))
      = (AtotP (allocatedLiveSource s hb cover G B) (JB B) * Y B) *
          ((2:ℝ)^(Fintype.card (JB B)) * M B) *
          (slotWidth (allocatedLiveSource s hb cover G B) (JB B)^4 *
            (profileCap (restOf s hb cover G B (JB B)))^2 * (Y B)^ε) := by ring
    _ ≤ (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N * (Wmax + Yr)) * ((2:ℝ)^N * Mc) *
          (Wmax^4 * (profileCap s)^2 * Yup^ε) :=
        mul_le_mul (mul_le_mul hAY h2M (mul_nonneg (by positivity) (hM B).1)
          (by have := hYr0.trans (hYr B); positivity)) hf (by positivity)
          (by have := hYr0.trans (hYr B); positivity)

end alloc

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
