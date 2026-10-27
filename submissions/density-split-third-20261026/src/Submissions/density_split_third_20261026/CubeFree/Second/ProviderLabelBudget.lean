/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M provider, part (c): the label part of one side against `balancedBudget`.

* `label_outer_bound` (`hlabel` form): a height-uniform per-split label bound
  `labelAvg B ξ ≤ Λ_B (1+|t|)^{2J}` gives
  `outerAvg … labelAvg ≤ (#B Σ_B ‖w_B‖² AtotP_B 2^{|J_B|} M_B #Ray² Λ_B)(1+|t|)^{2J}`.
* Volume bookkeeping: `alloc_slot_norm_le` (`N(B_i) ≤ 2P_i`), `alloc_common_norm`
  (`N G = plainNorm B · ∏ N(B_i)`), `live_volume_le`
  (`V(renorm r_B) · N G ≤ 2^{|ι|} V(s)`: the extracted live volume is the root volume over the
  first common factor), `rest_volume_mul` (`V(renorm rest_B) · ∏_{J_B} P = V(renorm r_B)`).
* `label_budget`: with the WP-M2 per-split size `Λ_B ≤ K_l · V(renorm rest_B)² · ∏_{J_B}P · N(V₀)`
  (`(vol/c_low)·gAmp·Z^{A-c+q_C+2ε}`, `A - c + q_C = colLog + twistLog + u`, `Z^u = ∏_{J_B}P`) and the
  packed twist identity `N(V₀)·N(opp) ≤ Nτ·N(G)` (`packed_norm_left/right`), the weighted label sum
  is at most `#B²·Mall⁴·pcMass·256^N·2^N·Mc·#Ray²·K_l·4^{|ι|} · Nτ·V²/(N G·N opp)`, i.e. the
  balanced budget's main term. -/
import Submissions.density_split_third_20261026.CubeFree.Second.ProviderRenorm
import Submissions.density_split_third_20261026.CubeFree.Second.ConcreteDiagAssembly3
import Submissions.density_split_third_20261026.CubeFree.Packet.FirstSidePacking

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Provider
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSupport
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open QRH.DensitySplitThird.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiteralAllocation
open MixedTupleRows MixedHeightEnergy MixedOriginalNormCap MixedInnerExceptionalBlock
open MixedFirstLiveSource MixedCommonCoefficient MixedFirstAllocatedRemainders
open QRH.DensitySplitThird.CubeFree.Second.Concrete QRH.DensitySplitThird.CubeFree.Second.ConcreteDiagAssembly
open RayFourExpansion ActualEisensteinCubic
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-! ### Generic residual volume -/

theorem rest_volume_mul {κ : Type*} [Fintype κ] (r : Source κ a b) (hB1 : ∀ k, r.B k = 1)
    (J : Finset κ) :
    sourceVolume (renorm (restSource r hB1 J)) * (∏ j : J, r.P j.val) =
      sourceVolume (renorm r) := by
  rw [sourceVolume_renorm, sourceVolume_renorm]
  have h1 : (∏ i, (restSource r hB1 J).P i) =
      ∏ i ∈ Finset.univ.filter (fun i => i ∉ J), r.P i := by
    rw [Finset.prod_subtype (Finset.univ.filter (fun i => i ∉ J)) (p := fun i => i ∉ J)
      (fun x => by simp)]
    rfl
  have h2 : (∏ j : J, r.P j.val) = ∏ i ∈ Finset.univ.filter (fun i => i ∈ J), r.P i := by
    rw [Finset.prod_coe_sort J (fun i => r.P i)]
    apply Finset.prod_congr (by ext; simp); intro i _; rfl
  have h3 := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ J) (fun i => r.P i)
  unfold sourceVolume
  change r.X₁ * r.X₂ * (∏ i, (restSource r hB1 J).P i) / (nrm r.d.1 * nrm r.d.2) *
    (∏ j : J, r.P j.val) = r.X₁ * r.X₂ * (∏ i, r.P i) / (nrm r.d.1 * nrm r.d.2)
  rw [h1, h2, ← h3]
  ring

/-! ### Allocations -/

section allocations
local instance (priority := 2000) instDecEqSumPLB {κ : Type*} : DecidableEq (κ ⊕ Fin 2) :=
  Classical.decEq _

theorem supportExtract_dvd (I : Id) (hI : I ≠ 0) (S : Finset Id) : supportExtract I S ∣ I := by
  unfold supportExtract
  calc ((UniqueFactorizationMonoid.normalizedFactors I).filter (fun P => P ∈ S)).prod
      ∣ (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
    _ = I := Ideal.prod_normalizedFactors_eq_self hI

theorem alloc_slot_norm_le (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G)
    (i : ι) : (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) ≤ 2 * s.P i := by
  obtain ⟨v, hv, hBv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hvi : v (Sum.inl i) ∈ s.pool i := (Fintype.mem_piFinset.mp hv) (Sum.inl i)
  have hne : v (Sum.inl i) ≠ 0 := (s.hp i _ hvi).ne_zero
  have hdvd : B.val (Sum.inl i) ∣ v (Sum.inl i) := by
    rw [← hBv]; exact supportExtract_dvd _ hne _
  exact (norm_le_of_dvd hne hdvd).trans (s.hpn i _ hvi).2

theorem alloc_common_norm (s : Source ι a b) (G : Id) (B : actualAllocations (tuplePools s) G) :
    (Ideal.absNorm G : ℝ) = plainNorm B.val * ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) := by
  have h := (Finset.mem_filter.mp B.property).2
  have e : (Ideal.absNorm G : ℝ) = (Ideal.absNorm (∏ i, B.val i) : ℝ) := by rw [h]
  rw [e, map_prod, Nat.cast_prod, Fintype.prod_sum_type, Fin.prod_univ_two]
  unfold plainNorm
  ring

/-- **The extracted live volume is the root volume over the first common factor.** -/
theorem live_volume_le (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    sourceVolume (renorm (allocatedLiveSource s hb cover G B)) * (Ideal.absNorm G : ℝ) ≤
      2^(Fintype.card ι) * sourceVolume s := by
  have hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  set r := allocatedLiveSource s hb cover G B
  rw [sourceVolume_renorm, alloc_common_norm s G B]
  have hd1 : r.d.1 = s.d.1 * B.val (Sum.inr 0) := rfl
  have hd2 : r.d.2 = s.d.2 * B.val (Sum.inr 1) := rfl
  have hn1 : nrm r.d.1 = nrm s.d.1 * nrm (B.val (Sum.inr 0)) := by rw [hd1, nrm_mul]
  have hn2 : nrm r.d.2 = nrm s.d.2 * nrm (B.val (Sum.inr 1)) := by rw [hd2, nrm_mul]
  have hs1 := nrm_one_le s.hd.1
  have hs2 := nrm_one_le s.hd.2
  have hb1 := nrm_one_le (hB (Sum.inr 0))
  have hb2 := nrm_one_le (hB (Sum.inr 1))
  have hplain : plainNorm B.val = nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) := rfl
  -- live and frozen slot products
  have hX : 0 < s.X₁ * s.X₂ := mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
  have hvolr : sourceVolume r = s.X₁ * s.X₂ * ∏ i ∈ liveIndices B.val, s.P i := by
    unfold sourceVolume
    change s.X₁ * s.X₂ * (∏ i : liveIndices B.val, s.P i.val) = _
    rw [Finset.prod_coe_sort (liveIndices B.val) s.P]
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => B.val (Sum.inl i) = 1) s.P
  have hfroz : (∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ)) ≤
      2^(Fintype.card ι) * ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i := by
    have hstep : (∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ)) ≤
        ∏ i, (if B.val (Sum.inl i) = 1 then (1:ℝ) else 2 * s.P i) := by
      apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
      intro i _
      split_ifs with h
      · rw [h]; simp
      · exact alloc_slot_norm_le s G B i
    calc (∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ))
        ≤ ∏ i, (if B.val (Sum.inl i) = 1 then (1:ℝ) else 2 * s.P i) := hstep
      _ = ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), 2 * s.P i := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
      _ ≤ _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
          apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _ => by linarith [s.hP i])
          exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)
  have hlive0 : 0 ≤ ∏ i ∈ liveIndices B.val, s.P i :=
    Finset.prod_nonneg fun i _ => by linarith [s.hP i]
  have hlive_eq : liveIndices B.val = Finset.univ.filter (fun i => B.val (Sum.inl i) = 1) := rfl
  rw [hvolr, hn1, hn2, hplain]
  have hden : 0 < nrm s.d.1 * nrm (B.val (Sum.inr 0)) * (nrm s.d.2 * nrm (B.val (Sum.inr 1))) := by
    positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have hV : sourceVolume s = s.X₁ * s.X₂ * ((∏ i ∈ liveIndices B.val, s.P i) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i) := by
    unfold sourceVolume; rw [hlive_eq, hsplit]
  rw [hV]
  have hF0 : 0 ≤ ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i :=
    Finset.prod_nonneg fun i _ => by linarith [s.hP i]
  have hpb : 0 ≤ nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) := by positivity
  have hds : 1 ≤ nrm s.d.1 * nrm s.d.2 := one_le_mul_of_one_le_of_one_le hs1 hs2
  have hN0 : 0 ≤ ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  calc s.X₁ * s.X₂ * (∏ i ∈ liveIndices B.val, s.P i) *
        (nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) *
          ∏ i, (Ideal.absNorm (B.val (Sum.inl i)) : ℝ))
      ≤ s.X₁ * s.X₂ * (∏ i ∈ liveIndices B.val, s.P i) *
        (nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1)) *
          (2^(Fintype.card ι) * ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1),
            s.P i)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hfroz hpb
    _ ≤ 2^(Fintype.card ι) * (s.X₁ * s.X₂ * ((∏ i ∈ liveIndices B.val, s.P i) *
          ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i)) *
        (nrm s.d.1 * nrm (B.val (Sum.inr 0)) * (nrm s.d.2 * nrm (B.val (Sum.inr 1)))) := by
        have hK : 0 ≤ 2^(Fintype.card ι) * (s.X₁ * s.X₂ * ((∏ i ∈ liveIndices B.val, s.P i) *
            ∏ i ∈ Finset.univ.filter (fun i => ¬ B.val (Sum.inl i) = 1), s.P i)) := by
          positivity
        have e : nrm s.d.1 * nrm (B.val (Sum.inr 0)) * (nrm s.d.2 * nrm (B.val (Sum.inr 1))) =
            (nrm s.d.1 * nrm s.d.2) * (nrm (B.val (Sum.inr 0)) * nrm (B.val (Sum.inr 1))) := by
          ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hds (mul_nonneg hK hpb)]

end allocations

/-! ### The `hlabel` form -/

section alloc
local instance (priority := 2000) instDecEqSubtypeLabelBudget {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

theorem labelAvg_nonneg (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b) (cover : OriginalEnclosure s)
    (G : Id) (J : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξr : ℝ)
    (W : actualAllocations (tuplePools s) G → ℝ) (B : actualAllocations (tuplePools s) G)
    (ξ : RayCharacter) : 0 ≤ labelAvg s ha hb cover G J τ χ₀ Q m t K Tsec Z ξr W B ξ := by
  unfold labelAvg; positivity

/-- **`hlabel` from a height-uniform per-split label bound.** -/
theorem label_outer_bound (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (K Tsec Z ξr : ℝ)
    (W M Λ : actualAllocations (tuplePools s) G → ℝ) (J : ℕ) (hM : ∀ B, 0 ≤ M B)
    (hsplit : ∀ B ξ (t : ℝ), labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ ≤
      Λ B * (1 + ‖t‖)^(2*J)) :
    ∀ t : ℝ, outerAvg s hb cover G JB τ t M (labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W) ≤
      (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B))) *
        (1 + ‖t‖)^(2*J) := by
  intro t
  have hT : 0 ≤ (1 + ‖t‖)^(2*J) := by positivity
  unfold outerAvg
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum; intro B _
  have hA := Atot_le (allocatedLiveSource s hb cover G B) (JB B) τ t
  have hA0 := Atot_nonneg (allocatedLiveSource s hb cover G B) (JB B) τ t
  have h2M : 0 ≤ (2:ℝ)^(Fintype.card (JB B)) * M B := mul_nonneg (by positivity) (hM B)
  have hsum : (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
        labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ) ≤
      (Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
        (1 + ‖t‖)^(2*J) := by
    calc (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
          labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ)
        ≤ ∑ _χ : RayCharacter, ∑ _ξ : RayCharacter, Λ B * (1 + ‖t‖)^(2*J) :=
          Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ξ _ => hsplit B ξ t
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hsum0 : 0 ≤ ∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
      labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ :=
    Finset.sum_nonneg fun χ _ => Finset.sum_nonneg fun ξ _ => labelAvg_nonneg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ
  have hAP0 := AtotP_nonneg (allocatedLiveSource s hb cover G B) (JB B)
  have key : Atot (allocatedLiveSource s hb cover G B) (JB B) τ t *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
          labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ)
      ≤ AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
          (1 + ‖t‖)^(2*J)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA h2M) hsum hsum0 (mul_nonneg hAP0 h2M)
  calc ‖allocWeight s G B‖^2 * (Atot (allocatedLiveSource s hb cover G B) (JB B) τ t *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (∑ _χ : RayCharacter, ∑ ξ : RayCharacter,
          labelAvg s ha hb cover G JB τ χ₀ Q m t K Tsec Z ξr W B ξ))
      ≤ ‖allocWeight s G B‖^2 * (AtotP (allocatedLiveSource s hb cover G B) (JB B) *
        ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B *
          (1 + ‖t‖)^(2*J))) := mul_le_mul_of_nonneg_left key (sq_nonneg _)
    _ = _ := by ring

/-! ### The label budget -/

/-- **The label part of one side against the balanced budget's main term.** -/
theorem label_budget (s : Source ι a b) (hb : 0 ≤ b) (cover : OriginalEnclosure s) (G : Id)
    (JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val))
    (M Λ : actualAllocations (tuplePools s) G → ℝ) (N : ℕ) (Mc Kl NV₀ Nopp Nτ : ℝ)
    (hJ : ∀ B, Fintype.card (JB B) ≤ N) (hM : ∀ B, 0 ≤ M B ∧ M B ≤ Mc) (hKl : 0 ≤ Kl)
    (hΛ : ∀ B, Λ B ≤ Kl * sourceVolume (renorm (restOf s hb cover G B (JB B)))^2 *
      (∏ j : JB B, (allocatedLiveSource s hb cover G B).P j.val) * NV₀)
    (hΛ0 : ∀ B, 0 ≤ Λ B) (hNV : 0 ≤ NV₀) (hNopp : 0 < Nopp) (hpack : NV₀ * Nopp ≤ Nτ * (Ideal.absNorm G : ℝ))
    (hG : G ≠ 0) :
    ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) * Λ B)) ≤
      ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ)^2 *
        ((∏ i, s.M i)^2 * (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) *
          ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)) * Kl *
          (4:ℝ)^(Fintype.card ι)) *
        (Nτ * sourceVolume s^2 / ((Ideal.absNorm G : ℝ) * Nopp)) := by
  have hMc : ∀ B : actualAllocations (tuplePools s) G, 0 ≤ Mc := fun B => (hM B).1.trans (hM B).2
  have hGn : 0 < (Ideal.absNorm G : ℝ) := nrm_pos hG
  have hm : 0 ≤ (∏ i, s.M i) := Finset.prod_nonneg fun i _ => zero_le_one.trans (s.hM i)
  have hpc := pcMass_nonneg
  set R2 : ℝ := (Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ)
  have hR2 : 0 ≤ R2 := by positivity
  set Tgt : ℝ := Nτ * sourceVolume s^2 / ((Ideal.absNorm G : ℝ) * Nopp)
  -- per-allocation bound
  have hper : ∀ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
      (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
        (R2 * Λ B)) ≤
      (∏ i, s.M i)^2 * (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) * R2 * Kl *
        (4:ℝ)^(Fintype.card ι) * Tgt := by
    intro B
    set r := allocatedLiveSource s hb cover G B
    set p := ∏ j : JB B, r.P j.val
    set vR := sourceVolume (renorm (restOf s hb cover G B (JB B)))
    set vL := sourceVolume (renorm r)
    have hp := alloc_P_ge s hb cover G JB B
    have hvR0 : 0 ≤ vR := (sourceVolume_pos _).le
    have hvRL : vR * p = vL := rest_volume_mul r (fun _ => rfl) (JB B)
    have hvL := live_volume_le s hb cover G B
    have hvL0 : 0 ≤ vL := (sourceVolume_pos _).le
    have hw : ‖allocWeight s G B‖ ≤ ∏ i, s.M i := frozen_scalar_bound s G B
    have hA := alloc_AtotP_le s hb cover G JB B
    have hA0 := AtotP_nonneg r (JB B)
    have h256 : (256:ℝ)^(Fintype.card (JB B)) ≤ 256^N := pow_le_pow_right₀ (by norm_num) (hJ B)
    have h2 : (2:ℝ)^(Fintype.card (JB B)) * M B ≤ 2^N * Mc :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) (hJ B)) (hM B).2 (hM B).1 (by positivity)
    -- AtotP · Λ ≤ pcM 256^N Kl vL² NV₀
    have hAΛ : AtotP r (JB B) * Λ B ≤
        (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * Kl * (vL^2 * NV₀) := by
      have hΛB := hΛ B
      by_cases hΛn : Λ B ≤ 0
      · have : AtotP r (JB B) * Λ B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0 hΛn
        refine this.trans ?_
        positivity
      push_neg at hΛn
      calc AtotP r (JB B) * Λ B
          ≤ (pcMass * (∏ i, s.M i)^2 * ((256:ℝ)^(Fintype.card (JB B)) * p)) *
              (Kl * vR^2 * p * NV₀) := mul_le_mul hA hΛB hΛn.le (by positivity)
        _ = pcMass * (∏ i, s.M i)^2 * (256:ℝ)^(Fintype.card (JB B)) * Kl * ((vR * p)^2 * NV₀) := by
            ring
        _ ≤ (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * Kl * (vL^2 * NV₀) := by
            rw [hvRL]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ hKl
            exact mul_le_mul_of_nonneg_left h256 (by positivity)
    -- vL² NV₀ ≤ 4^|ι| Tgt
    have hvT : vL^2 * NV₀ ≤ (4:ℝ)^(Fintype.card ι) * Tgt := by
      have e1 : (vL * (Ideal.absNorm G : ℝ))^2 ≤ (2^(Fintype.card ι) * sourceVolume s)^2 :=
        pow_le_pow_left₀ (by positivity) hvL 2
      have hV0 := (sourceVolume_pos s).le
      have e4 : (4:ℝ)^(Fintype.card ι) = (2^(Fintype.card ι))^2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      unfold Tgt
      rw [e4, div_eq_mul_inv]
      have hden : 0 < (Ideal.absNorm G : ℝ) * Nopp := mul_pos hGn hNopp
      rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hden]
      have hpack' : NV₀ * Nopp ≤ Nτ * (Ideal.absNorm G : ℝ) := hpack
      calc vL^2 * NV₀ * ((Ideal.absNorm G : ℝ) * Nopp)
          = (vL * (Ideal.absNorm G : ℝ))^2 / (Ideal.absNorm G : ℝ) * (NV₀ * Nopp) := by
            field_simp
        _ ≤ (2^(Fintype.card ι) * sourceVolume s)^2 / (Ideal.absNorm G : ℝ) *
              (Nτ * (Ideal.absNorm G : ℝ)) :=
            mul_le_mul (div_le_div_of_nonneg_right e1 hGn.le) hpack' (by positivity)
              (by positivity)
        _ = (2^(Fintype.card ι))^2 * (Nτ * sourceVolume s^2) := by field_simp
    have hTgt0 : 0 ≤ (4:ℝ)^(Fintype.card ι) * Tgt := by
      by_cases hz : NV₀ = 0
      · have : (0:ℝ) ≤ vL^2 * NV₀ := by rw [hz, mul_zero]
        exact this.trans hvT
      · exact (mul_nonneg (sq_nonneg _) hNV).trans hvT
    calc ‖allocWeight s G B‖^2 * (AtotP r (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) * (R2 * Λ B))
        = ‖allocWeight s G B‖^2 * ((2:ℝ)^(Fintype.card (JB B)) * M B) * R2 *
            (AtotP r (JB B) * Λ B) := by ring
      _ ≤ (∏ i, s.M i)^2 * ((2:ℝ)^N * Mc) * R2 *
            ((pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * Kl * ((4:ℝ)^(Fintype.card ι) * Tgt)) := by
          have hw2 : ‖allocWeight s G B‖^2 ≤ (∏ i, s.M i)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) hw 2
          apply mul_le_mul _ (hAΛ.trans (mul_le_mul_of_nonneg_left hvT (by positivity)))
            (mul_nonneg hA0 (hΛ0 B))
            (mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (hMc B))) hR2)
          exact mul_le_mul_of_nonneg_right (mul_le_mul hw2 h2 (mul_nonneg (by positivity)
            (hM B).1) (sq_nonneg _)) hR2
      _ = _ := by ring
  calc ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
          (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
            (R2 * Λ B))
      ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
        ∑ _B : actualAllocations (tuplePools s) G,
          (∏ i, s.M i)^2 * (pcMass * (∏ i, s.M i)^2 * (256:ℝ)^N) * ((2:ℝ)^N * Mc) * R2 * Kl *
            (4:ℝ)^(Fintype.card ι) * Tgt :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hper B) (Nat.cast_nonneg _)
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-! ### The packed twist identities (part (b)) -/

theorem modulus_norm_ge (τ η : Character) (e r : O)
    (h : τ.modulus = η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
      Ideal.span {(72:O)} * Ideal.span {e * r}) :
    (Ideal.absNorm (Ideal.span {e}) : ℝ) * (Ideal.absNorm (Ideal.span {r}) : ℝ) ≤
      (Ideal.absNorm τ.modulus : ℝ) := by
  have hne : τ.modulus ≠ ⊥ := τ.modulus_ne_bot
  rw [h] at hne ⊢
  have hX : η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
      Ideal.span {(72:O)} ≠ 0 := left_ne_zero_of_mul hne
  have hX1 := nrm_one_le hX
  set X := η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
    Ideal.span {(72:O)}
  have e1 : (Ideal.absNorm (X * Ideal.span {e * r}) : ℝ) =
      (Ideal.absNorm X : ℝ) * ((Ideal.absNorm (Ideal.span {e}) : ℝ) *
        (Ideal.absNorm (Ideal.span {r}) : ℝ)) := by
    rw [map_mul Ideal.absNorm X, ← Ideal.span_singleton_mul_span_singleton,
      map_mul Ideal.absNorm (Ideal.span {e})]
    push_cast; ring
  rw [e1]
  have h0 : (0:ℝ) ≤ (Ideal.absNorm (Ideal.span {e}) : ℝ) * (Ideal.absNorm (Ideal.span {r}) : ℝ) :=
    by positivity
  unfold nrm at hX1
  nlinarith

/-- **Left packed identity** (CF (3.1)): `N(V_C)·N D ≤ Nτ·N C` (with equality before the
`η`, mask and `72` factors). -/
theorem packed_norm_left (C D : Id) (hC : Supported C) (E : Finset (CommonIndex C D))
    (hcf : Packet.CubeFreeCommon C D) (hcpC : commonPart C D = C) (hcpD : commonPart D C = D)
    (τ η : Character)
    (hmod : τ.modulus = η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
      Ideal.span {(72:O)} * Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        activeConductor C D}) :
    (Ideal.absNorm (Ideal.span {Packet.firstPacked C D hC E}) : ℝ) * (Ideal.absNorm D : ℝ) ≤
      (Ideal.absNorm τ.modulus : ℝ) * (Ideal.absNorm C : ℝ) := by
  have h := Packet.firstPacked_norm C D hC E hcf
  rw [hcpC, hcpD] at h
  have hr : ((Ideal.absNorm (Ideal.span {Packet.firstPacked C D hC E}) : ℝ) * (Ideal.absNorm D : ℝ)) =
      (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) *
        (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) * (Ideal.absNorm C : ℝ) := by
    exact_mod_cast h
  rw [hr]
  exact mul_le_mul_of_nonneg_right (modulus_norm_ge τ η _ _ hmod) (Nat.cast_nonneg _)

/-- **Right packed identity**: `N(V_D)·N C ≤ Nτ·N D`. -/
theorem packed_norm_right (C D : Id) (hC : Supported C) (E : Finset (CommonIndex C D))
    (hcf : Packet.CubeFreeCommon C D) (hcpC : commonPart C D = C) (hcpD : commonPart D C = D)
    (τ η : Character)
    (hmod : τ.modulus = η.modulus * Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} *
      Ideal.span {(72:O)} * Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        activeConductor C D}) :
    (Ideal.absNorm (Ideal.span {Packet.firstPackedRight C D hC E}) : ℝ) * (Ideal.absNorm C : ℝ) ≤
      (Ideal.absNorm τ.modulus : ℝ) * (Ideal.absNorm D : ℝ) := by
  have h := Packet.firstPackedRight_norm C D hC E hcf
  rw [hcpC, hcpD] at h
  have hr : ((Ideal.absNorm (Ideal.span {Packet.firstPackedRight C D hC E}) : ℝ) *
      (Ideal.absNorm C : ℝ)) =
      (Ideal.absNorm (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) : ℝ) *
        (Ideal.absNorm (Ideal.span {activeConductor C D}) : ℝ) * (Ideal.absNorm D : ℝ) := by
    exact_mod_cast h
  rw [hr]
  exact mul_le_mul_of_nonneg_right (modulus_norm_ge τ η _ _ hmod) (Nat.cast_nonneg _)

end alloc

end
end QRH.DensitySplitThird.CubeFree.Second.Provider
