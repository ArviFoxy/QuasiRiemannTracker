/- Copyright (c) 2026 Sil. Apache-2.0.
The source side of the completion chain in leaf-domination form, part 2 (WP-G).

Reduction forms of FP's `MixedAllocatedEnergy.uniform_allocated_energy`,
`MixedUniformAllocated.uniform_allocated_subsets`,
`MixedCommonAllocated.uniform_common_allocated_source`,
`MixedCommonMasked.uniform_common_masked_source`, `MixedCommonSource.uniform_common_source`
and `MixedOriginalSource.uniform_original_source`, on the cube-free forks.

The masses keep every scalar of FP's bounds: the frozen common factor `1/N(G)`, the
centered normalization `1/pairNorm d`, the divisor mask `1/N(D)` (through the selected
divisors of each allocation) and the subpower counts `N(F)^δ`, `N(D)^δ`, `N(G)^δ`. -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.MixedDom
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedCommonSource
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.MixedOriginalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.SilDensitySplit.CubeFree.Packet.Reduce
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open NativeFiniteHoles NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedUniformSource MixedFrozenSource MixedSourceAssembly MixedAllocationCost
open MixedAllocationSource MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedAllocatedEnergy MixedUniformAllocated MixedCommonAllocated MixedDivisorMask
open MixedCommonMasked MixedCommonSource MixedOriginalSource MixedRestrictedDictionary
open MixedFixedSupport
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-! ### Divisor allocations -/

/-- The scalar budget of the bounded labels of one divisor allocation: a subpower of the
common ideal over the selected divisor product. -/
theorem scalar_selected_budget {α : Type*} [Fintype α] (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(S : (α⊕Fin 2)→Finset Id)(F : Id),F≠0 →
    ∀D : Id,∀a : Allocation D (Finset.univ : Finset (α⊕Fin 2)),
      scalarBudget (boundedLabels S F) (fun B=>allocationTerm D Finset.univ B.val a≠0)≤
        C*(F.absNorm:ℝ)^δ/((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := fixed_count_squared (ι:=α⊕Fin 2) δ hδ
  refine ⟨C,hC,?_⟩
  intro S F hF D a
  have hq : 0<((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun j _=>selectedDivisor_ne_zero D Finset.univ a j)))
  set q : ℝ := ((∏j,selectedDivisor D Finset.univ a j).absNorm:ℝ) with hqdef
  have hb : scalarBudget (boundedLabels S F) (fun B=>allocationTerm D Finset.univ B.val a≠0)≤
      ((boundedLabels S F).card:ℝ)^2*(1/q) := by
    unfold scalarBudget
    calc
      _ ≤ ((boundedLabels S F).card:ℝ)*∑_B : boundedLabels S F,(1/q) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro B _
        split_ifs with hn
        · have hB := (allocation_data S F B.val (Finset.mem_filter.mp B.property).1).1
          have hsel := selected_product_norm D a B.val hB hn
          exact one_div_le_one_div_of_le hq hsel
        · exact div_nonneg zero_le_one hq.le
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        ring
  apply hb.trans
  have h := mul_le_mul_of_nonneg_right (hcount S F hF) (div_nonneg zero_le_one hq.le)
  apply h.trans_eq
  ring

/-- **Divisor-allocated rows** (reduction form of
`MixedAllocatedEnergy.uniform_allocated_energy`). -/
theorem allocated_energy_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀D : Id,D∣F →
    ∀allocation : Allocation D (Finset.univ : Finset (α⊕Fin 2)),
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (nativeLeaf M Hray hHray W η₀ θ Z w σ freq t η keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(F.absNorm:ℝ)^δ/pairNorm d/
          ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))
        (radialEnergy (fun z=>allocatedRow (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
          (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd D R allocation
          (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
          (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K) := by
  obtain ⟨C,hC,hbase⟩ := frozen_sum_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap Bmask
    ε lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε
  obtain ⟨Ccount,hCcount,hcount⟩ := scalar_selected_budget (α:=α) δ hδ
  refine ⟨C*Ccount,mul_pos hC hCcount,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R F hR hF H hH
    hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd D hDF allocation
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  let T := sourcePools pool d hd b X₁ X₂ Y₁ Y₂
  let labels := boundedLabels T F
  let active := fun B : labels=>allocationTerm D Finset.univ B.val allocation≠0
  let phase := fun (B : labels)(z : O)=>
    frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val*
    allocationTerm D Finset.univ B.val allocation*
    idealCoeff (naturalCharacter η z) (finiteTupleProduct B.val)
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hlabels (B : labels) : ∀j,B.val j≠0 :=
    (allocation_data T F B.val (Finset.mem_filter.mp B.property).1).1
  have hphase (B : labels) (z : O) : ‖phase B z‖≤1 := by
    have hwB : ‖frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val‖≤1 := by
      unfold frozenWeight
      split_ifs <;> norm_num
    have ht := allocation_term_norm D Finset.univ B.val allocation
    dsimp only [phase]
    rw [norm_mul,norm_mul]
    have hpB : ‖frozenWeight (punctureProduct (enclosure (Cap*Z^Lcap)) H) B.val‖*
        ‖allocationTerm D Finset.univ B.val allocation‖≤1 :=
      (mul_le_mul hwB ht (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul hpB (idealCoeff_norm_le_one _ _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs
    hΦ hkeep R F hR hF H hH hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd labels hlabels active phase
    (fun B z _=>hphase B z)
    (fun B hn z=>actual_phase_zero _ D allocation B.val (not_not.mp hn) (naturalCharacter η z))
    (fun B _ i P hP=>hHR i.val P hP)
  have hrow (z : O) := allocated_row_identity (naturalCharacter η z)
    (enclosure (Cap*Z^Lcap)) H pool hp d hd D F R hF hDF allocation
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
  refine ⟨Lf,hLf,(he.of_eq ?_).mass_le ?_⟩
  · rw [funext hrow]
  · have hb' := hcount T F hF D allocation
    have hZε : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
    have hd' := pairNorm_pos hd.1 hd.2
    have hA : 0≤C*Z^ε/pairNorm d := by positivity
    have h := mul_le_mul_of_nonneg_left hb' hA
    apply h.trans_eq
    ring

/-- **Divisor-allocated rows on every remaining marked subset** (reduction form of
`MixedUniformAllocated.uniform_allocated_subsets`). -/
theorem allocated_subsets_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R F : Id,R≠0 → F≠0 → ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport (R*F)∪holes H,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀T : Finset α,
      (∀i : T,∀P∈H,P.val∈R₀ i.val) → ∀D : Id,D∣F →
    ∀allocation : Allocation D (Finset.univ : Finset (T⊕Fin 2)),
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (nativeLeaf M Hray hHray W η₀ θ Z w σ freq t η keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂)) Lf
        (C*Z^ε*(F.absNorm:ℝ)^δ/pairNorm d/
          ((∏j,selectedDivisor D Finset.univ allocation j).absNorm:ℝ))
        (radialEnergy (fun z=>allocatedRow (naturalCharacter η z) (enclosure (Cap*Z^Lcap)) H
          (fun i : T=>supportedPool (primePool M Hray 2 (Z^(w i.val)))) d hd D R allocation
          (slotCoefficient (fun i : T=>relativeCharacter M Hray hHray η₀ (θ i.val))
            (fun i=>R₀ i.val) t)
          (fun i : T=>slotProfile W (σ i.val) (freq i.val)) (fun i : T=>Z^(w i.val))
          (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂) keep Φ K) := by
  choose CT hCT hbase using fun T : Finset α=>
    allocated_energy_dom M Hray hHray (α:=T) Holes W a b L Lslot Lcap Cap Bmask ε δ lo hi
      hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  let C := 1+∑T : Finset α,CT T
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset α)))=>(hCT T).le)
    dsimp [C]
    linarith
  have hCTC (T : Finset α) : CT T≤C := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CT)
      (fun T _=>(hCT T).le) (Finset.mem_univ T)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R F hR hF H hH
    hcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd T hHR D hDF
    allocation
  obtain ⟨Lf,hLf,he⟩ := hbase T Z hZ η₀ (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
    (fun i=>freq i.val) t (fun i=>R₀ i.val) (fun i=>hw i.val) (fun i=>hwL i.val)
    (fun i=>hσ i.val) (fun i=>hσhi i.val) (fun i=>hR₀ i.val) η keep Φ K radial hK hs hΦ hkeep
    R F hR hF H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY
    d hd D hDF allocation
  refine ⟨Lf,hLf,((he.reindex (fun A=>A.map (Function.Embedding.subtype (fun i=>i∈T)))
    (fun A X₁ X₂=>nativeLeaf_finset M Hray hHray T W η₀ θ Z w σ freq t η keep Φ K W₁ W₂
      (2*Real.pi*t₁) (2*Real.pi*t₂) A X₁ X₂))).mass_le ?_⟩
  have hZε : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hFδ : 0≤(F.absNorm:ℝ)^δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd' := pairNorm_pos hd.1 hd.2
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ hd'.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCTC T) hZε) hFδ

end

end QRH.SilDensitySplit.CubeFree.Packet.Reduce
