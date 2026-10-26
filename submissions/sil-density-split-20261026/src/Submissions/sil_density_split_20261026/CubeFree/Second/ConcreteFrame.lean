/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, item 2: the concrete second-step labels as `Packet.Grouped.GLabel`s with all `Fits`
fields (CF §§3, 5; CPL §3).

* `second_packed_child` (+ `_right`): the variant of `Packet.Dictionary.second_packed` for the
  base character `childCharacter F.left ξ` of the residual after the D⁴ transfer
  (`ConcreteResidual4.residual_transfer`): on supported columns coprime to the first-step
  exponent-zero primes and to `C₂` (or `D₂`),
    `h_{τχ}(t, I) = h_{anchors η (ξ₁·firstPhase·ξ·χ)}(t, I) · χ_I(V_C·A₂)`.
* CONTRACT MISMATCH and its resolution. `Fits` asks both `coef` (the packing off the mask)
  and `G_mask : (G, I) = 1 → (I, mask) = 1`, i.e. the mask may only contain primes of the
  genuine second common factor `G = C₂`. The packing of the actual character `τχ` fails at the
  first-step exponent-zero primes `Z₀` (`firstZeroPrimes C D`), which are coprime to `C₂`;
  so `Fits` can NOT hold for the label with the literal character `τχ` (any admissible mask
  would have to contain `Z₀`). It does hold for its PACKED TWIN `packedChar η j (V₀A₂)`
  (a genuine Hecke character, from OAI `exists_second_family`, whose coefficients are
  `anchors η j · χ_I(V₀A₂)` on EVERY supported ideal), with mask `1`. The twin and `τχ` have
  the same literal label energy whenever the residual columns are coprime to `Z₀`
  (`labelEnergy_packed`): their coefficients agree on supported columns coprime to
  `packMask Z₀ C₂`, the keep sets agree (`Packet.keep_transfer`, mask multiplication), and
  every residual column with a nonzero coefficient is coprime to `C₂` (residual pool) and,
  by hypothesis, to `Z₀` (the residual of the first common factor is coprime to it).
* `LabelData.toLabel`, `toLabel_fits`: the label with the twin character, all `Fits`
  fields; `G_cap`, `D_cap` from the radical cap (`ConcreteCaps`); `rawEnergy_toLabel`: its
  frame energy is the literal label energy of `τχ`. -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedFrame
import Submissions.sil_density_split_20261026.CubeFree.Packet.Dictionary
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open NativeFiniteHoles NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedCommonSource MixedOriginalSource MixedRestrictedDictionary MixedHeightEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyChildState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergySlotHeight
open CenteredMomentEnergyAllocatedChildren CenteredMomentLattice CenteredMomentTwist
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentHeckeExpansion
open CanonicalRowCompletion CompletedGauss RayFourExpansion CenteredMomentFirstPhysicalSource
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows
local notation "O" => HeckeFamily.O

/-! ### 1. The packed dictionary for the child base character -/

theorem heightCoeff_child (τ : Character) (ξ : RayCharacter) (t : ℝ) (I : Ideal O)
    (hI : Supported I) :
    heightCoeff (childCharacter τ ξ) t I =
      heightCoeff τ t I * rayCharacter ξ (primaryGenerator I) := by
  unfold heightCoeff
  rw [CenteredMomentSecondChildProfile.child_ideal_primary τ ξ I hI]
  ring

/-- Dictionary index of a second label on the left residual with D⁴-transfer ray `ξ`. -/
def childIdx (C D : Ideal O) (hC : Supported C) (ξ₁ ξ χ : RayCharacter) : DictIdx :=
  ξ₁ * firstPhase C D hC * ξ * χ

/-- Dictionary index of a second label on the right residual. -/
def childIdxRight (C D : Ideal O) (hC : Supported C) (ξ₂ ξ χ : RayCharacter) : DictIdx :=
  ξ₂ * firstPhase C D hC * ξ * χ

section Left
variable {η : Character} {C D : Ideal O} {hC : Supported C} {E : Finset (CommonIndex C D)}
  {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) (ξ : RayCharacter)
  {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂} {U : Finset (CommonIndex C₂ D₂)}
  {τ : RayCharacter → Character}

/-- **Second-step packing for the child base (left).** -/
theorem second_packed_child (h : Family (childCharacter F.left ξ) C₂ D₂ hC₂ hD₂ U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I (firstZeroPrimes C D))
    (hi : IsCoprime C₂ I ∨ IsCoprime D₂ I) (t : ℝ) :
    heightCoeff (τ χ) t I =
      heightCoeff (anchors η (childIdx C D hC ξ₁ ξ χ)) t I *
        idealRowHom (leftRow C D hC E C₂ D₂ U) I := by
  rw [h.height_eq χ I hI hi t, heightCoeff_child F.left ξ t I hI, left_packed F I hI hZ t,
    anchors, childIdx, rayAnchor_mul_height η _ χ I hI t, rayAnchor_mul_height η _ ξ I hI t,
    leftRow, secondTwist]
  simp only [idealRowHom_argument_mul]
  ring

end Left

section Right
variable {η : Character} {C D : Ideal O} {hC : Supported C} {E : Finset (CommonIndex C D)}
  {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) (ξ : RayCharacter)
  {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂} {U : Finset (CommonIndex C₂ D₂)}
  {τ : RayCharacter → Character}

/-- **Second-step packing for the child base (right).** -/
theorem second_packed_child_right (h : Family (childCharacter F.right ξ) C₂ D₂ hC₂ hD₂ U τ)
    (χ : RayCharacter) (I : Ideal O) (hI : Supported I)
    (hZ : IsCoprime I (firstZeroPrimesRight C D))
    (hi : IsCoprime C₂ I ∨ IsCoprime D₂ I) (t : ℝ) :
    heightCoeff (τ χ) t I =
      heightCoeff (anchors η (childIdxRight C D hC ξ₂ ξ χ)) t I *
        idealRowHom (rightRow C D hC E C₂ D₂ U) I := by
  rw [h.height_eq χ I hI hi t, heightCoeff_child F.right ξ t I hI, right_packed F I hI hZ t,
    anchors, childIdxRight, rayAnchor_mul_height η _ χ I hI t, rayAnchor_mul_height η _ ξ I hI t,
    rightRow, secondTwist]
  simp only [idealRowHom_argument_mul]
  ring

end Right

/-! ### 2. The packed twin character -/

/-- The packed twin: a Hecke character with coefficients `anchors η j · χ_I(V)` on every
supported ideal. -/
def packedChar (η : Character) (j : DictIdx) (V : O) : Character :=
  if hV : V ≠ 0 then Classical.choose (exists_second_family (anchors η j) 1 V hV)
  else anchors η j

theorem packedChar_height (η : Character) (j : DictIdx) (V : O) (hV : V ≠ 0) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    heightCoeff (packedChar η j V) t I = heightCoeff (anchors η j) t I * idealRowHom V I := by
  have hspec := (Classical.choose_spec (exists_second_family (anchors η j) 1 V hV)).2 I hI t
  have hone : heightCoeff (anchors η j) t I * rayCharacter 1 (primaryGenerator I) =
      heightCoeff (anchors η j) t I := by
    have h := rayAnchor_mul_height η j 1 I hI t
    rw [mul_one] at h
    exact h.symm
  unfold packedChar
  rw [dif_pos hV, hspec, mul_assoc, mul_comm (idealRowHom V I), ← mul_assoc, hone]

theorem packedChar_coef (η : Character) (j : DictIdx) (V : O) (hV : V ≠ 0) (I : Ideal O)
    (hI : Supported I) :
    idealCoeff (packedChar η j V) I = idealCoeff (anchors η j) I * idealRowHom V I := by
  have h := packedChar_height η j V hV I hI 0
  rwa [Packet.heightCoeff_zero, Packet.heightCoeff_zero] at h

/-! ### 3. Energy transfer between characters agreeing on the residual columns -/

theorem keep_congr (τ τ' : Character) (Q : Ideal O) (n : Fin 4 → ℤ) (wm : O) (hwm : wm ≠ 0)
    (hcoef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {wm}) →
      idealCoeff τ I = idealCoeff τ' I) :
    (canonicalRadial τ Q n).keep = (canonicalRadial τ' Q n).keep := by
  funext z
  apply propext
  have h1 := keep_transfer τ τ' Q n 1 wm z hwm one_ne_zero (fun I hI hw => by
    rw [hcoef I hI hw, idealRowHom_one_supported I hI, mul_one])
  have h2 := keep_transfer τ' τ' Q n 1 wm z hwm one_ne_zero (fun I hI _ => by
    rw [idealRowHom_one_supported I hI, mul_one])
  exact h1.trans h2.symm

/-- **Character congruence of the literal label energy.** -/
theorem labelEnergy_congr (M : Ideal O) [NeZero M] (Hray : Subgroup (O ⧸ M)ˣ)
    (hHray : RayOrthogonality.globalUnits M ≤ Hray) {α : Type*} [Fintype α] (W : ℝ → ℂ)
    (η₀ : Character) (θ : α → RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α → ℝ)
    (t : ℝ) (R₀ : α → Finset (Ideal O)) (τ τ' : Character) (Q : Ideal O) (n : Fin 4 → ℤ)
    (Cap Lcap : ℝ) (R G : Ideal O) (hG : G ≠ 0) (seed D : Ideal O) (H : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Ideal O × Ideal O) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (v : ℝ) (wm : O) (hwm : wm ≠ 0)
    (hcoef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {wm}) →
      idealCoeff τ I = idealCoeff τ' I)
    (hcol : ∀ I : Ideal O, Supported I → IsCoprime G I → D ∣ I →
      originalColumn (enclosure (Cap*Z^Lcap)) H
        (fun i => supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i => relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i => slotProfile W (σ i) (freq i)) (fun i => Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) ≠ 0 →
      IsCoprime I (Ideal.span {wm})) :
    labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ Q n Cap Lcap R G hG seed D H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v =
      labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ' Q n Cap Lcap R G hG seed D H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v := by
  unfold labelEnergy sourceRestrictedEnergy
  rw [keep_congr τ τ' Q n wm hwm hcoef]
  congr 1
  funext I
  have hs : Supported (I : Ideal O) := (Finset.mem_filter.mp I.property).2
  beta_reduce
  by_cases hc : IsCoprime G (I : Ideal O) ∧ D ∣ (I : Ideal O)
  · rw [if_pos hc]
    by_cases h0 : originalColumn (enclosure (Cap*Z^Lcap)) H
        (fun i => supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i => relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i => slotProfile W (σ i) (freq i)) (fun i => Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) = 0
    · rw [h0, zero_mul, zero_mul]
    · unfold heightCoeff
      rw [hcoef I hs (hcol I hs hc.1 hc.2 h0)]
  · rw [if_neg hc, zero_mul, zero_mul]

/-- **The twin has the literal energy of the actual second character** (left side): the
energy of `τχ` equals the energy of `packedChar η (ξ₁·firstPhase·ξ·χ) (V_C·A₂)` when the
residual columns with a nonzero coefficient are coprime to the first exponent-zero primes. -/
theorem labelEnergy_packed {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
    (ξ : RayCharacter) {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CommonIndex C₂ D₂)} {τ : RayCharacter → Character}
    (hfam : Family (childCharacter F.left ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (M : Ideal O) [NeZero M] (Hray : Subgroup (O ⧸ M)ˣ)
    (hHray : RayOrthogonality.globalUnits M ≤ Hray) {α : Type*} [Fintype α] (W : ℝ → ℂ)
    (η₀ : Character) (θ : α → RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α → ℝ)
    (t : ℝ) (R₀ : α → Finset (Ideal O)) (Q : Ideal O) (n : Fin 4 → ℤ)
    (Cap Lcap : ℝ) (R : Ideal O) (hG : C₂ ≠ 0) (seed D' : Ideal O) (H : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Ideal O × Ideal O) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (v : ℝ)
    (hZ₀ : ∀ I : Ideal O, Supported I → IsCoprime C₂ I → D' ∣ I →
      originalColumn (enclosure (Cap*Z^Lcap)) H
        (fun i => supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i => relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i => slotProfile W (σ i) (freq i)) (fun i => Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (C₂*I) ≠ 0 →
      IsCoprime I (firstZeroPrimes C D)) :
    labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ (τ χ) Q n Cap Lcap R C₂ hG seed D' H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v =
      labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀
        (packedChar η (childIdx C D hC ξ₁ ξ χ) (leftRow C D hC E C₂ D₂ U)) Q n Cap Lcap R C₂ hG
        seed D' H W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v := by
  have hV : leftRow C D hC E C₂ D₂ U ≠ 0 :=
    mul_ne_zero (firstPacked_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U)
  apply labelEnergy_congr M Hray hHray W η₀ θ Z w σ freq t R₀ _ _ Q n Cap Lcap R C₂ hG seed D' H
    W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v (packMask (firstZeroPrimes C D) C₂)
    (packMask_ne_zero _ _ (firstZeroPrimes_ne_zero C D) hC₂)
  · intro I hI hw
    obtain ⟨hz, hc⟩ := packMask_coprime _ _ I hw
    have h1 := second_packed_child F ξ hfam χ I hI hz (Or.inl hc) 0
    rw [Packet.heightCoeff_zero, Packet.heightCoeff_zero] at h1
    rw [h1, packedChar_coef η _ _ hV I hI]
  · intro I hI hc hD h0
    have hz := hZ₀ I hI hc hD h0
    rw [packMask, ConcretePrimeRowBridge.span_idealGenerator]
    exact IsCoprime.mul_right hz hc.symm

/-- **The twin has the literal energy of the actual second character** (right side): the
energy of `τχ` equals the energy of `packedChar η (ξ₁·firstPhase·ξ·χ) (V_C·A₂)` when the
residual columns with a nonzero coefficient are coprime to the first exponent-zero primes. -/
theorem labelEnergy_packed_right {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
    (ξ : RayCharacter) {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CommonIndex C₂ D₂)} {τ : RayCharacter → Character}
    (hfam : Family (childCharacter F.right ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (M : Ideal O) [NeZero M] (Hray : Subgroup (O ⧸ M)ˣ)
    (hHray : RayOrthogonality.globalUnits M ≤ Hray) {α : Type*} [Fintype α] (W : ℝ → ℂ)
    (η₀ : Character) (θ : α → RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α → ℝ)
    (t : ℝ) (R₀ : α → Finset (Ideal O)) (Q : Ideal O) (n : Fin 4 → ℤ)
    (Cap Lcap : ℝ) (R : Ideal O) (hG : C₂ ≠ 0) (seed D' : Ideal O) (H : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Ideal O × Ideal O) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (v : ℝ)
    (hZ₀ : ∀ I : Ideal O, Supported I → IsCoprime C₂ I → D' ∣ I →
      originalColumn (enclosure (Cap*Z^Lcap)) H
        (fun i => supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i => relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i => slotProfile W (σ i) (freq i)) (fun i => Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (C₂*I) ≠ 0 →
      IsCoprime I (firstZeroPrimesRight C D)) :
    labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ (τ χ) Q n Cap Lcap R C₂ hG seed D' H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v =
      labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀
        (packedChar η (childIdxRight C D hC ξ₂ ξ χ) (rightRow C D hC E C₂ D₂ U)) Q n Cap Lcap R C₂ hG
        seed D' H W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v := by
  have hV : rightRow C D hC E C₂ D₂ U ≠ 0 :=
    mul_ne_zero (firstPackedRight_ne_zero C D hC E) (secondTwist_ne_zero C₂ D₂ hC₂ U)
  apply labelEnergy_congr M Hray hHray W η₀ θ Z w σ freq t R₀ _ _ Q n Cap Lcap R C₂ hG seed D' H
    W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v (packMask (firstZeroPrimesRight C D) C₂)
    (packMask_ne_zero _ _ (firstZeroPrimesRight_ne_zero C D) hC₂)
  · intro I hI hw
    obtain ⟨hz, hc⟩ := packMask_coprime _ _ I hw
    have h1 := second_packed_child_right F ξ hfam χ I hI hz (Or.inl hc) 0
    rw [Packet.heightCoeff_zero, Packet.heightCoeff_zero] at h1
    rw [h1, packedChar_coef η _ _ hV I hI]
  · intro I hI hc hD h0
    have hz := hZ₀ I hI hc hD h0
    rw [packMask, ConcretePrimeRowBridge.span_idealGenerator]
    exact IsCoprime.mul_right hz hc.symm

/-! ### 4. The concrete labels and their `Fits` -/

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The data of one concrete second-step label (one genuine common factor `G = C₂` with unit
set, one dyad vector, one second artificial divisor `t₂ = D`, the puncture `R`, the seed, the
holes, the extracted ordinary pair and the scalar prefactor). -/
structure LabelData where
  /-- dictionary index (`childIdx …` on the left, `childIdxRight …` on the right) -/
  j : DictIdx
  /-- the second-step frequency twist `A₂` -/
  A₂ : O
  n : Fin 4 → ℤ
  R : Ideal O
  G : Ideal O
  seed : Ideal O
  D : Ideal O
  holesH : Finset PrimeIdeal
  d : Ideal O × Ideal O
  prefactor : ℂ

/-- The frame label of the concrete data: the packed twin as character, mask `1`. -/
def LabelData.toLabel (η : Character) (x : LabelData) : GLabel θ mesh Z where
  char r := packedChar η x.j (r.V₀ * x.A₂)
  anchor _ := x.j
  mask _ := 1
  twist := x.A₂
  n := x.n
  R := x.R
  G := x.G
  seed := x.seed
  D := x.D
  holesH := x.holesH
  d := x.d
  common := x.G
  prefactor := x.prefactor

/-- The hypotheses on the concrete label data under which it is a packet of the source. -/
structure LabelData.Good (r : GSrc θ mesh Z) (x : LabelData) : Prop where
  A_ne : x.A₂ ≠ 0
  R_ne : x.R ≠ 0
  G_ne : x.G ≠ 0
  seed_dvd : x.seed ∣ x.G
  D_sq : Squarefree x.D
  /-- `G` cube-free: `G ∣ rad(G)²` -/
  G_cube : x.G ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport x.G, P)^2
  holes_sub : x.holesH ⊆ enclosure (θ.Cap * Z^θ.Lcap)
  cap : (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((x.R * x.G) * x.D) ∪
    holes x.holesH, I) : ℝ) ≤ Z^θ.Bmask
  holes_R₀ : ∀ i, ∀ P ∈ x.holesH, P.val ∈ r.R₀ i
  d₁ : x.d.1 ≠ 0
  d₂ : x.d.2 ≠ 0
  dual : Real.logb Z (((Ideal.span {x.A₂}).absNorm : ℝ) * dyadicScale (x.n 1)) ≤
    2 * r.colLog - r.kLog + mesh

/-- **All `Fits` fields for a concrete label.** -/
theorem toLabel_fits (η : Character) (r : GSrc θ mesh Z) (x : LabelData) (hx : x.Good r) :
    Fits η r (x.toLabel (θ := θ) (mesh := mesh) (Z := Z) η) where
  twist_ne := hx.A_ne
  mask_ne := one_ne_zero
  coef I hI _ := packedChar_coef η x.j _ (mul_ne_zero r.hV₀ hx.A_ne) I hI
  R_ne := hx.R_ne
  G_ne := hx.G_ne
  seed_dvd := hx.seed_dvd
  D_sq := hx.D_sq
  G_cap := Concrete.G_cap_of_cap x.R x.G x.D x.holesH hx.R_ne hx.G_ne hx.D_sq.ne_zero hx.G_cube Z
    θ.Bmask (zero_le_one.trans r.hZ.le) hx.cap
  D_cap := Concrete.D_cap_of_cap x.R x.G x.D x.holesH hx.R_ne hx.G_ne hx.D_sq Z θ.Bmask hx.cap
  G_mask I _ := by
    change IsCoprime I (Ideal.span {(1:O)})
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  holes_sub := hx.holes_sub
  cap := hx.cap
  holes_R₀ := hx.holes_R₀
  d₁ := hx.d₁
  d₂ := hx.d₂
  dual := hx.dual

theorem toLabel_weight (η : Character) (x : LabelData) :
    gWeight (x.toLabel (θ := θ) (mesh := mesh) (Z := Z) η) =
      rho x.G * ‖x.prefactor‖ / (x.D.absNorm : ℝ) := rfl

theorem toLabel_envelope (η : Character) (r : GSrc θ mesh Z) (x : LabelData) :
    gEnvelope r (x.toLabel (θ := θ) (mesh := mesh) (Z := Z) η) =
      Real.logb Z (((Ideal.span {r.V₀ * x.A₂}).absNorm : ℝ) * dyadicScale (x.n 1)) := rfl

/-- **The frame energy of a concrete label is the literal label energy of the actual second
character `τχ`** (left side; the residual columns coprime to the first exponent-zero primes). -/
theorem rawEnergy_toLabel {η : Character} {C D : Ideal O} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂)
    (ξ : RayCharacter) {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CommonIndex C₂ D₂)} {τ : RayCharacter → Character}
    (hfam : Family (childCharacter F.left ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (r : GSrc θ mesh Z) (hV₀ : r.V₀ = firstPacked C D hC E) (x : LabelData)
    (hj : x.j = childIdx C D hC ξ₁ ξ χ) (hA : x.A₂ = secondTwist C₂ D₂ U) (hG : x.G = C₂)
    (hx : x.Good r) (v : ℝ)
    (hZ₀ : ∀ I : Ideal O, Supported I → IsCoprime C₂ I → x.D ∣ I →
      originalColumn (enclosure (θ.Cap*Z^θ.Lcap)) x.holesH
        (fun i => supportedPool (primePool θ.rayM θ.Hray 2 (Z^(r.w i)))) x.d ⟨hx.d₁, hx.d₂⟩
        x.R x.seed
        (slotCoefficient (fun i => relativeCharacter θ.rayM θ.Hray θ.hH θ.η₀ (r.χ i)) r.R₀ r.t)
        (fun i => slotProfile θ.W (r.σ i) (r.freq i)) (fun i => Z^(r.w i))
        (phaseProfile r.W₁ r.t₁) (phaseProfile r.W₂ r.t₂) θ.b r.X₁ r.X₂ r.Y₁ r.Y₂ (C₂*I) ≠ 0 →
      IsCoprime I (firstZeroPrimes C D)) :
    rawEnergy η r (x.toLabel η) (toLabel_fits η r x hx) v =
      labelEnergy θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq r.t r.R₀ (τ χ)
        (internalQ θ.Q θ.η₀) x.n θ.Cap θ.Lcap x.R C₂ (hG ▸ hx.G_ne) x.seed x.D x.holesH
        r.W₁ r.W₂ r.t₁ r.t₂ θ.b r.X₁ r.X₂ r.Y₁ r.Y₂ x.d ⟨hx.d₁, hx.d₂⟩ v := by
  obtain ⟨j, A₂, n, R, G, seed, D', holesH, d, pre⟩ := x
  simp only at hj hA hG hZ₀ ⊢
  subst hj hA hG
  rw [labelEnergy_packed F ξ hfam χ θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq r.t r.R₀
    (internalQ θ.Q θ.η₀) n θ.Cap θ.Lcap R _ seed D' holesH r.W₁ r.W₂ r.t₁ r.t₂ θ.b r.X₁ r.X₂
    r.Y₁ r.Y₂ d _ v hZ₀]
  rw [leftRow, ← hV₀]
  rfl

end
end QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
