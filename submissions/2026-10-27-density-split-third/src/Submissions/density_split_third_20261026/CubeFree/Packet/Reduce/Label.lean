/- Copyright (c) 2026 Sil. Apache-2.0.
Label reduction: one second-step label's literal one-sided energy in leaf-domination form,
packed at the physical row (WP-G; design `label_reduction`).

For a label with character `τ`, packed by an anchor `σA` and a row multiplier `V`
(`idealCoeff τ = idealCoeff σA · idealRowHom V` on supported columns coprime to a mask
`wm` that divides every residual column's complement, as supplied by `Packet.Dictionary`),
the literal energy of FP's `MixedCanonicalEnvelope.uniform_canonical_source_envelope` is
dominated (`label_reduction`) by the canonical leaves

  `nativeLeaf … σA (fun y => V ∣ y ∧ initialKeep σA Q y) ballProfile (N(V)·K) …`

of the packed state (rows `y = V z`, scale `N(V)·K`, `K = dyadicScale (n 1)`), with the mass

  `C·Z^ε·(X₁X₂∏ᵢZ^{wᵢ})·N(G)^δ·N(D)^δ / (N(G)·pairNorm d·N(D))`.

The leaf lengths are below `(X₁,X₂)` or `(Y₁,Y₂)`, the leaves carry the original relative
characters and annular weights (heights `t+v`, `2π tᵢ + v`), canonical prime pools and every
slot subset.  Each leaf is a canonical packed energy (`packedLeaf_eq`):

  `energy σA (fixedBadMask*idealGenerator 1) V 0 p₀ p₁ (primePool (Z^{wᵢ}))
     (relative character · annular weight at frequency t+v+freqᵢ) (Z^{wᵢ}) X₁' X₂'
     (fun z => initialKeep σA Q (V*z)) ballProfile K`,

which is the left side of Seam A (`PricedPackedAt`) for the slot set `A`.
`label_reduction_single` gives the consumer form: the label energy is at most the mass
times one canonical packed energy (or is `≤ 0`). -/
import Submissions.density_split_third_20261026.CubeFree.Packet.Reduce.MixedDom3
import Submissions.density_split_third_20261026.CubeFree.FP.MixedHeightEnergy
import Submissions.density_split_third_20261026.CubeFree.Packet.Dictionary
import Submissions.density_split_third_20261026.CubeFree.Packet.Sublattice
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.DensitySplitThird.CubeFree.Packet.Reduce
open Candidate.FourthPower QRH.DensitySplitThird.CubeFree.FP

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
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-! ### Packing at the physical row -/

/-- The original residual-column row sees its character only on columns coprime to the
genuine common ideal. -/
theorem originalMaskedRow_congr_char {α : Type*} [Fintype α] (χ χ' : Character)
    (S H : Finset PrimeIdeal) (pool : α→Finset Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (G R seed D : Id) (hG : G≠0) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (h : ∀I : Id,IsCoprime G I → idealCoeff χ I=idealCoeff χ' I) :
    originalMaskedRow χ S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂=
      originalMaskedRow χ' S H pool d hd G R seed D hG ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ := by
  unfold originalMaskedRow
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : IsCoprime G I ∧ D∣I
  · simp [hI,h I hI.1]
  · simp [hI]

/-- **Packing a radial energy.**  If the kept rows `z` correspond to the kept rows `V z` of
the packed keep, and the rows agree there, the radial energy is the packed radial energy on
the sublattice `V·O` at scale `N(V)·K`. -/
theorem radialEnergy_pack (f g : O→ℂ) (keep keep' : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (V : O)
    (hV : V≠0) (hkeep : ∀z,keep z ↔ keep' (V*z)) (hdvd : ∀y,keep' y → V∣y)
    (hfg : ∀z,keep z → f z=g (V*z)) :
    radialEnergy f keep Φ K=radialEnergy g keep' Φ (((Ideal.span {V}).absNorm:ℝ)*K) := by
  unfold radialEnergy
  let F : O→ℝ := fun y=>if keep' y then
    ‖g y‖^2*(Φ (‖eisEmbedding y‖^2/(((Ideal.span {V}).absNorm:ℝ)*K))).re else 0
  have hinj : Function.Injective (fun z : O=>V*z) := mul_right_injective₀ hV
  have hsupp : Function.support F⊆Set.range (fun z : O=>V*z) := by
    intro y hy
    have hk : keep' y := by
      by_contra hk
      exact hy (by simp only [F,hk,ite_false])
    obtain ⟨c,hc⟩ := hdvd y hk
    exact ⟨c,hc.symm⟩
  change _=∑'y,F y
  rw [←hinj.tsum_eq hsupp]
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · have hz' := (hkeep z).mp hz
    simp only [F,hz,hz',ite_true,hfg z hz,Packet.radial_packed_scale V hV K z]
  · have hz' : ¬keep' (V*z) := fun h=>hz ((hkeep z).mpr h)
    simp only [F,hz,hz',ite_false]

/-- The packed keep of a label: the sublattice `V·O` and the source keep of the anchor. -/
def packedKeep (σA : Character) (Q : Id) (V : O) (y : O) : Prop :=
  V∣y ∧ initialKeep σA Q y

theorem packedKeep_ne_zero (σA : Character) (Q : Id) (V : O) (y : O)
    (hy : packedKeep σA Q V y) : y≠0 := hy.2.1

/-- The packed canonical leaf family of a label (anchor `σA`, packed row multiplier `V`,
second-step dyadic scale `K`). -/
def packedLeaf {α : Type*} (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M Hray)
    (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (σA : Character) (Q : Id) (V : O) (K : ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ) : Finset α → ℝ → ℝ → ℝ :=
  nativeLeaf M Hray hHray W η₀ θ Z w σ freq t σA (packedKeep σA Q V) ballProfile
    (((Ideal.span {V}).absNorm:ℝ)*K) W₁ W₂ t₁ t₂

/-- The label mass. -/
def labelMass {α : Type*} [Fintype α] (C Z ε δ : ℝ) (w : α→ℝ) (X₁ X₂ : ℝ) (G D : Id)
    (d : Id×Id) : ℝ :=
  C*Z^ε*(X₁*X₂*∏i,Z^(w i))*(G.absNorm:ℝ)^δ*(D.absNorm:ℝ)^δ/(G.absNorm:ℝ)/pairNorm d/
    (D.absNorm:ℝ)

/-- The literal one-sided energy of one second-step label: the left side of FP's
`MixedCanonicalEnvelope.uniform_canonical_source_envelope` (cube-free columns). -/
def labelEnergy {α : Type*} [Fintype α] (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (R₀ : α→Finset Id)
    (τ : Character) (Q : Id) (n : Fin 4→ℤ) (Cap Lcap : ℝ) (R G : Id) (hG : G≠0) (seed D : Id)
    (H : Finset PrimeIdeal) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Id×Id)
    (hd : d.1≠0 ∧ d.2≠0) (v : ℝ) : ℝ :=
  sourceRestrictedEnergy (canonicalRadial τ Q n).keep
    (residualPool G hG (finiteColumns (Fintype.piFinset
      (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂))))
    (fun I=>if IsCoprime G I ∧ D∣I then
      originalColumn (enclosure (Cap*Z^Lcap)) H
        (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
        (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
        (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
        (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
    (heightCoeff τ v) ballProfile (dyadicScale (n 1))

/-- **Label reduction.**  One second-step label's literal one-sided energy (the left side of
FP's `MixedCanonicalEnvelope.uniform_canonical_source_envelope`) is dominated by the packed
canonical leaves, with the label mass.  The constant precedes every label datum. -/
theorem label_reduction {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(τ σA : Character)(Q : Id)(n : Fin 4→ℤ)(V wm : O),V≠0 → wm≠0 →
      (∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) →
        idealCoeff τ I=idealCoeff σA I*CanonicalRowCompletion.idealRowHom V I) →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
      (∀I : Id,IsCoprime G I → IsCoprime I (Ideal.span {wm})) →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀_hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀_hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
    ∃Lf : Finset (ℝ×ℝ),LengthsBelow₂ Lf X₁ X₂ Y₁ Y₂ ∧
      LeafDom (packedLeaf M Hray hHray W η₀ θ Z w σ freq (t+v) σA Q V (dyadicScale (n 1)) W₁ W₂
          (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))) Lf
        (labelMass C Z ε δ w X₁ X₂ G D d)
        (labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ Q n Cap Lcap R G hG seed D H
          W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v) := by
  obtain ⟨C,hC,hbase⟩ := original_source_dom M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap
    Bmask ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ τ σA Q n V wm hV hwm hcoef R G seed D hR hG
    hseed hD hGw H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄
    hXY d hd v
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2.1
  have hP (i : α) : 0<Z^(w i) := Real.rpow_pos_of_pos hZ0 _
  let K := dyadicScale (n 1)
  have hK : 0<K := dyadicScale_pos _
  have hNV : 0<((Ideal.span {V}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  -- the exact height dictionary
  have hh := canonical_source_height_energy τ v (enclosure (Cap*Z^Lcap)) H pool hp d hd
    G R seed D hG (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i)) hP W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hXY (canonicalRadial τ Q n).keep (fun z hz=>hz.1) ballProfile K
  -- packing at the physical row
  have hpack := radialEnergy_pack
    (fun z=>originalMaskedRow (naturalCharacter τ z) (enclosure (Cap*Z^Lcap)) H pool d hd
      G R seed D hG (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ (t+v))
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
    (fun y=>originalMaskedRow (naturalCharacter σA y) (enclosure (Cap*Z^Lcap)) H pool d hd
      G R seed D hG (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ (t+v))
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ (t₁+v/(2*Real.pi))) (phaseProfile W₂ (t₂+v/(2*Real.pi))) b X₁ X₂ Y₁ Y₂)
    (canonicalRadial τ Q n).keep (packedKeep σA Q V) ballProfile K V hV
    (by
      intro z
      rw [Packet.keep_transfer τ σA Q n V wm z hwm hV hcoef]
      exact ⟨fun h=>⟨dvd_mul_right V z,h⟩,fun h=>h.2⟩)
    (fun y hy=>hy.1)
    (by
      intro z hz
      have hz0 : z≠0 := hz.1
      apply originalMaskedRow_congr_char
      intro I hI
      by_cases hs : Supported I
      · exact Packet.naturalCharacter_transfer τ σA V wm z hV hz0 hcoef I hs (hGw I hI)
      · rw [natural_character_off_supported τ z hz0 I hs,
          natural_character_off_supported σA (V*z) (mul_ne_zero hV hz0) I hs])
  -- the source chain on the packed state
  obtain ⟨Lf,hLf,he⟩ := hbase Z hZ η₀ θ w σ freq (t+v) R₀ hw hwL hσ hσhi hR₀ σA
    (packedKeep σA Q V) ballProfile (((Ideal.span {V}).absNorm:ℝ)*K) 2 (mul_pos hNV hK)
    ball_support (fun _=>ballProfile_nonneg _) (packedKeep_ne_zero σA Q V)
    R G seed D hR hG hseed hD H hH hcap hHR W₁ W₂ hs₁ hs₂
    (t₁+v/(2*Real.pi)) (t₂+v/(2*Real.pi)) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
  refine ⟨Lf,hLf,?_⟩
  have hT : 0<X₁*X₂*∏i,Z^(w i) :=
    mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hlabel := (div_eq_iff hT.ne').mp hh
  unfold labelEnergy
  rw [hlabel,hpack]
  have hs := he.smul hT.le
  refine (hs.of_eq (by ring)).mass_le (le_of_eq ?_)
  unfold labelMass
  ring

/-! ### The leaves as canonical packed energies -/

/-- A native leaf is a canonical OAI energy with the independent profiles and the inherited
height moved into the annular frequencies. -/
theorem nativeLeaf_energy {α : Type*} (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (hZ : 0<Z) (w σ freq : α→ℝ) (t : ℝ)
    (η : Character) (keep : O→Prop) (hkeep : ∀z,keep z → z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hK : 0<K) (hΦ : ∀x,0≤(Φ x).re) {a b : ℝ} (ha : 0<a) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ : ℝ) (A : Finset α) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    nativeLeaf M Hray hHray W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂=
      energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
        (fun i : A=>primePool M Hray 2 (Z^(w i)))
        (fun (i : A) I=>idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (t+freq i) I)
        (fun i : A=>Z^(w i)) X₁ X₂ keep Φ K := by
  let r : CenteredMomentRadialEligibleEnergy.Radial := ⟨keep,Φ,K,hK,fun _=>hΦ _⟩
  have hh := natural_subset_radial_eq_energy η r hkeep A
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    (fun i=>primePool M Hray 2 (Z^(w i)))
    (fun i=>heightCoefficient (slotBeta M Hray hHray W η₀ θ Z w σ freq i) t)
    (fun i=>Z^(w i)) X₁ X₂ hX₁ hX₂ (fun i _=>Real.rpow_pos_of_pos hZ _)
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at hh
  unfold nativeLeaf leafEnergy leafRow
  rw [hh]
  have hi := inherited_height_energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    (fun i : A=>primePool M Hray 2 (Z^(w i)))
    (fun (i : A) I=>idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I) (fun _=>W)
    (fun i : A=>Z^(w i)) (fun i : A=>σ i) (fun i : A=>freq i)
    (fun i=>Real.rpow_pos_of_pos hZ _)
    (fun i I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero) t 0 X₁ X₂ keep Φ K
  simp only [independentProfiles,show (1:Fin 2)≠0 by decide,ite_false,ite_true]
  exact hi

/-- The packed energy on the sublattice `V·O` at scale `N(V)·K` is the energy with frozen
factor `V` at scale `K`. -/
theorem energy_sublattice_eq {ι : Type*} [Fintype ι] (η : Character) (m V : O) (hV : V≠0)
    (t : ℝ) (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m 1 t W₁ W₂ S β P X₁ X₂ (fun y=>V∣y ∧ keep y) Φ
        (((Ideal.span {V}).absNorm:ℝ)*K)=
      energy η m V t W₁ W₂ S β P X₁ X₂ (fun z=>keep (V*z)) Φ K := by
  change radialEnergy (fun y=>positiveSlotRow η m 1 y W₁ W₂ S β P t X₁ X₂)
      (fun y=>V∣y ∧ keep y) Φ (((Ideal.span {V}).absNorm:ℝ)*K)=
    radialEnergy (fun z=>positiveSlotRow η m V z W₁ W₂ S β P t X₁ X₂) (fun z=>keep (V*z)) Φ K
  exact (radialEnergy_pack _ _ (fun z=>keep (V*z)) (fun y=>V∣y ∧ keep y) Φ K V hV
    (fun z=>⟨fun h=>⟨dvd_mul_right V z,h⟩,fun h=>h.2⟩) (fun y hy=>hy.1)
    (fun z _=>Packet.positiveSlotRow_frozen_eq η m V z W₁ W₂ S β P t X₁ X₂)).symm

/-- **The packed leaves are canonical packed energies** (the left side of Seam A
`PricedPackedAt` for the slot set `A`, height `0`, slot frequencies `t+freqᵢ`). -/
theorem packedLeaf_eq {α : Type*} (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (hZ : 0<Z) (w σ freq : α→ℝ) (t : ℝ)
    (σA : Character) (Q : Id) (V : O) (hV : V≠0) (K : ℝ) (hK : 0<K) {a b : ℝ} (ha : 0<a)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b) (t₁ t₂ : ℝ) (A : Finset α)
    (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    packedLeaf M Hray hHray W η₀ θ Z w σ freq t σA Q V K W₁ W₂ t₁ t₂ A X₁ X₂=
      energy σA (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) V 0
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
        (fun i : A=>primePool M Hray 2 (Z^(w i)))
        (fun (i : A) I=>idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (t+freq i) I)
        (fun i : A=>Z^(w i)) X₁ X₂ (fun z=>initialKeep σA Q (V*z)) ballProfile K := by
  have hNV : 0<((Ideal.span {V}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))
  unfold packedLeaf
  rw [nativeLeaf_energy M Hray hHray W η₀ θ Z hZ w σ freq t σA (packedKeep σA Q V)
    (packedKeep_ne_zero σA Q V) ballProfile _ (mul_pos hNV hK) ballProfile_nonneg ha W₁ W₂
    hs₁ hs₂ t₁ t₂ A X₁ X₂ hX₁ hX₂]
  exact energy_sublattice_eq σA _ V hV 0 _ _ _ _ _ X₁ X₂ (initialKeep σA Q) ballProfile K

theorem packedLeaf_nonneg {α : Type*} (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M Hray) (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ)
    (σA : Character) (Q : Id) (V : O) (K : ℝ) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ) (A : Finset α)
    (X₁ X₂ : ℝ) : 0≤packedLeaf M Hray hHray W η₀ θ Z w σ freq t σA Q V K W₁ W₂ t₁ t₂ A X₁ X₂ :=
  nativeLeaf_nonneg M Hray hHray W η₀ θ Z w σ freq t σA _ ballProfile _
    (fun _=>ballProfile_nonneg _) W₁ W₂ t₁ t₂ A X₁ X₂

/-! ### Consumer form -/

/-- **Label reduction, consumer form.**  The label energy is at most the label mass times
one canonical packed energy (the left side of Seam A for a slot set `A ⊆ α`, lengths below
`(X₁,X₂)` or `(Y₁,Y₂)`), or it is `≤ 0`. -/
theorem label_reduction_single {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(τ σA : Character)(Q : Id)(n : Fin 4→ℤ)(V wm : O),V≠0 → wm≠0 →
      (∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) →
        idealCoeff τ I=idealCoeff σA I*CanonicalRowCompletion.idealRowHom V I) →
    ∀R G seed D : Id,R≠0 → ∀hG : G≠0,seed∣G → Squarefree D →
      (∀I : Id,IsCoprime G I → IsCoprime I (Ideal.span {wm})) →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
      labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ Q n Cap Lcap R G hG seed D H
          W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v≤0 ∨
      ∃(A : Finset α)(X₁' X₂' : ℝ),0<X₁' ∧ 0<X₂' ∧
        ((X₁'≤X₁ ∧ X₂'≤X₂) ∨ (X₁'≤Y₁ ∧ X₂'≤Y₂)) ∧
        labelEnergy M Hray hHray W η₀ θ Z w σ freq t R₀ τ Q n Cap Lcap R G hG seed D H
            W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v≤
          labelMass C Z ε δ w X₁ X₂ G D d*
            energy σA (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) V 0
              ((independentProfiles ha W₁ W₂ hs₁ hs₂
                (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).profile 0)
              ((independentProfiles ha W₁ W₂ hs₁ hs₂
                (2*Real.pi*(t₁+v/(2*Real.pi))) (2*Real.pi*(t₂+v/(2*Real.pi)))).profile 1)
              (fun i : A=>primePool M Hray 2 (Z^(w i)))
              (fun (i : A) I=>idealCoeff (relativeCharacter M Hray hHray η₀ (θ i)) I*
                HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (t+v+freq i) I)
              (fun i : A=>Z^(w i)) X₁' X₂' (fun z=>initialKeep σA Q (V*z)) ballProfile
              (dyadicScale (n 1)) := by
  obtain ⟨C,hC,hred⟩ := label_reduction M Hray hHray (α:=α) Holes W a b L Lslot Lcap Cap Bmask
    ε δ lo hi hWs hW ha hb hLslot hLcap hCap hBmask hCapb hLordinary hε hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ τ σA Q n V wm hV hwm hcoef R G seed D hR hG
    hseed hD hGw H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄
    hXY d hd v
  obtain ⟨Lf,hLf,hdom⟩ := hred Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ τ σA Q n V wm hV hwm
    hcoef R G seed D hR hG hseed hD hGw H hH hcap hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
  rcases hdom.exists_leaf (packedLeaf_nonneg M Hray hHray W η₀ θ Z w σ freq (t+v) σA Q V _ _ _ _ _)
    with hx | ⟨A,p,hp,hx⟩
  · exact Or.inl hx
  · obtain ⟨h₁,h₂,h₃⟩ := hLf p hp
    refine Or.inr ⟨A,p.1,p.2,h₁,h₂,h₃,?_⟩
    rw [packedLeaf_eq M Hray hHray W η₀ θ Z (zero_lt_one.trans_le hZ) w σ freq (t+v) σA Q V hV
      _ (dyadicScale_pos _) ha W₁ W₂ hs₁ hs₂ _ _ A p.1 p.2 h₁ h₂] at hx
    exact hx

end

end QRH.DensitySplitThird.CubeFree.Packet.Reduce
