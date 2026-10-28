/- Copyright (c) 2026 Sil. Apache-2.0.
exact retained nonexceptional aggregation for originalColumn.
The actual child-envelope geometry is summed over all actual blocks.
Source estimates are supplied by MixedActualEnvelopePhysical, not assumed.
The localized scale 16*K*Wblock^4 and outer 1/Wblock are unchanged.
Modified by Sil (2026-10-26): reroute: MixedActualEnvelopePhysical (replaced) is no longer imported; new CanonicalSideSupply (one-sided canonical label-energy bound at a uniform exponent expo w, supplied by Seam B / WP-H) with native instance canonicalSideSupply_native (WP-G Packet/Reduce chain); uniform_actual_child_envelope_of_supply and uniform_actual_retained_nonexceptional_of_supply take the supply; the FP-named uniform_actual_retained_nonexceptional is unchanged (native instance).
-/
import Submissions.density_split_fourth.CubeFree.FP.MixedActualGeometry
import Submissions.density_split_fourth.CubeFree.FP.MixedLocalizedDictionary
import Submissions.density_split_fourth.CubeFree.Packet.Reduce.MixedCanonicalEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.MixedActualRetained
open Candidate.FourthPower
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedLocalizedDictionary
open MixedActualGeometry CenteredMomentSecondBlockHarmonicMass
open MixedOriginalNormCap MixedLiteralAllocation NativeInjectiveEnergy MixedPoissonLocalization
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondWindowBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondWholeKernel
open CenteredMomentSecondActivePhysicalDictionary
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Common analytic factor, including the raw source volume and the
ordinary prefix denominator. Independent of actual label and block. -/
def analyticBudget (degree : ℕ) (Cp Z δ volume A base tp : ℝ) (d : Id×Id) : ℝ :=
  volume*(Cp*Z^δ*(A/pairNorm d)*Z^base*
    heightEnvelope tp^(2*degree)*profileMoment degree^2)

/-- The actual retained-label subsum with zero physical blocks removed. -/
def retainedLiveGeometry (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K radius Hsource : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  ∑p∈liveLabels η S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
    ∑n : SourceBlocks p.val.1 p.val.2 U K radius Hsource,
      liveChildGeometry η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ K (fun i=>(n i:ℤ))

/-- Extending the retained-label subsum introduces only nonnegative
terms. The full sum is exactly the one controlled by generic harmonic mass. -/
theorem retainedLiveGeometry_le_full (η : Character) (tp : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Ψ : 𝓢(ℝ,ℂ)) (K radius Hsource : ℝ) (hK : 0≤K) (Q : Id) (m : O)
    (χ₀ : RayCharacter) :
    retainedLiveGeometry η tp S β Ψ K radius Hsource Q m χ₀≤
      fullRetainedGeometry η tp S β Ψ K radius Hsource Q m χ₀ := by
  unfold retainedLiveGeometry fullRetainedGeometry
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro p _hp _hnot
  apply Finset.sum_nonneg
  intro U _hU
  apply Finset.sum_nonneg
  intro n _hn
  exact liveChildGeometry_nonneg η tp S β p.val.1 p.val.2
    (commonLabels_supported (activeSource S β) _ _ p.property).1
    (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
    (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ K hK (fun i=>(n i:ℤ))
variable {α : Type*} [Fintype α]

/-- The finite upper support cap is a fixed profile/slot factor times
the actual volume, divided by the original pair of prefix norms. -/
theorem sourceNormCap_eq_volume (P : α→ℝ) (b T : ℝ) (d : Id×Id) :
    sourceNormCap P b T d =
      b^2*(2:ℝ)^(Fintype.card α)*(T*∏i,P i)/pairNorm d := by
  unfold sourceNormCap
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ]
  ring

local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-! ### The one-sided canonical side supply (replaces FP `MixedActualEnvelopePhysical`)

FP proved the per-label one-sided canonical envelope inside the replaced per-label lane
(`MixedCanonicalEnvelope.uniform_canonical_source_envelope`, native exponent `κ·∑w + ε`).
The cube-free skeleton obtains the same one-sided bound, at a general uniform exponent
`expo w` (CF: the leaf price paid by the selected width), from Seam B
(`Second.GroupedSideBound`) on the canonical one-sided label energies; WP-H discharges it.
`CanonicalSideSupply` is exactly the shape consumed by the block adapter
`MixedPhysicalEnvelopes.actual_canonical_source_envelopes`; the native instance is
`canonicalSideSupply_native` (WP-G's `Packet/Reduce` chain). -/

section Supply
open MixedCanonicalEnvelope MixedActualFamily MixedOriginalCoprimality MixedPhysicalEnvelopes
open CenteredMomentEnergyChildState CenteredMomentEnergyState CenteredMomentFirstSectors
open CenteredMomentRestrictedSource CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondNonexceptionalScalar

/-- One-sided canonical label-energy supply at the uniform exponent `expo w`. -/
def CanonicalSideSupply (Holes : ℕ) (W : ℝ→ℂ) (a b Mcap L Lslot Lcap Cap Bmask Bnorm lo hi : ℝ)
    (Q : Id) (expo : (α→ℝ)→ℝ) : Prop :=
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀(Bstate : ℝ)(τ : Character)(n : Fin 4→ℤ),1≤dyadicScale (n 1) →
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀R G seed D : Id,∀hR : R≠0,(R.absNorm:ℝ)≤Z^Bstate →
    ∀hG : G≠0,seed∣G → Squarefree D →
      (G.absNorm:ℝ)≤Z^Bnorm → (D.absNorm:ℝ)≤Z^Bnorm →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      (Ideal.absNorm (∏I∈QRH.Record1252270103KernelMass.primeSupport ((R*G)*D)∪holes H,I):ℝ)≤Z^Bmask →
      (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,∀v : ℝ,
      sourceRestrictedEnergy (canonicalRadial τ Q n).keep
        (residualPool G hG (finiteColumns (Fintype.piFinset
          (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd b X₁ X₂ Y₁ Y₂))))
        (fun I=>if IsCoprime G I ∧ D∣I then
          originalColumn (enclosure (Cap*Z^Lcap)) H
            (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) d hd R seed
            (slotCoefficient
              (fun i=>CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
            (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
            (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ (G*I) else 0)
        (heightCoeff τ v) ballProfile (dyadicScale (n 1)) ≤
      (rawBudget (X₁*X₂*∏i,Z^(w i))
        ((C*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
          (sourceHeight t V t₁ t₂)^degree)*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1))
        Z (expo w) G d/(D.absNorm:ℝ))*(1+‖v‖)^(2*degree)

/-- The native instance (exponent `κ·∑w + ε`), from WP-G's reduction chain. -/
theorem canonicalSideSupply_native
    (Holes : ℕ) (W : ℝ→ℂ) (a b Mcap L Lslot Lcap Cap Bmask Bnorm ε lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap) (hBmask : 0≤Bmask)
    (hBnorm : 0≤Bnorm) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    CanonicalSideSupply M Hray hHray Holes W a b Mcap L Lslot Lcap Cap Bmask Bnorm lo hi Q
      (fun w : α→ℝ=>κ*(∑i,w i)+ε) :=
  uniform_canonical_source_envelope (α:=α) M Hray hHray Holes W a b Mcap L Lslot Lcap Cap
    Bmask Bnorm ε lo hi κ hWs hW ha haUpper hb hM hLslot hLcap hCap hBmask hBnorm hCapb
    hLordinary hε hβ hκ Q hQt hQ72 hQM

/-- Monotonicity in the literal conductor-times-scale cost (verbatim from FP
`MixedActualEnvelopePhysical`). -/
theorem raw_cost_mono (volume A Z exponent cost cost' : ℝ)
    (hvolume : 0≤volume) (hA : 0≤A) (hZ : 0<Z) (hcost : cost≤cost')
    (G : Id) (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) :
    rawBudget volume (A*cost) Z exponent G d≤
      rawBudget volume (A*cost') Z exponent G d := by
  let F := volume*A*Z^exponent/(G.absNorm:ℝ)/pairNorm d
  have hF : 0≤F := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    dsimp only [F]
    positivity
  calc
    _ = F*cost := by dsimp only [F,rawBudget];ring
    _ ≤ F*cost' := mul_le_mul_of_nonneg_left hcost hF
    _ = _ := by dsimp only [F,rawBudget];ring

/-- FP `MixedActualEnvelopePhysical.uniform_actual_child_envelope` with the one-sided
source envelope taken from a `CanonicalSideSupply` at exponent `expo`. -/
theorem uniform_actual_child_envelope_of_supply
    (Holes decay : ℕ) (W : ℝ→ℂ) (Ψ : 𝓢(ℝ,ℂ))
    (a b Mcap L Lslot Lcap Cap BR BH B δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (ha : 0<a)
    (hB : 0≤B) (hδ : 0<δ)
    (Q : Id) (hQ72 : Q≤Ideal.span {(72:O)}) (expo : (α→ℝ)→ℝ)
    (hsupply : CanonicalSideSupply M Hray hHray Holes W a b Mcap L Lslot Lcap Cap
      ((BR+B)+B+BH) B lo hi Q expo) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀R seed : Id,R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH → (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
    let S := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    let Hsource := sourceNormCap (fun i=>Z^(w i)) b (X₁*X₂) d
    let volume := X₁*X₂*∏i,Z^(w i)
    let A := Cs*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
      (sourceHeight t V t₁ t₂)^degree
    Hsource≤Z^B →
    ∀(η : Character)(p : ActiveLabel S β)(U : Finset (CommonIndex p.val.1 p.val.2)),
    ∃τ : RayCharacter→Character,
    Family η p.val.1 p.val.2
      (commonLabels_supported (activeSource S β) _ _ p.property).1
      (commonLabels_supported (activeSource S β) _ _ p.property).2 U τ ∧
    ∀(tp radius Kphys ρ : ℝ)(m : O)(χ₀ : RayCharacter)(n : Fin 4→ℤ),0<Kphys →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n≠0 →
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ → ρ≤Mcap →
      ‖physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U radius
        (partRows false η χ₀ Q m p.val.1 p.val.2 U radius) Ψ Kphys n‖ ≤
      Cp*Z^δ*(outerScalar p.val.1 p.val.2 Kphys n*normalizer p.val.1 p.val.2 U)*
        (windowBudget degree tp (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (expo w) p.val.1 d)*
          windowBudget degree tp (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (expo w) p.val.2 d))/
        (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay := by
  obtain ⟨degree,control,hsource⟩ := hsupply
  obtain ⟨Cp,hCp,hphysical⟩ := actual_canonical_source_envelopes Ψ decay degree degree B δ hB hδ
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  obtain ⟨Cs,hCs,hsource⟩ := hsource η₀ hQη
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [hsource,hphysical] with Z hsourceZ hphysicalZ
  refine ⟨hsourceZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    pool S β Hsource volume A hsourcecap η p U
  have hZ0 : 0<Z := zero_lt_one.trans hsourceZ.1
  have hP : ∀i,0<Z^(w i) := fun _=>Real.rpow_pos_of_pos hZ0 _
  have hvolume : 0<volume := mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hheight := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [A]
    positivity
  have hHsource : 0≤Hsource := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    change 0≤b^2*((X₁*X₂)/pairNorm d)*(∏i,2*Z^(w i))
    positivity
  have hcolumns (I : Id) (hi : β I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (MixedOriginalNormCap.original_column_norm (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      W hWs σ freq (fun i=>Z^(w i)) hP W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2
  have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
  have hseedp := original_active_common_seed (enclosure (Cap*Z^Lcap)) H pool d hd R seed
    (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
    (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ S hseed p
  obtain ⟨τall,hτall⟩ := exists_actual_families η S β
  let τ := τall p U
  have hf := hτall p U
  refine ⟨τ,hf,?_⟩
  intro tp radius Kphys ρ m χ₀ n hKphys hm hml hm2 hne hledger hρ
  let rows := partRows false η χ₀ Q m p.val.1 p.val.2 U radius
  have hgeometry (χ : RayCharacter) := actual_canonical_geometry hf tp S β radius rows Ψ Kphys
    hKphys n hne Z BR ρ hsourceZ.1 χ Q R hR hRN hledger
  have hcost (χ : RayCharacter) :
      ((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤childEnvelope η p.val.1 p.val.2 U n :=
    family_child_envelope hf tp S β radius rows Ψ Kphys hKphys n hne χ
  have hnormone : (1:ℝ)≤(p.val.2.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsupp.2.1)
  have hdivision : Hsource/(p.val.2.absNorm:ℝ)≤Z^B :=
    (div_le_self hHsource hnormone).trans hsourcecap
  have hbudget (G : Id) : 0≤rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (expo w) G d := by
    have hchild : 0≤childEnvelope η p.val.1 p.val.2 U n := by
      have hdyad := (dyadicScale_pos (n 1)).le
      unfold childEnvelope
      positivity
    have hpair := (pairNorm_pos hd.1 hd.2).le
    unfold rawBudget
    positivity
  apply hphysicalZ.2 Kphys hKphys n η τ tp S β p.val.1 p.val.2 hsupp.1 hsupp.2
    (active_equal_support S β p) U hf Hsource hcolumns hdivision radius Q m χ₀ hQ72 hm hml hm2
    (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (expo w) p.val.1 d)
    (rawBudget volume (A*childEnvelope η p.val.1 p.val.2 U n) Z (expo w) p.val.2 d)
    (hbudget p.val.1) (hbudget p.val.2)
  all_goals
    intro L2 _hL2 hL2N hL2 χ v
    have hcaps := active_mask_caps S β p Hsource Z B BR BH hHsource hZ0
      (fun I _ hi=>hcolumns I hi) hsourcecap R L2 hR hL2 hRN hL2N H hholes
  · have he := hsourceZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
      BR (τ χ) n (hgeometry χ).1 ((hgeometry χ).2.trans hρ)
      R p.val.1 seed L2 hR hRN hsupp.1.1 hseedp.1 hL2 hcaps.1 hcaps.2.2.1
      H hH hcaps.2.2.2.2.1 hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
    have hb := raw_cost_mono volume A Z (expo w)
      (((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)) (childEnvelope η p.val.1 p.val.2 U n) hvolume.le hA hZ0 (hcost χ) p.val.1 d hd
    have hb' := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hb (Nat.cast_nonneg L2.absNorm)) (by positivity : 0≤(1+‖v‖)^(2*degree))
    apply he.trans
    simpa only [A,volume,mul_assoc,add_assoc] using hb'
  · have he := hsourceZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
      BR (τ χ) n (hgeometry χ).1 ((hgeometry χ).2.trans hρ)
      R p.val.2 seed L2 hR hRN hsupp.2.1 hseedp.2 hL2 hcaps.2.1 hcaps.2.2.1
      H hH hcaps.2.2.2.2.2 hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd v
    have hb := raw_cost_mono volume A Z (expo w)
      (((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)) (childEnvelope η p.val.1 p.val.2 U n) hvolume.le hA hZ0 (hcost χ) p.val.2 d hd
    have hb' := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hb (Nat.cast_nonneg L2.absNorm)) (by positivity : 0≤(1+‖v‖)^(2*degree))
    apply he.trans
    simpa only [A,volume,mul_assoc,add_assoc] using hb'

end Supply

/-- FP `uniform_actual_retained_nonexceptional` with the physical estimate taken from a
`CanonicalSideSupply` at the uniform exponent `expo` (Seam B in the cube-free skeleton). -/
theorem uniform_actual_retained_nonexceptional_of_supply
    (Holes : ℕ) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH B δ lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (ha : 0<a) (hB : 0≤B) (hδ : 0<δ)
    (Q : Id) (hQ72 : Q≤Ideal.span {(72:O)}) (expo : (α→ℝ)→ℝ)
    (hsupply : CanonicalSideSupply M Hray hHray Holes W a b Mcap L Lslot Lcap Cap
      ((BR+B)+B+BH) B lo hi Q expo) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀R seed : Id,R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH → (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
    let S := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    let Hsource := sourceNormCap (fun i=>Z^(w i)) b (X₁*X₂) d
    let volume := X₁*X₂*∏i,Z^(w i)
    let A := Cs*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
      (sourceHeight t V t₁ t₂)^degree
    Hsource≤Z^B →
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → 0<Wblock → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
    ∀ρ : (p : ActiveLabel S β)→(U : Finset (CommonIndex p.val.1 p.val.2))→
      SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource→ℝ,
    (∀p∈liveLabels η S β,∀U,∀n : SourceBlocks p.val.1 p.val.2 U
        (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource,
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))≠0 →
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ p U n ∧
        ρ p U n≤Mcap) →
      ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
          (fun I : supportedColumns S=>β I*heightCoeff η tp I) K Wblock
          (retainedWeight (frequencyRadius Tsec Z ξ))-
        partEnergy true η χ₀ Q m tp S β ballProfile (16*K*Wblock^4) Tsec Z ξ Hsource/(Wblock:ℂ)‖ ≤
      (analyticBudget degree Cp Z δ volume A (expo w) tp d)*
        fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock := by
  obtain ⟨degree,control,hphysical⟩ := uniform_actual_child_envelope_of_supply (α:=α) M Hray hHray
    Holes 1 W ballProfile a b Mcap L Lslot Lcap Cap BR BH B δ lo hi hWs ha hB hδ Q hQ72 expo hsupply
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  obtain ⟨Cs,Cp,hCs,hCp,hphysical⟩ := hphysical η₀ hQη
  refine ⟨Cs,Cp,hCs,hCp,hphysical.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ R seed hR hRN hseed H hH hholes hHR
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd
    pool S β Hsource volume A hsourcecap η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 ρ hgeometry
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hK4 : 0<16*K*Wblock^4 := by positivity
  have hvolume : 0<volume := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos hZ0 (w i)))
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hheight := sourceHeight_one_le t V t₁ t₂ hV
    dsimp only [A]
    positivity
  let F := analyticBudget degree Cp Z δ volume A (expo w) tp d
  have hF : 0≤F := by
    have hpair := (pairNorm_pos hd.1 hd.2).le
    have hheight := (heightEnvelope_pos tp).le
    dsimp only [F,analyticBudget]
    positivity
  have hcolumns (I : Id) (hi : β I≠0) : (I.absNorm:ℝ)≤Hsource :=
    (MixedOriginalNormCap.original_column_norm (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      W hWs σ freq (fun i=>Z^(w i)) (fun _=>Real.rpow_pos_of_pos hZ0 _)
      W₁ W₂ a b ha hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
      hX₁ hX₂ hY₁ hY₂ hXY I hi).2
  have hpoint := hZ.2 θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    R seed hR hRN hseed H hH hholes hHR W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hc₁ hc₂ hc₃ hc₄ hXY d hd hsourcecap
  have hpart : ‖partEnergy false η χ₀ Q m tp S β ballProfile (16*K*Wblock^4)
      Tsec Z ξ Hsource‖≤F*fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
        (frequencyRadius Tsec Z ξ) Hsource Q m χ₀ := by
    apply (partEnergy_norm_le false η χ₀ Q m tp S β ballProfile (16*K*Wblock^4)
      Tsec Z ξ Hsource).trans
    apply le_trans (b:=F*retainedLiveGeometry η tp S β ballProfile (16*K*Wblock^4)
      (frequencyRadius Tsec Z ξ) Hsource Q m χ₀)
    · unfold retainedLiveGeometry
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U _hU
      apply Finset.sum_le_sum
      intro n _hn
      have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
      rw [←physicalBlock_active η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
        (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))]
      by_cases hzero : physicalBlock η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (frequencyRadius Tsec Z ξ)
          (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))=0
      · simp only [liveChildGeometry,if_pos hzero,mul_zero]
        rw [hzero,norm_zero]
      · obtain ⟨τ,_hf,hb⟩ := hpoint η p U
        obtain ⟨hg,hcap⟩ := hgeometry p hp U n hzero
        have hbound := hb tp (frequencyRadius Tsec Z ξ) (16*K*Wblock^4) (ρ p U n) m χ₀
          (fun i=>(n i:ℤ)) hK4 hm hml hm2 hzero hg hcap
        have he := childBlockBudget_normalized degree Cp Z δ volume A (expo w)
          tp (16*K*Wblock^4) hZ0 hvolume hA d hd η p.val.1 p.val.2 hsupp.1 hsupp.2 U
          (fun i=>(n i:ℤ))
        have hnorm : childBlockBudget degree Cp Z δ volume A (expo w)
            tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ)) =
            F*childGeometry η p.val.1 p.val.2 U (16*K*Wblock^4) (fun i=>(n i:ℤ)) := by
          calc
            _ = (childBlockBudget degree Cp Z δ volume A (expo w)
              tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ))/volume)*volume :=
                (div_mul_cancel₀ _ hvolume.ne').symm
            _ = _ := by rw [he];dsimp only [F,analyticBudget];ring
        have hb' : ‖physicalBlock η tp S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
            (frequencyRadius Tsec Z ξ)
            (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
            ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))‖≤
            childBlockBudget degree Cp Z δ volume A (expo w)
              tp (16*K*Wblock^4) d η p.val.1 p.val.2 U (fun i=>(n i:ℤ)) := by
          simpa only [childBlockBudget,pow_one] using hbound
        rw [hnorm] at hb'
        simpa only [liveChildGeometry,if_neg hzero] using hb'
    · exact mul_le_mul_of_nonneg_left
        (retainedLiveGeometry_le_full η tp S β ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource hK4.le Q m χ₀) hF
  rw [source_retained_split η χ₀ Q m tp S β K Wblock Tsec Z ξ Hsource hK hWblock
    (fun I _ hi=>hcolumns I hi),add_div,add_sub_cancel_left,norm_div,
    Complex.norm_real,Real.norm_of_nonneg hWblock.le]
  exact div_le_div_of_nonneg_right hpart hWblock.le

/-- (Native instance, FP statement unchanged.) The localized retained density minus its EXACT exceptional part is
bounded by the common analytic factor times fullRetainedGeometry.
The latter has the proved generic harmonic bound in MixedActualGeometry.
This theorem supplies all analytic envelopes internally. -/
theorem uniform_actual_retained_nonexceptional
    (Holes : ℕ) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH B ε δ lo hi κ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hB : 0≤B)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃Cs Cp : ℝ,0<Cs ∧ 0<Cp ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : α→RayQuotient.Characters M Hray)(w σ freq : α→ℝ)(t V : ℝ)(R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀R seed : Id,R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed →
    ∀H : Finset PrimeIdeal,H⊆enclosure (Cap*Z^Lcap) →
      ((∏I∈holes H,I).absNorm:ℝ)≤Z^BH → (∀i,∀P∈H,P.val∈R₀ i) →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀(t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ),0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ →
      X₁≤Z^L → X₂≤Z^L → Y₁≤Z^L → Y₂≤Z^L → X₁*X₂=Y₁*Y₂ →
    ∀d : Id×Id,∀hd : d.1≠0 ∧ d.2≠0,
    let pool := fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))
    let S := finiteColumns (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂))
    let β := originalColumn (enclosure (Cap*Z^Lcap)) H pool d hd R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t)
      (fun i=>slotProfile W (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂
    let Hsource := sourceNormCap (fun i=>Z^(w i)) b (X₁*X₂) d
    let volume := X₁*X₂*∏i,Z^(w i)
    let A := Cs*diagonalControl ballProfile*(sourceControl control W₁*sourceControl control W₂)^2*
      (sourceHeight t V t₁ t₂)^degree
    Hsource≤Z^B →
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      0<K → 0<Wblock → m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
    ∀ρ : (p : ActiveLabel S β)→(U : Finset (CommonIndex p.val.1 p.val.2))→
      SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource→ℝ,
    (∀p∈liveLabels η S β,∀U,∀n : SourceBlocks p.val.1 p.val.2 U
        (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) Hsource,
      physicalBlock η tp S β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))≠0 →
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤ρ p U n ∧
        ρ p U n≤Mcap) →
      ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
          (fun I : supportedColumns S=>β I*heightCoeff η tp I) K Wblock
          (retainedWeight (frequencyRadius Tsec Z ξ))-
        partEnergy true η χ₀ Q m tp S β ballProfile (16*K*Wblock^4) Tsec Z ξ Hsource/(Wblock:ℂ)‖ ≤
      (analyticBudget degree Cp Z δ volume A (κ*(∑i,w i)+ε) tp d)*
        fullRetainedGeometry η tp S β ballProfile (16*K*Wblock^4)
          (frequencyRadius Tsec Z ξ) Hsource Q m χ₀/Wblock :=
  uniform_actual_retained_nonexceptional_of_supply (α:=α) M Hray hHray Holes W
    a b Mcap L Lslot Lcap Cap BR BH B δ lo hi hWs ha hB hδ Q hQ72 (fun w : α→ℝ=>κ*(∑i,w i)+ε)
    (canonicalSideSupply_native (α:=α) M Hray hHray Holes W a b Mcap L Lslot Lcap Cap
      ((BR+B)+B+BH) B ε lo hi κ hWs hW ha haUpper hb hM hLslot hLcap hCap (by positivity) hB
      hCapb hLordinary hε hβ hκ Q hQt hQ72 hQM)

end
end QRH.DensitySplitThird.CubeFree.FP.MixedActualRetained
