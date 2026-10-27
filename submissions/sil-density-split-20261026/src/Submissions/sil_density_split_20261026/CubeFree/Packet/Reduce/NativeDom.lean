/- Copyright (c) 2026 Sil. Apache-2.0.
The native completion chain in leaf-domination form (WP-G).

Reduction form of FP's `NativePuncturedChildren`, `NativePuncturedInjective`,
`NativePuncturedForward` (with `NativeFiniteHoles`, `NativeInjectiveEnergy`,
`NativeRemainingEnergy`, `NativeForwardEnergy`), on the cube-free kernels.  Each FP
step is an energy inequality with an abstract inner bound; here the steps are composed
down to the canonical leaf energies

  `nativeLeaf … A X₁' X₂' = radialEnergy (poly(χ_z,W₁,X₁') · poly(χ_z,W₂,X₂') ·
     ∏_{i∈A} naturalSlot(χ_z, primePool(Z^{w i}), β_i)) keep Φ K`,

`χ_z = naturalCharacter η z`, with the original relative characters and annular weights in
`β_i` and no holes.  No estimate for a leaf is used: the native leaf
(`NativeNonfixedEnergy.canonical_energy`) is replaced by the abstract bound `E`.

The row data is generic: a character `η`, a keep predicate, a radial profile `Φ` with
bounded support and nonnegative weights, and a scale `K`.  The packed second-step state
of the cube-free step is such a datum.

* `subsets_dom`: common punctures `R` (Möbius over `D ⊆ R`) and finite marked holes;
* `injective_dom`: injective prime tuples (reverse collision completion);
* `remaining_dom`, `uniform_remaining_dom`: frozen labels of the forward expansion;
* `forward_dom`: the forward restriction with its prime-assignment and divisor scalars.

The lengths of the leaves are `X/N(d)/N(D)` (divisor pool `d`, punctures `D ⊆ R`). -/
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.Dom
import Submissions.sil_density_split_20261026.CubeFree.Packet.Reduce.NativePuncturedForward

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.SilDensitySplit.CubeFree.Packet.Reduce
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelRowPools KernelRowProfiles
open ReferencePrimeEnclosure RestorationFamily NativeFiniteHoles NativeInjectiveEnergy
open NativeRemainingEnergy NativeForwardEnergy NativePuncturedInjective
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentLattice CenteredMomentTwist
open OAI.SevenEighths.Record12518109GainDeletion KernelCollisionMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

section Defs
variable {α : Type*}

/-- The original slot coefficient: relative character times annular weight. -/
def slotBeta (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M H) (Z : ℝ)
    (w σ freq : α→ℝ) (i : α) (I : Id) : ℂ :=
  idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
    HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I

/-- The canonical native leaf energy (canonical prime pools, original coefficients at the
inherited height `t`, no holes). -/
def nativeLeaf (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M H) (Z : ℝ)
    (w σ freq : α→ℝ) (t : ℝ) (η : Character) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ) : Finset α → ℝ → ℝ → ℝ :=
  leafEnergy η keep Φ K W₁ W₂ t₁ t₂ (fun i=>primePool M H 2 (Z^(w i)))
    (fun i=>heightCoefficient (slotBeta M H hH W η₀ θ Z w σ freq i) t) (fun i=>Z^(w i))

theorem nativeLeaf_nonneg (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (η : Character) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ)
    (A : Finset α) (X₁ X₂ : ℝ) :
    0≤nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂ :=
  leafEnergy_nonneg η keep Φ K hΦ _ _ _ _ _ _ _ A X₁ X₂

end Defs

theorem holes_height (α : Type*) (β : α→Id→ℂ) (R : α→Finset Id) (t : ℝ) (i : α) :
    holeCoefficient (fun i=>heightCoefficient (β i) t) R i =
      heightCoefficient (holeCoefficient β R i) t := by
  funext I
  by_cases h : I∈R i <;> simp [holeCoefficient,heightCoefficient,h]

theorem shortLengths_below {X₁ X₂ : ℝ} {R : Finset Id} (hR : ∀I∈R,Prime I) (hX₁ : 0<X₁)
    (hX₂ : 0<X₂) : LengthsBelow (shortLengths X₁ X₂ R) X₁ X₂ := by
  intro p hp
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hp
  have hne (E : Finset Id) (hE : E∈R.powerset) : (∏I∈E,I)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hE hI)).ne_zero)
  have h₁ := shortened_positive_le hX₁ (hne D.1 (Finset.mem_product.mp hD).1)
  have h₂ := shortened_positive_le hX₂ (hne D.2 (Finset.mem_product.mp hD).2)
  exact ⟨h₁.1,h₁.2,h₂.1,h₂.2⟩

/-! ### Punctures and holes -/

/-- **Common punctures and finite holes** (reduction form of
`NativePuncturedChildren.canonical_punctured_subsets`). -/
theorem subsets_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 0≤b) (hBmask : 0≤Bmask) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀F : Finset α,∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      LeafDom (nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂)
        (shortLengths X₁ X₂ R) (C*Z^ε)
        (radialEnergy (fun z=>polynomial ((naturalCharacter η z).excludePrimes R hR)
            false W₁ X₁ 0 t₁ *
          polynomial ((naturalCharacter η z).excludePrimes R hR) false W₂ X₂ 0 t₂ *
          ∏i∈F,naturalSlot ((naturalCharacter η z).excludePrimes R hR)
            (primePool M H 2 (Z^(w i)))
            (heightCoefficient (holeCoefficient (slotBeta M H hH W η₀ θ Z w σ freq) R₀ i) t)
            (Z^(w i))) keep Φ K) := by
  classical
  let δ := ε/(2*(Bmask+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  have hδeq : δ*(2*(Bmask+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hbudget : Bmask*δ≤ε/2 := by nlinarith
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  choose CdF hCdF hdelete using fun F : Finset α=>
    CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy F (fun _=>2) (fun _=>B)
      (fun _ _=>hB.le) δ hδ
  let Cd := 1+∑F : Finset α,CdF F
  have hCd : 0<Cd := by
    have hh := Finset.sum_nonneg (fun F (_ : F∈(Finset.univ : Finset (Finset α)))=>(hCdF F).le)
    dsimp [Cd]
    linarith
  have hCdFCd (F : Finset α) : CdF F≤Cd := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=CdF)
      (fun F _=>(hCdF F).le) (Finset.mem_univ F)
    dsimp [Cd]
    linarith
  let cost : ℝ := ((2:ℝ)^(Fintype.card α)*(max 1 ((Holes:ℝ)*B))^(Fintype.card α))^2
  have hcost : 0≤cost := by positivity
  refine ⟨Cd*cost+1,by positivity,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hσ hσhi hR₀ η keep Φ K radial hK hs hΦ R hR hRcap
    F W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let P := fun i=>Z^(w i)
  let pool := fun i=>primePool M H 2 (P i)
  let β₀ := slotBeta M H hH W η₀ θ Z w σ freq
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Prime I := (Finset.mem_filter.mp hI).2.1
  have hβ (i : α) (I : Id) (hI : I∈pool i) : ‖heightCoefficient (β₀ i) t I‖≤B :=
    (hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).ne_zero).1
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using hB.le
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi] using hβ i I hI
  have hD (D : Finset Id) (hD : D∈R.powerset) : (∏I∈D,I)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hD hI)).ne_zero)
  have hmass : (Ideal.absNorm (∏I∈R,I):ℝ)^δ≤Z^(ε/2) := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hRcap hδ.le
    rw [←Real.rpow_mul hZ0.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ hbudget)
  let child : Finset Id×Finset Id×Finset α→ℝ := fun k=>
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁
        (X₁/(Ideal.absNorm (∏I∈k.1,I):ℝ)) 0 t₁ *
      polynomial (naturalCharacter η z) false W₂ (X₂/(Ideal.absNorm (∏I∈k.2.1,I):ℝ)) 0 t₂ *
      ∏i∈F\k.2.2,naturalSlot (naturalCharacter η z) (pool i) (βc i) (P i)) keep Φ K
  have hNR : 0≤(Ideal.absNorm (∏I∈R,I):ℝ)^δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine (LeafDom.comp (fun k : Finset Id×Finset Id×Finset α=>
      k.1∈R.powerset ∧ k.2.1∈R.powerset ∧ k.2.2∈F.powerset) child
      (c:=CdF F*(Ideal.absNorm (∏I∈R,I):ℝ)^δ) hcost ?_ ?_).mass_le ?_
  · intro E hE hE'
    have he := hdelete F R hR (fun z=>naturalCharacter η z)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
      X₁ X₂ a b a b pool βc P keep Φ K E
      hX₁ hX₂ hb hb
      ((normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁)
      ((normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂)
      (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hβc i)
      (fun i _ I hI _=>canonical_pool_norm_le M H _ (hP i) I hI)
      hK hΦ hE (by
        intro D₁ hD₁ D₂ hD₂ J hJ
        simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
          CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂]
        exact hE' (D₁,D₂,J) ⟨hD₁,hD₂,hJ⟩)
    simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
      CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at he
    exact he
  · rintro ⟨D₁,D₂,J⟩ ⟨hD₁,hD₂,hJ⟩
    refine (LeafDom.comp (fun A : Finset α=>A⊆F\J)
      (fun A=>nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂ A
        (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)))
      (c:=cost) (m:=1) zero_le_one ?_ ?_).mass_le (by rw [mul_one])
    · intro E hE hE'
      have he := radial_holes (F\J) (Fintype.card α) Holes (Finset.card_le_univ _)
        (fun z=>polynomial (naturalCharacter η z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 t₁ *
          polynomial (naturalCharacter η z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 t₂)
        (fun z=>naturalCharacter η z) pool R₀ (fun i=>heightCoefficient (β₀ i) t) P B E radial
        hB.le hE (fun i _=>Real.one_le_rpow hZ (hw i)) (fun i _=>hR₀ i)
        (fun i _ I hI=>hβ i I hI) keep Φ K hK hs hΦ (fun A hA=>hE' A hA)
      simp_rw [holes_height] at he
      exact he
    · intro A _
      exact LeafDom.self A (mem_shortLengths D₁ D₂ hD₁ hD₂)
  · have h1 : CdF F*(Ideal.absNorm (∏I∈R,I):ℝ)^δ≤Cd*Z^ε := by
      apply mul_le_mul (hCdFCd F) (hmass.trans (Real.rpow_le_rpow_of_exponent_le hZ
        (by linarith))) hNR hCd.le
    have hZε : 0≤Z^ε := Real.rpow_nonneg hZ0.le _
    nlinarith [mul_le_mul_of_nonneg_right h1 hcost]

/-! ### Injective prime tuples -/

/-- **Reverse collision completion** (reduction form of
`NativePuncturedInjective.canonical_punctured_injective`). -/
theorem injective_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b Lslot Lcap Cap Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 0≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
    ∀(η₀ : Character)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)(t : ℝ)
      (R₀ : α→Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → (∀i,(R₀ i).card≤Holes) →
    ∀(η : Character)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K radial : ℝ),0<K →
      Function.support (Φ:ℝ→ℂ)⊆Set.Iic radial → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,keep z → z≠0) →
    ∀R : Finset Id,∀hR : ∀I∈R,Prime I,(Ideal.absNorm (∏I∈R,I):ℝ)≤Z^Bmask →
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
    ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      LeafDom (nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂)
        (shortLengths X₁ X₂ R) (C*Z^ε)
        (radialEnergy (fun z=>polynomial ((naturalCharacter η z).excludePrimes R hR)
            false W₁ X₁ 0 t₁ *
          polynomial ((naturalCharacter η z).excludePrimes R hR) false W₂ X₂ 0 t₂ *
          injectiveTuplePolynomial (fun i=>fun p : ReferencePrimeEnclosure.primePool (Cap*Z^Lcap)=>
            slotTerm ((naturalCharacter η z).excludePrimes R hR)
              (supportedPool (primePool M H 2 (Z^(w i))))
              (heightCoefficient (holeCoefficient (slotBeta M H hH W η₀ θ Z w σ freq) R₀ i) t)
              (Z^(w i)) p.val)) keep Φ K) := by
  classical
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let ηc := ε/(2*(Lcap+1))
  have hηc : 0<ηc := div_pos hε (by positivity)
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Ci,hCi,hinj⟩ := natural_radial_energy (α:=α) (2*B) ηc (by linarith) hηc
  obtain ⟨Cs,hCs,hsub⟩ := subsets_dom M H hH (α:=α) (Holes+Fintype.card α*Fintype.card α) W
    a b Bmask (ε/2) lo hi hWs hW ha hb hBmask (half_pos hε)
  refine ⟨Cap^ηc*Ci*Cs+1,by positivity,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let X := Cap*Z^Lcap
  let atoms := ReferencePrimeEnclosure.primePool X
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := slotBeta M H hH W η₀ θ Z w σ freq
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  let χ := fun z=>(naturalCharacter η z).excludePrimes R hR
  let D := fun z=>polynomial (χ z) false W₁ X₁ 0 t₁*polynomial (χ z) false W₂ X₂ 0 t₂
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_rpow hZ hLcap0)
  have hatoms (I : Id) (hI : I∈atoms) : Supported I ∧ (I.absNorm:ℝ)≤X :=
    ⟨(Finset.mem_filter.mp hI).2.2,
      ((CenteredMomentSourceMass.mem_idealBall _ _).mp (Finset.mem_filter.mp hI).1).2⟩
  have hpool (i : α) : pool i⊆atoms :=
    canonical_pool_enclosed M H Z (w i) Lcap Cap hZ ((hwL i).trans hLcap) hCap
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i :=
    ⟨(Finset.mem_filter.mp hI).2,canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1⟩
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,slotBeta,B] using he
  refine (LeafDom.comp (fun k : Finset α×(α→Finset Id)=>
      ∀i∈k.1,(k.2 i).card≤Fintype.card α*Fintype.card α)
    (fun k=>radialEnergy (fun z=>D z*∏i∈k.1,naturalSlot (χ z) (pool i)
      (holeCoefficient βc k.2 i) (P i)) keep Φ K)
    (c:=Ci*X^ηc) (m:=Cs*Z^(ε/2)) (by positivity) ?_ ?_).mass_le ?_
  · intro E hE hE'
    exact hinj X hX atoms hatoms D χ pool βc P E hpool hE
      (fun z i p=>slotTerm_bound _ _ _ _ B (hP i) (zero_le_one.trans hB) (hp i) (hβc i) p.val)
      keep Φ K radial hK hs hΦ (fun T Rf hRf=>hE' (T,Rf) hRf)
  · rintro ⟨T,Rf⟩ hRf
    have hbudget (i : α) :
        (R₀ i∪(if i∈T then Rf i else ∅)).card≤Holes+Fintype.card α*Fintype.card α := by
      by_cases hi : i∈T
      · simpa only [hi,ite_true] using (Finset.card_union_le (R₀ i) (Rf i)).trans
          (Nat.add_le_add (hR₀ i) (hRf i hi))
      · simp only [hi,ite_false,Finset.union_empty]
        exact (hR₀ i).trans (Nat.le_add_right _ _)
    have hh := hsub Z hZ η₀ θ w σ freq t (fun i=>R₀ i∪(if i∈T then Rf i else ∅))
      hw hσ hσhi hbudget η keep Φ K radial hK hs hΦ R hR hRcap T W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂
    refine hh.of_eq ?_
    have hm (i : α) (hi : i∈T) : holeCoefficient βc Rf i=
        heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t := by
      funext I
      by_cases h₁ : I∈R₀ i <;> by_cases h₂ : I∈Rf i <;>
        simp [βc,holeCoefficient,heightCoefficient,hi,h₁,h₂]
    have hmask : (fun z=>D z*∏i∈T,naturalSlot (χ z) (pool i) (holeCoefficient βc Rf i) (P i))=
        (fun z=>D z*∏i∈T,naturalSlot (χ z) (pool i)
          (heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t)
            (P i)) := by
      funext z
      congr 1
      exact Finset.prod_congr rfl (fun i hi=>by rw [hm i hi])
    dsimp only
    rw [hmask,punctured_supported_slots η R hR D T (fun i=>primePool M H 2 (P i))
      (fun i=>heightCoefficient (holeCoefficient β₀ (fun i=>R₀ i∪(if i∈T then Rf i else ∅)) i) t) P
      keep hkeep]
  · have hcut := cutoff_loss Z Lcap Cap ε 0 hZ hLcap0 hCap0.le hε
    simp only [zero_add] at hcut
    have hX0 : 0≤X^ηc := Real.rpow_nonneg (by positivity) _
    have h1 : Ci*X^ηc*(Cs*Z^(ε/2))=Ci*Cs*(X^ηc*Z^(ε/2)) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hcut (show 0≤Ci*Cs by positivity)
    have hZε : 0≤Z^ε := Real.rpow_nonneg hZ0.le _
    nlinarith

end

end QRH.SilDensitySplit.CubeFree.Packet.Reduce
