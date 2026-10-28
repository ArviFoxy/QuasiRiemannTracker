/- Copyright (c) 2026 Sil. Apache-2.0.
The forward restriction in leaf-domination form (WP-G).

Reduction form of FP's `NativePuncturedForward` (`canonical_punctured_remaining`,
`canonical_uniform_punctured_remaining`, `canonical_punctured_forward`), on the cube-free
kernels: the forward K₃ expansion of the punctured row (prime assignments `frozen`, divisor
pool `d`, scalars summed before the physical norm by the cube-free forward mass
`KernelFamilyEnergy.actual_subpower_energy`) followed by the frozen-label remaining sums,
which are injective tuples on the unfrozen slots with the frozen primes as marked holes
(`NativeDom.injective_dom`).  The leaves are the canonical native leaves on all slots,
with lengths `X/N(d)/N(D)` (`forwardLengths`) and heights `2πtᵢ`. -/
import Submissions.density_split_fourth.CubeFree.Packet.Reduce.NativeDom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace QRH.DensitySplitThird.CubeFree.Packet.Reduce
open Candidate.FourthPower QRH.DensitySplitThird.CubeFree.FP

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
open CenteredMomentRayMaskedFloor HeckeDyadic
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Leaves on a subtype of the slots are leaves on all slots. -/
theorem nativeLeaf_subtype {α : Type*} (p : α→Prop) (W : ℝ→ℂ) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (Z : ℝ) (w σ freq : α→ℝ) (t : ℝ) (η : Character)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ : ℝ)
    (A : Finset {i // p i}) (X₁ X₂ : ℝ) :
    nativeLeaf M H hH W η₀ (fun i=>θ i.val) Z (fun i=>w i.val) (fun i=>σ i.val)
        (fun i=>freq i.val) t η keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂ =
      nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂
        (A.map (Function.Embedding.subtype p)) X₁ X₂ := by
  unfold nativeLeaf leafEnergy leafRow
  congr 1
  funext z
  rw [Finset.prod_map]
  rfl

/-- **Frozen-label remaining sums** for a fixed frozen slot set (reduction form of
`NativePuncturedForward.canonical_punctured_remaining`). -/
theorem remaining_dom {α : Type*} [Fintype α] (T : Finset α) (Holes : ℕ)
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
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀frozen : T→enclosure (Cap*Z^Lcap),
      LeafDom (nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂)
        (shortLengths (X₁/(D₁.absNorm:ℝ)) (X₂/(D₂.absNorm:ℝ)) R) (C*Z^ε)
        (radialEnergy (fun z=>polynomial ((naturalCharacter η z).excludePrimes R hR) false W₁
            (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
          polynomial ((naturalCharacter η z).excludePrimes R hR) false W₂
            (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
          remainingSum T (naturalCoefficients ((naturalCharacter η z).excludePrimes R hR)
            (enclosure (Cap*Z^Lcap)) (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
            (fun i=>heightCoefficient (holeCoefficient (slotBeta M H hH W η₀ θ Z w σ freq) R₀ i) t)
            (fun i=>Z^(w i))) frozen (fun _=>1)) keep Φ K) := by
  classical
  obtain ⟨C,hC,hinj⟩ := injective_dom M H hH (α:={i // i∉T}) (Holes+T.card) W
    a b Lslot Lcap Cap Bmask ε lo hi hWs hW ha hb hLslot hLcap hCap hBmask hε
  refine ⟨C,hC,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ D₁ D₂ hD₁ hD₂ frozen
  have hbudget (i : {i // i∉T}) :
      (R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen).card≤Holes+T.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (hR₀ i.val) (frozenHoles_card _ _ _))
  have he := hinj Z hZ η₀ (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
    t (fun i=>R₀ i.val∪frozenHoles T (enclosure (Cap*Z^Lcap)) frozen)
    (fun i=>hw i.val) (fun i=>hwL i.val) (fun i=>hσ i.val) (fun i=>hσhi i.val) hbudget
    η keep Φ K radial hK hs hΦ hkeep R hR hRcap W₁ W₂ hs₁ hs₂
    t₁ t₂ (X₁/(D₁.absNorm:ℝ)) (X₂/(D₂.absNorm:ℝ))
    (shortened_positive_le hX₁ hD₁).1 (shortened_positive_le hX₂ hD₂).1
  refine (he.reindex (fun A=>A.map (Function.Embedding.subtype _))
    (fun A X₁ X₂=>nativeLeaf_subtype M H hH (fun i=>i∉T) W η₀ θ Z w σ freq t η keep Φ K
      W₁ W₂ t₁ t₂ A X₁ X₂)).of_eq ?_
  simp_rw [remaining_as_injective,combined_height_holes]
  rfl

/-- The frozen-label remaining sums with one constant for every frozen slot set (reduction
form of `NativePuncturedForward.canonical_uniform_punctured_remaining`). -/
theorem uniform_remaining_dom {α : Type*} [Fintype α] (Holes : ℕ)
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
    ∀D₁ D₂ : Ideal O,D₁≠0 → D₂≠0 →
    ∀T : Finset α,∀frozen : T→enclosure (Cap*Z^Lcap),
      LeafDom (nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂)
        (shortLengths (X₁/(D₁.absNorm:ℝ)) (X₂/(D₂.absNorm:ℝ)) R) (C*Z^ε)
        (radialEnergy (fun z=>polynomial ((naturalCharacter η z).excludePrimes R hR) false W₁
            (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
          polynomial ((naturalCharacter η z).excludePrimes R hR) false W₂
            (X₂/(D₂.absNorm:ℝ)) 0 t₂ *
          remainingSum T (naturalCoefficients ((naturalCharacter η z).excludePrimes R hR)
            (enclosure (Cap*Z^Lcap)) (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
            (fun i=>heightCoefficient (holeCoefficient (slotBeta M H hH W η₀ θ Z w σ freq) R₀ i) t)
            (fun i=>Z^(w i))) frozen (fun _=>1)) keep Φ K) := by
  classical
  choose CT hCT hrem using fun T : Finset α=>
    remaining_dom M H hH T Holes W a b Lslot Lcap Cap Bmask ε lo hi hWs hW ha hb hLslot hLcap
      hCap hBmask hε
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
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ D₁ D₂ hD₁ hD₂ T frozen
  exact (hrem T Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep
    R hR hRcap W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ D₁ D₂ hD₁ hD₂ frozen).mass_le
    (mul_le_mul_of_nonneg_right (hCTC T) (Real.rpow_nonneg (zero_le_one.trans hZ) _))

/-- The leaf length pairs of the forward restriction: `(X₁/N(d₁)/N(D₁), X₂/N(d₂)/N(D₂))` over
the divisor pool `d` and the common punctures `D₁, D₂ ⊆ R`. -/
def forwardLengths (S : Finset PrimeIdeal) (b X₁ X₂ : ℝ) (R : Finset Id) : Finset (ℝ×ℝ) :=
  (divisorPool (supportedRectangle S b X₁ X₂)).biUnion (fun d=>
    shortLengths (X₁/(d.1.absNorm:ℝ)) (X₂/(d.2.absNorm:ℝ)) R)

theorem forwardLengths_below {S : Finset PrimeIdeal} {b X₁ X₂ : ℝ} {R : Finset Id}
    (hR : ∀I∈R,Prime I) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    LengthsBelow (forwardLengths S b X₁ X₂ R) X₁ X₂ := by
  intro p hp
  obtain ⟨d,hd,hp⟩ := Finset.mem_biUnion.mp hp
  have hn := divisor_supported hd
  have h₁ := shortened_positive_le hX₁ hn.1
  have h₂ := shortened_positive_le hX₂ hn.2.1
  exact (shortLengths_below hR h₁.1 h₂.1).mono h₁.2 h₂.2 p hp

/-- **Forward restriction with common punctures and marked holes** (reduction form of
`NativePuncturedForward.canonical_punctured_forward`).  The prime-assignment and divisor
scalars of the forward K₃ expansion are summed before the physical norm; the leaves have
heights `2πtᵢ` and lengths in `forwardLengths`. -/
theorem forward_dom {α : Type*} [Fintype α] (Holes : ℕ)
    (W : ℝ→ℂ) (a b L Lslot Lcap Cap Bmask ε lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (hb : 1≤b) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBmask : 0≤Bmask) (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) :
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
    ∀(t₁ t₂ X₁ X₂ : ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
      LeafDom (nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂
          (2*Real.pi*t₁) (2*Real.pi*t₂))
        (forwardLengths (enclosure (Cap*Z^Lcap)) b X₁ X₂ R) (C*Z^ε)
        (radialEnergy (fun z=>row false (enclosure (Cap*Z^Lcap))
          ((naturalCharacter η z).excludePrimes R hR)
          (fun i=>supportedPool (primePool M H 2 (Z^(w i))))
          (fun i=>heightCoefficient (holeCoefficient (slotBeta M H hH W η₀ θ Z w σ freq) R₀ i) t)
          (fun i=>Z^(w i)) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂) keep Φ K) := by
  have hLcap0 := hLslot.trans hLcap
  have hCap0 : 0<Cap := by linarith
  let δ := ε/(2*(Lcap+1))
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨B₀,hB₀,hcoeff⟩ := slot_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW.continuous
  let B := max 1 B₀
  have hB : 1≤B := le_max_left _ _
  obtain ⟨Cf,hCf,hforward⟩ := radial_forward_energy (α:=α) B δ (zero_le_one.trans hB) hδ
  obtain ⟨Cc,hCc,hchildren⟩ := uniform_remaining_dom M H hH (α:=α) Holes W
    a b Lslot Lcap Cap Bmask (ε/2) lo hi hWs hW ha (zero_le_one.trans hb) hLslot hLcap hCap
    hBmask (half_pos hε)
  refine ⟨Cf*Cap^δ*Cc+1,by positivity,?_⟩
  intro Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep R hR hRcap
    W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  let X := Cap*Z^Lcap
  let primes := enclosure X
  let P := fun i=>Z^(w i)
  let pool := fun i=>supportedPool (primePool M H 2 (P i))
  let β₀ := slotBeta M H hH W η₀ θ Z w σ freq
  let βc := fun i=>heightCoefficient (holeCoefficient β₀ R₀ i) t
  have hX : 1≤X := one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_rpow hZ hLcap0)
  have hP (i : α) : 0<P i := Real.rpow_pos_of_pos hZ0 _
  have hp (i : α) (I : Id) (hI : I∈pool i) : Supported I ∧ (I.absNorm:ℝ)≤2*P i := by
    refine ⟨(Finset.mem_filter.mp hI).2,?_⟩
    exact canonical_pool_norm_le M H _ (hP i) I (Finset.mem_filter.mp hI).1
  have hβc (i : α) (I : Id) (hI : I∈pool i) : ‖βc i I‖≤B := by
    have he := ((hcoeff (relativeCharacter M H hH η₀ (θ i)) (P i) (σ i) (freq i) t
      (hP i) (hσ i) (hσhi i) I (hp i I hI).1.1).1).trans (le_max_right 1 B₀)
    by_cases hi : I∈R₀ i
    · simpa [βc,holeCoefficient,heightCoefficient,hi] using (zero_le_one.trans hB)
    · simpa only [βc,heightCoefficient,holeCoefficient,ite_eq_right hi,β₀,slotBeta,B] using he
  have henclose (I : Id) (hI : Supported I)
      (hlen : (I.absNorm:ℝ)≤b*X₁ ∨ (I.absNorm:ℝ)≤b*X₂) :
      primeSupport I⊆primeValues primes := by
    apply support_enclosed X I hI
    have hc (Y : ℝ) (hY : 0<Y) (hYc : Y≤Z^L) : b*Y≤X :=
      mul_le_mul hCapb (hYc.trans (Real.rpow_le_rpow_of_exponent_le hZ hLordinary))
        hY.le hCap0.le
    exact hlen.elim (fun h=>h.trans (hc X₁ hX₁ hc₁)) (fun h=>h.trans (hc X₂ hX₂ hc₂))
  let Dpool := divisorPool (supportedRectangle primes b X₁ X₂)
  refine (LeafDom.comp (fun k : (Σ T : Finset α,T→primes)×(Id×Id)=>
      Function.Injective k.1.2 ∧ k.2∈Dpool)
    (fun k=>radialEnergy (fun z=>
      polynomial ((naturalCharacter η z).excludePrimes R hR) false W₁
        (X₁/(k.2.1.absNorm:ℝ)) 0 (2*Real.pi*t₁)*
      polynomial ((naturalCharacter η z).excludePrimes R hR) false W₂
        (X₂/(k.2.2.absNorm:ℝ)) 0 (2*Real.pi*t₂)*
      remainingSum k.1.1 (naturalCoefficients ((naturalCharacter η z).excludePrimes R hR)
        primes pool βc P) k.1.2 (fun _=>1)) keep Φ K)
    (c:=Cf*X^δ) (m:=Cc*Z^(ε/2)) (by positivity) ?_ ?_).mass_le ?_
  · intro E hE hE'
    exact hforward X hX primes (enclosure_bound X)
      (fun z=>(naturalCharacter η z).excludePrimes R hR)
      pool βc P hP hp hβc W₁ W₂ b X₁ X₂ t₁ t₂ E (zero_le_one.trans hb) hX₁ hX₂ hE
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2)
      keep Φ K radial hK hs hΦ
      (fun z hz=>deleted_off_supported _
        (natural_character_off_supported η z (hkeep z hz)) R hR)
      henclose (fun T frozen hf d hd=>hE' (⟨T,frozen⟩,d) ⟨hf,hd⟩)
  · rintro ⟨⟨T,frozen⟩,d⟩ ⟨_,hd⟩
    have hn := divisor_supported hd
    refine (hchildren Z hZ η₀ θ w σ freq t R₀ hw hwL hσ hσhi hR₀ η keep Φ K radial hK hs hΦ hkeep
      R hR hRcap W₁ W₂ hs₁ hs₂ (2*Real.pi*t₁) (2*Real.pi*t₂) X₁ X₂ hX₁ hX₂
      d.1 d.2 hn.1 hn.2.1 T frozen).family_le ?_
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨d,hd,hp⟩
  · have hcut := cutoff_loss Z Lcap Cap ε 0 hZ hLcap0 hCap0.le hε
    simp only [zero_add] at hcut
    have h1 : Cf*X^δ*(Cc*Z^(ε/2))=Cf*Cc*(X^δ*Z^(ε/2)) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hcut (show 0≤Cf*Cc by positivity)
    have hZε : 0≤Z^ε := Real.rpow_nonneg hZ0.le _
    have hCapδ : 0≤Cap^δ := Real.rpow_nonneg hCap0.le _
    nlinarith

end

end QRH.DensitySplitThird.CubeFree.Packet.Reduce
