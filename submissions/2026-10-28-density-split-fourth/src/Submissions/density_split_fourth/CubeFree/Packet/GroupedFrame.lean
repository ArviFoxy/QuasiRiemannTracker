/- Copyright (c) 2026 Sil. Apache-2.0.
The concrete side frame of the cube-free second step (Seam B, WP-H).

Structural data `GData L` (slot count `N`, ray modulus, slot profile `W`, `bΦ`, `η₀`, `Q`, and
the constants of the reduction chain); a *source* `GSrc` (one physical column after the
selection, the D-Cauchy and the D⁴ transfer: slot data, its two ordinary profiles and
lengths, the first-step packed twist `V₀ = V_C` and the Gauss row log-scale `k`); a *label*
`GLabel` (second-step packet: side characters and dictionary indices, row twist
`A₂ = commonFrequencyGenerator·nonunitFrequencyGenerator`, dyadic index `n`, genuine common
ideal `G`, seed, artificial divisor `D = t₂`, holes, extracted pair `d`, the common factor
whose `ρ = 2^ω` enters, and the scalar prefactor). `Fits η r x` records the hypotheses under
which the label is a packet of the source (packing `τ = anchor · idealRowHom(V₀A₂)` off the
mask, as supplied by `Packet.Dictionary.second_packed_idealCoeff`; the cube-free column data
of `MixedCanonicalEnvelope.uniform_canonical_source_envelope`; and the Poisson geometry
`N(A₂)·K ≤ Z^{2a-k+mesh}`).

Frame (`gFrame`):
* `energy r x v = N(G)·N(t₂)·N(d₁)N(d₂)·Z^k / X² · labelEnergy` (the literal one-sided label energy of
  `Reduce.labelEnergy`, i.e. the left side of FP's `uniform_canonical_source_envelope`,
  times the source normalization `(Z^k/X)·X⁻¹`, CF (5.3)); `0` off `Fits`;
* `weight x = ρ(common)·‖prefactor‖·N(t₂)⁻¹`;
* `onRow x y = A₂ ∣ y` (the packed row of side `r` is `V₀ y`);
* `envelope r x = log_Z (N(V₀A₂)·K)` (the original `H = 2a - k + q₀`), `logScale r = a + q₀`
  with `a = log_Z(X₁X₂∏Z^{wᵢ})`, `q₀ = log_Z N(V₀)`;
* `P r = max(ℓ(X₁)+ℓ(X₂), ℓ(Y₁)+ℓ(Y₂))`, `s r = ∑ wᵢ`.

The amplitude of the grouped bound must depend on the (existential) degree and seminorm set
(heights and ordinary profiles are source data quantified after `Z`): `gAmp r J S =
(‖W₁‖_S ‖W₂‖_S)² · (1+|t|+V+|t₁|+|t₂|)^J`, as FP's `amplitude d.root d.t₀ d.V J control Cside`.
`GroupedSideBoundA` is `Second.GroupedSideBound` with this amplitude. -/
import Submissions.density_split_fourth.CubeFree.Packet.GroupedClass
import Submissions.density_split_fourth.CubeFree.Packet.GroupedCount
import Submissions.density_split_fourth.CubeFree.Second.SeamBUse
import Submissions.density_split_fourth.CubeFree.Leaf.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace QRH.DensitySplitThird.CubeFree.Packet.Grouped
open Candidate.FourthPower QRH.DensitySplitThird.CubeFree.FP QRH.DensitySplitThird.CubeFree.Packet.Reduce

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
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O

/-! ### Structural data, sources, labels -/

/-- Structural data `θ` of the grouped side frame (fixed before the constants). The ordinary
length exponent `L` (`X ≤ Z^L`) is a parameter of the frame family; the Seam A call needs
the plain-length cap `L + 1`. -/
structure GData (L : ℝ) where
  N : ℕ
  rayM : Ideal O
  [nz : NeZero rayM]
  Hray : Subgroup (O ⧸ rayM)ˣ
  hH : RayOrthogonality.globalUnits rayM ≤ Hray
  W : ℝ → ℂ
  hW : ContDiff ℝ ∞ W
  hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2
  bΦ : ℝ
  hbΦ : 2 ≤ bΦ
  η₀ : Character
  Q : Ideal O
  hQ : Q ≤ rayM
  hQ0 : internalQ Q η₀ ≠ 0
  hQt : internalQ Q η₀ ≠ ⊤
  hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}
  Holes : ℕ
  a : ℝ
  b : ℝ
  Lcap : ℝ
  Cap : ℝ
  Bmask : ℝ
  ha : 1/4 ≤ a
  hb1 : 1 ≤ b
  hb : b ≤ 9/4
  hLcap : 1 ≤ Lcap
  hLL : L ≤ Lcap
  hCap : 2 ≤ Cap
  hCapb : b ≤ Cap
  hBmask : 0 ≤ Bmask

attribute [instance] GData.nz

local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem GData.ha0 {L : ℝ} (θ : GData L) : 0 < θ.a := lt_of_lt_of_le (by norm_num) θ.ha

/-- One physical column (source) of the second step at scale `Z`. -/
structure GSrc {L : ℝ} (θ : GData L) (mesh Z : ℝ) where
  hZ : 1 < Z
  χ : Fin θ.N → RayQuotient.Characters θ.rayM θ.Hray
  w : Fin θ.N → ℝ
  σ : Fin θ.N → ℝ
  freq : Fin θ.N → ℝ
  t : ℝ
  Vf : ℝ
  R₀ : Fin θ.N → Finset (Ideal O)
  hw : ∀ i, 0 ≤ w i
  hwm : ∀ i, w i ≤ mesh
  hσ : ∀ i, σ i = 33/50
  hVf : 0 ≤ Vf
  hfreq : ∀ i, |freq i| ≤ Vf
  hR₀ : ∀ i, (R₀ i).card ≤ θ.Holes
  W₁ : 𝓢(ℝ,ℂ)
  W₂ : 𝓢(ℝ,ℂ)
  hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc θ.a θ.b
  hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc θ.a θ.b
  t₁ : ℝ
  t₂ : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  hX₁ : 0 < X₁
  hX₂ : 0 < X₂
  hY₁ : 0 < Y₁
  hY₂ : 0 < Y₂
  hX₁L : X₁ ≤ Z^L
  hX₂L : X₂ ≤ Z^L
  hY₁L : Y₁ ≤ Z^L
  hY₂L : Y₂ ≤ Z^L
  hXY : X₁ * X₂ = Y₁ * Y₂
  V₀ : O
  hV₀ : V₀ ≠ 0
  kLog : ℝ

/-- A second-step label at scale `Z`; side-dependent data are functions of the source. -/
structure GLabel {L : ℝ} (θ : GData L) (mesh Z : ℝ) where
  char : GSrc θ mesh Z → Character
  anchor : GSrc θ mesh Z → DictIdx
  mask : GSrc θ mesh Z → O
  twist : O
  n : Fin 4 → ℤ
  R : Ideal O
  G : Ideal O
  seed : Ideal O
  D : Ideal O
  holesH : Finset PrimeIdeal
  d : Ideal O × Ideal O
  common : Ideal O
  prefactor : ℂ

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The column volume `X = X₁X₂∏Z^{wᵢ}` and its log-width `a`. -/
def GSrc.vol (r : GSrc θ mesh Z) : ℝ := r.X₁ * r.X₂ * ∏ i, Z^(r.w i)
def GSrc.colLog (r : GSrc θ mesh Z) : ℝ := Real.logb Z r.vol
/-- The twist log-width `q₀ = log_Z N(V₀)`. -/
def GSrc.twistLog (r : GSrc θ mesh Z) : ℝ := Real.logb Z ((Ideal.span {r.V₀}).absNorm : ℝ)
/-- The source height polynomial base. -/
def GSrc.height (r : GSrc θ mesh Z) : ℝ := 1 + |r.t| + r.Vf + |r.t₁| + |r.t₂|

theorem GSrc.vol_pos (r : GSrc θ mesh Z) (hZ : 0 < Z) : 0 < r.vol :=
  mul_pos (mul_pos r.hX₁ r.hX₂) (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos hZ _)

theorem GSrc.one_le_height (r : GSrc θ mesh Z) : 1 ≤ r.height := by
  unfold GSrc.height
  linarith [abs_nonneg r.t, r.hVf, abs_nonneg r.t₁, abs_nonneg r.t₂]

/-- The label is a packet of the source. -/
structure Fits (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : Prop where
  twist_ne : x.twist ≠ 0
  mask_ne : x.mask r ≠ 0
  coef : ∀ I : Ideal O, Supported I → IsCoprime I (Ideal.span {x.mask r}) →
    idealCoeff (x.char r) I = idealCoeff (anchors η (x.anchor r)) I *
      CanonicalRowCompletion.idealRowHom (r.V₀ * x.twist) I
  R_ne : x.R ≠ 0
  G_ne : x.G ≠ 0
  seed_dvd : x.seed ∣ x.G
  D_sq : Squarefree x.D
  /-- norm caps of the genuine common ideal and of `t₂` (from the radical cap: `G` cube-free,
  `t₂` squarefree) -/
  G_cap : (x.G.absNorm : ℝ) ≤ Z^(2*θ.Bmask)
  D_cap : (x.D.absNorm : ℝ) ≤ Z^θ.Bmask
  G_mask : ∀ I : Ideal O, IsCoprime x.G I → IsCoprime I (Ideal.span {x.mask r})
  holes_sub : x.holesH ⊆ enclosure (θ.Cap * Z^θ.Lcap)
  cap : (Ideal.absNorm (∏ I ∈ primeSupport ((x.R * x.G) * x.D) ∪ holes x.holesH, I) : ℝ) ≤
    Z^θ.Bmask
  holes_R₀ : ∀ i, ∀ P ∈ x.holesH, P.val ∈ r.R₀ i
  d₁ : x.d.1 ≠ 0
  d₂ : x.d.2 ≠ 0
  dual : Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1)) ≤
    2 * r.colLog - r.kLog + mesh

/-- The literal one-sided label energy of a fitting label on a source. -/
def rawEnergy (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (h : Fits η r x)
    (v : ℝ) : ℝ :=
  labelEnergy θ.rayM θ.Hray θ.hH θ.W θ.η₀ r.χ Z r.w r.σ r.freq r.t r.R₀ (x.char r)
    (internalQ θ.Q θ.η₀) x.n θ.Cap θ.Lcap x.R x.G h.G_ne x.seed x.D x.holesH r.W₁ r.W₂
    r.t₁ r.t₂ θ.b r.X₁ r.X₂ r.Y₁ r.Y₂ x.d ⟨h.d₁, h.d₂⟩ v

theorem rawEnergy_nonneg (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z)
    (h : Fits η r x) (v : ℝ) : 0 ≤ rawEnergy η r x h v := by
  unfold rawEnergy labelEnergy
  exact CenteredMomentRestrictedSourceNormalization.sourceRestrictedEnergy_nonneg _ _ _ _ _ _
    (dyadicScale_pos _) (fun _ => ballProfile_nonneg _)

/-- The source normalization `Z^k / X²`. -/
def GSrc.norm (r : GSrc θ mesh Z) : ℝ := Z^r.kLog / r.vol^2

/-- The frame energy: the literal label energy with the label's extraction gains
`N(G)·N(t₂)·N(d₁)N(d₂)` (`pairNorm d`, written out) and the source normalization
`Z^k/X²`. -/
def gEnergy (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (v : ℝ) : ℝ :=
  if h : Fits η r x then
    (x.G.absNorm : ℝ) * (x.D.absNorm : ℝ) *
      ((x.d.1.absNorm : ℝ) * (x.d.2.absNorm : ℝ)) * r.norm * rawEnergy η r x h v else 0

/-- `ρ(G) = 2^{ω(G)}`. -/
def rho (G : Ideal O) : ℝ := (2:ℝ)^(primeSupport G).card

def gWeight (x : GLabel θ mesh Z) : ℝ := rho x.common * ‖x.prefactor‖ / (x.D.absNorm : ℝ)

theorem gWeight_nonneg (x : GLabel θ mesh Z) : 0 ≤ gWeight x := by
  unfold gWeight rho; positivity

def gEnvelope (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : ℝ :=
  Real.logb Z (((Ideal.span {r.V₀ * x.twist}).absNorm : ℝ) * dyadicScale (x.n 1))

def gP (r : GSrc θ mesh Z) : ℝ :=
  max (length Z r.X₁ + length Z r.X₂) (length Z r.Y₁ + length Z r.Y₂)

/-- The concrete side frame. -/
def gFrame (L : ℝ) (θ : GData L) (mesh : ℝ) (η : Character) (Z : ℝ) : Second.SideFrame where
  Src := GSrc θ mesh Z
  Label := GLabel θ mesh Z
  energy := gEnergy η
  energy_nonneg r x v := by
    unfold gEnergy
    split_ifs with h
    · have hZ : 0 ≤ Z^r.kLog / r.vol^2 :=
        div_nonneg (Real.rpow_nonneg (zero_le_one.trans r.hZ.le) _) (sq_nonneg _)
      exact mul_nonneg (mul_nonneg (by positivity) hZ) (rawEnergy_nonneg η r x h v)
    · exact le_rfl
  weight := gWeight
  onRow x y := x.twist ∣ y
  envelope := gEnvelope
  logScale r := r.colLog + r.twistLog
  P := gP
  s r := ∑ i, r.w i
  amplitude _ := 1
  amplitude_nonneg _ := zero_le_one

/-- The grouped amplitude with degree `J` and seminorm set `S`. -/
def gAmp (L : ℝ) (θ : GData L) (mesh : ℝ) (η : Character) (Z : ℝ)
    (r : (gFrame L θ mesh η Z).Src) (J : ℕ) (S : Finset (ℕ×ℕ)) : ℝ :=
  (sourceControl S r.W₁ * sourceControl S r.W₂)^2 * r.height^J

/-- **Seam B with the corrected amplitude.** Identical to `Second.GroupedSideBound` except
that the amplitude of the source may depend on the existential degree and seminorm set. -/
def GroupedSideBoundA {Θ : Type}
    (Frame : Θ → ℝ → Character → ℝ → Second.SideFrame)
    (amp : ∀ θ mesh η Z, (Frame θ mesh η Z).Src → ℕ → Finset (ℕ×ℕ) → ℝ)
    (price : Price) (Mmin Mmax : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
  ∀ (θ : Θ) (η : Character),
  ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
  ∀ (r : (Frame θ mesh η Z).Src) (labels : Finset (Frame θ mesh η Z).Label) (w₀ H : ℝ),
    Second.AdmissibleGroup (Frame θ mesh η Z) Mmin Mmax mesh ε Z r labels H →
    ∀ v : ℝ,
      ∑ x ∈ labels, (Frame θ mesh η Z).weight x * (Frame θ mesh η Z).energy r x v ≤
        C * amp θ mesh η Z r degree control * (1 + ‖v‖)^(2*degree) *
          Z^((Frame θ mesh η Z).logScale r +
            price.f w₀ ((Frame θ mesh η Z).P r) ((Frame θ mesh η Z).s r) H + ε)

/-! ### Elementary frame facts -/

theorem absNorm_span_pos (V : O) (hV : V ≠ 0) : 0 < ((Ideal.span {V}).absNorm : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hV))

theorem absNorm_span_mul (V A : O) :
    ((Ideal.span {V * A}).absNorm : ℝ) =
      ((Ideal.span {V}).absNorm : ℝ) * ((Ideal.span {A}).absNorm : ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]

theorem gEnvelope_eq (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (hx : x.twist ≠ 0) :
    gEnvelope r x = r.twistLog +
      Real.logb Z (((Ideal.span {x.twist}).absNorm : ℝ) * dyadicScale (x.n 1)) := by
  unfold gEnvelope GSrc.twistLog
  rw [absNorm_span_mul, mul_assoc, Real.logb_mul (absNorm_span_pos _ r.hV₀).ne'
    (mul_pos (absNorm_span_pos _ hx) (dyadicScale_pos _)).ne']

/-- The fibre at a packed row `y` of side `r` is the frame fibre at `y / V₀`. -/
theorem fibre_packed (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
    (f : GLabel θ mesh Z → ℝ) (hf : ∀ x, 0 ≤ f x) (B R : ℝ) (hB : 0 ≤ B)
    (hfib : ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ R →
      ∑ x ∈ labels.filter (fun x => x.twist ∣ y), f x ≤ B)
    (y : O) (hy : y ≠ 0) (hyR : ((Ideal.span {y}).absNorm : ℝ) ≤ R) :
    ∑ x ∈ labels.filter (fun x => r.V₀ * x.twist ∣ y), f x ≤ B := by
  by_cases hV : r.V₀ ∣ y
  · obtain ⟨y', rfl⟩ := hV
    have hy' : y' ≠ 0 := fun h => hy (by rw [h, mul_zero])
    have heq : labels.filter (fun x => r.V₀ * x.twist ∣ r.V₀ * y') =
        labels.filter (fun x => x.twist ∣ y') := by
      apply Finset.filter_congr
      intro x _
      exact mul_dvd_mul_iff_left r.hV₀
    rw [heq]
    refine hfib y' hy' (le_trans ?_ hyR)
    rw [absNorm_span_mul]
    have h1 := absNorm_span_pos _ r.hV₀
    have h2 : (1:ℝ) ≤ ((Ideal.span {r.V₀}).absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h1.ne')
    have h3 : (0:ℝ) ≤ ((Ideal.span {y'}).absNorm : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hempty : labels.filter (fun x => r.V₀ * x.twist ∣ y) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ h
      exact hV (dvd_trans (dvd_mul_right _ _) h)
    rw [hempty, Finset.sum_empty]; exact hB

end
end QRH.DensitySplitThird.CubeFree.Packet.Grouped
