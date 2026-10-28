/- Copyright (c) 2026 Sil. Apache-2.0.
Seam A: the priced packed leaf contract of the cube-free step.

`PricedPackedAt` is PR69's `InitialAffineAt` with three changes:
* the row is packed, `A := V` with keep condition `initialKeep η (internalQ Q η₀) (V*z)`;
* the scale `K` is free and the envelope is `M = log_Z (N(V)·K) ∈ [Mmin, Mmax]`;
* the face admissibility is replaced by an exponential price
  `price.f w₀ (ℓ(X₁)+ℓ(X₂)) (∑ w) M` (paid deletion, CF (5.2); density split, DS §3–4),
  with only the ordinary lengths capped by `Lplain`.
In `PricedPackedSource` the finite anchor family is fixed before the constants, and the
live width `w₀` is quantified after `∀ᶠ Z` (uniformity in the density threshold).
Smaller prices and narrower envelopes give weaker statements
(`PricedPackedAt.mono`, `PricedPackedSource.mono`). -/
import Submissions.density_split_fourth.CubeFree.Price
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
variable (H : Subgroup (O ⧸ rayM)ˣ)
variable (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The priced packed estimate at one scale parameter `Z` and one character `η`. -/
def PricedPackedAt (price : Price) (w₀ : ℝ) (W : ℝ → ℂ) (bΦ mesh Mmin Mmax Lplain ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ (V : O) (K : ℝ), V ≠ 0 → 0 < K →
    Mmin ≤ Real.logb Z ((Ideal.span {V}).absNorm * K) →
    Real.logb Z ((Ideal.span {V}).absNorm * K) ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ → (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles (1/4) (9/4), ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
    energy η (fixedBadMask*idealGenerator 1) V t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (fun z => initialKeep η (internalQ Q η₀) (V*z)) Φ K ≤
    C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*
      Z^(Real.logb Z ((Ideal.span {V}).absNorm*K) +
        price.f w₀ (length Z X₁ + length Z X₂) (∑ i, w i)
          (Real.logb Z ((Ideal.span {V}).absNorm*K)) + ε)

/-- Monotonicity of the packed contract: a pointwise smaller price, a larger envelope
interval, a larger plain-length cap, a larger mesh or a smaller loss give a stronger
statement (for `1 ≤ Z`, `0 ≤ C`). -/
theorem PricedPackedAt.mono {price price' : Price} {w₀ : ℝ} {W : ℝ → ℂ}
    {bΦ mesh mesh' Mmin Mmax Mmin' Mmax' Lplain Lplain' ε ε' Z : ℝ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {S : Finset (ℕ×ℕ)} {C : ℝ}
    (hprice : ∀ w P s M, price.f w P s M ≤ price'.f w P s M)
    (hmesh : mesh' ≤ mesh) (hMmin : Mmin ≤ Mmin') (hMmax : Mmax' ≤ Mmax)
    (hL : Lplain' ≤ Lplain) (hε : ε ≤ ε') (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (h : PricedPackedAt (α:=α) rayM H hH price w₀ W bΦ mesh Mmin Mmax Lplain ε Z
      η η₀ Q degree S C) :
    PricedPackedAt (α:=α) rayM H hH price' w₀ W bΦ mesh' Mmin' Mmax' Lplain' ε' Z
      η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσ₁ hσ₂ hh hv V K hV hK hM₁ hM₂ Φ hΦ hΦpos p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  refine (h T θ w σ v t height hw (fun i => (hwm i).trans hmesh) hσ₁ hσ₂ hh hv V K hV hK
    (hMmin.trans hM₁) (hM₂.trans hMmax) Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ (hl₁.trans hL)
    (hl₂.trans hL)).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ
    have := hprice w₀ (length Z X₁ + length Z X₂) (∑ i, w i)
      (Real.logb Z ((Ideal.span {V}).absNorm*K))
    linarith
  · have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
    have h1 : 0 ≤ 1+|t|+height := by positivity
    positivity

end

/-- Seam A: the priced packed source, uniform in the finite anchor family and in the
live width `w₀`. -/
def PricedPackedSource (price : Price) (Mmin Mmax Lplain : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (κ : Type) [Fintype κ] (anchors : κ → Character)
    (η₀ : Character) (Q : Ideal O),
    Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
  ∃ degree : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (j : κ) (w₀ : ℝ), PricedPackedAt (α:=α) rayM H hH price w₀ W bΦ mesh Mmin Mmax Lplain ε Z
      (anchors j) η₀ Q degree S C

/-- Monotonicity of Seam A in the price (pointwise smaller is stronger), in the envelope
interval `[Mmin, Mmax]` (larger is stronger) and in the plain-length cap. -/
theorem PricedPackedSource.mono {price price' : Price} {Mmin Mmax Mmin' Mmax' Lplain Lplain' : ℝ}
    (hprice : ∀ w P s M, price.f w P s M ≤ price'.f w P s M)
    (hMmin : Mmin ≤ Mmin') (hMmax : Mmax' ≤ Mmax) (hL : Lplain' ≤ Lplain)
    (h : PricedPackedSource price Mmin Mmax Lplain) :
    PricedPackedSource price' Mmin' Mmax' Lplain' := by
  intro ε hε
  obtain ⟨meshMax, hmesh, h⟩ := h ε hε
  refine ⟨meshMax, hmesh, fun mesh hm α _ _ rayM _ H hH W hW hWs bΦ hbΦ κ _ anchors η₀ Q
    hQ hQ0 hQt hQ72 => ?_⟩
  obtain ⟨degree, S, C, hC, hev⟩ := h mesh hm α rayM H hH W hW hWs bΦ hbΦ κ anchors η₀ Q
    hQ hQ0 hQt hQ72
  refine ⟨degree, S, C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1:ℝ)] with Z hZ hZ1 j w₀
  exact PricedPackedAt.mono rayM H hH hprice le_rfl hMmin hMmax hL le_rfl hZ1 hC.le (hZ j w₀)

end
end QRH.DensitySplitThird.CubeFree
