/- Copyright (c) 2026 Sil. Apache-2.0.
The form of Seam B (`GroupedSideBound`, WP-H) used by the second-step skeleton (WP-I).

This file only STATES the grouped packet estimate (CF Section 5, CPL Sections 1 and 3) as a
`Prop`; WP-H proves it from Seam A (`Leaf.Contract.PricedPackedSource`) through the packing
dictionary, the linear-form reduction chain and the weighted common separation. The
skeleton theorems of `Second/Side.lean` take it as a hypothesis.

Shape of the estimate. A *side frame* collects, at one scale `Z`, the residual (post-D⁴
transfer) sources `r`, the second-step labels `x` (genuine second common factor `G`, packed
row `V`, unit part `U`, second artificial divisor `t₂` and its allocations, frozen-slot
assignments, dictionary index), the literal one-sided label energies, and the scalar label
weights (`ρ(G)` times the absolute second-step prefactor, including `N(t₂)⁻¹`). For a group of
labels whose ORIGINAL envelopes `H = 2a - k + q₀` lie within one mesh of a common `H` in
`[Mmin, Mmax]`, and whose weighted row fibres are subpower (`∑_{x : V_x ∣ y, G_x ∣ y} w_x ≤
Z^{ε/8}` for every nonzero packed row `y`), the weighted sum of label energies is at most
`Z^{a + q₀ + price(P, s, H) + ε}` (CF (5.3)).

Quantifier order (risk 2 of the design): `ε`, then the mesh, then the structural data `θ`
(slot type, ray modulus, profiles, ...) and the character `η`, THEN the constants
`degree, C`, then `∀ᶠ Z`, then the actual sources, labels and the density parameter `w₀`. -/
import Submissions.density_split_fourth.CubeFree.Price
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Family

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second
noncomputable section
open scoped BigOperators Classical
open Filter
local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- One grouped side at one scale: sources, labels, literal one-sided label energies at
height `v`, scalar label weights, the packed-row divisibility relation of the fibre
condition, and the scalar widths of a source. -/
structure SideFrame where
  /-- residual sources (after selection, D-Cauchy and the D⁴ transfer) -/
  Src : Type
  /-- second-step labels -/
  Label : Type
  /-- literal one-sided label energy `∑_rows |A_x(r)|²` at height `v` -/
  energy : Src → Label → ℝ → ℝ
  energy_nonneg : ∀ r x v, 0 ≤ energy r x v
  /-- scalar label weight: `ρ(G) · |prefactor| · N(t₂)⁻¹` -/
  weight : Label → ℝ
  /-- the label lives on the packed row `y` (`V_x ∣ y ∧ G_x ∣ y`) -/
  onRow : Label → O → Prop
  /-- original packed envelope `H = 2a - k + q₀` of the label on the source -/
  envelope : Src → Label → ℝ
  /-- `a + q₀`: column log-width plus twist log-width -/
  logScale : Src → ℝ
  /-- ordinary width `P` and retained marked width `s` of the source -/
  P : Src → ℝ
  s : Src → ℝ
  /-- legacy fixed amplitude (unused by `GroupedSideBound`, which takes an `AmpFamily`) -/
  amplitude : Src → ℝ
  amplitude_nonneg : ∀ r, 0 ≤ amplitude r

/-- The groups of labels admitted by Seam B at scale `Z`. -/
def AdmissibleGroup (F : SideFrame) (Mmin Mmax mesh ε Z : ℝ) (r : F.Src)
    (labels : Finset F.Label) (H : ℝ) : Prop :=
  Mmin ≤ H ∧ H ≤ Mmax ∧
  (∀ x ∈ labels, |F.envelope r x - H| ≤ mesh) ∧
  (∀ x ∈ labels, 0 ≤ F.weight x) ∧
  (∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^(Mmax + 2) →
    ∑ x ∈ labels.filter (fun x => F.onRow x y), F.weight x ≤ Z^(ε/8))

/-- Source amplitudes of a frame family that may depend on the existential degree and seminorm
set of the bound (profile seminorms and the height polynomial; FP's
`amplitude d.root d.t₀ d.V J control Cside`). -/
abbrev AmpFamily {Θ : Type}
    (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame) : Type :=
  ∀ θ mesh η Z, (Frame θ mesh η Z).Src → ℕ → Finset (ℕ×ℕ) → ℝ

/-- Nonnegative amplitudes, monotone in the degree and in the seminorm set. -/
def AmpMono {Θ : Type} {Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame}
    (amp : AmpFamily Frame) : Prop :=
  ∀ θ mesh η Z (r : (Frame θ mesh η Z).Src),
    (∀ J S, 0 ≤ amp θ mesh η Z r J S) ∧
    (∀ J J' S S', J ≤ J' → S ⊆ S' → amp θ mesh η Z r J S ≤ amp θ mesh η Z r J' S')

/-- **Seam B as used by WP-I.** `Frame θ mesh η Z` is the side frame for structural data
`θ`, mesh, character `η` and scale `Z`; the source amplitude `amp` takes the existential
degree and seminorm set. This is literally WP-H's `Packet.Grouped.GroupedSideBoundA`
(the frame field `SideFrame.amplitude` is no longer used by the bound). -/
def GroupedSideBound {Θ : Type} (Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame)
    (amp : AmpFamily Frame) (price : Price) (Mmin Mmax : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
  ∀ (θ : Θ) (η : OAI.SevenEighths.HeckeFamily.Character),
  ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
  ∀ (r : (Frame θ mesh η Z).Src) (labels : Finset (Frame θ mesh η Z).Label) (w₀ H : ℝ),
    AdmissibleGroup (Frame θ mesh η Z) Mmin Mmax mesh ε Z r labels H →
    ∀ v : ℝ,
      ∑ x ∈ labels, (Frame θ mesh η Z).weight x * (Frame θ mesh η Z).energy r x v ≤
        C * amp θ mesh η Z r degree control * (1 + ‖v‖)^(2*degree) *
          Z^((Frame θ mesh η Z).logScale r +
            price.f w₀ ((Frame θ mesh η Z).P r) ((Frame θ mesh η Z).s r) H + ε)

namespace GroupedSideBound
variable {Θ : Type} {Frame : Θ → ℝ → OAI.SevenEighths.HeckeFamily.Character → ℝ → SideFrame}

/-- A cheaper price (pointwise) keeps Seam B. -/
theorem mono_price {amp : AmpFamily Frame} (hamp : AmpMono amp) {p q : Price} {Mmin Mmax : ℝ}
    (hpq : ∀ w P s M, p.f w P s M ≤ q.f w P s M)
    (h : GroupedSideBound Frame amp p Mmin Mmax) : GroupedSideBound Frame amp q Mmin Mmax := by
  intro ε hε
  obtain ⟨meshMax, hm, h1⟩ := h ε hε
  refine ⟨meshMax, hm, fun mesh hmesh hmm θ η => ?_⟩
  obtain ⟨degree, control, C, hC, hZ⟩ := h1 mesh hmesh hmm θ η
  refine ⟨degree, control, C, hC, ?_⟩
  filter_upwards [hZ, eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  intro r labels w₀ H hadm v
  refine (hZ r labels w₀ H hadm v).trans ?_
  have hA : 0 ≤ C * amp θ mesh η Z r degree control * (1 + ‖v‖)^(2*degree) :=
    mul_nonneg (mul_nonneg hC.le ((hamp θ mesh η Z r).1 _ _)) (by positivity)
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.rpow_le_rpow_of_exponent_le hZ1
  linarith [hpq w₀ ((Frame θ mesh η Z).P r) ((Frame θ mesh η Z).s r) H]

end GroupedSideBound

end
end QRH.DensitySplitThird.CubeFree.Second
