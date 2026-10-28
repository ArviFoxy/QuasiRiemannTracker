/- Copyright (c) 2026 Sil. Apache-2.0.
Leaf domination: the reduction form of FP's native completion chain (WP-G).

FP proves one label's energy bound by pushing the native estimate through the chain
NativeNaturalChild → … → MixedCanonicalEnvelope.  The cube-free step instead groups the
labels at the packed physical row before a source is applied, so the chain is needed in
reduction form: the parent energy is controlled by the canonical *leaf* energies, with an
explicit scalar `M` and without any estimate for the leaves.

`LeafDom leaf L M x` says: `x ≤ M*E` for every common bound `E ≥ 0` of the leaf energies
`leaf A X₁ X₂` over all slot subsets `A` and over the finitely many pairs of ordinary
lengths `(X₁,X₂) ∈ L`.  Every step of FP's chain is an energy inequality with an abstract
inner bound `E`; such steps compose (`LeafDom.comp`), even when the step quantifies over
infinitely many children, as long as all children are dominated by one leaf family.

Since the leaf family is finite, a leaf domination is the same as a nonnegative linear
combination of leaf energies with coefficient mass `M` (`LeafDom.linear`); it is even
carried by a single leaf (`LeafDom.exists_leaf`).  This is the form consumed by the
grouped side bound (WP-H): a label of weight `w` contributes `w*M` times the energy of one
canonical packed child, and these children are grouped at the packed row. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial

set_option autoImplicit false

namespace QRH.DensitySplitThird.CubeFree.Packet.Reduce

noncomputable section
open scoped Classical BigOperators SchwartzMap

open OAI OAI.SevenEighths
open OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeDyadic
open OAI.SevenEighths.CenteredMomentOriginalRadialComparison
open OAI.SevenEighths.CenteredMomentCommonMaskExpansion
open OAI.SevenEighths.CenteredMomentAllocatedNaturalRadial

local notation "O" => OAI.SevenEighths.HeckeFamily.O

section Abstract
variable {α : Type*}

/-- **Leaf domination.** -/
def LeafDom (leaf : Finset α → ℝ → ℝ → ℝ) (L : Finset (ℝ×ℝ)) (M x : ℝ) : Prop :=
  ∀ E : ℝ, 0 ≤ E → (∀ A : Finset α, ∀ p ∈ L, leaf A p.1 p.2 ≤ E) → x ≤ M*E

variable {leaf : Finset α → ℝ → ℝ → ℝ} {L L' : Finset (ℝ×ℝ)} {M M' x x' : ℝ}

theorem LeafDom.mono (h : LeafDom leaf L M x) (hL : L ⊆ L') (hM : M ≤ M') (hx : x' ≤ x) :
    LeafDom leaf L' M' x' := by
  intro E hE hl
  exact hx.trans ((h E hE (fun A p hp => hl A p (hL hp))).trans
    (mul_le_mul_of_nonneg_right hM hE))

theorem LeafDom.of_le (h : LeafDom leaf L M x) (hx : x' ≤ x) : LeafDom leaf L M x' :=
  h.mono subset_rfl le_rfl hx

theorem LeafDom.of_eq (h : LeafDom leaf L M x) (hx : x' = x) : LeafDom leaf L M x' :=
  h.of_le hx.le

theorem LeafDom.mass_le (h : LeafDom leaf L M x) (hM : M ≤ M') : LeafDom leaf L M' x :=
  h.mono subset_rfl hM le_rfl

theorem LeafDom.family_le (h : LeafDom leaf L M x) (hL : L ⊆ L') : LeafDom leaf L' M x :=
  h.mono hL le_rfl le_rfl

/-- A leaf dominates itself. -/
theorem LeafDom.self (A : Finset α) {X₁ X₂ : ℝ} (hp : (X₁, X₂) ∈ L) :
    LeafDom leaf L 1 (leaf A X₁ X₂) := by
  intro _ _ hl
  simpa only [one_mul] using hl A (X₁, X₂) hp

theorem LeafDom.of_nonpos (hx : x ≤ 0) (hM : 0 ≤ M) : LeafDom leaf L M x :=
  fun _ hE _ => hx.trans (mul_nonneg hM hE)

theorem LeafDom.smul {a : ℝ} (ha : 0 ≤ a) (h : LeafDom leaf L M x) :
    LeafDom leaf L (a*M) (a*x) := by
  intro E hE hl
  have := mul_le_mul_of_nonneg_left (h E hE hl) ha
  linarith [show a*(M*E) = a*M*E by ring]

theorem LeafDom.add {M₁ M₂ x₁ x₂ : ℝ} (h₁ : LeafDom leaf L M₁ x₁)
    (h₂ : LeafDom leaf L M₂ x₂) : LeafDom leaf L (M₁+M₂) (x₁+x₂) := by
  intro E hE hl
  have := h₁ E hE hl
  have := h₂ E hE hl
  nlinarith

theorem LeafDom.sum {ι : Type*} (s : Finset ι) (m y : ι → ℝ)
    (h : ∀ i ∈ s, LeafDom leaf L (m i) (y i)) :
    LeafDom leaf L (∑ i ∈ s, m i) (∑ i ∈ s, y i) := by
  intro E hE hl
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => h i hi E hE hl)

/-- **Composition.**  A step with an abstract inner bound over an arbitrary child family
(`hparent`) followed by leaf dominations of all children by one common leaf family. -/
theorem LeafDom.comp {ι : Type*} (P : ι → Prop) (y : ι → ℝ) {c m : ℝ} (hm : 0 ≤ m)
    (hparent : ∀ E : ℝ, 0 ≤ E → (∀ k, P k → y k ≤ E) → x ≤ c*E)
    (hchild : ∀ k, P k → LeafDom leaf L m (y k)) : LeafDom leaf L (c*m) x := by
  intro E hE hl
  have h := hparent (m*E) (mul_nonneg hm hE) (fun k hk => hchild k hk E hE hl)
  linarith [show c*(m*E) = c*m*E by ring]

/-- Change of slot index: leaves indexed by subsets of another slot type that are leaves of
the target family. -/
theorem LeafDom.reindex {β : Type*} {leaf' : Finset β → ℝ → ℝ → ℝ} (f : Finset β → Finset α)
    (hf : ∀ A X₁ X₂, leaf' A X₁ X₂ = leaf (f A) X₁ X₂) (h : LeafDom leaf' L M x) :
    LeafDom leaf L M x := by
  intro E hE hl
  exact h E hE (fun A p hp => (hf A p.1 p.2).trans_le (hl (f A) p hp))

/-- A leaf domination is carried by a single leaf, or the dominated value is `≤ 0`. -/
theorem LeafDom.exists_leaf [Fintype α] (h : LeafDom leaf L M x)
    (hleaf : ∀ A X₁ X₂, 0 ≤ leaf A X₁ X₂) :
    x ≤ 0 ∨ ∃ A : Finset α, ∃ p ∈ L, x ≤ M*leaf A p.1 p.2 := by
  classical
  let S : Finset (Finset α × (ℝ×ℝ)) := (Finset.univ : Finset (Finset α)) ×ˢ L
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc, hmax⟩ := S.exists_max_image (fun c => leaf c.1 c.2.1 c.2.2) hS
    have hc' := Finset.mem_product.mp hc
    refine Or.inr ⟨c.1, c.2, hc'.2, h _ (hleaf _ _ _) ?_⟩
    intro A p hp
    exact hmax (A, p) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hp⟩)
  · refine Or.inl ?_
    have h0 := h 0 le_rfl (fun A p hp => absurd ⟨(A, p), Finset.mem_product.mpr
      ⟨Finset.mem_univ _, hp⟩⟩ hS)
    simpa only [mul_zero] using h0

/-- **Linear form.**  A leaf domination with scalar `M` is a finite nonnegative combination
of leaf energies with coefficient mass at most `M`. -/
theorem LeafDom.linear [Fintype α] (h : LeafDom leaf L M x) (hM : 0 ≤ M)
    (hleaf : ∀ A X₁ X₂, 0 ≤ leaf A X₁ X₂) :
    ∃ (S : Finset (Finset α × (ℝ×ℝ))) (coef : Finset α × (ℝ×ℝ) → ℝ),
      (∀ c ∈ S, 0 ≤ coef c ∧ c.2 ∈ L) ∧ (∑ c ∈ S, coef c) ≤ M ∧
      x ≤ ∑ c ∈ S, coef c*leaf c.1 c.2.1 c.2.2 := by
  classical
  rcases h.exists_leaf hleaf with hx | ⟨A, p, hp, hx⟩
  · exact ⟨∅, fun _ => 0, by simp, by simpa using hM, by simpa using hx⟩
  · refine ⟨{(A, p)}, fun _ => M, ?_, by simp, by simpa using hx⟩
    intro c hc
    rw [Finset.mem_singleton.mp hc]
    exact ⟨hM, hp⟩

end Abstract

/-! ### The canonical leaf -/

section Leaf
variable {α : Type*}

/-- The canonical leaf row: two ordinary dyadic polynomials and the slot product, all with
the same character. -/
def leafRow (χ : Character) (W₁ W₂ : ℝ → ℂ) (t₁ t₂ : ℝ) (pool : α → Finset (Ideal O))
    (β : α → Ideal O → ℂ) (P : α → ℝ) (A : Finset α) (X₁ X₂ : ℝ) : ℂ :=
  polynomial χ false W₁ X₁ 0 t₁ * polynomial χ false W₂ X₂ 0 t₂ *
    ∏ i ∈ A, naturalSlot χ (pool i) (β i) (P i)

/-- The canonical leaf energy: the leaf row with the natural character of the row, in the
radial norm of the (packed) state. -/
def leafEnergy (η : Character) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ : ℝ) (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ)
    (P : α → ℝ) (A : Finset α) (X₁ X₂ : ℝ) : ℝ :=
  radialEnergy (fun z => leafRow (naturalCharacter η z) W₁ W₂ t₁ t₂ pool β P A X₁ X₂) keep Φ K

theorem radialEnergy_nonneg (F : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0 ≤ radialEnergy F keep Φ K := by
  unfold radialEnergy
  exact tsum_nonneg (fun z => by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ z)
    · exact le_rfl)

theorem leafEnergy_nonneg (η : Character) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ : ℝ) (pool : α → Finset (Ideal O)) (β : α → Ideal O → ℂ)
    (P : α → ℝ) (A : Finset α) (X₁ X₂ : ℝ) :
    0 ≤ leafEnergy η keep Φ K W₁ W₂ t₁ t₂ pool β P A X₁ X₂ :=
  radialEnergy_nonneg _ keep Φ K hΦ

/-- Shortened length pairs `(X₁/N(D₁), X₂/N(D₂))` over pairs of subsets of a finite set of
ideals (the common punctures). -/
def shortLengths (X₁ X₂ : ℝ) (R : Finset (Ideal O)) : Finset (ℝ×ℝ) :=
  (R.powerset ×ˢ R.powerset).image (fun D =>
    (X₁/(Ideal.absNorm (∏ I ∈ D.1, I) : ℝ), X₂/(Ideal.absNorm (∏ I ∈ D.2, I) : ℝ)))

theorem mem_shortLengths {X₁ X₂ : ℝ} {R : Finset (Ideal O)} (D₁ D₂ : Finset (Ideal O))
    (hD₁ : D₁ ∈ R.powerset) (hD₂ : D₂ ∈ R.powerset) :
    (X₁/(Ideal.absNorm (∏ I ∈ D₁, I) : ℝ), X₂/(Ideal.absNorm (∏ I ∈ D₂, I) : ℝ)) ∈
      shortLengths X₁ X₂ R :=
  Finset.mem_image.mpr ⟨(D₁, D₂), Finset.mem_product.mpr ⟨hD₁, hD₂⟩, rfl⟩

/-- Every length pair of the family is positive and componentwise below `(X₁, X₂)`. -/
def LengthsBelow (L : Finset (ℝ×ℝ)) (X₁ X₂ : ℝ) : Prop :=
  ∀ p ∈ L, 0 < p.1 ∧ p.1 ≤ X₁ ∧ 0 < p.2 ∧ p.2 ≤ X₂

theorem LengthsBelow.mono {L : Finset (ℝ×ℝ)} {X₁ X₂ Y₁ Y₂ : ℝ} (h : LengthsBelow L X₁ X₂)
    (h₁ : X₁ ≤ Y₁) (h₂ : X₂ ≤ Y₂) : LengthsBelow L Y₁ Y₂ :=
  fun p hp => ⟨(h p hp).1, (h p hp).2.1.trans h₁, (h p hp).2.2.1, (h p hp).2.2.2.trans h₂⟩

theorem LengthsBelow.union {L L' : Finset (ℝ×ℝ)} {X₁ X₂ : ℝ} (h : LengthsBelow L X₁ X₂)
    (h' : LengthsBelow L' X₁ X₂) : LengthsBelow (L ∪ L') X₁ X₂ := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

/-- Every length pair is positive and componentwise below `(X₁, X₂)` or below `(Y₁, Y₂)`
(the two sides of a centered difference). -/
def LengthsBelow₂ (L : Finset (ℝ×ℝ)) (X₁ X₂ Y₁ Y₂ : ℝ) : Prop :=
  ∀ p ∈ L, 0 < p.1 ∧ 0 < p.2 ∧ ((p.1 ≤ X₁ ∧ p.2 ≤ X₂) ∨ (p.1 ≤ Y₁ ∧ p.2 ≤ Y₂))

theorem LengthsBelow₂.left {L : Finset (ℝ×ℝ)} {X₁ X₂ : ℝ} (Y₁ Y₂ : ℝ)
    (h : LengthsBelow L X₁ X₂) : LengthsBelow₂ L X₁ X₂ Y₁ Y₂ :=
  fun p hp => ⟨(h p hp).1, (h p hp).2.2.1, Or.inl ⟨(h p hp).2.1, (h p hp).2.2.2⟩⟩

theorem LengthsBelow₂.right {L : Finset (ℝ×ℝ)} (X₁ X₂ : ℝ) {Y₁ Y₂ : ℝ}
    (h : LengthsBelow L Y₁ Y₂) : LengthsBelow₂ L X₁ X₂ Y₁ Y₂ :=
  fun p hp => ⟨(h p hp).1, (h p hp).2.2.1, Or.inr ⟨(h p hp).2.1, (h p hp).2.2.2⟩⟩

theorem LengthsBelow₂.union {L L' : Finset (ℝ×ℝ)} {X₁ X₂ Y₁ Y₂ : ℝ}
    (h : LengthsBelow₂ L X₁ X₂ Y₁ Y₂) (h' : LengthsBelow₂ L' X₁ X₂ Y₁ Y₂) :
    LengthsBelow₂ (L ∪ L') X₁ X₂ Y₁ Y₂ := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem LengthsBelow₂.biUnion {ι : Type*} (s : Finset ι) (L : ι → Finset (ℝ×ℝ))
    {X₁ X₂ Y₁ Y₂ : ℝ} (h : ∀ i ∈ s, LengthsBelow₂ (L i) X₁ X₂ Y₁ Y₂) :
    LengthsBelow₂ (s.biUnion L) X₁ X₂ Y₁ Y₂ := by
  intro p hp
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact h i hi p hp

theorem radialEnergy_congr_keep {F G : O → ℂ} {keep : O → Prop} (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : ∀ z, keep z → F z = G z) : radialEnergy F keep Φ K = radialEnergy G keep Φ K := by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz, ite_true, h z hz]
  · simp only [hz, ite_false]

end Leaf

end

end QRH.DensitySplitThird.CubeFree.Packet.Reduce
