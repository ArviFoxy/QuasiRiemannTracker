import Submissions.arvi_kwall.SexticSpikeFree
import Submissions.arvi_selected_leaf.JointDetector.IdealAmplification

/-!
# The reciprocity bridge: selected constants of `(n/z)₆` and `(z/n)₆` agree up to a bounded factor

Research file (QRH, K-wall program). Generic `IsSelected` lemmas live in `QRH.ArviKWall.BalancedSieve`, the
concrete bridge in `QRH.ArviKWall.ReciprocityBridge`. The file imports `SexticSpikeFree.lean` and the
selected-leaf library (`Qrh.JointDetector`, through `IdealAmplification`). **Nothing is assumed**: there is no
hypothesis structure and no unproved step, and every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (see the `#print` lines at the end). It checks in about 10 s on a warm cache, after the imports.

## The gap this closes

* `SexticSpikeFree.lean` sieves over the *ideals* `z` (rows) with the numerator coming from the source:
  `orderKernel k z n = (pg n / z)₆^k` (numerator = primary generator of the source ideal `n`) and
  `twistKernel k z m = (m / z)₆^k` (numerator = the twist `m = x + yω`).
  `IsSelected K W S S0` is its notion of selected constant.
* The selected-leaf library (`selectedNorm rows sources`) uses the reciprocal symbol `(z / J)₆`, with *elements*
  `z` as rows and *ideals* `J` as sources. This is the form for which `selectedNorm_inverse_amplification` holds.
* Sextic reciprocity gives `(pg n / z)₆ = ε · (pg z / n)₆`, with a sign `ε` depending only on the residues of
  the two primary generators mod `4`. A twist is `pg · unit` (and `λ^a 2^b · pg · unit` in general).

## What is proved

**1. Generic linear algebra** (any kernels `K : ρ → σ → ℂ`; no number theory).
* `IsSelected.mono_sources`, `IsSelected.mono_rows`: restriction. `IsSelected.swap`: duality in kernel form.
  `IsSelected.comap`, `IsSelected.image`: re-indexing along maps that are injective on the index sets.
* `IsSelected.of_class_twist` is the engine. Suppose `K z n = ψ z (c n) · K₀ z n` with `‖ψ‖ ≤ 1`, where the class
  map `c : σ → γ` takes values in a finite set `C`, and each class block `{n : c n = g}` has the selected constant
  `S0` for `K₀`. Then `|C| · S0` is a selected constant for `K`. (Cauchy–Schwarz over the classes, row by row.)
* (a) `IsSelected.sign_blocks`: `K' z n = s (cr z) (cs n) · K z n` with `‖s‖ ≤ 1` gives the constant
  `|cs(S)| · S0`, for any real `S0`. Only the *source* classes cost a factor, because the row class is just a
  coefficient of the block sums; there is no need to cut the rows. `IsSelected.sign_blocks_card` is the stated form
  `Fintype.card α · Fintype.card β · S0` (for `S0 ≥ 0`), which is weaker.
* (b) `IsSelected.unit_twist_iff`: `K' z m = u z · K z m` with `‖u z‖ = 1` gives *equal* selected constants.
* (c) `IsSelected.associates`: sources `U × σ` with `K' z (u, m) = χ z u · K z m`, `‖χ‖ ≤ 1`, give `|U| · S0`
  (so `6 S0` for the six units).

**2. Sextic reciprocity for composite moduli.** OAI already proves it for all supported ideals
(`idealRowHom_ideal_reciprocity`, and for primary elements `idealRowHom_primary_reciprocity`), so nothing is
left as a hypothesis. `reciprocity_composite` restates it as `(pg J / I)₆ = recSign (pg I mod 4) (pg J mod 4) ·
(pg I / J)₆`, where `recSign` is OAI's `quadraticRaySign` of the residues mod `4`. `recSign` is symmetric
(`recSign_symm`), zero unless both classes are odd, and `±1` on the `12` odd classes (`recSign_mul_self`,
`norm_recSign_eq`). `norm_idealRowHom_unit`: `|(u / z)₆| = 1` for a unit `u` and supported `z`.
`numerator_factor`: `(pg d · e / z)₆^k = classPhase · (pg z / d)₆^k`, with a row factor of absolute value `≤ 1`.

**3. The bridge** (theorems of `QRH.ArviKWall.ReciprocityBridge`).
* `isSelected_selectedNorm`, `selectedNorm_le_of_isSelected`: `selectedNorm rows sources` is exactly the best
  selected constant of the kernel `(z/I)₆` in `IsSelected` form.
* `isSelected_numerator_of_leaf` and `isSelected_leaf_of_numerator`: abstract two-way bridge for sources `n` with
  numerator `num n = pg (d n) · e` and denominator ideal `d n`. The factor is `|E| · 12`, where `E` is the set of
  multipliers `e` and `12` is the number of odd residue classes mod `4`. They hold for every power `k`.
* The twist sieve (6 units, so `6 · 12 = 72`). The headline statements are
  `twistKernel_one_isSelected_image : IsSelected (twistKernel 1) W T
     (72 * selectedNorm (W.image primaryGenerator) (T.image twistIdeal))` and
  `selectedNorm_image_le_of_twistKernel_one : selectedNorm (W.image primaryGenerator) (T.image twistIdeal)
     ≤ 72 * S0`, for supported rows `W`, supported twists `T` and `IsSelected (twistKernel 1) W T S0`.
  The general forms with `rows ⊇ pg(W)` and `sources ⊇ {(m)}` are `twistKernel_one_isSelected` and
  `selectedNorm_le_of_twistKernel_one`; they come from `twistKernel_isSelected_of_leaf` and
  `leaf_isSelected_of_twistKernel`, valid for every `k`.
* The sextic kernel `orderKernel` of the conjecture (the numerator is already primary, so only the sign
  classes remain, factor `12`): `orderKernel_one_isSelected`, `selectedNorm_le_of_orderKernel_one`, and the forms
  for `sexticRows B` and `sexticSources L`: `orderKernel_one_isSelected_sextic`,
  `selectedNorm_le_of_orderKernel_one_sextic`.
* `twistKernel_one_amplification`: the end-to-end chain. A selected constant `S1` for `twistKernel 1` on `W × Tbig`
  gives `72 · (C D · 72 S1 / A)` on `W × Tsmall`, when the amplifier data are those of
  `selectedNorm_inverse_amplification`. The two factors `72` are the two bridge directions.
* `twistKernel_isSelected_of_leaf_supplementary`: twists divisible by `λ` or `2` (the supplementary symbols),
  given as `λ^a 2^b · x_m` with `x_m` coprime to `6`: factor `72 · |AB|`, with `AB` the set of types `(a, b)`.
  `exists_supported_decomposition`: such a decomposition exists for every nonzero element.
  `exponent_bound`: for a twist of norm `≤ M`, `a ≤ log₃ M` and `b ≤ log₄ M` (norm multiplicativity,
  `N λ = 3`, `N 2 = 4`). `twistKernel_isSelected_of_leaf_box`: so the whole twist box of norm `≤ M` costs
  `72 (1 + log₃ M)(1 + log₄ M)`.

## The factor

For the twist sieve the factor is `72 = 6 · 12`: the six associates of an ideal and the twelve odd residue classes
mod `4` of the primary generator of the source. This is at most the expected `6 · 12² = 864`, because Cauchy–Schwarz
over the source classes alone suffices (row classes cost nothing). The sign is bimultiplicative with values `±1`
(OAI: `quadraticRaySign_mul_left`, `quadraticRaySign_mul_right`) on `(O/4)ˣ ≅ ℤ/3 × (ℤ/2)²`, so it kills the `ℤ/3`
and at most `4` of the `12` source classes give different sign patterns. Merging them would lower the `12` to `4`;
that refinement is not formalized.

## What is not covered

* Rows and sources must be *supported* (coprime to `6`): `Supported z`. Reciprocity, and with it the bridge, is only
  available there. Twists divisible by `λ` or `2` are handled in the forward direction only, by the supplementary theorems
  above. The converse direction is stated for supported twists, which is all the amplification chain needs, since a
  selected constant on `Tbig` restricts to its supported part (`IsSelected.mono_sources`).
* `k = 2`. The library only has the sextic norm, so there is no cubic `selectedNorm`. The theorems with a general
  exponent `k` take the selected constant for the kernel `(z/I)₆^k` as the hypothesis `hlib`; for `k = 2` this
  is the cubic symbol. For even `k` the sign disappears (`ε² = 1`), so the factor `12` could be dropped; not formalized.
* The coverage hypotheses (`pg z ∈ rows`, `(m) ∈ sources`, and for the converse the surjectivity of the
  re-indexing) say how the library's finite sets relate to the sieve's. They are exactly what `Finset.image` provides.
-/

set_option autoImplicit false

namespace QRH.ArviKWall.BalancedSieve

open Finset
open scoped BigOperators

section GenericBlocks

variable {ρ σ : Type*}

/-- Fewer sources keep a selected constant (extend the coefficients by zero). -/
theorem IsSelected.mono_sources {K : ρ → σ → ℂ} {W : Finset ρ} {S S' : Finset σ} {S0 : ℝ}
    (h : IsSelected K W S S0) (hS : S' ⊆ S) : IsSelected K W S' S0 := by
  classical
  intro a
  have key := h (fun n => if n ∈ S' then a n else 0)
  have h1 : ∀ z, ∑ n ∈ S, (if n ∈ S' then a n else 0) * K z n = ∑ n ∈ S', a n * K z n := by
    intro z
    rw [← Finset.sum_subset hS (fun n _ hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  have h2 : ∑ n ∈ S, ‖(if n ∈ S' then a n else 0)‖ ^ 2 = ∑ n ∈ S', ‖a n‖ ^ 2 := by
    rw [← Finset.sum_subset hS (fun n _ hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  simp only [h1, h2] at key
  exact key

/-- Fewer rows keep a selected constant. -/
theorem IsSelected.mono_rows {K : ρ → σ → ℂ} {W W' : Finset ρ} {S : Finset σ} {S0 : ℝ}
    (h : IsSelected K W S S0) (hW : W' ⊆ W) : IsSelected K W' S S0 := fun a =>
  (Finset.sum_le_sum_of_subset_of_nonneg hW fun _ _ _ => by positivity).trans (h a)

/-- Duality in kernel form: for `S0 ≥ 0`, a selected constant for `K` on `W × S` is one for the transposed
kernel `(n, z) ↦ K z n` on `S × W`. This is `IsSelected.transpose` as an `IsSelected` statement. -/
theorem IsSelected.swap {K : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ} {S0 : ℝ}
    (h : IsSelected K W S S0) (hS0 : 0 ≤ S0) : IsSelected (fun n z => K z n) S W S0 :=
  fun c => h.transpose hS0 c

/-- **Pull-back along injections.** If `K'` has the selected constant `S0` on `W' × S'`, and
`K z n = K' (f z) (g n)` on `W × S` with `f`, `g` injective on `W`, `S` and mapping into `W'`, `S'`, then `K` has
the constant `S0` on `W × S`. The coefficients are extended along `g` by zero. -/
theorem IsSelected.comap {ρ' σ' : Type*} {K' : ρ' → σ' → ℂ} {W' : Finset ρ'} {S' : Finset σ'}
    {S0 : ℝ} (h : IsSelected K' W' S' S0) {K : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ}
    (f : ρ → ρ') (g : σ → σ') (hf : Set.InjOn f W) (hg : Set.InjOn g S)
    (hfW : ∀ z ∈ W, f z ∈ W') (hgS : ∀ n ∈ S, g n ∈ S')
    (hK : ∀ z ∈ W, ∀ n ∈ S, K z n = K' (f z) (g n)) : IsSelected K W S S0 := by
  classical
  intro a
  -- extend the coefficients along `g`
  let a' : σ' → ℂ := fun s => if hs : ∃ n ∈ S, g n = s then a hs.choose else 0
  have ha' : ∀ n ∈ S, a' (g n) = a n := by
    intro n hn
    have hex : ∃ k ∈ S, g k = g n := ⟨n, hn, rfl⟩
    have : a' (g n) = a hex.choose := dite_eq_left hex
    rw [this]
    exact congrArg a (hg hex.choose_spec.1 hn hex.choose_spec.2)
  have ha'0 : ∀ s, s ∉ S.image g → a' s = 0 := by
    intro s hs
    have : ¬ ∃ n ∈ S, g n = s := fun ⟨n, hn, hns⟩ => hs (Finset.mem_image.mpr ⟨n, hn, hns⟩)
    exact dite_eq_right this
  have himg : S.image g ⊆ S' := fun s hs => by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
    exact hgS n hn
  have hin : ∀ z ∈ W, ∑ n ∈ S, a n * K z n = ∑ s ∈ S', a' s * K' (f z) s := by
    intro z hz
    rw [← Finset.sum_subset himg (fun s _ hs => by rw [ha'0 s hs, zero_mul]),
      Finset.sum_image hg]
    exact Finset.sum_congr rfl fun n hn => by rw [ha' n hn, hK z hz n hn]
  have hnorm : ∑ s ∈ S', ‖a' s‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [← Finset.sum_subset himg (fun s _ hs => by rw [ha'0 s hs, norm_zero]; ring),
      Finset.sum_image hg]
    exact Finset.sum_congr rfl fun n hn => by rw [ha' n hn]
  calc ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2
      = ∑ z ∈ W, ‖∑ s ∈ S', a' s * K' (f z) s‖ ^ 2 :=
        Finset.sum_congr rfl fun z hz => by rw [hin z hz]
    _ = ∑ z' ∈ W.image f, ‖∑ s ∈ S', a' s * K' z' s‖ ^ 2 :=
        (Finset.sum_image (f := fun z' => ‖∑ s ∈ S', a' s * K' z' s‖ ^ 2) hf).symm
    _ ≤ ∑ z' ∈ W', ‖∑ s ∈ S', a' s * K' z' s‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro z' hz'
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hz'
        exact hfW z hz
    _ ≤ S0 * ∑ s ∈ S', ‖a' s‖ ^ 2 := h a'
    _ = S0 * ∑ n ∈ S, ‖a n‖ ^ 2 := by rw [hnorm]

/-- **Push-forward along injections.** If `K` has the selected constant `S0` on `W × S` and `K' (f z) (g n) = K z n`
with `f`, `g` injective on `W`, `S`, then `K'` has the constant `S0` on the image sets `f(W) × g(S)`. -/
theorem IsSelected.image {K : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ} {S0 : ℝ}
    (h : IsSelected K W S S0) {ρ' σ' : Type*} [DecidableEq ρ'] [DecidableEq σ']
    {K' : ρ' → σ' → ℂ} (f : ρ → ρ') (g : σ → σ') (hf : Set.InjOn f W) (hg : Set.InjOn g S)
    (hK : ∀ z ∈ W, ∀ n ∈ S, K' (f z) (g n) = K z n) :
    IsSelected K' (W.image f) (S.image g) S0 := by
  intro a'
  have key := h fun n => a' (g n)
  calc ∑ z' ∈ W.image f, ‖∑ s ∈ S.image g, a' s * K' z' s‖ ^ 2
      = ∑ z ∈ W, ‖∑ s ∈ S.image g, a' s * K' (f z) s‖ ^ 2 := Finset.sum_image hf
    _ = ∑ z ∈ W, ‖∑ n ∈ S, a' (g n) * K z n‖ ^ 2 := by
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [Finset.sum_image hg]
        exact congrArg (fun x => ‖x‖ ^ 2) (Finset.sum_congr rfl fun n hn => by rw [hK z hz n hn])
    _ ≤ S0 * ∑ n ∈ S, ‖a' (g n)‖ ^ 2 := key
    _ = S0 * ∑ s ∈ S.image g, ‖a' s‖ ^ 2 := by rw [Finset.sum_image hg]

/-- **Class-twisted kernels (the engine).** Suppose `K z n = ψ z (c n) · K₀ z n` on `W × S`, with `‖ψ z g‖ ≤ 1`
for the classes `g` in a finite set `C ⊇ c(S)`, and suppose each class block `{n ∈ S : c n = g}` has the selected
constant `S0` for `K₀`. Then `|C| · S0` is a selected constant for `K` on `W × S`. For each row `z` the sum over `n`
splits into the class sums `A_g(z) = Σ_{c n = g} a_n K₀ z n`; Cauchy–Schwarz over the classes gives
`|Σ_g ψ z g A_g z|² ≤ |C| Σ_g |A_g z|²`; then sum over the rows and use the block constants. -/
theorem IsSelected.of_class_twist {γ : Type*} [DecidableEq γ] {K K₀ : ρ → σ → ℂ} {W : Finset ρ}
    {S : Finset σ} {S0 : ℝ} (c : σ → γ) (C : Finset γ) (hC : ∀ n ∈ S, c n ∈ C) (ψ : ρ → γ → ℂ)
    (hψ : ∀ z ∈ W, ∀ g ∈ C, ‖ψ z g‖ ≤ 1)
    (hK : ∀ z ∈ W, ∀ n ∈ S, K z n = ψ z (c n) * K₀ z n)
    (hblock : ∀ g ∈ C, IsSelected K₀ W (S.filter fun n => c n = g) S0) :
    IsSelected K W S (C.card * S0) := by
  intro a
  -- the block sums
  let A : γ → ρ → ℂ := fun g z => ∑ n ∈ S.filter (fun n => c n = g), a n * K₀ z n
  have hsplit : ∀ z ∈ W, ∑ n ∈ S, a n * K z n = ∑ g ∈ C, ψ z g * A g z := by
    intro z hz
    calc ∑ n ∈ S, a n * K z n
        = ∑ n ∈ S, ψ z (c n) * (a n * K₀ z n) :=
          Finset.sum_congr rfl fun n hn => by rw [hK z hz n hn]; ring
      _ = ∑ g ∈ C, ∑ n ∈ S.filter (fun n => c n = g), ψ z (c n) * (a n * K₀ z n) :=
          (Finset.sum_fiberwise_of_maps_to hC _).symm
      _ = ∑ g ∈ C, ψ z g * A g z := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n hn => by rw [(Finset.mem_filter.mp hn).2]
  -- Cauchy-Schwarz over the classes, row by row
  have hrow : ∀ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 ≤ C.card * ∑ g ∈ C, ‖A g z‖ ^ 2 := by
    intro z hz
    rw [hsplit z hz]
    refine (norm_sum_mul_sq_le C (ψ z) (fun g => A g z)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun g _ => by positivity)
    calc ∑ g ∈ C, ‖ψ z g‖ ^ 2 ≤ ∑ g ∈ C, (1 : ℝ) :=
          Finset.sum_le_sum fun g hg => pow_le_one₀ (norm_nonneg _) (hψ z hz g hg)
      _ = C.card := by simp
  calc ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2
      ≤ ∑ z ∈ W, ((C.card : ℝ) * ∑ g ∈ C, ‖A g z‖ ^ 2) := Finset.sum_le_sum hrow
    _ = C.card * ∑ g ∈ C, ∑ z ∈ W, ‖A g z‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ C.card * ∑ g ∈ C, S0 * ∑ n ∈ S.filter (fun n => c n = g), ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => hblock g hg a) (Nat.cast_nonneg _)
    _ = (C.card * S0) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hC (fun n => ‖a n‖ ^ 2)]
        ring

/-- **(a) Sign blocks.** If `K' z n = s (cr z) (cs n) · K z n` with `‖s a b‖ ≤ 1` and `K` has the selected constant
`S0` on `W × S`, then `K'` has the constant `(number of source classes occupied) · S0`. No sign condition on
`S0` is needed. -/
theorem IsSelected.sign_blocks {α β : Type*} [DecidableEq β] {K K' : ρ → σ → ℂ} {W : Finset ρ}
    {S : Finset σ} {S0 : ℝ} (cr : ρ → α) (cs : σ → β) (s : α → β → ℂ) (hs : ∀ a b, ‖s a b‖ ≤ 1)
    (hK' : ∀ z ∈ W, ∀ n ∈ S, K' z n = s (cr z) (cs n) * K z n) (h : IsSelected K W S S0) :
    IsSelected K' W S ((S.image cs).card * S0) :=
  IsSelected.of_class_twist (K₀ := K) cs (S.image cs)
    (fun _ hn => Finset.mem_image_of_mem cs hn) (fun z g => s (cr z) g)
    (fun _ _ _ _ => hs _ _) hK' (fun _ _ => h.mono_sources (Finset.filter_subset _ _))

/-- **(a) Sign blocks, in the stated form** `|α| · |β| · S0` (for `S0 ≥ 0`). The sharper constant is
`IsSelected.sign_blocks`. -/
theorem IsSelected.sign_blocks_card {α β : Type*} [Fintype α] [Fintype β]
    {K K' : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ} {S0 : ℝ} (hS0 : 0 ≤ S0)
    (cr : ρ → α) (cs : σ → β) (s : α → β → ℂ) (hs : ∀ a b, ‖s a b‖ ≤ 1)
    (hK' : ∀ z ∈ W, ∀ n ∈ S, K' z n = s (cr z) (cs n) * K z n) (h : IsSelected K W S S0) :
    IsSelected K' W S (Fintype.card α * Fintype.card β * S0) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · have hα : IsEmpty α := Fintype.card_eq_zero_iff.mp h0
    have hW : W = ∅ := Finset.eq_empty_of_forall_notMem fun z _ => hα.false (cr z)
    subst hW
    intro a
    simp
  · refine (h.sign_blocks cr cs s hs hK').mono ?_
    have hc : ((S.image cs).card : ℝ) ≤ Fintype.card β := by
      exact_mod_cast Finset.card_le_univ _
    have hα1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast hpos
    calc ((S.image cs).card : ℝ) * S0 ≤ Fintype.card β * S0 := mul_le_mul_of_nonneg_right hc hS0
      _ ≤ (Fintype.card α * Fintype.card β) * S0 :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg _) hα1) hS0

/-- **(b) Unit twists.** If `K' z n = u z · K z n` with `‖u z‖ = 1`, then `K` and `K'` have the same selected
constants: the row factor `u z` drops out of `|Σ_n a_n K' z n|`. -/
theorem IsSelected.unit_twist_iff {K K' : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ} {S0 : ℝ}
    (u : ρ → ℂ) (hu : ∀ z ∈ W, ‖u z‖ = 1) (hK' : ∀ z ∈ W, ∀ n ∈ S, K' z n = u z * K z n) :
    IsSelected K' W S S0 ↔ IsSelected K W S S0 := by
  have hsum : ∀ a : σ → ℂ, ∑ z ∈ W, ‖∑ n ∈ S, a n * K' z n‖ ^ 2 =
      ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 := by
    intro a
    refine Finset.sum_congr rfl fun z hz => ?_
    have : ∑ n ∈ S, a n * K' z n = u z * ∑ n ∈ S, a n * K z n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n hn => by rw [hK' z hz n hn]; ring
    rw [this, norm_mul, hu z hz, one_mul]
  simp only [IsSelected, hsum]

/-- **(c) Associates.** If the sources are `Us ×ˢ S₀` (a label `u ∈ Us` and a base source `m ∈ S₀`), with
`K' z (u, m) = χ z u · K z m` and `‖χ z u‖ ≤ 1`, and `K` has the constant `S0` on `W × S₀`, then `K'` has the
constant `|Us| · S0`; for the six units of `ℤ[ω]` this is `6 S0`. -/
theorem IsSelected.associates {U : Type*} {K : ρ → σ → ℂ} {K' : ρ → U × σ → ℂ}
    {W : Finset ρ} {S₀ : Finset σ} {S0 : ℝ} (Us : Finset U) (χ : ρ → U → ℂ)
    (hχ : ∀ z ∈ W, ∀ u ∈ Us, ‖χ z u‖ ≤ 1)
    (hK' : ∀ z ∈ W, ∀ u ∈ Us, ∀ m ∈ S₀, K' z (u, m) = χ z u * K z m)
    (h : IsSelected K W S₀ S0) : IsSelected K' W (Us ×ˢ S₀) (Us.card * S0) := by
  classical
  have hblock : ∀ g ∈ Us, IsSelected (fun (z : ρ) (p : U × σ) => K z p.2) W
      ((Us ×ˢ S₀).filter fun n => n.1 = g) S0 := by
    intro g _
    have hinj : Set.InjOn (Prod.snd : U × σ → σ)
        (((Us ×ˢ S₀).filter fun n => n.1 = g : Finset (U × σ)) : Set (U × σ)) := by
      intro n hn n₁ hn₁ hnn
      have h1 := (Finset.mem_filter.mp hn).2
      have h2 := (Finset.mem_filter.mp hn₁).2
      exact Prod.ext (h1.trans h2.symm) hnn
    have hmem : ∀ n ∈ (Us ×ˢ S₀).filter (fun n => n.1 = g), n.2 ∈ S₀ := fun n hn =>
      (Finset.mem_product.mp (Finset.mem_filter.mp hn).1).2
    exact h.comap (K := fun (z : ρ) (p : U × σ) => K z p.2) id Prod.snd (fun a _ b _ hab => hab)
      hinj (fun z hz => hz) hmem (fun z _ n _ => rfl)
  refine IsSelected.of_class_twist (K₀ := fun (z : ρ) (p : U × σ) => K z p.2) Prod.fst Us
    (fun n hn => (Finset.mem_product.mp hn).1) χ hχ ?_ hblock
  intro z hz n hn
  obtain ⟨hu, hm⟩ := Finset.mem_product.mp hn
  exact hK' z hz n.1 hu n.2 hm

end GenericBlocks

end QRH.ArviKWall.BalancedSieve

namespace QRH.ArviKWall.ReciprocityBridge

open QRH.ArviKWall.BalancedSieve
open scoped BigOperators

local notation "O" => OAI.ActualEisensteinCubic.O

open OAI.CanonicalRowCompletion (idealRowHom idealRowHom_norm idealRowHom_argument_mul
  idealRowHom_ideal_reciprocity idealRowHom_one_supported sexticReciprocityPhase
  supported_residue_odd)
open OAI.CanonicalQuadraticSieve (Supported supported_primaryGenerator_ne_zero)
open OAI.CompletedGauss (primaryGenerator primaryGenerator_spec)
open OAI.ActualEisensteinCoordinates (residue)
open OAI.EisensteinEPrimaryPhase (Coord)
open Qrh.JointDetector (selectedNorm selectedMatrix selectedDualEnergy selectedDualEnergy_le
  selectedNorm_le_of_energy)

/-! ### The selected-leaf norm as an `IsSelected` statement -/

section Leaf

/-- The selected-leaf norm gives a selected constant for the kernel `(z/I)₆`, with the ideals `I` as
the outer sum and the elements `z` as the coefficients. -/
theorem isSelected_selectedNorm (rows : Finset O) (sources : Finset (Ideal O)) :
    IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I) sources rows
      (selectedNorm rows sources) := by
  intro a
  have h := selectedDualEnergy_le rows sources (fun z => a z.val)
  have e1 : ∀ I : sources, ∑ z ∈ rows, a z * idealRowHom z I.val =
      ∑ z : rows, selectedMatrix rows sources I z * a z.val := by
    intro I
    rw [← Finset.sum_coe_sort rows]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  calc ∑ I ∈ sources, ‖∑ z ∈ rows, a z * idealRowHom z I‖ ^ 2
      = ∑ I : sources, ‖∑ z ∈ rows, a z * idealRowHom z I.val‖ ^ 2 :=
        (Finset.sum_coe_sort sources (fun I => ‖∑ z ∈ rows, a z * idealRowHom z I‖ ^ 2)).symm
    _ = selectedDualEnergy rows sources (fun z => a z.val) := by
        unfold selectedDualEnergy
        exact Finset.sum_congr rfl fun I _ => by rw [e1 I]
    _ ≤ selectedNorm rows sources * ∑ z : rows, ‖a z.val‖ ^ 2 := h
    _ = selectedNorm rows sources * ∑ z ∈ rows, ‖a z‖ ^ 2 := by
        rw [Finset.sum_coe_sort rows (fun z => ‖a z‖ ^ 2)]

/-- Conversely, a selected constant for `(z/I)₆` bounds the selected-leaf norm. -/
theorem selectedNorm_le_of_isSelected (rows : Finset O) (sources : Finset (Ideal O)) {N : ℝ}
    (hN : 0 ≤ N)
    (h : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I) sources rows N) :
    selectedNorm rows sources ≤ N := by
  classical
  refine selectedNorm_le_of_energy rows sources N hN fun coeff => ?_
  obtain ⟨ext, hext⟩ : ∃ ext : O → ℂ, ext = fun z => if hz : z ∈ rows then coeff ⟨z, hz⟩ else 0 :=
    ⟨_, rfl⟩
  have hext' : ∀ z : rows, ext z.val = coeff z := fun z => by
    rw [hext]
    exact dite_eq_left z.property
  have key := h ext
  have e1 : ∀ I : sources, ∑ z : rows, selectedMatrix rows sources I z * coeff z =
      ∑ z ∈ rows, ext z * idealRowHom z I.val := by
    intro I
    rw [← Finset.sum_coe_sort rows]
    exact Finset.sum_congr rfl fun z _ => by rw [hext' z]; exact mul_comm _ _
  calc selectedDualEnergy rows sources coeff
      = ∑ I : sources, ‖∑ z ∈ rows, ext z * idealRowHom z I.val‖ ^ 2 := by
        unfold selectedDualEnergy
        exact Finset.sum_congr rfl fun I _ => by rw [e1 I]
    _ = ∑ I ∈ sources, ‖∑ z ∈ rows, ext z * idealRowHom z I‖ ^ 2 :=
        Finset.sum_coe_sort sources (fun I => ‖∑ z ∈ rows, ext z * idealRowHom z I‖ ^ 2)
    _ ≤ N * ∑ z ∈ rows, ‖ext z‖ ^ 2 := key
    _ = N * ∑ z : rows, ‖coeff z‖ ^ 2 := by
        rw [← Finset.sum_coe_sort rows (fun z => ‖ext z‖ ^ 2)]
        exact congrArg (N * ·) (Finset.sum_congr rfl fun z _ => by rw [hext' z])

theorem selectedNorm_nonneg (rows : Finset O) (sources : Finset (Ideal O)) :
    0 ≤ selectedNorm rows sources := by
  unfold selectedNorm
  positivity

end Leaf


/-! ### Reciprocity signs, unit twists and the factorization of the numerator -/

section Reciprocity

/-- The reciprocity sign of two residue classes mod `4`: OAI's `quadraticRaySign`, as a complex number.
It is `0` unless both classes are odd, and `±1` on odd classes. -/
def recSign (r t : Coord) : ℂ := ((OAI.QuadraticAllOddCRT.quadraticRaySign r t : ℤ) : ℂ)

/-- OAI's `sexticReciprocityPhase` is the sign of the residues mod `4`. -/
theorem sexticReciprocityPhase_eq (a b : O) :
    sexticReciprocityPhase a b = recSign (residue a) (residue b) := rfl

/-- The sign is symmetric in the two residue classes. -/
theorem recSign_symm (r t : Coord) : recSign r t = recSign t r := by
  unfold recSign
  rw [OAI.QuadraticAllOddCRT.quadraticRaySign_symm]

/-- On odd classes the sign is `±1`: its square is `1`. -/
theorem recSign_mul_self (r t : Coord) (hr : OAI.EisensteinEPrimaryPhase.odd r)
    (ht : OAI.EisensteinEPrimaryPhase.odd t) : recSign r t * recSign r t = 1 := by
  have hsq := OAI.QuadraticAllOddCRT.quadraticRaySign_sq r t hr ht
  unfold recSign
  rw [← Int.cast_mul, ← pow_two, hsq, Int.cast_one]

theorem norm_recSign_le (r t : Coord) : ‖recSign r t‖ ≤ 1 := by
  unfold recSign OAI.QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> simp

theorem norm_recSign_eq (r t : Coord) (hr : OAI.EisensteinEPrimaryPhase.odd r)
    (ht : OAI.EisensteinEPrimaryPhase.odd t) : ‖recSign r t‖ = 1 := by
  have hsq := OAI.QuadraticAllOddCRT.quadraticRaySign_sq r t hr ht
  have h1 : ((OAI.QuadraticAllOddCRT.quadraticRaySign r t : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast hsq
  have h2 : |((OAI.QuadraticAllOddCRT.quadraticRaySign r t : ℤ) : ℝ)| ^ 2 = 1 := by
    rw [sq_abs]
    exact h1
  unfold recSign
  rw [Complex.norm_intCast]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp h2

/-- A supported ideal is generated by its primary generator. -/
theorem span_primaryGenerator (I : Ideal O) (hI : Supported I) :
    Ideal.span {primaryGenerator I} = I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1

/-- The residue of the primary generator of a supported ideal is odd. -/
theorem odd_residue_primaryGenerator (I : Ideal O) (hI : Supported I) :
    OAI.EisensteinEPrimaryPhase.odd (residue (primaryGenerator I)) :=
  supported_residue_odd _ (by rw [span_primaryGenerator I hI]; exact hI)

/-- The primary generator is injective on supported ideals. -/
theorem primaryGenerator_injOn (W : Finset (Ideal O)) (hW : ∀ z ∈ W, Supported z) :
    Set.InjOn primaryGenerator (W : Set (Ideal O)) := by
  intro z hz z₁ hz₁ h
  rw [← span_primaryGenerator z (hW z hz), ← span_primaryGenerator z₁ (hW z₁ hz₁), h]

/-- A unit twist has absolute value `1` on every supported row. -/
theorem norm_idealRowHom_unit (x : O) (hx : IsUnit x) (z : Ideal O) (hz : Supported z) :
    ‖idealRowHom x z‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 := idealRowHom_norm (u : O) z
  have h2 := idealRowHom_norm ((u⁻¹ : Oˣ) : O) z
  have h3 : idealRowHom (u : O) z * idealRowHom ((u⁻¹ : Oˣ) : O) z = 1 := by
    rw [← idealRowHom_argument_mul, Units.mul_inv, idealRowHom_one_supported z hz]
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖idealRowHom (u : O) z‖ * ‖idealRowHom ((u⁻¹ : Oˣ) : O) z‖ := h4.symm
    _ ≤ ‖idealRowHom (u : O) z‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖idealRowHom (u : O) z‖ := mul_one _

/-- **Sextic reciprocity for composite moduli (OAI), in the form used here.** For supported ideals `I`, `J`
with primary generators `a = pg I`, `b = pg J`,
`(b / I)₆ = ε(a, b) · (a / J)₆`, where `ε(a, b) = recSign (a mod 4) (b mod 4)` depends only on the residue
classes mod `4`. This is `OAI.CanonicalRowCompletion.idealRowHom_ideal_reciprocity`; the composite case is
already proved there, so nothing is assumed here. -/
theorem reciprocity_composite (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    idealRowHom (primaryGenerator J) I =
      recSign (residue (primaryGenerator I)) (residue (primaryGenerator J)) *
        idealRowHom (primaryGenerator I) J :=
  idealRowHom_ideal_reciprocity I J hI hJ

/-- The same for primary elements `a`, `b` with supported spans. -/
theorem reciprocity_primary (a b : O) (ha : OAI.ActualEisensteinCubic.lambda ^ 2 ∣ a - 1)
    (hb : OAI.ActualEisensteinCubic.lambda ^ 2 ∣ b - 1) (hsa : Supported (Ideal.span {a}))
    (hsb : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a}) = recSign (residue a) (residue b) * idealRowHom a (Ideal.span {b}) :=
  OAI.CanonicalRowCompletion.idealRowHom_primary_reciprocity a b ha hb hsa hsb

/-- The class of a source: the multiplier `ce n` of its numerator (a unit, or a unit times `λ^a 2^b`) and
the residue mod `4` of the primary generator of its denominator. -/
noncomputable def srcClass {σ : Type*} (ce : σ → O) (d : σ → Ideal O) (n : σ) : O × Coord :=
  (ce n, residue (primaryGenerator (d n)))

/-- The row-dependent factor of a class `(e, t)`: `((e / z)₆ · ε(pg z, t))^k`. Its absolute value is `≤ 1`
always, and `= 1` on supported rows, unit multipliers and odd classes. -/
noncomputable def classPhase (k : ℕ) (z : Ideal O) (g : O × Coord) : ℂ :=
  (idealRowHom g.1 z * recSign (residue (primaryGenerator z)) g.2) ^ k

theorem norm_classPhase_le (k : ℕ) (z : Ideal O) (g : O × Coord) : ‖classPhase k z g‖ ≤ 1 := by
  unfold classPhase
  rw [norm_pow]
  refine pow_le_one₀ (norm_nonneg _) ?_
  rw [norm_mul]
  calc ‖idealRowHom g.1 z‖ * ‖recSign (residue (primaryGenerator z)) g.2‖ ≤ 1 * 1 :=
        mul_le_mul (idealRowHom_norm _ _) (norm_recSign_le _ _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_classPhase_eq (k : ℕ) (z : Ideal O) (hz : Supported z) (g : O × Coord)
    (hu : IsUnit g.1) (hg : OAI.EisensteinEPrimaryPhase.odd g.2) : ‖classPhase k z g‖ = 1 := by
  unfold classPhase
  rw [norm_pow, norm_mul, norm_idealRowHom_unit g.1 hu z hz,
    norm_recSign_eq _ _ (odd_residue_primaryGenerator z hz) hg, one_mul, one_pow]

/-- **The factorization of the numerator.** If the numerator `x` of `(x/z)₆^k` is `pg d · e`, then for
supported `z` and `d`
`(x/z)₆^k = classPhase k z (e, pg d mod 4) · (pg z / d)₆^k`. This is sextic reciprocity
(`reciprocity_composite`) together with multiplicativity in the numerator. -/
theorem numerator_factor (k : ℕ) (z d : Ideal O) (hz : Supported z) (hd : Supported d) (e : O)
    (x : O) (hx : x = primaryGenerator d * e) :
    idealRowHom x z ^ k =
      classPhase k z (e, residue (primaryGenerator d)) * idealRowHom (primaryGenerator z) d ^ k := by
  unfold classPhase
  rw [← mul_pow, hx, idealRowHom_argument_mul, reciprocity_composite z d hz hd]
  ring

/-- The odd residue classes mod `4`: there are `12`. -/
def oddCoords : Finset Coord := Finset.univ.filter fun r => OAI.EisensteinEPrimaryPhase.odd r

theorem mem_oddCoords {r : Coord} : r ∈ oddCoords ↔ OAI.EisensteinEPrimaryPhase.odd r := by
  simp [oddCoords]

theorem card_oddCoords : oddCoords.card = 12 := by
  decide

end Reciprocity


/-! ### The abstract bridge: numerators against the leaf kernel -/

section Abstract

variable {σ : Type*}

/-- **Bridge, leaf to numerator kernel.** Sources `n : σ` carry a numerator `num n ∈ O` and a denominator
ideal `d n`, with `num n = pg (d n) · e` for a multiplier `e ∈ E`. If `N` is a selected constant for the leaf
kernel `(z'/I)₆^k` (elements `z'` in `rows`, ideals `I` in `sources`), then `(E.card · 12) · N` is a
selected constant for the kernel `(num n / z)₆^k` on the rows `W` and the sources `S`, provided `pg z ∈ rows`,
`d n ∈ sources`, and `(d, num)` is injective on `S`.

The factor is `E.card` for the multiplier classes times `12` for the odd residue classes mod `4`. Only
the bound `|(e / z)₆| ≤ 1` is used, so `E` may contain non-units (the supplementary symbols `λ^a 2^b`). -/
theorem isSelected_numerator_of_leaf (k : ℕ) (num : σ → O) (d : σ → Ideal O)
    (W : Finset (Ideal O)) (S : Finset σ) (E : Finset O)
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported (d n))
    (hnum : ∀ n ∈ S, ∃ e ∈ E, num n = primaryGenerator (d n) * e)
    (hinj : ∀ n ∈ S, ∀ n₁ ∈ S, d n = d n₁ → num n = num n₁ → n = n₁)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) (hsrc : ∀ n ∈ S, d n ∈ sources)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hlib : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows N) :
    IsSelected (fun (z : Ideal O) (n : σ) => idealRowHom (num n) z ^ k) W S
      (((E.card * 12 : ℕ) : ℝ) * N) := by
  classical
  choose! ce hceE hce using hnum
  have hswap := hlib.swap hN0
  have hC : ∀ n ∈ S, srcClass ce d n ∈ E ×ˢ oddCoords := fun n hn =>
    Finset.mem_product.mpr ⟨hceE n hn, mem_oddCoords.mpr (odd_residue_primaryGenerator _ (hS n hn))⟩
  have hK : ∀ z ∈ W, ∀ n ∈ S, idealRowHom (num n) z ^ k =
      classPhase k z (srcClass ce d n) * idealRowHom (primaryGenerator z) (d n) ^ k :=
    fun z hz n hn => numerator_factor k z (d n) (hW z hz) (hS n hn) (ce n) (num n) (hce n hn)
  have hblock : ∀ g ∈ E ×ˢ oddCoords,
      IsSelected (fun (z : Ideal O) (n : σ) => idealRowHom (primaryGenerator z) (d n) ^ k) W
        (S.filter fun n => srcClass ce d n = g) N := by
    intro g _
    refine hswap.comap primaryGenerator d (primaryGenerator_injOn W hW) ?_ hrows ?_
      (fun z _ n _ => rfl)
    · intro n hn n₁ hn₁ hd
      obtain ⟨hnS, hng⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn₁S, hn₁g⟩ := Finset.mem_filter.mp hn₁
      have hce_eq : ce n = ce n₁ := congrArg Prod.fst (hng.trans hn₁g.symm)
      refine hinj n hnS n₁ hn₁S hd ?_
      rw [hce n hnS, hce n₁ hn₁S, hd, hce_eq]
    · intro n hn
      exact hsrc n (Finset.mem_filter.mp hn).1
  have hmain := IsSelected.of_class_twist
    (K := fun (z : Ideal O) (n : σ) => idealRowHom (num n) z ^ k)
    (K₀ := fun (z : Ideal O) (n : σ) => idealRowHom (primaryGenerator z) (d n) ^ k)
    (srcClass ce d) (E ×ˢ oddCoords) hC (classPhase k)
    (fun z _ g _ => norm_classPhase_le k z g) hK hblock
  have hcard : (E ×ˢ oddCoords).card = E.card * 12 := by
    rw [Finset.card_product, card_oddCoords]
  rw [hcard] at hmain
  exact hmain

/-- **Bridge, numerator kernel to leaf.** Conversely, if the multipliers in `E` are units, a selected
constant `S0` for `(num n / z)₆^k` on `W × S` gives the selected constant `(E.card · 12) · S0` for the leaf
kernel `(z'/I)₆^k`, where `rows` is contained in the primary generators of `W` and `sources` in the
denominators of `S`. No injectivity is needed here: one source is chosen for each denominator. -/
theorem isSelected_leaf_of_numerator (k : ℕ) (num : σ → O) (d : σ → Ideal O)
    (W : Finset (Ideal O)) (S : Finset σ) (E : Finset O) (hE : ∀ e ∈ E, IsUnit e)
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported (d n))
    (hnum : ∀ n ∈ S, ∃ e ∈ E, num n = primaryGenerator (d n) * e)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r)
    (hsrc : ∀ I ∈ sources, ∃ n ∈ S, d n = I)
    {S0 : ℝ} (hS0 : 0 ≤ S0)
    (h : IsSelected (fun (z : Ideal O) (n : σ) => idealRowHom (num n) z ^ k) W S S0) :
    IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows
      (((E.card * 12 : ℕ) : ℝ) * S0) := by
  classical
  have hcard : (E ×ˢ oddCoords).card = E.card * 12 := by
    rw [Finset.card_product, card_oddCoords]
  have hnn : 0 ≤ (((E.card * 12 : ℕ) : ℝ) * S0) := mul_nonneg (Nat.cast_nonneg _) hS0
  by_cases hne : Nonempty σ
  swap
  · -- no sources at all, so the target is a statement about the empty outer sum
    have hsrc0 : sources = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun I hI => ?_
      obtain ⟨n, _, _⟩ := hsrc I hI
      exact hne ⟨n⟩
    subst hsrc0
    intro a
    simpa using mul_nonneg hnn
      (Finset.sum_nonneg fun z (_ : z ∈ rows) => (by positivity : (0 : ℝ) ≤ ‖a z‖ ^ 2))
  choose! ce hceE hce using hnum
  choose! rep hrepS hrepd using hsrc
  choose! zrep hzrepW hzrepP using hrows
  -- restrict to one source per denominator and one row per primary generator
  have h' : IsSelected (fun (z : Ideal O) (n : σ) => idealRowHom (num n) z ^ k)
      (rows.image zrep) (sources.image rep) S0 := by
    refine (h.mono_rows ?_).mono_sources ?_
    · intro z hz
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
      exact hzrepW r hr
    · intro n hn
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hn
      exact hrepS I hI
  have hWr : ∀ z ∈ rows.image zrep, Supported z := fun z hz => by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    exact hW _ (hzrepW r hr)
  have hSr : ∀ n ∈ sources.image rep, n ∈ S := fun n hn => by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hn
    exact hrepS I hI
  have hC : ∀ n ∈ sources.image rep, srcClass ce d n ∈ E ×ˢ oddCoords := fun n hn =>
    Finset.mem_product.mpr ⟨hceE n (hSr n hn),
      mem_oddCoords.mpr (odd_residue_primaryGenerator _ (hS n (hSr n hn)))⟩
  have hphase : ∀ z ∈ rows.image zrep, ∀ g ∈ E ×ˢ oddCoords, ‖classPhase k z g‖ = 1 :=
    fun z hz g hg => norm_classPhase_eq k z (hWr z hz) g (hE _ (Finset.mem_product.mp hg).1)
      (mem_oddCoords.mp (Finset.mem_product.mp hg).2)
  have hK : ∀ z ∈ rows.image zrep, ∀ n ∈ sources.image rep,
      idealRowHom (primaryGenerator z) (d n) ^ k =
        (classPhase k z (srcClass ce d n))⁻¹ * idealRowHom (num n) z ^ k := by
    intro z hz n hn
    have hne0 : classPhase k z (srcClass ce d n) ≠ 0 := by
      intro h0
      have := hphase z hz _ (hC n hn)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hfac := numerator_factor k z (d n) (hWr z hz) (hS n (hSr n hn)) (ce n) (num n)
      (hce n (hSr n hn))
    have hsc : srcClass ce d n = (ce n, residue (primaryGenerator (d n))) := rfl
    rw [hsc] at hne0 ⊢
    rw [hfac, inv_mul_cancel_left₀ hne0]
  have hrev : IsSelected (fun (z : Ideal O) (n : σ) => idealRowHom (primaryGenerator z) (d n) ^ k)
      (rows.image zrep) (sources.image rep) ((E ×ˢ oddCoords).card * S0) := by
    refine IsSelected.of_class_twist (K₀ := fun (z : Ideal O) (n : σ) => idealRowHom (num n) z ^ k)
      (srcClass ce d) (E ×ˢ oddCoords) hC (fun z g => (classPhase k z g)⁻¹) ?_ hK ?_
    · intro z hz g hg
      rw [norm_inv, hphase z hz g hg, inv_one]
    · intro g _
      exact h'.mono_sources (Finset.filter_subset _ _)
  -- transport along `z ↦ pg z` and `n ↦ d n`
  have hf : Set.InjOn primaryGenerator ((rows.image zrep : Finset (Ideal O)) : Set (Ideal O)) :=
    (primaryGenerator_injOn _ hWr)
  have hg : Set.InjOn d ((sources.image rep : Finset σ) : Set σ) := by
    intro n hn n₁ hn₁ hd
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨I₁, hI₁, rfl⟩ := Finset.mem_image.mp hn₁
    rw [hrepd I hI, hrepd I₁ hI₁] at hd
    rw [hd]
  have himg := hrev.image (K' := fun (z' : O) (I : Ideal O) => idealRowHom z' I ^ k)
    primaryGenerator d hf hg (fun z _ n _ => rfl)
  rw [hcard] at himg
  have hsw := himg.swap (mul_nonneg (Nat.cast_nonneg _) hS0)
  refine (hsw.mono_rows ?_).mono_sources ?_
  · intro I hI
    exact Finset.mem_image.mpr ⟨rep I, Finset.mem_image.mpr ⟨I, hI, rfl⟩, hrepd I hI⟩
  · intro r hr
    exact Finset.mem_image.mpr ⟨zrep r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, hzrepP r hr⟩

end Abstract


/-! ### The two concrete kernels of `SexticSpikeFree.lean` -/

section Instances

open scoped Classical

/-- The coordinates `(x, y) ↦ x + y ω` are injective. -/
theorem twistElement_injective : Function.Injective twistElement := by
  intro p q h
  have := OAI.ActualEisensteinCoordinates.unique_coordinates
    (a := p.1) (b := p.2) (c := q.1) (d := q.2) h
  exact Prod.ext this.1 this.2

/-- The denominator ideal `(m)` of a twist `m`. -/
noncomputable def twistIdeal (m : ℤ × ℤ) : Ideal O := Ideal.span {twistElement m}

/-- The six units of `ℤ[ω]`. -/
noncomputable local instance unitsFintype : Fintype Oˣ :=
  @Fintype.ofFinite _ OAI.PrimaryIdealUnitReindex.finite_units

/-- The six units of `ℤ[ω]`, as elements. -/
noncomputable def unitElements : Finset O := Finset.univ.image fun u : Oˣ => (u : O)

theorem card_unitElements : unitElements.card = 6 := by
  rw [unitElements, Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ← Nat.card_eq_fintype_card, OAI.PrimaryIdealUnitReindex.card_units_eq_six]

theorem unit_mem_unitElements (u : Oˣ) : (u : O) ∈ unitElements :=
  Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

theorem isUnit_of_mem_unitElements {e : O} (he : e ∈ unitElements) : IsUnit e := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  exact u.isUnit

/-- A twist with supported ideal is its primary generator times a unit of `unitElements`. -/
theorem twistElement_assoc (m : ℤ × ℤ) (hm : Supported (twistIdeal m)) :
    ∃ e ∈ unitElements, twistElement m = primaryGenerator (twistIdeal m) * e := by
  have h1 : Ideal.span {primaryGenerator (twistIdeal m)} = Ideal.span {twistElement m} :=
    span_primaryGenerator _ hm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h1
  exact ⟨(u : O), unit_mem_unitElements u, hu.symm⟩

/-- **Twist sieve from the leaf kernel.** A selected constant `N` for the leaf kernel `(z'/I)₆^k` on
`rows × sources` gives the selected constant `72 N = 6 · 12 · N` for the twist sieve `twistKernel k` on
the rows `W` (supported ideals, with `pg z ∈ rows`) and the supported twists `T` (with `(m) ∈ sources`).
The factor is `6` for the associates of each ideal and `12` for the odd residue classes mod `4`, which is
`≤ 6 · 12²`. -/
theorem twistKernel_isSelected_of_leaf (k : ℕ) (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m))
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) (hsrc : ∀ m ∈ T, twistIdeal m ∈ sources)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hlib : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows N) :
    IsSelected (twistKernel k) W T (72 * N) := by
  have h := isSelected_numerator_of_leaf k twistElement twistIdeal W T unitElements hW hT
    (fun m hm => twistElement_assoc m (hT m hm))
    (fun m _ m₁ _ _ h => twistElement_injective h) rows sources hrows hsrc hN0 hlib
  rw [card_unitElements] at h
  have h72 : (((6 * 12 : ℕ) : ℝ) * N) = 72 * N := by norm_num
  rw [h72] at h
  exact h

/-- **Leaf kernel from the twist sieve.** Conversely, a selected constant `S0` for `twistKernel k` on
`W × T` gives `72 S0` for the leaf kernel on any `rows` among the primary generators of `W` and any
`sources` among the ideals `(m)`, `m ∈ T`. Associates collapse to one ideal. -/
theorem leaf_isSelected_of_twistKernel (k : ℕ) (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m))
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r)
    (hsrc : ∀ I ∈ sources, ∃ m ∈ T, twistIdeal m = I)
    {S0 : ℝ} (hS0 : 0 ≤ S0) (h : IsSelected (twistKernel k) W T S0) :
    IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows (72 * S0) := by
  have h' := isSelected_leaf_of_numerator k twistElement twistIdeal W T unitElements
    (fun _ he => isUnit_of_mem_unitElements he) hW hT
    (fun m hm => twistElement_assoc m (hT m hm)) rows sources hrows hsrc hS0 h
  rw [card_unitElements] at h'
  have h72 : (((6 * 12 : ℕ) : ℝ) * S0) = 72 * S0 := by norm_num
  rw [h72] at h'
  exact h'

/-- **The sextic kernel from the leaf kernel** (units are trivial: the numerator is the primary
generator of the source). The factor is `12`, the number of odd residue classes mod `4`. -/
theorem orderKernel_isSelected_of_leaf (k : ℕ) (W S : Finset (Ideal O))
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported n)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) (hsrc : ∀ n ∈ S, n ∈ sources)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hlib : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows N) :
    IsSelected (orderKernel k) W S (12 * N) := by
  have h := isSelected_numerator_of_leaf k primaryGenerator id W S {1} hW hS
    (fun n _ => ⟨1, Finset.mem_singleton_self _, (mul_one _).symm⟩) (fun n _ n₁ _ h _ => h) rows
    sources hrows hsrc hN0 hlib
  have h12 : ((({1} : Finset O).card * 12 : ℕ) : ℝ) * N = 12 * N := by simp
  rw [h12] at h
  exact h

/-- The leaf kernel from the sextic kernel `orderKernel k`, with factor `12`. -/
theorem leaf_isSelected_of_orderKernel (k : ℕ) (W S : Finset (Ideal O))
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported n)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r) (hsrc : ∀ I ∈ sources, I ∈ S)
    {S0 : ℝ} (hS0 : 0 ≤ S0) (h : IsSelected (orderKernel k) W S S0) :
    IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows (12 * S0) := by
  have h' := isSelected_leaf_of_numerator k primaryGenerator id W S {1}
    (fun e he => by rw [Finset.mem_singleton.mp he]; exact isUnit_one) hW hS
    (fun n _ => ⟨1, Finset.mem_singleton_self _, (mul_one _).symm⟩) rows sources hrows
    (fun I hI => ⟨I, hsrc I hI, rfl⟩) hS0 h
  have h12 : ((({1} : Finset O).card * 12 : ℕ) : ℝ) * S0 = 12 * S0 := by simp
  rw [h12] at h'
  exact h'

end Instances


/-! ### The case `k = 1`: the selected-leaf norm itself -/

section KOne

open scoped Classical

/-- The selected-leaf norm as an `IsSelected` statement for `(z/I)₆^1`. -/
theorem isSelected_selectedNorm_one (rows : Finset O) (sources : Finset (Ideal O)) :
    IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ 1) sources rows
      (selectedNorm rows sources) := by
  simpa only [pow_one] using isSelected_selectedNorm rows sources

/-- **Bridge (`k = 1`), leaf norm to twist sieve.** For supported rows `W` and supported twists `T`,
`72 · selectedNorm rows sources` is a selected constant for `twistKernel 1` on `W × T`, whenever the
primary generators of `W` lie in `rows` and the ideals `(m)`, `m ∈ T`, lie in `sources`. The factor `72`
is `6` associates times `12` odd classes mod `4`, and is at most `6 · 12² = 864`. -/
theorem twistKernel_one_isSelected (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m))
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) (hsrc : ∀ m ∈ T, twistIdeal m ∈ sources) :
    IsSelected (twistKernel 1) W T (72 * selectedNorm rows sources) :=
  twistKernel_isSelected_of_leaf 1 W T hW hT rows sources hrows hsrc
    (selectedNorm_nonneg rows sources) (isSelected_selectedNorm_one rows sources)

/-- **Bridge (`k = 1`), twist sieve to leaf norm.** A selected constant `S0 ≥ 0` for `twistKernel 1` on
`W × T` bounds the selected-leaf norm by `72 · S0`, for `rows` among the primary generators of `W` and
`sources` among the ideals `(m)`, `m ∈ T`. -/
theorem selectedNorm_le_of_twistKernel_one (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m))
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r)
    (hsrc : ∀ I ∈ sources, ∃ m ∈ T, twistIdeal m = I)
    {S0 : ℝ} (hS0 : 0 ≤ S0) (h : IsSelected (twistKernel 1) W T S0) :
    selectedNorm rows sources ≤ 72 * S0 :=
  selectedNorm_le_of_isSelected rows sources (mul_nonneg (by norm_num) hS0)
    (by simpa only [pow_one] using
      leaf_isSelected_of_twistKernel 1 W T hW hT rows sources hrows hsrc hS0 h)

/-- **Bridge (`k = 1`), leaf norm to the sextic kernel `orderKernel 1`**, with factor `12`. -/
theorem orderKernel_one_isSelected (W S : Finset (Ideal O))
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported n)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) (hsrc : ∀ n ∈ S, n ∈ sources) :
    IsSelected (orderKernel 1) W S (12 * selectedNorm rows sources) :=
  orderKernel_isSelected_of_leaf 1 W S hW hS rows sources hrows hsrc
    (selectedNorm_nonneg rows sources) (isSelected_selectedNorm_one rows sources)

/-- **Bridge (`k = 1`), sextic kernel to leaf norm**, with factor `12`. -/
theorem selectedNorm_le_of_orderKernel_one (W S : Finset (Ideal O))
    (hW : ∀ z ∈ W, Supported z) (hS : ∀ n ∈ S, Supported n)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r) (hsrc : ∀ I ∈ sources, I ∈ S)
    {S0 : ℝ} (hS0 : 0 ≤ S0) (h : IsSelected (orderKernel 1) W S S0) :
    selectedNorm rows sources ≤ 12 * S0 :=
  selectedNorm_le_of_isSelected rows sources (mul_nonneg (by norm_num) hS0)
    (by simpa only [pow_one] using
      leaf_isSelected_of_orderKernel 1 W S hW hS rows sources hrows hsrc hS0 h)

/-- **The bridge theorem (`k = 1`).** For supported rows `W` and supported twists `T`, the selected-leaf
norm of the primary generators of `W` against the ideals `(m)`, `m ∈ T`, gives the selected constant
`72 · selectedNorm` for the twist sieve `twistKernel 1` on `W × T`. -/
theorem twistKernel_one_isSelected_image (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m)) :
    IsSelected (twistKernel 1) W T
      (72 * selectedNorm (W.image primaryGenerator) (T.image twistIdeal)) :=
  twistKernel_one_isSelected W T hW hT _ _ (fun _ hz => Finset.mem_image_of_mem _ hz)
    (fun _ hm => Finset.mem_image_of_mem _ hm)

/-- **The bridge theorem, converse (`k = 1`).** A selected constant `S0 ≥ 0` for `twistKernel 1` on
`W × T` bounds the selected-leaf norm of the primary generators of `W` against the ideals `(m)`,
`m ∈ T`, by `72 · S0`. -/
theorem selectedNorm_image_le_of_twistKernel_one (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, Supported (twistIdeal m))
    {S0 : ℝ} (hS0 : 0 ≤ S0) (h : IsSelected (twistKernel 1) W T S0) :
    selectedNorm (W.image primaryGenerator) (T.image twistIdeal) ≤ 72 * S0 :=
  selectedNorm_le_of_twistKernel_one W T hW hT _ _
    (fun _ hr => Finset.mem_image.mp hr) (fun _ hI => Finset.mem_image.mp hI) hS0 h

end KOne


/-! ### Feeding the selected-leaf amplification -/

section Amplification

open scoped Classical
open Qrh.JointDetector (selectedNorm_inverse_amplification)

/-- **The twist sieve is amplified by the selected-leaf theorem.** Let `Tsmall`, `Tbig` be sets of
supported twists, `W` supported rows, and let `monomials`, `merged` be ideal sets with
`(m) · J ∈ merged` for `m ∈ Tsmall`, `J ∈ monomials`, and every ideal of `merged` of the form `(m')`,
`m' ∈ Tbig`. Suppose the monomials have amplifier response `≥ A` on the primary generators of `W`
(coefficient mass `C`, product-fibre bound `D`, exactly as in `selectedNorm_inverse_amplification`). Then
a selected constant `S1 ≥ 0` for `twistKernel 1` on `W × Tbig` gives the selected constant
`72 · (C D · 72 S1 / A)` on `W × Tsmall`. The two factors `72` are the two bridge directions. -/
theorem twistKernel_one_amplification (W : Finset (Ideal O)) (Tsmall Tbig : Finset (ℤ × ℤ))
    (hW : ∀ z ∈ W, Supported z) (hTs : ∀ m ∈ Tsmall, Supported (twistIdeal m))
    (hTb : ∀ m ∈ Tbig, Supported (twistIdeal m)) (monomials merged : Finset (Ideal O))
    (hclosed : ∀ m ∈ Tsmall, ∀ J ∈ monomials, twistIdeal m * J ∈ merged)
    (hmerged : ∀ I ∈ merged, ∃ m ∈ Tbig, twistIdeal m = I)
    (c : monomials → ℂ) (A C D : ℝ) (hA : 0 < A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hresponse : ∀ z ∈ W,
      A ≤ ‖∑ J : monomials, c J * idealRowHom (primaryGenerator z) J.val‖ ^ 2)
    (hcoeff : ∑ J : monomials, ‖c J‖ ^ 2 ≤ C)
    (hfiber : ∀ T ∈ merged,
      ((((Tsmall.image twistIdeal) ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℝ) ≤ D)
    {S1 : ℝ} (hS1 : 0 ≤ S1) (hbig : IsSelected (twistKernel 1) W Tbig S1) :
    IsSelected (twistKernel 1) W Tsmall (72 * (C * D * (72 * S1) / A)) := by
  obtain ⟨rows, hrows⟩ : ∃ rows : Finset O, rows = W.image primaryGenerator := ⟨_, rfl⟩
  obtain ⟨sources, hsources⟩ : ∃ sources : Finset (Ideal O), sources = Tsmall.image twistIdeal :=
    ⟨_, rfl⟩
  have hrowsW : ∀ z ∈ W, primaryGenerator z ∈ rows := fun z hz => by
    rw [hrows]
    exact Finset.mem_image_of_mem _ hz
  have hrowsW' : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r := fun r hr => by
    rw [hrows] at hr
    exact Finset.mem_image.mp hr
  have hsrcT : ∀ m ∈ Tsmall, twistIdeal m ∈ sources := fun m hm => by
    rw [hsources]
    exact Finset.mem_image_of_mem _ hm
  have hcl : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged := by
    intro I hI J hJ
    rw [hsources] at hI
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hI
    exact hclosed m hm J hJ
  have hres : ∀ z : rows, A ≤ ‖∑ J : monomials, c J * idealRowHom z.val J.val‖ ^ 2 := by
    intro z
    obtain ⟨w, hw, hwz⟩ := hrowsW' z.val z.property
    rw [← hwz]
    exact hresponse w hw
  have hfib : ∀ T ∈ merged,
      ((((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℕ) : ℝ) ≤ D := by
    rw [hsources]
    exact hfiber
  have hamp := selectedNorm_inverse_amplification rows sources monomials merged hcl c A C D hA hC hD
    hres hcoeff hfib
  have hbigNorm : selectedNorm rows merged ≤ 72 * S1 :=
    selectedNorm_le_of_twistKernel_one W Tbig hW hTb rows merged hrowsW' hmerged hS1 hbig
  have hsmall := twistKernel_one_isSelected W Tsmall hW hTs rows sources hrowsW hsrcT
  refine hsmall.mono ?_
  have hCD : 0 ≤ C * D := mul_nonneg hC hD
  have h1 : selectedNorm rows sources ≤ C * D * (72 * S1) / A :=
    hamp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbigNorm hCD) hA.le)
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

end Amplification


/-! ### Twists divisible by `λ` or `2` -/

section Supplementary

open scoped Classical

/-- Every nonzero element of `ℤ[ω]` is `λ^a 2^b y` with `y` coprime to `6`. -/
theorem exists_supported_decomposition (x : O) (hx : x ≠ 0) :
    ∃ (a b : ℕ) (y : O), x = OAI.ActualEisensteinCubic.lambda ^ a * 2 ^ b * y ∧
      Supported (Ideal.span {y}) := by
  have hl : ¬ IsUnit OAI.ActualEisensteinCubic.lambda := fun h =>
    OAI.CanonicalQuadraticSieve.lambdaIdeal_maximal.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have h2 : ¬ IsUnit (2 : O) := fun h =>
    OAI.CanonicalQuadraticSieve.twoIdeal_maximal.ne_top (Ideal.span_singleton_eq_top.mpr h)
  obtain ⟨c, hc, hlc⟩ := (FiniteMultiplicity.of_not_isUnit hl hx).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity OAI.ActualEisensteinCubic.lambda x = a at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (by rw [hc, mul_zero])
  obtain ⟨y, hy, h2y⟩ := (FiniteMultiplicity.of_not_isUnit h2 hc0).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity (2 : O) c = b at hy
  refine ⟨a, b, y, ?_, ?_⟩
  · rw [hc, hy]
    ring
  · rw [OAI.CanonicalQuadraticSieve.supported_span_iff]
    refine ⟨fun hly => hlc ?_, h2y⟩
    rw [hy]
    exact Dvd.dvd.mul_left hly _

/-- **Twists divisible by `λ` or `2` (the supplementary symbols).** Suppose every twist `m ∈ T` is
`λ^a 2^b x_m` with `x_m` coprime to `6` and with the type `(a, b)` in a finite set `AB`. Then
`72 |AB| N` is a selected constant for `twistKernel k` on `W × T`, where `N` is a selected constant for
the leaf kernel on `rows × sources` and `sources` contains the ideals `(x_m)`. The factors
`(λ/z)₆^a (2/z)₆^b` are unimodular row factors of the kind in `IsSelected.unit_twist_iff`; they only add
the types `(a, b)` to the classes. By `exists_supported_decomposition` such data exist for every nonzero
twist; for twists of norm `≤ M` one has `3^a 4^b ≤ M`, so `|AB| ≤ (1 + log₃ M)(1 + log₄ M)`. -/
theorem twistKernel_isSelected_of_leaf_supplementary (k : ℕ) (W : Finset (Ideal O))
    (T : Finset (ℤ × ℤ)) (AB : Finset (ℕ × ℕ)) (ab : ℤ × ℤ → ℕ × ℕ) (x : ℤ × ℤ → O)
    (hW : ∀ z ∈ W, Supported z)
    (hdec : ∀ m ∈ T, twistElement m =
      OAI.ActualEisensteinCubic.lambda ^ (ab m).1 * 2 ^ (ab m).2 * x m)
    (hxs : ∀ m ∈ T, Supported (Ideal.span {x m})) (hab : ∀ m ∈ T, ab m ∈ AB)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows)
    (hsrc : ∀ m ∈ T, Ideal.span {x m} ∈ sources)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hlib : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows N) :
    IsSelected (twistKernel k) W T (72 * (AB.card : ℝ) * N) := by
  obtain ⟨E, hE⟩ : ∃ E : Finset O, E = (unitElements ×ˢ AB).image
      fun p => OAI.ActualEisensteinCubic.lambda ^ p.2.1 * 2 ^ p.2.2 * p.1 := ⟨_, rfl⟩
  have hnum : ∀ m ∈ T, ∃ e ∈ E, twistElement m =
      primaryGenerator (Ideal.span {x m}) * e := by
    intro m hm
    have h1 : Ideal.span {primaryGenerator (Ideal.span {x m})} = Ideal.span {x m} :=
      span_primaryGenerator _ (hxs m hm)
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h1
    generalize primaryGenerator (Ideal.span {x m}) = p at hu ⊢
    refine ⟨OAI.ActualEisensteinCubic.lambda ^ (ab m).1 * 2 ^ (ab m).2 * (u : O), ?_, ?_⟩
    · rw [hE]
      exact Finset.mem_image.mpr ⟨((u : O), ab m),
        Finset.mem_product.mpr ⟨unit_mem_unitElements u, hab m hm⟩, by ring⟩
    · rw [hdec m hm, ← hu]
      ring
  have h := isSelected_numerator_of_leaf k twistElement (fun m => Ideal.span {x m}) W T E hW hxs
    hnum (fun m _ m₁ _ _ h => twistElement_injective h) rows sources hrows hsrc hN0 hlib
  refine h.mono ?_
  have hcard : E.card ≤ 6 * AB.card := by
    rw [hE]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, card_unitElements]
  have hcard' : ((E.card * 12 : ℕ) : ℝ) ≤ 72 * (AB.card : ℝ) := by
    have : E.card * 12 ≤ 72 * AB.card := by omega
    exact_mod_cast this
  calc ((E.card * 12 : ℕ) : ℝ) * N ≤ (72 * (AB.card : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hcard' hN0
    _ = 72 * (AB.card : ℝ) * N := rfl

/-- The absolute norm of the ideal `(m)` is the norm form `x² − xy + y²` of the twist. -/
theorem absNorm_twistIdeal (m : ℤ × ℤ) :
    ((Ideal.absNorm (twistIdeal m) : ℕ) : ℝ) = (twistNorm m : ℝ) := by
  have h1 := OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span (twistElement m)
  have h2 := OAI.ActualEisensteinCubic.eisEmbedding_eval_norm_sq m.1 m.2
  have h3 : twistElement m = OAI.ActualEisensteinCoordinates.eval m.1 m.2 := rfl
  unfold twistIdeal
  rw [← h1, h3, h2]
  unfold twistNorm
  push_cast
  ring

/-- `N(λ^a 2^b y) ≥ 3^a 4^b` for `y ≠ 0`. -/
theorem pow_mul_pow_le_absNorm (a b : ℕ) (y : O) (hy : y ≠ 0) :
    3 ^ a * 4 ^ b ≤
      Ideal.absNorm (Ideal.span {OAI.ActualEisensteinCubic.lambda ^ a * 2 ^ b * y}) := by
  have h2 : Ideal.absNorm (Ideal.span {(2 : O)}) = 4 := by
    have h := OAI.ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span (2 : O)
    rw [map_ofNat] at h
    have h4 : ((Ideal.absNorm (Ideal.span {(2 : O)}) : ℕ) : ℝ) = 4 := by
      rw [← h]
      simp
      norm_num
    exact_mod_cast h4
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, map_mul, map_mul, map_pow, map_pow,
    OAI.CubicEisenstein.absNorm_span_lambda, h2]
  have hpos : 1 ≤ Ideal.absNorm (Ideal.span {y}) := by
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hy
  calc 3 ^ a * 4 ^ b = 3 ^ a * 4 ^ b * 1 := (mul_one _).symm
    _ ≤ 3 ^ a * 4 ^ b * Ideal.absNorm (Ideal.span {y}) := Nat.mul_le_mul_left _ hpos

/-- The exponents of `λ` and `2` in a twist of norm `≤ M` are at most `log₃ M` and `log₄ M`. -/
theorem exponent_bound (m : ℤ × ℤ) (M : ℕ) (hm : twistNorm m ≤ M) (a b : ℕ) (y : O) (hy : y ≠ 0)
    (h : twistElement m = OAI.ActualEisensteinCubic.lambda ^ a * 2 ^ b * y) :
    a ≤ Nat.log 3 M ∧ b ≤ Nat.log 4 M := by
  have h1 := pow_mul_pow_le_absNorm a b y hy
  rw [← h] at h1
  have h3 : ((3 ^ a * 4 ^ b : ℕ) : ℝ) ≤ (M : ℝ) :=
    calc ((3 ^ a * 4 ^ b : ℕ) : ℝ) ≤ (Ideal.absNorm (twistIdeal m) : ℝ) := by exact_mod_cast h1
      _ = (twistNorm m : ℝ) := absNorm_twistIdeal m
      _ ≤ (M : ℝ) := by exact_mod_cast hm
  have h4 : 3 ^ a * 4 ^ b ≤ M := by exact_mod_cast h3
  exact ⟨Nat.le_log_of_pow_le (by norm_num)
      ((Nat.le_mul_of_pos_right _ (by positivity)).trans h4),
    Nat.le_log_of_pow_le (by norm_num) ((Nat.le_mul_of_pos_left _ (by positivity)).trans h4)⟩

theorem twistElement_ne_zero {m : ℤ × ℤ} (hm : m ≠ 0) : twistElement m ≠ 0 := by
  intro h
  apply hm
  apply twistElement_injective
  rw [h]
  simp [twistElement]

/-- **The whole twist box.** Every nonzero twist `m ∈ T` of norm `≤ M` is `λ^a 2^b y` with `y` coprime to `6`
and `a ≤ log₃ M`, `b ≤ log₄ M`. If `sources` contains the ideal `(y)` for each such decomposition, a selected
constant `N` for the leaf kernel on `rows × sources` gives
`72 (1 + log₃ M)(1 + log₄ M) N` for `twistKernel k` on `W × T`. -/
theorem twistKernel_isSelected_of_leaf_box (k : ℕ) (W : Finset (Ideal O)) (T : Finset (ℤ × ℤ))
    (M : ℕ) (hW : ∀ z ∈ W, Supported z) (hT : ∀ m ∈ T, m ≠ 0 ∧ twistNorm m ≤ M)
    (rows : Finset O) (sources : Finset (Ideal O))
    (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows)
    (hsrc : ∀ m ∈ T, ∀ (a b : ℕ) (y : O),
      twistElement m = OAI.ActualEisensteinCubic.lambda ^ a * 2 ^ b * y →
        Supported (Ideal.span {y}) → Ideal.span {y} ∈ sources)
    {N : ℝ} (hN0 : 0 ≤ N)
    (hlib : IsSelected (fun (I : Ideal O) (z : O) => idealRowHom z I ^ k) sources rows N) :
    IsSelected (twistKernel k) W T
      (72 * (((Nat.log 3 M + 1) * (Nat.log 4 M + 1) : ℕ) : ℝ) * N) := by
  have hex : ∀ m ∈ T, ∃ (a b : ℕ) (y : O), twistElement m =
      OAI.ActualEisensteinCubic.lambda ^ a * 2 ^ b * y ∧ Supported (Ideal.span {y}) :=
    fun m hm => exists_supported_decomposition _ (twistElement_ne_zero (hT m hm).1)
  choose! a b y hdec hys using hex
  have hy0 : ∀ m ∈ T, y m ≠ 0 := by
    intro m hm h0
    apply twistElement_ne_zero (hT m hm).1
    rw [hdec m hm, h0, mul_zero]
  have hab : ∀ m ∈ T, (fun m => (a m, b m)) m ∈
      Finset.range (Nat.log 3 M + 1) ×ˢ Finset.range (Nat.log 4 M + 1) := by
    intro m hm
    obtain ⟨ha, hb⟩ := exponent_bound m M (hT m hm).2 (a m) (b m) (y m) (hy0 m hm) (hdec m hm)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have h := twistKernel_isSelected_of_leaf_supplementary k W T
    (Finset.range (Nat.log 3 M + 1) ×ˢ Finset.range (Nat.log 4 M + 1)) (fun m => (a m, b m)) y hW
    hdec hys hab rows sources hrows
    (fun m hm => hsrc m hm (a m) (b m) (y m) (hdec m hm) (hys m hm)) hN0 hlib
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at h
  exact h

end Supplementary

/-! ### The rows and sources of `SpikeFreeLargeSieve` -/

section SexticObjects

open scoped Classical

/-- The rows `sexticRows B` are supported ideals. -/
theorem supported_of_mem_sexticRows {B : ℕ} {z : Ideal O} (hz : z ∈ sexticRows B) : Supported z :=
  (OAI.CanonicalQuadraticSieve.mem_fullRange.mp (Finset.mem_filter.mp hz).1).1

/-- The sources `sexticSources L` are supported ideals. -/
theorem supported_of_mem_sexticSources {L : ℕ} {n : Ideal O} (hn : n ∈ sexticSources L) :
    Supported n :=
  (OAI.CanonicalQuadraticSieve.mem_fullRange.mp hn).1

/-- **The kernel of the conjecture against the selected-leaf norm.** For any row subset
`W ⊆ sexticRows B`, `12 · selectedNorm rows (sexticSources L)` is a selected constant for
`orderKernel 1` on `W × sexticSources L`, whenever `rows` contains the primary generators of `W`. -/
theorem orderKernel_one_isSelected_sextic (B L : ℕ) (W : Finset (Ideal O)) (hW : W ⊆ sexticRows B)
    (rows : Finset O) (hrows : ∀ z ∈ W, primaryGenerator z ∈ rows) :
    IsSelected (orderKernel 1) W (sexticSources L) (12 * selectedNorm rows (sexticSources L)) :=
  orderKernel_one_isSelected W (sexticSources L) (fun _ hz => supported_of_mem_sexticRows (hW hz))
    (fun _ hn => supported_of_mem_sexticSources hn) rows (sexticSources L) hrows (fun _ hn => hn)

/-- Conversely, a selected constant `S0 ≥ 0` for `orderKernel 1` on `W × sexticSources L` bounds the
selected-leaf norm of the primary generators of `W` against any `sources ⊆ sexticSources L` by `12 S0`. -/
theorem selectedNorm_le_of_orderKernel_one_sextic (B L : ℕ) (W : Finset (Ideal O))
    (hW : W ⊆ sexticRows B) (rows : Finset O)
    (hrows : ∀ r ∈ rows, ∃ z ∈ W, primaryGenerator z = r) (sources : Finset (Ideal O))
    (hsrc : sources ⊆ sexticSources L) {S0 : ℝ} (hS0 : 0 ≤ S0)
    (h : IsSelected (orderKernel 1) W (sexticSources L) S0) :
    selectedNorm rows sources ≤ 12 * S0 :=
  selectedNorm_le_of_orderKernel_one W (sexticSources L)
    (fun _ hz => supported_of_mem_sexticRows (hW hz))
    (fun _ hn => supported_of_mem_sexticSources hn) rows sources hrows (fun _ hI => hsrc hI) hS0 h

end SexticObjects

end QRH.ArviKWall.ReciprocityBridge

#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.mono_sources
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.swap
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.comap
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.image
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.of_class_twist
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.sign_blocks
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.sign_blocks_card
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.unit_twist_iff
#print axioms QRH.ArviKWall.BalancedSieve.IsSelected.associates
#print axioms QRH.ArviKWall.ReciprocityBridge.isSelected_selectedNorm
#print axioms QRH.ArviKWall.ReciprocityBridge.selectedNorm_le_of_isSelected
#print axioms QRH.ArviKWall.ReciprocityBridge.reciprocity_composite
#print axioms QRH.ArviKWall.ReciprocityBridge.numerator_factor
#print axioms QRH.ArviKWall.ReciprocityBridge.isSelected_numerator_of_leaf
#print axioms QRH.ArviKWall.ReciprocityBridge.isSelected_leaf_of_numerator
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_isSelected_of_leaf
#print axioms QRH.ArviKWall.ReciprocityBridge.leaf_isSelected_of_twistKernel
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_one_isSelected
#print axioms QRH.ArviKWall.ReciprocityBridge.selectedNorm_le_of_twistKernel_one
#print axioms QRH.ArviKWall.ReciprocityBridge.orderKernel_one_isSelected
#print axioms QRH.ArviKWall.ReciprocityBridge.selectedNorm_le_of_orderKernel_one
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_one_isSelected_image
#print axioms QRH.ArviKWall.ReciprocityBridge.selectedNorm_image_le_of_twistKernel_one
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_one_amplification
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_isSelected_of_leaf_supplementary
#print axioms QRH.ArviKWall.ReciprocityBridge.exists_supported_decomposition
#print axioms QRH.ArviKWall.ReciprocityBridge.exponent_bound
#print axioms QRH.ArviKWall.ReciprocityBridge.twistKernel_isSelected_of_leaf_box
#print axioms QRH.ArviKWall.ReciprocityBridge.orderKernel_one_isSelected_sextic
#print axioms QRH.ArviKWall.ReciprocityBridge.selectedNorm_le_of_orderKernel_one_sextic
