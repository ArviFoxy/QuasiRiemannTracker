import Submissions.arvi_kwall.SexticSpikeFree

/-!
# The source-side theta, and the balanced-point conjecture with both thetas removed

Research file (QRH, K-wall program). It corrects the conjecture of `SexticSpikeFree.lean` and proves the reductions
for the corrected form. Nothing here proves either conjecture.

## Why the one-sided statement is expected to fail

`SexticSpikeFree.lean` removes spikes on the row side only: the twisted row thetas `g̃(z) conj χ_z(m)^k` and the
plain characters `χ_z(m)^k`, `conj χ_z(m)^k` with `N(m) ≤ C B^{1−qε}`. At the balanced point the matrix is self-dual
under reciprocity, and Poisson summation in the *row* variable produces a second theta, on the source side.

Numerics (`research/rip/theta`: `theta_mech_*.py`, `theta_blockcover.py`) [numerical]:
* The top singular pair of the sextic matrix at `B = L = 3·10³ … 3·10⁵` is a spiked-Wishart outlier. Its source
  vector is `f(x) = A(x mod 4) (3/x)₃ ε(x) conj g̃(x) N(x)^{−1/3}`, with `g̃(x)` the source's sextic Gauss sum, `A` a
  twelfth root of unity on each class mod 4, `(3/x)₃` a cubic character mod 9, and `ε(x) = −1` on odd-class sources
  with an odd number of prime factors. The BBP formula with this spike reproduces the top eigenvalue to 3%, and the
  spike strength grows like `0.38 B^{1/6}`.
* Its row image `E f` has no component along the row thetas. Its energy in the span of
  `g̃(z)·(class functions mod 36)·(two profiles)` equals that of a random vector: 0.170 against 0.153 at `B = 10⁴`,
  and 0.067 against 0.051 at `B = 3·10⁴`.
* It does meet the plain characters, but `E f = Σ_x f(x) χ_·(x)` uses every source `x`, and the spike lives at
  large `N(x)`. Restrict `f` to `N(x) > 3000` and project its image off the low-twist family. The Rayleigh quotient
  `s²/S` of what is left is 1.74 at `B = 10⁴` (cutoff `0.3 B`; random phases 1.57) and 2.60 at `B = 3·10⁴` (cutoff
  `0.1 B`; random phases 1.85). The residual grows with `B`.
* The plain kinds of `SexticSpikeFree` reach only `N(m) ≤ C B^{1−qε}`. If the source theta keeps its profile and its
  `B^{1/6}` growth, the share of `|f|²` above that cutoff tends to 1. Then, for large `B`, there is a row vector `b`
  orthogonal to every spike of `SexticSpikeFree` with `b* G b ≫ B^{7/6} ‖b‖²`, and `SpikeFreeLargeSieve 1 6` fails
  for every `ε < 1/6`. [derived from the numerical model; not a proof]

## The corrected statement

Remove both thetas. The row vector `b` must be orthogonal to the row spikes, as before. Its dual sum
`n ↦ Σ_z b_z conj χ_z(n)^k` must also be orthogonal to the source spikes (`rowInner_rowImage`). These are the row
shapes with the source as the modulus: `conj g̃(n) χ_n(m)^k`, `g̃(n) conj χ_n(m)^k`, `χ_n(m)^k` and
`conj χ_n(m)^k`. Each comes with or without the Liouville sign `(−1)^{Ω(n)}`, on dyadic windows
`2^w ≤ N n < 2^{w+1}` with profiles `(2^w / N n)^{j/2}`.
- The class phases `A(x mod 4) (3/x)₃` are twists by units, `λ` and `2`, which the twist box contains.
- The sign `ε(x)` is a combination of `1`, `χ_x(−1)`, the Liouville sign and their product.

* `TwoSidedSpikeFree k q` is the corrected conjecture. `twoSided_of_spikeFree`: the one-sided conjecture implies it.
* `GradedTwoSided k q` is its graded form. The source images are weighted by `C B^ε 2^{−w} 2^{−j}`, which is
  `1/‖ψ‖²` for a window of about `2^w` sources, up to `C B^ε`. The weights are a first choice; the recursion has not
  priced them.
* `twoSided_of_graded`: the graded form implies the corrected conjecture.
* `selected_of_gradedTwoSided`: the selected bound `C B^{1+ε} + Λ_row + Λ_src` on any row set `W`. Here `Λ_src` is
  the Bessel constant of the source images on `W`; `spikeBessel_disjSum` adds the two families.

## Numerical tests of the corrected statement

The null is the masked random matrix (i.i.d. phases on E's zero pattern) projected off the same spans. E's zeros put
its edge about 4.5% below the Marchenko–Pastur formula, which an earlier version of this table used. [numerical]

Fixed families (`theta_twosided.py`, `theta_twosided_free.py`): the row family holds the thetas and plain characters
on classes mod 36 plus twists `N(m) ≤ 30` (dimension 1080); the source family holds `conj g̃(x)` and `g̃(x)` times
`N(x)^{−1/3}` on cells mod 36 × parity (dimension 432). Top `s²/S`:

| `B = L` | full (null) | off both (null, same spans) | random spans |
|---|---|---|---|
| 3·10⁴ | 4.550 (3.992) | 3.773 (3.616) | 3.992 |
| 10⁵ | 4.949 (3.990) | 4.442 (3.879) | 4.758 |
| 2·10⁵ | 5.279 | 4.756 | 5.171 |

Growing families (`theta_twosided_grow.py`): row twists `N(m) ≤ M`, and twisted source thetas `N(m) ≤ M′` (the
class-signed source theta times `(x/m)₆^{±1}`, and the plain `(x/m)₆^{±1}`). Excess of the top over the null:

| (M, M′) | (30, 0) | (100, 0) | (100, 30) | (300, 0) | (300, 100) |
|---|---|---|---|---|---|
| 3·10⁴ | +4.3% | +2.1% | +1.1% | −0.4% | −1.7% |
| 10⁵ | +14.5% | +13.4% | | +10.3% | |

- At 3·10⁴ families that grow reach the null, and random spans of the same dimensions stay above it.
- At 10⁵ the same families are a third of the relative size (the row family is 13% of the rows, against 42%) and
  remove less. The statement removes twists up to `C B^{1−qε}`, a positive fraction of the rows, so these runs are
  consistent with it but do not test it at 10⁵.
- The source spike is a residue: `E f(z)` is a partial sum of the sextic Kubota series at the index `z`, and its row
  image is one vector built over every scale of the sources (`research/journal`, "The block outlier is a residue").
  [numerical; identification with the theta coefficients heuristic]

## What the K-wall recursion needs now

- `Λ_row` is the twist sieve of `SexticSpikeFree`, bridged to PR 93's selected norm in `ReciprocityBridge.lean`.
- `Λ_src` is new. Numerically the untwisted source image is flat on the rows: `|E f(z)|²` follows the exponential law.
  It puts exactly its density on slot-selected rows. On the top 10% of rows by a slot sum its share is 0.098 and
  0.103 at `B = 10⁴`, and 0.102 and 0.096 at `3·10⁴`. On the top 1% it is 0.0096 and 0.0082, and 0.0085 and 0.0077.
- A flat image adds about `θ S |W| / R ≈ B^{7/6−δ}` for `|W| = B^{1−δ}`. That is below `B^{1+ε}` once `δ ≥ 1/6`, so
  the barrier range `1/3 ≤ δ < 1/2` is untouched.
- Twisted source spikes. `rowImage_twist_dilation` (proved): the image of `ψ·χ_m^k` at `z` is the image of `ψ` at
  `z·m`, so the twisted spikes are dilations `z ↦ Φ(zm)` of one series, and `twisted_energy_eq` moves their energy on
  `W` to the dilated set. Numerically only the `+1` twists carry a spike, with strength decaying roughly like
  `N(m)^{−1/q}`, and their images are flat on slot-selected rows at 3·10⁴ (`research/journal`, 2026-10-31).
  [numerical]
-/

namespace QRH.ArviKWall.BalancedSieve

open Finset
open scoped BigOperators ComplexConjugate

section GenericSource

variable {ρ σ κ ι : Type*}

/-- The row image `z ↦ Σ_{n∈S} K(z,n) ψ(n)` of a source vector `ψ`: the polynomial with coefficients `ψ`, evaluated
at the rows. -/
def rowImage (K : ρ → σ → ℂ) (S : Finset σ) (ψ : σ → ℂ) (z : ρ) : ℂ := ∑ n ∈ S, K z n * ψ n

/-- A row vector is orthogonal to the row image of `ψ` exactly when its dual sum `n ↦ Σ_z b_z conj K(z,n)` is
orthogonal to `ψ`. -/
theorem rowInner_rowImage (K : ρ → σ → ℂ) (R : Finset ρ) (S : Finset σ) (b : ρ → ℂ) (ψ : σ → ℂ) :
    rowInner R b (rowImage K S ψ) = ∑ n ∈ S, (∑ z ∈ R, b z * conj (K z n)) * conj (ψ n) := by
  have hL : rowInner R b (rowImage K S ψ) = ∑ z ∈ R, ∑ n ∈ S, b z * (conj (K z n) * conj (ψ n)) := by
    unfold rowInner rowImage
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [map_mul]
  have hR : ∑ n ∈ S, (∑ z ∈ R, b z * conj (K z n)) * conj (ψ n) =
      ∑ n ∈ S, ∑ z ∈ R, b z * (conj (K z n) * conj (ψ n)) :=
    Finset.sum_congr rfl fun n _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ => by ring
  rw [hL, hR, Finset.sum_comm]

/-- Bessel constants add over a disjoint union of spike families. -/
theorem spikeBessel_disjSum {W : Finset ρ} {T₁ : Finset κ} {T₂ : Finset ι} {f₁ : κ → ρ → ℂ}
    {f₂ : ι → ρ → ℂ} {w₁ : κ → ℝ} {w₂ : ι → ℝ} {Λ₁ Λ₂ : ℝ} (h₁ : SpikeBessel W T₁ f₁ w₁ Λ₁)
    (h₂ : SpikeBessel W T₂ f₂ w₂ Λ₂) :
    SpikeBessel W (T₁.disjSum T₂) (Sum.elim f₁ f₂) (Sum.elim w₁ w₂) (Λ₁ + Λ₂) := by
  intro b
  rw [Finset.sum_disjSum, add_mul]
  exact add_le_add (h₁ b) (h₂ b)

end GenericSource

section ConcreteSource

open OAI
open scoped Classical

local notation "O" => OAI.ActualEisensteinCubic.O

/-- `a b ≤ 1` for `a ≤ 1` and `0 ≤ b ≤ 1`. -/
theorem mul_le_one_of_le_one {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  calc a * b ≤ 1 * 1 := mul_le_mul ha hb hb0 zero_le_one
    _ = 1 := one_mul 1

/-- The Liouville sign `(−1)^{Ω(n)}`, with `Ω(n)` the number of prime ideal factors of `n` counted with multiplicity.
On squarefree ideals it is the Möbius sign. -/
noncomputable def liouvilleSign (n : Ideal O) : ℂ := (-1) ^ (UniqueFactorizationMonoid.factors n).card

theorem norm_liouvilleSign (n : Ideal O) : ‖liouvilleSign n‖ = 1 := by
  simp [liouvilleSign]

/-- Source spike shapes: the row shapes with the source as the modulus. Kind `0` is `conj g̃(n) χ_n(m)^k` (the
orientation the numerics find), `1` is `g̃(n) conj χ_n(m)^k`, `2` is `χ_n(m)^k` and `3` is `conj χ_n(m)^k`. With the
flag set, the shape is multiplied by the Liouville sign. -/
noncomputable def sourceShape (k : ℕ) (c : Fin 4) (s : Bool) (m : ℤ × ℤ) (n : Ideal O) : ℂ :=
  (if s then liouvilleSign n else 1) *
    (if c = 0 then conj (gaussPhase k n) * CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k
    else if c = 1 then gaussPhase k n * conj (CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k)
    else if c = 2 then CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k
    else conj (CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k))

theorem norm_sourceShape_le (k : ℕ) (c : Fin 4) (s : Bool) (m : ℤ × ℤ) (n : Ideal O) :
    ‖sourceShape k c s m n‖ ≤ 1 := by
  have hχ : ‖CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (CanonicalRowCompletion.idealRowHom_norm _ _)
  have hg := norm_gaussPhase_le k n
  have hs : ‖(if s then liouvilleSign n else 1 : ℂ)‖ ≤ 1 := by
    split_ifs
    · exact (norm_liouvilleSign n).le
    · simp
  have hc : ‖(if c = 0 then conj (gaussPhase k n) * CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k
      else if c = 1 then gaussPhase k n * conj (CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k)
      else if c = 2 then CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k
      else conj (CanonicalRowCompletion.idealRowHom (twistElement m) n ^ k))‖ ≤ 1 := by
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_one_of_le_one hg (norm_nonneg _) hχ
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_one_of_le_one hg (norm_nonneg _) hχ
    · exact hχ
    · rw [Complex.norm_conj]
      exact hχ
  unfold sourceShape
  rw [norm_mul]
  exact mul_le_one_of_le_one hs (norm_nonneg _) hc

/-- The window profile: `(2^w / N n)^{j/2}` on the dyadic window `2^w ≤ N n < 2^{w+1}`, zero outside. On the window it
lies in `(2^{−j/2}, 1]`. -/
noncomputable def sourceProfile (w j : ℕ) (n : Ideal O) : ℝ :=
  if 2 ^ w ≤ Ideal.absNorm n ∧ Ideal.absNorm n < 2 ^ (w + 1) then
    Real.sqrt ((2 : ℝ) ^ w / (Ideal.absNorm n : ℝ)) ^ j
  else 0

theorem sourceProfile_nonneg (w j : ℕ) (n : Ideal O) : 0 ≤ sourceProfile w j n := by
  unfold sourceProfile
  split_ifs
  · exact pow_nonneg (Real.sqrt_nonneg _) _
  · exact le_refl 0

theorem sourceProfile_le_one (w j : ℕ) (n : Ideal O) : sourceProfile w j n ≤ 1 := by
  unfold sourceProfile
  split_ifs with h
  · have hpos : (0 : ℝ) < (Ideal.absNorm n : ℝ) := by
      have h1 : (1 : ℕ) ≤ Ideal.absNorm n := le_trans (Nat.one_le_two_pow) h.1
      exact_mod_cast h1
    have hle : (2 : ℝ) ^ w ≤ (Ideal.absNorm n : ℝ) := by exact_mod_cast h.1
    have hq : (2 : ℝ) ^ w / (Ideal.absNorm n : ℝ) ≤ 1 := (div_le_one hpos).mpr hle
    have hs : Real.sqrt ((2 : ℝ) ^ w / (Ideal.absNorm n : ℝ)) ≤ 1 := by
      calc Real.sqrt ((2 : ℝ) ^ w / (Ideal.absNorm n : ℝ)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hq
        _ = 1 := Real.sqrt_one
    exact pow_le_one₀ (Real.sqrt_nonneg _) hs
  · exact zero_le_one

/-- Source spike index: (kind, Liouville flag), twist, window, profile degree. -/
abbrev SourceIdx := (Fin 4 × Bool) × (ℤ × ℤ) × ℕ × ℕ

/-- The source spike vector: shape times window profile. -/
noncomputable def sourceSpike (k : ℕ) (i : SourceIdx) (n : Ideal O) : ℂ :=
  sourceShape k i.1.1 i.1.2 i.2.1 n * (sourceProfile i.2.2.1 i.2.2.2 n : ℂ)

theorem norm_sourceSpike_le (k : ℕ) (i : SourceIdx) (n : Ideal O) : ‖sourceSpike k i n‖ ≤ 1 := by
  unfold sourceSpike
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sourceProfile_nonneg _ _ _)]
  exact mul_le_one_of_le_one (norm_sourceShape_le _ _ _ _ _) (sourceProfile_nonneg _ _ _)
    (sourceProfile_le_one _ _ _)

/-- Source spike indices: every kind and flag, twists of norm `≤ M`, windows `w < V`, profile degrees `j < J`. -/
def sourceIndex (M V J : ℕ) : Finset SourceIdx :=
  Finset.univ ×ˢ (twistBox M ×ˢ (Finset.range V ×ˢ Finset.range J))

/-- The number of dyadic windows that cover the norms `1, …, B`. -/
def windowCount (B : ℕ) : ℕ := Nat.log 2 B + 1

/-- **Conjecture: the large sieve at the balanced point with both thetas removed.** For every `ε > 0` there is
`C > 0` such that for every `B ≥ 1` and every row vector `b` the bound
`Σ_n |Σ_z b_z conj χ_z(n)^k|² ≤ C B^{1+ε} Σ_z |b_z|²` holds, provided two orthogonality conditions hold:
- `b` is orthogonal to the row spikes of `SpikeFreeLargeSieve`;
- `b` is orthogonal to the row images of the source spikes (twist norm `≤ C B^{1−qε}`, every dyadic window up to `B`,
  profile degree `≤ C B^ε`). Equivalently, the dual sum is orthogonal to those source spikes (`rowInner_rowImage`).
-/
def TwoSidedSpikeFree (k q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ b : Ideal O → ℂ,
    (∀ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B),
        rowInner (sexticRows B) b (spikeVector k B i) = 0) →
    (∀ i ∈ sourceIndex (twistCutoff q C ε B) (windowCount B) (profileCutoff C ε B),
        rowInner (sexticRows B) b (rowImage (orderKernel k) (sexticSources B) (sourceSpike k i)) = 0) →
      dualForm (orderKernel k) (sexticRows B) (sexticSources B) b ≤
        C * (B : ℝ) ^ (1 + ε) * ∑ z ∈ sexticRows B, ‖b z‖ ^ 2

/-- The sextic case. -/
def SexticTwoSided : Prop := TwoSidedSpikeFree 1 6

/-- The cubic case. -/
def CubicTwoSided : Prop := TwoSidedSpikeFree 2 3

/-- The one-sided conjecture implies the two-sided one, which asks the same bound of fewer vectors. -/
theorem twoSided_of_spikeFree {k q : ℕ} (h : SpikeFreeLargeSieve k q) : TwoSidedSpikeFree k q := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  exact ⟨C, hC, fun B hB1 b hrow _ => hB B hB1 b hrow⟩

/-- The source weights `C B^ε 2^{−w} 2^{−j}`. -/
noncomputable def sourceWeight (C ε : ℝ) (B : ℕ) (i : SourceIdx) : ℝ :=
  C * (B : ℝ) ^ ε * (1 / 2) ^ i.2.2.1 * (1 / 2) ^ i.2.2.2

theorem sourceWeight_nonneg {C : ℝ} (hC : 0 ≤ C) (ε : ℝ) (B : ℕ) (i : SourceIdx) :
    0 ≤ sourceWeight C ε B i := by
  unfold sourceWeight
  have h1 : (0 : ℝ) ≤ (B : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- The two-sided spike index: the row spikes, then the source spikes. -/
noncomputable def twoSidedIndex (q : ℕ) (C ε : ℝ) (B : ℕ) : Finset ((Fin 3 × (ℤ × ℤ) × ℕ) ⊕ SourceIdx) :=
  (spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B)).disjSum
    (sourceIndex (twistCutoff q C ε B) (windowCount B) (profileCutoff C ε B))

/-- The two-sided spike vectors: the row spikes, and the row images of the source spikes. -/
noncomputable def twoSidedVector (k B : ℕ) : (Fin 3 × (ℤ × ℤ) × ℕ) ⊕ SourceIdx → Ideal O → ℂ :=
  Sum.elim (spikeVector k B) fun i => rowImage (orderKernel k) (sexticSources B) (sourceSpike k i)

/-- The two-sided weights. -/
noncomputable def twoSidedWeight (q : ℕ) (C ε : ℝ) (B : ℕ) : (Fin 3 × (ℤ × ℤ) × ℕ) ⊕ SourceIdx → ℝ :=
  Sum.elim (gradedWeight q C ε B) (sourceWeight C ε B)

/-- **Conjecture (graded form, both thetas).** The row Gram is at most `C B^{1+ε} I` plus the weighted row spikes plus
the weighted row images of the source spikes. -/
def GradedTwoSided (k q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B →
    CorrectedLargeSieve (orderKernel k) (sexticRows B) (sexticSources B) (C * (B : ℝ) ^ (1 + ε))
      (twoSidedIndex q C ε B) (twoSidedVector k B) (twoSidedWeight q C ε B)

/-- The graded form implies the two-sided conjecture. -/
theorem twoSided_of_graded (k q : ℕ) (h : GradedTwoSided k q) : TwoSidedSpikeFree k q := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  refine ⟨C, hC, fun B hB1 b hrow hsrc => dualForm_le_of_orthogonal (hB B hB1) b ?_⟩
  intro i hi
  rcases Finset.mem_disjSum.mp hi with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact hrow a ha
  · exact hsrc a ha

/-- **Selected bound from the graded two-sided form.** On any row set `W`, the sieve sums are at most
`C B^{1+ε} + Λ_row + Λ_src` times `‖a‖²`. Here `Λ_row` is the Bessel constant of the weighted row spikes on `W`, and
`Λ_src` is that of the weighted row images of the source spikes. -/
theorem selected_of_gradedTwoSided (k q : ℕ) (h : GradedTwoSided k q) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ W : Finset (Ideal O), W ⊆ sexticRows B →
      ∀ Λr Λs : ℝ, 0 ≤ Λr → 0 ≤ Λs →
      SpikeBessel W (spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B)) (spikeVector k B)
        (gradedWeight q C ε B) Λr →
      SpikeBessel W (sourceIndex (twistCutoff q C ε B) (windowCount B) (profileCutoff C ε B))
        (fun i => rowImage (orderKernel k) (sexticSources B) (sourceSpike k i)) (sourceWeight C ε B) Λs →
      ∀ a : Ideal O → ℂ,
        ∑ z ∈ W, ‖∑ n ∈ sexticSources B, a n * orderKernel k z n‖ ^ 2 ≤
          (C * (B : ℝ) ^ (1 + ε) + (Λr + Λs)) * ∑ n ∈ sexticSources B, ‖a n‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  refine ⟨C, hC, fun B hB1 W hW Λr Λs hr hs hΛr hΛs a => ?_⟩
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact selected_of_corrected (hB B hB1) hW (spikeBessel_disjSum hΛr hΛs)
    (add_nonneg (mul_nonneg hC.le hpow) (add_nonneg hr hs)) a

/-- The source part of the selected bound, by the union bound: `Λ_src ≤ Σ_i w_i Σ_{z∈W} |E ψ_i(z)|²`, the weighted
energy of the source images on `W`. This is the quantity the numerics measure (its share on slot-selected rows). -/
theorem sourceBessel_union (k q : ℕ) {C : ℝ} (hC : 0 ≤ C) (ε : ℝ) (B : ℕ) (W : Finset (Ideal O)) :
    SpikeBessel W (sourceIndex (twistCutoff q C ε B) (windowCount B) (profileCutoff C ε B))
      (fun i => rowImage (orderKernel k) (sexticSources B) (sourceSpike k i)) (sourceWeight C ε B)
      (∑ i ∈ sourceIndex (twistCutoff q C ε B) (windowCount B) (profileCutoff C ε B),
        sourceWeight C ε B i * ∑ z ∈ W, ‖rowImage (orderKernel k) (sexticSources B) (sourceSpike k i) z‖ ^ 2) :=
  spikeBessel_union W _ _ _ fun i _ => sourceWeight_nonneg hC ε B i

/-- **Dilation.** Twisting a source vector by the symbol modulo `m` dilates its row image: the image of
`n ↦ ψ(n) χ_m(n)^k` at the row `z` is the image of `ψ` at the modulus `z·m`. The residue symbol is a
monoid-with-zero homomorphism in the modulus (`idealRowHom`), so no coprimality is needed. This is why the twisted
source spikes are the dilations `z ↦ Φ(zm)` of one series `Φ` (research journal, "The block outlier is a residue"). -/
theorem rowImage_twist_dilation (k : ℕ) (S : Finset (Ideal O)) (ψ : Ideal O → ℂ) (m z : Ideal O) :
    rowImage (orderKernel k) S (fun n => ψ n * orderKernel k m n) z = rowImage (orderKernel k) S ψ (z * m) := by
  unfold rowImage orderKernel
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, mul_pow]
  ring

/-- The energy of a twisted image on a row set is the energy of the untwisted image on the dilated row set. -/
theorem twisted_energy_eq (k : ℕ) (S W : Finset (Ideal O)) (ψ : Ideal O → ℂ) (m : Ideal O) :
    ∑ z ∈ W, ‖rowImage (orderKernel k) S (fun n => ψ n * orderKernel k m n) z‖ ^ 2 =
      ∑ z ∈ W, ‖rowImage (orderKernel k) S ψ (z * m)‖ ^ 2 :=
  Finset.sum_congr rfl fun z _ => by rw [rowImage_twist_dilation]

end ConcreteSource

end QRH.ArviKWall.BalancedSieve

#print axioms QRH.ArviKWall.BalancedSieve.rowInner_rowImage
#print axioms QRH.ArviKWall.BalancedSieve.spikeBessel_disjSum
#print axioms QRH.ArviKWall.BalancedSieve.norm_liouvilleSign
#print axioms QRH.ArviKWall.BalancedSieve.norm_sourceShape_le
#print axioms QRH.ArviKWall.BalancedSieve.sourceProfile_le_one
#print axioms QRH.ArviKWall.BalancedSieve.norm_sourceSpike_le
#print axioms QRH.ArviKWall.BalancedSieve.twoSided_of_spikeFree
#print axioms QRH.ArviKWall.BalancedSieve.twoSided_of_graded
#print axioms QRH.ArviKWall.BalancedSieve.selected_of_gradedTwoSided
#print axioms QRH.ArviKWall.BalancedSieve.sourceBessel_union
