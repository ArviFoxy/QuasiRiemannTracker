/-
SKETCH — this file contains `sorry` on purpose.

At Arvi's request (2026-10-31) the polar theorems are stated first, with `sorry`, so that their downstream use can be
explored before committing to proofs. No submission may import this package. `polarInput` is the only `sorry`. The consequences
take the polar input as a hypothesis (`PolarInput`), so they are proved outright; only a use of `polarInput` itself
brings in `sorryAx`.

What is stated (`polarInput`, the only `sorry`): for twisted Gauss-sum sums of order `q ∈ {6, 3}` over `ℤ[ω]`, with a
smooth weight supported in `[v₀, v₁] ⊂ (0, ∞)`,
* the polar asymptotic `Σ_n W(N n/X) g̃(n) conj χ_n(m)^k = ρ(m) W̃(s₀) X^{s₀} + O(X^{1/2+ε}(1 + N m)^A)`,
  with `s₀ = 1/2 + 1/q` and residues `ρ(m)` of polynomial size;
* Lindelöf on average in the twist aspect: the errors have mean square `≪ (M X)^{1+ε}` over twists of norm `≤ M`.
The cubic case is Patterson (and David–de Faveri–Dunn–Stucky, Lemmas 6.6–6.7, for the mean value). The sextic case
is Kubota's theory for the 6-fold cover (Kazhdan–Patterson), which no proof assistant has.

What is proved from it:
* `mellin_zero_bounds`: a weight with `W̃(s₀) = 0` has correlations of square-root size, pointwise and on average.
* `height_meanvalue`: for the height-twisted weight `W(t) t^{−iγ}` the polar term survives with the factor
  `W̃(s₀ − iγ)`. This is the low-height remainder, now an explicit term.
* `weighted_bessel`: with the spike strengths `w_m ≤ (B / N m)^{1/q}` of the corrected sieve, a Mellin-zero vector
  has `Σ_m w_m |⟨v, f_m⟩|² ≪ B^{1/q} M^{1 − 1/q + ε} X^{1+ε} log M`. That is the K-wall's source-spike term.

The spikes here are full range: one vector `f_m(n) = conj g̃(n) χ_n(m)^k` per twist, with no dyadic window and no
radial profile. The windowed family of `arvi_kwall/SourceSpike.lean` cannot be used with a Mellin zero: a vector
inside one window meets the profile `(2^w/N)^{j/2}` with the factor `W̃(s₀ − j/2) ≠ 0`. See `README.md`.
-/
import Submissions.arvi_kwall.SexticSpikeFree
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
namespace QRH.ArviPolarSketch
noncomputable section
open scoped BigOperators ComplexConjugate ContDiff
open OAI QRH.ArviKWall.BalancedSieve

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The Kubota pole `s₀ = 1/2 + 1/q` of normalized order-`q` Gauss sums. -/
def pole (q : ℕ) : ℂ := 1 / 2 + 1 / (q : ℂ)

/-- The full-range twisted theta correlation of a radial weight `W` at scale `X`,
`Σ_{N n ≤ v₁ X} W(N n/X) · g̃_k(n) · conj χ_n(m)^k`. It is `⟨v, f_m⟩` for `v_n = W(N n/X)` and the kind-0, level-0
source spike `f_m(n) = conj g̃_k(n) χ_n(m)^k` without window or profile. -/
def thetaCorr (k : ℕ) (W : ℝ → ℂ) (v₁ X : ℝ) (p : ℤ × ℤ) : ℂ :=
  ∑ n ∈ sexticSources ⌈v₁ * X⌉₊, W ((Ideal.absNorm n : ℝ) / X) * gaussPhase k n *
    conj (CanonicalRowCompletion.idealRowHom (twistElement p) n ^ k)

/-- The polar main term `r · W̃(s₀) · X^{s₀}`. -/
def polarMain (q : ℕ) (W : ℝ → ℂ) (X : ℝ) (r : ℂ) : ℂ := r * mellin W (pole q) * (X : ℂ) ^ (pole q)

/-- The size `1 + |N m|` of a twist. -/
def twistSize (p : ℤ × ℤ) : ℝ := 1 + |(twistNorm p : ℝ)|

theorem twistSize_pos (p : ℤ × ℤ) : 0 < twistSize p := by
  unfold twistSize; positivity

/-- **The polar input** at order `q` for a weight `W` and a loss `ε`: residues of polynomial size, the polar
asymptotic with square-root error, and Lindelöf on average in the twist aspect. -/
def PolarInput (k q : ℕ) (W : ℝ → ℂ) (v₁ ε : ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∃ ρ : ℤ × ℤ → ℂ,
    (∀ p, ‖ρ p‖ ≤ C * twistSize p ^ A) ∧
    (∀ p, ∀ X : ℝ, 1 ≤ X →
      ‖thetaCorr k W v₁ X p - polarMain q W X (ρ p)‖ ≤ C * X ^ (1 / 2 + ε) * twistSize p ^ A) ∧
    (∀ M : ℕ, ∀ X : ℝ, 1 ≤ X →
      ∑ p ∈ twistBox M, ‖thetaCorr k W v₁ X p - polarMain q W X (ρ p)‖ ^ 2 ≤ C * ((M : ℝ) * X) ^ (1 + ε))

/-- **SORRY — the sketch hypothesis.** Kubota–Patterson theory for `q = 3` (Patterson's continuation, the polar
Voronoi formula, the index-aspect mean value of David–de Faveri–Dunn–Stucky), and its unformalized analogue on the
6-fold cover for `q = 6`, for every smooth weight supported in `[v₀, v₁] ⊂ (0, ∞)`. -/
theorem polarInput (k q : ℕ) (hkq : (k = 1 ∧ q = 6) ∨ (k = 2 ∧ q = 3)) (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (v₀ v₁ : ℝ) (hv₀ : 0 < v₀) (hsupp : Function.support W ⊆ Set.Icc v₀ v₁) (ε : ℝ) (hε : 0 < ε) :
    PolarInput k q W v₁ ε := by
  sorry

/-! ### Mellin-zero weights -/

theorem polarMain_of_mellin_zero {q : ℕ} {W : ℝ → ℂ} (h : mellin W (pole q) = 0) (X : ℝ) (r : ℂ) :
    polarMain q W X r = 0 := by
  simp [polarMain, h]

/-- A weight with `W̃(s₀) = 0` has correlations of square-root size, pointwise and on average over twists. -/
theorem mellin_zero_bounds {k q : ℕ} {W : ℝ → ℂ} {v₁ ε : ℝ} (hP : PolarInput k q W v₁ ε)
    (h0 : mellin W (pole q) = 0) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      (∀ p, ∀ X : ℝ, 1 ≤ X → ‖thetaCorr k W v₁ X p‖ ≤ C * X ^ (1 / 2 + ε) * twistSize p ^ A) ∧
      (∀ M : ℕ, ∀ X : ℝ, 1 ≤ X →
        ∑ p ∈ twistBox M, ‖thetaCorr k W v₁ X p‖ ^ 2 ≤ C * ((M : ℝ) * X) ^ (1 + ε)) := by
  obtain ⟨C, A, hC, hA, ρ, -, hpt, hmv⟩ := hP
  refine ⟨C, A, hC, hA, fun p X hX => ?_, fun M X hX => ?_⟩
  · simpa [polarMain_of_mellin_zero h0] using hpt p X hX
  · simpa [polarMain_of_mellin_zero h0] using hmv M X hX

/-! ### Height twists: the low-height remainder -/

/-- The height-twisted weight `W(t) t^{−iγ}`: the radial weight of a plain block at a zero of height `γ`. -/
def heightTwist (γ : ℝ) (W : ℝ → ℂ) : ℝ → ℂ := fun t => (t : ℂ) ^ (-((γ : ℂ) * Complex.I)) * W t

theorem mellin_heightTwist (γ : ℝ) (W : ℝ → ℂ) (s : ℂ) :
    mellin (heightTwist γ W) s = mellin W (s - (γ : ℂ) * Complex.I) := by
  have h := mellin_cpow_smul W s (-((γ : ℂ) * Complex.I))
  simp only [smul_eq_mul] at h
  rw [show heightTwist γ W = fun t : ℝ => (t : ℂ) ^ (-((γ : ℂ) * Complex.I)) * W t from rfl, h, sub_eq_add_neg]

theorem norm_sq_le_two_mul (a b : ℂ) : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le (a - b) b
  rw [sub_add_cancel] at h
  have h2 : ‖a‖ ^ 2 ≤ (‖a - b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg a) h 2
  nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]

/-- **The low-height remainder.** For the height-twisted weight, the twist mean square is the error term plus the
explicit polar term `|W̃(s₀ − iγ)|² |X^{s₀}|² Σ |ρ_m|²`. A Mellin zero at `s₀` removes it only at `γ = 0`; smoothness
of `W` makes it decay in `|γ|`. -/
theorem height_meanvalue {k q : ℕ} {W : ℝ → ℂ} {v₁ ε γ : ℝ} (hP : PolarInput k q (heightTwist γ W) v₁ ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℤ × ℤ → ℂ, ∀ M : ℕ, ∀ X : ℝ, 1 ≤ X →
      ∑ p ∈ twistBox M, ‖thetaCorr k (heightTwist γ W) v₁ X p‖ ^ 2 ≤
        2 * (C * ((M : ℝ) * X) ^ (1 + ε)) +
          2 * (‖mellin W (pole q - (γ : ℂ) * Complex.I)‖ ^ 2 * ‖(X : ℂ) ^ (pole q)‖ ^ 2 *
            ∑ p ∈ twistBox M, ‖ρ p‖ ^ 2) := by
  obtain ⟨C, A, hC, hA, ρ, -, -, hmv⟩ := hP
  refine ⟨C, hC, ρ, fun M X hX => ?_⟩
  have hsplit : ∀ p ∈ twistBox M, ‖thetaCorr k (heightTwist γ W) v₁ X p‖ ^ 2 ≤
      2 * ‖thetaCorr k (heightTwist γ W) v₁ X p - polarMain q (heightTwist γ W) X (ρ p)‖ ^ 2 +
        2 * (‖mellin W (pole q - (γ : ℂ) * Complex.I)‖ ^ 2 * ‖(X : ℂ) ^ (pole q)‖ ^ 2 * ‖ρ p‖ ^ 2) := by
    intro p _
    have h := norm_sq_le_two_mul (thetaCorr k (heightTwist γ W) v₁ X p) (polarMain q (heightTwist γ W) X (ρ p))
    have hm : ‖polarMain q (heightTwist γ W) X (ρ p)‖ ^ 2 =
        ‖mellin W (pole q - (γ : ℂ) * Complex.I)‖ ^ 2 * ‖(X : ℂ) ^ (pole q)‖ ^ 2 * ‖ρ p‖ ^ 2 := by
      rw [polarMain, mellin_heightTwist, norm_mul, norm_mul]
      ring
    rw [hm] at h
    exact h
  calc ∑ p ∈ twistBox M, ‖thetaCorr k (heightTwist γ W) v₁ X p‖ ^ 2
      ≤ ∑ p ∈ twistBox M, (2 * ‖thetaCorr k (heightTwist γ W) v₁ X p -
          polarMain q (heightTwist γ W) X (ρ p)‖ ^ 2 +
          2 * (‖mellin W (pole q - (γ : ℂ) * Complex.I)‖ ^ 2 * ‖(X : ℂ) ^ (pole q)‖ ^ 2 * ‖ρ p‖ ^ 2)) :=
        Finset.sum_le_sum hsplit
    _ = 2 * ∑ p ∈ twistBox M, ‖thetaCorr k (heightTwist γ W) v₁ X p -
          polarMain q (heightTwist γ W) X (ρ p)‖ ^ 2 +
          2 * (‖mellin W (pole q - (γ : ℂ) * Complex.I)‖ ^ 2 * ‖(X : ℂ) ^ (pole q)‖ ^ 2 *
            ∑ p ∈ twistBox M, ‖ρ p‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
        have := hmv M X hX
        nlinarith [this]

end
end QRH.ArviPolarSketch
