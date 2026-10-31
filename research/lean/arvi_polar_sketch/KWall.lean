/-
SKETCH package (see `Polar.lean`). No `sorry` here: the two open inputs enter as hypotheses.

How the polar input meets the K-wall. The corrected sieve (input C of `research/frontier/PROGRAM.md`, the off-spike
recursion) is stated here in **full-range** form: the source-side corrections are the twisted thetas
`f_m(n) = conj g̃_k(n) χ_n(m)^k` over the whole source range, one per twist, weighted by the spike strengths
`C (B / N m)^{1/q}`. With a Mellin-zero radial vector `v_n = W(N n/X)`:

* `kwall_source_term`: the energy is `≤ C B^{1+γ+ε} ‖v‖² + (log₂ M + 1) C' B^{1/q} M^{1+ε−1/q} X^{1+ε}`;
* `source_exponent_le`: with the twist cutoff `M ≤ B^{1−qγ}` the second term's `B`-exponent is at most `1 + ε`
  (for `X ≤ B`), so it sits below the diagonal `B^{1+γ}` times `‖v‖² ≈ X`.

Not covered (see `README.md`): the row-side corrections (the two-sided form), the selected rows and the slots of the
actual leaf, convolution vectors, and heights.
-/
import Submissions.arvi_polar_sketch.Bessel

set_option autoImplicit false
namespace QRH.ArviPolarSketch
noncomputable section
open scoped BigOperators ComplexConjugate
open OAI QRH.ArviKWall.BalancedSieve

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The radial source vector `v_n = W(N n / X)`. -/
def radialVector (W : ℝ → ℂ) (X : ℝ) (n : Ideal O) : ℂ := W ((Ideal.absNorm n : ℝ) / X)

/-- The energy `Σ_{z ∈ R} |Σ_{n ∈ S} v_n K(z, n)|²` of a source vector. -/
def primalForm (K : Ideal O → Ideal O → ℂ) (R S : Finset (Ideal O)) (v : Ideal O → ℂ) : ℝ :=
  ∑ z ∈ R, ‖∑ n ∈ S, v n * K z n‖ ^ 2

/-- The full-range source spike `f_m(n) = conj g̃_k(n) χ_n(m)^k`. -/
def fullSpike (k : ℕ) (p : ℤ × ℤ) (n : Ideal O) : ℂ :=
  conj (gaussPhase k n) * CanonicalRowCompletion.idealRowHom (twistElement p) n ^ k

/-- The correlation of a radial vector with a full-range spike is the theta correlation. -/
theorem radial_corr (k : ℕ) (W : ℝ → ℂ) (v₁ X : ℝ) (p : ℤ × ℤ) :
    ∑ n ∈ sexticSources ⌈v₁ * X⌉₊, radialVector W X n * conj (fullSpike k p n) = thetaCorr k W v₁ X p := by
  unfold thetaCorr radialVector fullSpike
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_mul, Complex.conj_conj, map_pow]
  ring

/-- **Input C, full-range form (open; a hypothesis here).** For each `ε > 0` there is `C` such that for every scale
`B ≥ 1` and source length `L`, every source vector `v` satisfies
`Σ_{z ∈ rows(B)} |Σ_{n ∈ sources(L)} v_n χ_z(n)^k|² ≤ C B^{1+γ+ε} Σ |v_n|² + Σ_{m ∈ twistBox M} C (B/N m)^{1/q} |⟨v, f_m⟩|²`
with the twist cutoff `M = ⌊B^{1−qγ}⌋`. -/
def FullRangeCorrected (k q : ℕ) (γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ L : ℕ, ∀ v : Ideal O → ℂ,
    primalForm (orderKernel k) (sexticRows B) (sexticSources L) v ≤
      C * (B : ℝ) ^ (1 + γ + ε) * ∑ n ∈ sexticSources L, ‖v n‖ ^ 2 +
        ∑ p ∈ twistBox ⌊(B : ℝ) ^ (1 - (q : ℝ) * γ)⌋₊,
          C * ((B : ℝ) / (twistNorm p : ℝ)) ^ (1 / (q : ℝ)) *
            ‖∑ n ∈ sexticSources L, v n * conj (fullSpike k p n)‖ ^ 2

/-- **The K-wall source term for a Mellin-zero radial vector.** Input C (full-range) and the polar input give
`energy ≤ C B^{1+γ+ε} ‖v‖² + (log₂ M + 1) C C' B^{1/q} M^{1+ε'−1/q} X^{1+ε'}`, `M = ⌊B^{1−qγ}⌋`. -/
theorem kwall_source_term {k q : ℕ} {γ : ℝ} {W : ℝ → ℂ} {v₁ ε' : ℝ} (hq : 1 ≤ q) (hε' : 0 ≤ ε')
    (hC : FullRangeCorrected k q γ) (hP : PolarInput k q W v₁ ε') (h0 : mellin W (pole q) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ B : ℕ, 1 ≤ B → ∀ X : ℝ, 1 ≤ X →
      1 ≤ ⌊(B : ℝ) ^ (1 - (q : ℝ) * γ)⌋₊ →
      primalForm (orderKernel k) (sexticRows B) (sexticSources ⌈v₁ * X⌉₊) (radialVector W X) ≤
        C * (B : ℝ) ^ (1 + γ + ε) * ∑ n ∈ sexticSources ⌈v₁ * X⌉₊, ‖radialVector W X n‖ ^ 2 +
          C * (((Nat.log 2 ⌊(B : ℝ) ^ (1 - (q : ℝ) * γ)⌋₊ + 1 : ℕ) : ℝ) *
            (C' * ((B : ℝ) ^ (1 / (q : ℝ)) * 2 ^ (1 + ε') * X ^ (1 + ε') *
              (⌊(B : ℝ) ^ (1 - (q : ℝ) * γ)⌋₊ : ℝ) ^ (1 + ε' - 1 / (q : ℝ))))) := by
  obtain ⟨C, hC0, hCb⟩ := hC ε hε
  obtain ⟨C', hC'0, hB'⟩ := weighted_bessel hq hε' hP h0
  refine ⟨C, C', hC0, hC'0, fun B hB X hX hM => ?_⟩
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 := hCb B hB ⌈v₁ * X⌉₊ (radialVector W X)
  set M := ⌊(B : ℝ) ^ (1 - (q : ℝ) * γ)⌋₊
  have hcorr : ∀ p ∈ twistBox M, ∑ n ∈ sexticSources ⌈v₁ * X⌉₊, radialVector W X n * conj (fullSpike k p n) =
      thetaCorr k W v₁ X p := fun p _ => radial_corr k W v₁ X p
  have h2 : ∑ p ∈ twistBox M, C * ((B : ℝ) / (twistNorm p : ℝ)) ^ (1 / (q : ℝ)) *
        ‖∑ n ∈ sexticSources ⌈v₁ * X⌉₊, radialVector W X n * conj (fullSpike k p n)‖ ^ 2 =
      C * ∑ p ∈ twistBox M, ((B : ℝ) / (twistNorm p : ℝ)) ^ (1 / (q : ℝ)) * ‖thetaCorr k W v₁ X p‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hcorr p hp]
    ring
  have h3 := hB' (B : ℝ) X M hBpos hX hM (fun p => ((B : ℝ) / (twistNorm p : ℝ)) ^ (1 / (q : ℝ)))
    (fun p _ => le_rfl)
  calc primalForm (orderKernel k) (sexticRows B) (sexticSources ⌈v₁ * X⌉₊) (radialVector W X)
      ≤ _ := h1
    _ = C * (B : ℝ) ^ (1 + γ + ε) * ∑ n ∈ sexticSources ⌈v₁ * X⌉₊, ‖radialVector W X n‖ ^ 2 +
          C * ∑ p ∈ twistBox M, ((B : ℝ) / (twistNorm p : ℝ)) ^ (1 / (q : ℝ)) * ‖thetaCorr k W v₁ X p‖ ^ 2 := by
        rw [h2]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h3 hC0.le
        linarith

/-- **The exponent count.** With `M ≤ B^{1−qγ}`, `0 ≤ γ`, `q ≥ 1`: `B^{1/q} M^{1+ε−1/q} ≤ B^{1+ε}`. So for `X ≤ B` the
source term is at most `B^{1+ε} X^{1+ε}` (times logarithms), below the diagonal `B^{1+γ} X`. -/
theorem source_exponent_le {B M γ ε : ℝ} {q : ℕ} (hq : 1 ≤ q) (hB : 1 ≤ B) (hM0 : 0 ≤ M)
    (hM : M ≤ B ^ (1 - (q : ℝ) * γ)) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) :
    B ^ (1 / (q : ℝ)) * M ^ (1 + ε - 1 / (q : ℝ)) ≤ B ^ (1 + ε) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr0 : 0 ≤ 1 / (q : ℝ) := by positivity
  have hr1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq'
  have he : 0 ≤ 1 + ε - 1 / (q : ℝ) := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  calc B ^ (1 / (q : ℝ)) * M ^ (1 + ε - 1 / (q : ℝ))
      ≤ B ^ (1 / (q : ℝ)) * (B ^ (1 - (q : ℝ) * γ)) ^ (1 + ε - 1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0 hM he) (by positivity)
    _ = B ^ (1 / (q : ℝ) + (1 - (q : ℝ) * γ) * (1 + ε - 1 / (q : ℝ))) := by
        rw [← Real.rpow_mul hB0.le, ← Real.rpow_add hB0]
    _ ≤ B ^ (1 + ε) := by
        apply Real.rpow_le_rpow_of_exponent_le hB
        have hqγ : 0 ≤ (q : ℝ) * γ := by positivity
        nlinarith [mul_nonneg hqγ he]

end
end QRH.ArviPolarSketch

#print axioms QRH.ArviPolarSketch.kwall_source_term
#print axioms QRH.ArviPolarSketch.source_exponent_le
