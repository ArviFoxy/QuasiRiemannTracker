import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical

/-!
# The sextic (and cubic) large sieve at the balanced point, with the theta term removed

Research file (QRH, K-wall program). It states a **conjecture** with the OpenAI baseline's own definitions and
proves the reductions from it to the bounds the chain would use. Nothing here proves the conjecture.

## The objects (all from the OAI stack)

* `O = ℤ[ω]`, the Eisenstein integers (`OAI.ActualEisensteinCubic.O`).
* Rows `sexticRows B`: squarefree ideals `z` coprime to 6 (`Supported`) with `B ≤ N z ≤ 2B`.
* Sources `sexticSources L`: all ideals `n` coprime to 6 with `N n ≤ L`, each represented by its primary generator
  (`primaryGenerator`, multiplicative). This source set is closed under products, which the amplification step of
  the K-wall recursion needs. The numerics use the squarefree-norm subfamily `squarefreeSources L`. Fewer sources
  only lower `b* G b` (`dualForm_mono_sources`), so the conjecture for all sources implies it for that subfamily
  (`spikeFree_squarefree`).
* The kernel `orderKernel k z n = χ_z(n)^k`, where `χ_z(x) = (x/z)₆ = ∏_{P ∣ z} (x mod P)₆` is OAI's
  `idealRowHom x z`. Here `k = 1` is the sextic symbol and `k = 2` the cubic one (`χ₆² = χ₃`).

The large sieve inequality asks for the least `Δ` with `Σ_z |Σ_n a_n χ_z(n)^k|² ≤ Δ Σ_n |a_n|²`. By duality this is
the top eigenvalue of the row Gram `G = E E*`, so the inequality is the same as `b* G b ≤ Δ ‖b‖²` for every row vector
`b`. In this file `dualForm K R S b` is `b* G b = Σ_n |Σ_z b_z conj χ_z(n)^k|²`.

## Where the theta term comes from

At the balanced point `L = B`, de Faveri's sextic bound is `Δ ≪ B^{7/6+ε}`, and Xu–Sang show the `B^{7/6}` is
attained. Heath-Brown's cubic bound `(Q + N + (QN)^{2/3})(QN)^ε` gives `B^{4/3+ε}` there. The excess over `B` is the
theta term. Poisson summation in the sources turns each off-diagonal entry of `G` into Gauss sums at dual frequencies
`h`. A frequency `h = m j^q` (`q = 6/k`, the order of the symbol) has the same value of `χ_z(h)` as `m` for every row
coprime to `j`. So every twist `m` repeats about `(B/N m)^{1/q}` times and leaves a rank-one excess along the twisted
theta vector
  `f_m(z) = g̃(z) conj(χ_z(m)^k)`,  where `g̃(z) = g(z)/|g(z)|` is the phase of the Gauss sum of the row.
Two more kinds of vector enter the spike family.
* The plain characters `χ_z(m)^k` and `conj(χ_z(m)^k)`. The numerics (`research/rip/theta`) show a low-frequency
  outlier at the top of the spectrum, growing like `B^{1/6}`. It disappears off the span of these characters
  (`theta_offspan.py`). Its mechanism is not known, so both conjugations are included. The outlier and the theta
  excess both go away when reciprocity is broken (the RCHAR model).
* Radial profiles `(B / N z)^{j/2}`, `j < J`. The Poisson kernel depends smoothly on `N(z) N(z')`, so a dual
  frequency gives a rank-one form only after an expansion in such profiles. The numerics use `j = 1`.
The numerics mostly measure `|Eᵀ c|²`, so their vectors are the complex conjugates of these (`spikeVector`). In the
convention here the theta vector carries the excess and its conjugate does not: at `B = L = 10⁴`,
`|E* b|²/(S‖b‖²)` is about `1.12` for `b = g̃ conj χ(u)` and about `0.93` for the conjugate, against `0.96` for random
phases (`theta_offspan.py`).

## The conjecture

`SpikeFreeLargeSieve k q`: for every `ε > 0` there is `C` with the following property. For every `B ≥ 1` and every
row vector `b` orthogonal to all spike vectors with twist norm `N m ≤ C B^{1 − qε}` and profile degree `j ≤ C B^ε`
(all three kinds, every associate),
  `b* G b ≤ C B^{1+ε} ‖b‖²`.
`SexticSpikeFree` is `k = 1, q = 6`, and `CubicSpikeFree` is `k = 2, q = 3`. The cutoff `B^{1−qε}` is where the
multiplicity `(B/N m)^{1/q}` drops to `B^ε`. Twists above it carry less than `B^ε` copies each. The spike family
has `3 · #twists · J = O(C² B^{1−(q−1)ε}) = o(B)` members, so the condition on `b` leaves almost all of the row space
(`exists_orthogonal_of_card_lt`). Extra vectors in the family only weaken the conjecture. The constant `C` also
scales the cutoff, which absorbs the choice of additive
character. Another choice multiplies `g̃` by `χ_z(t)` or by `conj χ_z(t)` for a fixed `t` dividing a power of 3. On
the rows `|χ_z(t)| = 1` and `χ_z(t)^6 = 1`, so `χ_z(t) g̃ · conj χ_z(t m) = g̃ · conj χ_z(m)` and
`conj χ_z(t) g̃ · conj χ_z(t^5 m) = g̃ · conj χ_z(m)`. The family for one convention with cutoff `N(t)^5 M` therefore
contains the family for the other with cutoff `M`.

`GradedCorrectedLargeSieve k q` is a quantitative refinement. It says `G ≼ C B^{1+ε} I + Σ_i w_i f_i f_i*`, where
the weight `w = C B^{ε/q} (B / N m)^{1/q} 2^{−j}` is the multiplicity law: the dual frequencies `m j^q` up to the
dual length `B^{1+ε}`, with decaying profile weights. It implies the conjecture (`spikeFree_of_graded`).

## The K-wall from the graded conjecture: the recursion closes

`selected_of_corrected` prices a selected row set `W` by the spike Bessel constant `Λ_W`. That constant is not a
separate obstacle, because it is controlled by the selected norm itself.
* For a theta spike, `⟨b, f_{m,j}⟩ = Σ_{z∈W} c_z χ_z(m)^k` with `c_z = b_z conj g̃(z) (B/N z)^{j/2}` and
  `|c_z| ≤ |b_z|`. The plain kinds are the same with `conj χ` or `χ`. So a block of twists with `N m ≍ M_r` has
  Bessel constant at most `6 S_W(M_r)`, where `S_W(M)` is the selected norm on `W` with the twists of norm `≍ M` as
  sources, and 6 counts associates. Group the spikes into such blocks (`spikeBessel_of_blocks`).
* Amplification at slope `δ` (PR 93's rule `n(x) ≤ n(y) − δ(y − x)`) gives `S_W(M_r) ≤ (M_r/B)^δ B^{o(1)} S_W(B)`.
  This needs the sources at length `B` to contain the products of twists and slot primes, e.g. all elements of
  norm `≤ B`.
* Hence `Λ_W ≤ η S_W(B)` with `η ≲ B^{o(1)} Σ_r C B^{ε/q} (B/M_r)^{1/q} (M_r/B)^δ`. For `δ > 1/q` the top block
  `M_r ≍ C B^{1−qε}` dominates, so `η ≲ B^{−ε(qδ − 1 − 1/q) + o(1)} → 0` exactly when `δ > 1/q + 1/q²`. That is
  `7/36` for the sextic family and `4/9` for the cubic.
* `selected_of_amplified` (formal) then gives `S_W(B) ≤ C B^{1+ε} / (1 − η)`.

**[Conditional; the exponent count is not formal.]** The graded conjecture plus amplification give the selected
norm `B^{1+ε}` at the balanced point for every slope `δ > 7/36`. That includes the whole K-wall range
`1/3 ≤ δ < 1/2` of `Closure.lean`. So the K-wall reduces to a **full-family** statement about the sextic row Gram,
with no thin-set or detector hypothesis left over.

## What is proved

* `dualForm_le_of_orthogonal`: a corrected large sieve gives the plain bound off the spike span.
* `selected_of_corrected`: a corrected large sieve plus a Bessel bound `Λ_W` for the weighted spikes on a row set `W`
  give the selected bound `Σ_{z∈W} |Σ_n a_n K(z,n)|² ≤ (Δ + Λ_W) Σ |a_n|²`. This is the restriction step and the
  detector condition, in one inequality.
* `spikeBessel_union`, `spikeBessel_flat`: the union bound `Λ_W ≤ Σ_m w_m ‖f_m|_W‖²`. For flat spikes
  (`|f_m| ≤ 1`, proved for the concrete ones in `norm_spikeVector_le`) it is `≤ |W| Σ_m w_m`.
* `corrected_trivial`, `orderKernel_corrected_trivial`: every kernel bounded by 1 satisfies the corrected inequality
  with `Δ = |R||S|`, so the content of the conjecture is the size of `Δ`.
* `exists_orthogonal_of_card_lt`: fewer spike vectors than rows leaves a nonzero row vector orthogonal to all of them.
  So the condition in the conjecture is not vacuous.
* `spikeBessel_of_blocks`: the spike Bessel constant from per-block constants. `selected_of_amplified`: if every
  selected constant `S0` on `W` gives the spike Bessel constant `η S0` with `η < 1`, then `Δ / (1 − η)` is a
  selected constant. The proof iterates `S0 ↦ Δ + η S0` from the trivial constant (`isSelected_trivial`) and passes
  to the limit.
* Concrete links: `powerGauss_one` (the Gauss sum here is OAI's `sexticGauss` at frequency 1),
  `norm_orderKernel_le`, `norm_spikeVector_le`, `spikeFree_of_graded`, `selected_of_graded`,
  `selected_of_graded_flat`.

**Caveat on the union bound.** With the graded weights, `Σ_m w_m` over the whole spike family is about
`C³ B^{1−(q−3)ε}`. So the flat bound `|W| Σ_m w_m` is useful only for very small `W`. A useful selected bound needs
`Λ_W` from the near-orthogonality of the twisted thetas on `W`, and that is a large sieve for the spike vectors on
`W`. `selected_of_corrected` takes `Λ_W` as a hypothesis for that reason.
-/

namespace QRH.ArviKWall.BalancedSieve

open Finset
open scoped BigOperators ComplexConjugate

section Generic

variable {ρ σ κ : Type*}

/-- The row Gram's quadratic form `b* (K K*) b = Σ_{n∈S} |Σ_{z∈R} b_z conj K(z,n)|²`. -/
noncomputable def dualForm (K : ρ → σ → ℂ) (R : Finset ρ) (S : Finset σ) (b : ρ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖∑ z ∈ R, b z * conj (K z n)‖ ^ 2

/-- The row inner product `⟨b, f⟩_R = Σ_{z∈R} b_z conj f(z)`. -/
def rowInner (R : Finset ρ) (b f : ρ → ℂ) : ℂ := ∑ z ∈ R, b z * conj (f z)

/-- **Corrected large sieve.** The row Gram is at most `Δ · I` plus the weighted spike projections
`Σ_{k∈T} w_k f_k f_k*`. -/
def CorrectedLargeSieve (K : ρ → σ → ℂ) (R : Finset ρ) (S : Finset σ) (Δ : ℝ)
    (T : Finset κ) (f : κ → ρ → ℂ) (w : κ → ℝ) : Prop :=
  ∀ b : ρ → ℂ, dualForm K R S b ≤ Δ * ∑ z ∈ R, ‖b z‖ ^ 2 + ∑ k ∈ T, w k * ‖rowInner R b (f k)‖ ^ 2

/-- **Spike Bessel bound on a row set `W`.** The weighted spikes see at most `Λ ‖b‖²` of any `b` on `W`. -/
def SpikeBessel (W : Finset ρ) (T : Finset κ) (f : κ → ρ → ℂ) (w : κ → ℝ) (Λ : ℝ) : Prop :=
  ∀ b : ρ → ℂ, ∑ k ∈ T, w k * ‖rowInner W b (f k)‖ ^ 2 ≤ Λ * ∑ z ∈ W, ‖b z‖ ^ 2

/-- Cauchy–Schwarz for finite complex sums, squared. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * y i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * ∑ i ∈ s, ‖y i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, x i * y i‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  calc ‖∑ i ∈ s, x i * y i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ s, ‖x i‖ ^ 2) * ∑ i ∈ s, ‖y i‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖x i‖) fun i => ‖y i‖

/-- Off the spike span, a corrected large sieve is a plain one: if `b ⊥ f_k` for all `k ∈ T`, then
`b* G b ≤ Δ ‖b‖²`. -/
theorem dualForm_le_of_orthogonal {K : ρ → σ → ℂ} {R : Finset ρ} {S : Finset σ} {Δ : ℝ}
    {T : Finset κ} {f : κ → ρ → ℂ} {w : κ → ℝ} (h : CorrectedLargeSieve K R S Δ T f w)
    (b : ρ → ℂ) (hb : ∀ k ∈ T, rowInner R b (f k) = 0) :
    dualForm K R S b ≤ Δ * ∑ z ∈ R, ‖b z‖ ^ 2 := by
  have h0 : ∑ k ∈ T, w k * ‖rowInner R b (f k)‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [hb k hk, norm_zero]; ring
  have := h b
  rw [h0, add_zero] at this
  exact this

/-- Fewer sources give a smaller row Gram form. -/
theorem dualForm_mono_sources (K : ρ → σ → ℂ) (R : Finset ρ) {S' S : Finset σ} (h : S' ⊆ S) (b : ρ → ℂ) :
    dualForm K R S' b ≤ dualForm K R S b :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- **Selected bound from a corrected large sieve.** If the row Gram is at most `Δ I + Σ w_k f_k f_k*` and the
weighted spikes have Bessel constant `Λ` on `W ⊆ R`, then the sieve sums on `W` obey
`Σ_{z∈W} |Σ_n a_n K(z,n)|² ≤ (Δ + Λ) Σ_n |a_n|²`. -/
theorem selected_of_corrected {K : ρ → σ → ℂ} {R : Finset ρ} {S : Finset σ} {Δ Λ : ℝ}
    {T : Finset κ} {f : κ → ρ → ℂ} {w : κ → ℝ} (h : CorrectedLargeSieve K R S Δ T f w)
    {W : Finset ρ} (hWR : W ⊆ R) (hΛ : SpikeBessel W T f w Λ) (hΔΛ : 0 ≤ Δ + Λ) (a : σ → ℂ) :
    ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 ≤ (Δ + Λ) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ρ → ℂ, D = fun z => ∑ n ∈ S, a n * K z n := ⟨_, rfl⟩
  have hDz : ∀ z, ∑ n ∈ S, a n * K z n = D z := fun z => by rw [hD]
  simp only [hDz]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ z ∈ W, ‖D z‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ n ∈ S, ‖a n‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hA]
  have hX0 : 0 ≤ X := by rw [hX]; exact Finset.sum_nonneg fun z _ => by positivity
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun n _ => by positivity
  -- the test vector: `D` on `W`, zero elsewhere
  obtain ⟨b, hb⟩ : ∃ b : ρ → ℂ, b = fun z => if z ∈ W then D z else 0 := ⟨_, rfl⟩
  have hbz : ∀ z, b z = if z ∈ W then D z else 0 := fun z => by rw [hb]
  have hres : ∀ g : ρ → ℂ, ∑ z ∈ R, b z * g z = ∑ z ∈ W, D z * g z := by
    intro g
    have hsub : ∑ z ∈ W, b z * g z = ∑ z ∈ R, b z * g z :=
      Finset.sum_subset hWR fun z _ hz => by simp [hbz, hz]
    rw [← hsub]
    exact Finset.sum_congr rfl fun z hz => by simp [hbz, hz]
  have hbn : ∑ z ∈ R, ‖b z‖ ^ 2 = X := by
    have hsub : ∑ z ∈ W, ‖b z‖ ^ 2 = ∑ z ∈ R, ‖b z‖ ^ 2 :=
      Finset.sum_subset hWR fun z _ hz => by simp [hbz, hz]
    rw [← hsub, hX]
    exact Finset.sum_congr rfl fun z hz => by simp [hbz, hz]
  -- the corrected inequality at `b`, with the spike part bounded on `W`
  have hdual : dualForm K R S b = ∑ n ∈ S, ‖∑ z ∈ W, D z * conj (K z n)‖ ^ 2 := by
    unfold dualForm
    exact Finset.sum_congr rfl fun n _ => by rw [hres fun z => conj (K z n)]
  have hspike : ∀ k, rowInner R b (f k) = rowInner W D (f k) := fun k => by
    unfold rowInner
    exact hres fun z => conj (f k z)
  have hc : ∑ n ∈ S, ‖∑ z ∈ W, D z * conj (K z n)‖ ^ 2 ≤ (Δ + Λ) * X := by
    have h1 := h b
    rw [hdual, hbn] at h1
    simp only [hspike] at h1
    have h2 := hΛ D
    rw [← hX] at h2
    linarith
  -- duality: `X = Σ_n a_n conj(Σ_{z∈W} D_z conj K(z,n))`
  have hswap : ∑ n ∈ S, a n * conj (∑ z ∈ W, D z * conj (K z n)) =
      ∑ z ∈ W, conj (D z) * ∑ n ∈ S, a n * K z n := by
    calc ∑ n ∈ S, a n * conj (∑ z ∈ W, D z * conj (K z n))
        = ∑ n ∈ S, ∑ z ∈ W, conj (D z) * (a n * K z n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [map_mul, Complex.conj_conj]
          ring
      _ = ∑ z ∈ W, ∑ n ∈ S, conj (D z) * (a n * K z n) := Finset.sum_comm
      _ = ∑ z ∈ W, conj (D z) * ∑ n ∈ S, a n * K z n := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
  have hkey : (X : ℂ) = ∑ n ∈ S, a n * conj (∑ z ∈ W, D z * conj (K z n)) := by
    rw [hswap, hX]
    push_cast
    exact Finset.sum_congr rfl fun z _ => by rw [hDz, Complex.conj_mul']
  have hcs : ‖∑ n ∈ S, a n * conj (∑ z ∈ W, D z * conj (K z n))‖ ^ 2 ≤
      A * ∑ n ∈ S, ‖∑ z ∈ W, D z * conj (K z n)‖ ^ 2 := by
    have := norm_sum_mul_sq_le S a fun n => conj (∑ z ∈ W, D z * conj (K z n))
    simp only [Complex.norm_conj] at this
    rw [hA]
    exact this
  have hXn : ‖(X : ℂ)‖ = X := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
  have hXsq : X * X ≤ ((Δ + Λ) * A) * X := by
    calc X * X = ‖(X : ℂ)‖ ^ 2 := by rw [hXn]; ring
      _ ≤ A * ∑ n ∈ S, ‖∑ z ∈ W, D z * conj (K z n)‖ ^ 2 := by rw [hkey]; exact hcs
      _ ≤ A * ((Δ + Λ) * X) := mul_le_mul_of_nonneg_left hc hA0
      _ = ((Δ + Λ) * A) * X := by ring
  rcases hX0.lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_right hXsq hpos
  · rw [← hzero]
    exact mul_nonneg hΔΛ hA0

/-- The union bound for the spike part: `Λ_W = Σ_k w_k Σ_{z∈W} |f_k(z)|²`. -/
theorem spikeBessel_union (W : Finset ρ) (T : Finset κ) (f : κ → ρ → ℂ) (w : κ → ℝ)
    (hw : ∀ k ∈ T, 0 ≤ w k) :
    SpikeBessel W T f w (∑ k ∈ T, w k * ∑ z ∈ W, ‖f k z‖ ^ 2) := by
  intro b
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hcs : ‖rowInner W b (f k)‖ ^ 2 ≤ (∑ z ∈ W, ‖b z‖ ^ 2) * ∑ z ∈ W, ‖f k z‖ ^ 2 := by
    have := norm_sum_mul_sq_le W b fun z => conj (f k z)
    simp only [Complex.norm_conj] at this
    exact this
  calc w k * ‖rowInner W b (f k)‖ ^ 2
      ≤ w k * ((∑ z ∈ W, ‖b z‖ ^ 2) * ∑ z ∈ W, ‖f k z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (hw k hk)
    _ = w k * (∑ z ∈ W, ‖f k z‖ ^ 2) * ∑ z ∈ W, ‖b z‖ ^ 2 := by ring

/-- Flat spikes (`|f_k| ≤ 1` on `W`): `Λ_W ≤ |W| Σ_k w_k`. -/
theorem spikeBessel_flat (W : Finset ρ) (T : Finset κ) (f : κ → ρ → ℂ) (w : κ → ℝ)
    (hw : ∀ k ∈ T, 0 ≤ w k) (hf : ∀ k ∈ T, ∀ z ∈ W, ‖f k z‖ ≤ 1) :
    SpikeBessel W T f w ((W.card : ℝ) * ∑ k ∈ T, w k) := by
  intro b
  refine (spikeBessel_union W T f w hw b).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun z _ => by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hW : ∑ z ∈ W, ‖f k z‖ ^ 2 ≤ W.card := by
    calc ∑ z ∈ W, ‖f k z‖ ^ 2 ≤ ∑ z ∈ W, (1 : ℝ) :=
          Finset.sum_le_sum fun z hz =>
            pow_le_one₀ (norm_nonneg _) (hf k hk z hz)
      _ = W.card := by simp
  calc w k * ∑ z ∈ W, ‖f k z‖ ^ 2 ≤ w k * W.card := mul_le_mul_of_nonneg_left hW (hw k hk)
    _ = W.card * w k := by ring

/-- **Non-vacuity of the conclusion.** A kernel bounded by 1 satisfies the corrected inequality with the trivial
constant `Δ = |R| |S|` (any nonnegative weights). -/
theorem corrected_trivial (K : ρ → σ → ℂ) (hK : ∀ z n, ‖K z n‖ ≤ 1) (R : Finset ρ) (S : Finset σ)
    (T : Finset κ) (f : κ → ρ → ℂ) (w : κ → ℝ) (hw : ∀ k ∈ T, 0 ≤ w k) :
    CorrectedLargeSieve K R S ((R.card : ℝ) * S.card) T f w := by
  intro b
  have hspike : 0 ≤ ∑ k ∈ T, w k * ‖rowInner R b (f k)‖ ^ 2 :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (by positivity)
  have hn : ∀ n ∈ S, ‖∑ z ∈ R, b z * conj (K z n)‖ ^ 2 ≤ (∑ z ∈ R, ‖b z‖ ^ 2) * R.card := by
    intro n _
    refine (norm_sum_mul_sq_le R b fun z => conj (K z n)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun z _ => by positivity)
    calc ∑ z ∈ R, ‖conj (K z n)‖ ^ 2 ≤ ∑ z ∈ R, (1 : ℝ) :=
          Finset.sum_le_sum fun z _ => by
            rw [Complex.norm_conj]
            exact pow_le_one₀ (norm_nonneg _) (hK z n)
      _ = R.card := by simp
  have hsum : dualForm K R S b ≤ (R.card : ℝ) * S.card * ∑ z ∈ R, ‖b z‖ ^ 2 := by
    calc dualForm K R S b ≤ ∑ n ∈ S, (∑ z ∈ R, ‖b z‖ ^ 2) * R.card := Finset.sum_le_sum hn
      _ = (R.card : ℝ) * S.card * ∑ z ∈ R, ‖b z‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  linarith

/-- **Non-vacuity of the hypothesis.** With fewer spike vectors than rows, some row vector that is not zero on `R`
is orthogonal to all of them. -/
theorem exists_orthogonal_of_card_lt (R : Finset ρ) (T : Finset κ) (f : κ → ρ → ℂ)
    (hcard : T.card < R.card) :
    ∃ b : ρ → ℂ, (∃ z ∈ R, b z ≠ 0) ∧ ∀ k ∈ T, rowInner R b (f k) = 0 := by
  classical
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (R → ℂ) →ₗ[ℂ] (T → ℂ),
      ∀ c k, Φ c k = ∑ z : R, c z * conj (f k z) :=
    ⟨{ toFun := fun c k => ∑ z : R, c z * conj (f k z)
       map_add' := by
         intro c d
         funext k
         simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
       map_smul' := by
         intro t c
         funext k
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] },
      fun _ _ => rfl⟩
  have hdim : Module.finrank ℂ (T → ℂ) < Module.finrank ℂ (R → ℂ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hcard
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt hdim)
  refine ⟨fun z => if h : z ∈ R then c ⟨z, h⟩ else 0, ?_, ?_⟩
  · by_contra hall
    apply hc0
    funext ⟨z, hz⟩
    by_contra hne
    exact hall ⟨z, hz, by simpa [hz] using hne⟩
  · intro k hk
    have hk' := congrFun (LinearMap.mem_ker.mp hc) ⟨k, hk⟩
    rw [hΦ, Pi.zero_apply] at hk'
    unfold rowInner
    rw [← Finset.sum_coe_sort R]
    simpa using hk'

/-- **Blockwise spike Bessel bound.** Assign each spike `k` to a block `blk k ∈ I` with `w_k ≤ ω_r` on block `r`. If
block `r` has Bessel constant `s_r` on `W`, the weighted spikes have Bessel constant `Σ_r ω_r s_r`. -/
theorem spikeBessel_of_blocks {ι : Type*} [DecidableEq ι] (W : Finset ρ) (T : Finset κ) (f : κ → ρ → ℂ)
    (w : κ → ℝ) (I : Finset ι) (blk : κ → ι) (hblk : ∀ k ∈ T, blk k ∈ I) (ω s : ι → ℝ)
    (hwω : ∀ k ∈ T, w k ≤ ω (blk k)) (hω0 : ∀ r ∈ I, 0 ≤ ω r)
    (hs : ∀ r ∈ I, ∀ b : ρ → ℂ,
      ∑ k ∈ T.filter (fun k => blk k = r), ‖rowInner W b (f k)‖ ^ 2 ≤ s r * ∑ z ∈ W, ‖b z‖ ^ 2) :
    SpikeBessel W T f w (∑ r ∈ I, ω r * s r) := by
  intro b
  have h1 : ∑ k ∈ T, w k * ‖rowInner W b (f k)‖ ^ 2 =
      ∑ r ∈ I, ∑ k ∈ T.filter (fun k => blk k = r), w k * ‖rowInner W b (f k)‖ ^ 2 :=
    (Finset.sum_fiberwise_of_maps_to hblk _).symm
  rw [h1, Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  have h2 : ∑ k ∈ T.filter (fun k => blk k = r), w k * ‖rowInner W b (f k)‖ ^ 2 ≤
      ∑ k ∈ T.filter (fun k => blk k = r), ω r * ‖rowInner W b (f k)‖ ^ 2 := by
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hkT, hkr⟩ := Finset.mem_filter.mp hk
    have hw := hwω k hkT
    rw [hkr] at hw
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  calc ∑ k ∈ T.filter (fun k => blk k = r), w k * ‖rowInner W b (f k)‖ ^ 2
      ≤ ω r * ∑ k ∈ T.filter (fun k => blk k = r), ‖rowInner W b (f k)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact h2
    _ ≤ ω r * (s r * ∑ z ∈ W, ‖b z‖ ^ 2) := mul_le_mul_of_nonneg_left (hs r hr b) (hω0 r hr)
    _ = ω r * s r * ∑ z ∈ W, ‖b z‖ ^ 2 := by ring

/-- `S0` is a selected constant for the kernel `K` on the rows `W` and the sources `S`. -/
def IsSelected (K : ρ → σ → ℂ) (W : Finset ρ) (S : Finset σ) (S0 : ℝ) : Prop :=
  ∀ a : σ → ℂ, ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 ≤ S0 * ∑ n ∈ S, ‖a n‖ ^ 2

theorem IsSelected.mono {K : ρ → σ → ℂ} {W : Finset ρ} {S : Finset σ} {S0 S1 : ℝ}
    (h : IsSelected K W S S0) (h01 : S0 ≤ S1) : IsSelected K W S S1 := fun a =>
  (h a).trans (mul_le_mul_of_nonneg_right h01 (Finset.sum_nonneg fun n _ => by positivity))

/-- A kernel bounded by 1 has the trivial selected constant `|W| |S|`. -/
theorem isSelected_trivial (K : ρ → σ → ℂ) (hK : ∀ z n, ‖K z n‖ ≤ 1) (W : Finset ρ) (S : Finset σ) :
    IsSelected K W S ((W.card : ℝ) * S.card) := by
  intro a
  have hz : ∀ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 ≤ (∑ n ∈ S, ‖a n‖ ^ 2) * S.card := by
    intro z _
    refine (norm_sum_mul_sq_le S a fun n => K z n).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun n _ => by positivity)
    calc ∑ n ∈ S, ‖K z n‖ ^ 2 ≤ ∑ n ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => pow_le_one₀ (norm_nonneg _) (hK z n)
      _ = S.card := by simp
  calc ∑ z ∈ W, ‖∑ n ∈ S, a n * K z n‖ ^ 2 ≤ ∑ z ∈ W, (∑ n ∈ S, ‖a n‖ ^ 2) * S.card :=
        Finset.sum_le_sum hz
    _ = (W.card : ℝ) * S.card * ∑ n ∈ S, ‖a n‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The recursion closes.** Suppose the row Gram obeys a corrected large sieve with constant `Δ`, and the spike part
on `W` is controlled by the selected norm itself: every selected constant `S0` gives the spike Bessel constant
`η S0`, with `η < 1`. This is what amplification provides, because each block of twists is a selected sieve on `W` at
a shorter source length. Then `Δ / (1 − η)` is a selected constant on `W`. -/
theorem selected_of_amplified {K : ρ → σ → ℂ} {R : Finset ρ} {S : Finset σ} {Δ η S1 : ℝ}
    {T : Finset κ} {f : κ → ρ → ℂ} {w : κ → ℝ} (h : CorrectedLargeSieve K R S Δ T f w)
    {W : Finset ρ} (hWR : W ⊆ R) (hΔ : 0 ≤ Δ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hamp : ∀ S0 : ℝ, 0 ≤ S0 → IsSelected K W S S0 → SpikeBessel W T f w (η * S0))
    (hS1 : 0 ≤ S1) (hinit : IsSelected K W S S1) :
    IsSelected K W S (Δ / (1 - η)) := by
  have hpos : 0 < 1 - η := by linarith
  have hD : 0 ≤ Δ / (1 - η) := div_nonneg hΔ hpos.le
  -- one round: `S0 ↦ Δ + η S0`
  have step : ∀ S0 : ℝ, 0 ≤ S0 → IsSelected K W S S0 → IsSelected K W S (Δ + η * S0) := by
    intro S0 hS0 hsel a
    exact selected_of_corrected h hWR (hamp S0 hS0 hsel) (by positivity) a
  -- after `n` rounds: `Δ/(1−η) + η^n S1`
  have iter : ∀ n : ℕ, IsSelected K W S (Δ / (1 - η) + η ^ n * S1) := by
    intro n
    induction n with
    | zero => exact hinit.mono (by rw [pow_zero, one_mul]; linarith)
    | succ n ih =>
      have hX : 0 ≤ Δ / (1 - η) + η ^ n * S1 := by positivity
      have heq : Δ + η * (Δ / (1 - η) + η ^ n * S1) = Δ / (1 - η) + η ^ (n + 1) * S1 := by
        field_simp
        ring
      exact heq ▸ step _ hX ih
  intro a
  have hlim : Filter.Tendsto (fun n : ℕ => (Δ / (1 - η) + η ^ n * S1) * ∑ n ∈ S, ‖a n‖ ^ 2) Filter.atTop
      (nhds ((Δ / (1 - η) + 0 * S1) * ∑ n ∈ S, ‖a n‖ ^ 2)) :=
    ((tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hη0 hη1).mul tendsto_const_nhds)).mul
      tendsto_const_nhds)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => iter n a

end Generic

section Concrete

open OAI
open scoped Classical

local notation "O" => OAI.ActualEisensteinCubic.O

/-- Rows at scale `B`: squarefree ideals coprime to 6 with `B ≤ N z ≤ 2B`. -/
noncomputable def sexticRows (B : ℕ) : Finset (Ideal O) :=
  (CanonicalQuadraticSieve.fullRange (2 * B : ℝ)).filter fun z => B ≤ Ideal.absNorm z ∧ Squarefree z

/-- Sources of length `L`: all ideals coprime to 6 with norm `≤ L`. -/
noncomputable def sexticSources (L : ℕ) : Finset (Ideal O) :=
  CanonicalQuadraticSieve.fullRange (L : ℝ)

/-- The squarefree-norm sources of the numerics (`research/rip/theta`): products of distinct split primes, no two
conjugate. -/
noncomputable def squarefreeSources (L : ℕ) : Finset (Ideal O) :=
  (sexticSources L).filter fun n => Squarefree (Ideal.absNorm n)

/-- The kernel `χ_z(n)^k`: the sextic symbol (`k = 1`) or the cubic symbol (`k = 2`) of the primary generator of the
source `n` modulo the row `z`. -/
noncomputable def orderKernel (k : ℕ) (z n : Ideal O) : ℂ :=
  CanonicalRowCompletion.idealRowHom (CompletedGauss.primaryGenerator n) z ^ k

/-- The twist `m = x + y ω` with coordinates `p = (x, y)`. -/
noncomputable def twistElement (p : ℤ × ℤ) : O :=
  (p.1 : O) + (p.2 : O) * ActualEisensteinCubic.omega

/-- `N(x + yω) = x² − xy + y²`. -/
def twistNorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2

/-- All nonzero twists of norm `≤ M`, every associate included. -/
def twistBox (M : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).filter fun p => p ≠ 0 ∧ twistNorm p ≤ M

/-- Spike indices: a kind (`0` = twisted theta, `1` = plain character, `2` = its conjugate), a twist of norm `≤ M`
and a profile degree `j < J`. -/
def spikeIndex (M J : ℕ) : Finset (Fin 3 × (ℤ × ℤ) × ℕ) :=
  Finset.univ ×ˢ (twistBox M ×ˢ Finset.range J)

/-- The order-`k` Gauss sum `Σ_{d mod s} χ_s(d)^k e(d/s)` with OAI's additive character `quotientTrace`. -/
noncomputable def powerGauss (k : ℕ) (s : O) (hs : s ≠ 0) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s},
    CanonicalRowCompletion.idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s}) ^ k *
      CubicEisenstein.quotientTrace s hs d

/-- At `k = 1` this is OAI's `sexticGauss` at frequency 1. -/
theorem powerGauss_one (s : O) (hs : s ≠ 0) :
    powerGauss 1 s hs = SevenEighths.ProbePhysical.sexticGauss s hs 1 := by
  simp only [powerGauss, SevenEighths.ProbePhysical.sexticGauss, pow_one, map_one, one_mul]

/-- The phase `g / |g|` (zero at `g = 0`). -/
noncomputable def phase (g : ℂ) : ℂ := g / (‖g‖ : ℂ)

theorem norm_phase_le (g : ℂ) : ‖phase g‖ ≤ 1 := by
  rw [phase, norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

/-- The phase of the row's Gauss sum. For squarefree `z` coprime to 6, `|g(z)| = √N(z)`, so this is the normalized
Gauss sum `g̃(z)`. The phase form is bounded by 1 by construction. -/
noncomputable def gaussPhase (k : ℕ) (z : Ideal O) : ℂ :=
  if h : CompletedGauss.primaryGenerator z ≠ 0 then
    phase (powerGauss k (CompletedGauss.primaryGenerator z) h)
  else 0

theorem norm_gaussPhase_le (k : ℕ) (z : Ideal O) : ‖gaussPhase k z‖ ≤ 1 := by
  unfold gaussPhase
  split_ifs
  · exact norm_phase_le _
  · simp

/-- The radial profile `√(B / N z)`, capped at 1. On the rows it lies in `[1/√2, 1]`. -/
noncomputable def rowProfile (B : ℕ) (z : Ideal O) : ℝ := Real.sqrt (min 1 ((B : ℝ) / (Ideal.absNorm z : ℝ)))

theorem rowProfile_nonneg (B : ℕ) (z : Ideal O) : 0 ≤ rowProfile B z := Real.sqrt_nonneg _

theorem rowProfile_le_one (B : ℕ) (z : Ideal O) : rowProfile B z ≤ 1 := by
  unfold rowProfile
  calc Real.sqrt (min 1 ((B : ℝ) / (Ideal.absNorm z : ℝ))) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt (min_le_left _ _)
    _ = 1 := Real.sqrt_one

/-- The shape of a spike, in the convention of `dualForm` (`b* E E* b`): the twisted theta `g̃(z) conj(χ_z(m)^k)`
(kind `0`), the plain character `χ_z(m)^k` (kind `1`) or its conjugate (kind `2`). Poisson summation writes the
off-diagonal entry `Σ_n χ_z(n)^k conj χ_{z'}(n)^k` through
`τ(χ_z conj χ_{z'}, h) = conj χ_z(h) χ_{z'}(h) τ(χ_z) conj τ(χ_{z'})`, up to the reciprocity sign and units. That is
`f_h(z) conj f_h(z')` with `f_h = g̃ · conj χ(h)`. The numerics (`research/rip/theta`) mostly measure `|Eᵀ c|²`,
whose spike `c = conj g̃ · χ(h)` is the complex conjugate. -/
noncomputable def spikeShape (k : ℕ) (c : Fin 3) (m : ℤ × ℤ) (z : Ideal O) : ℂ :=
  if c = 0 then gaussPhase k z * conj (CanonicalRowCompletion.idealRowHom (twistElement m) z ^ k)
  else if c = 1 then CanonicalRowCompletion.idealRowHom (twistElement m) z ^ k
  else conj (CanonicalRowCompletion.idealRowHom (twistElement m) z ^ k)

/-- The spike vector with index `(c, m, j)`: the shape times the profile `(B / N z)^{j/2}`. -/
noncomputable def spikeVector (k B : ℕ) (i : Fin 3 × (ℤ × ℤ) × ℕ) (z : Ideal O) : ℂ :=
  spikeShape k i.1 i.2.1 z * (rowProfile B z : ℂ) ^ i.2.2

theorem norm_orderKernel_le (k : ℕ) (z n : Ideal O) : ‖orderKernel k z n‖ ≤ 1 := by
  unfold orderKernel
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem norm_spikeShape_le (k : ℕ) (c : Fin 3) (m : ℤ × ℤ) (z : Ideal O) : ‖spikeShape k c m z‖ ≤ 1 := by
  have hχ : ‖CanonicalRowCompletion.idealRowHom (twistElement m) z ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (CanonicalRowCompletion.idealRowHom_norm _ _)
  unfold spikeShape
  split_ifs
  · rw [norm_mul, Complex.norm_conj]
    calc _ ≤ 1 * 1 := mul_le_mul (norm_gaussPhase_le k z) hχ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · exact hχ
  · rw [Complex.norm_conj]
    exact hχ

theorem norm_spikeVector_le (k B : ℕ) (i : Fin 3 × (ℤ × ℤ) × ℕ) (z : Ideal O) :
    ‖spikeVector k B i z‖ ≤ 1 := by
  unfold spikeVector
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rowProfile_nonneg B z)]
  calc _ ≤ 1 * 1 := mul_le_mul (norm_spikeShape_le k i.1 i.2.1 z)
        (pow_le_one₀ (rowProfile_nonneg B z) (rowProfile_le_one B z)) (pow_nonneg (rowProfile_nonneg B z) _)
        zero_le_one
    _ = 1 := one_mul 1

/-- The twist cutoff `⌊C B^{1 − qε}⌋`. -/
noncomputable def twistCutoff (q : ℕ) (C ε : ℝ) (B : ℕ) : ℕ := ⌊C * (B : ℝ) ^ (1 - (q : ℝ) * ε)⌋₊

/-- The profile cutoff `⌊C B^ε⌋ + 1`. The flat profile `j = 0` is always included. -/
noncomputable def profileCutoff (C ε : ℝ) (B : ℕ) : ℕ := ⌊C * (B : ℝ) ^ ε⌋₊ + 1

/-- **Conjecture: the large sieve at the balanced point `L = B` with the theta term removed.** For every `ε > 0` there
is `C > 0` such that for every `B ≥ 1` and every row vector `b` orthogonal to the spike vectors with twist norm
`≤ C B^{1−qε}` and profile degree `≤ C B^ε`, `Σ_n |Σ_z b_z conj χ_z(n)^k|² ≤ C B^{1+ε} Σ_z |b_z|²`. -/
def SpikeFreeLargeSieve (k q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ b : Ideal O → ℂ,
    (∀ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B),
        rowInner (sexticRows B) b (spikeVector k B i) = 0) →
      dualForm (orderKernel k) (sexticRows B) (sexticSources B) b ≤
        C * (B : ℝ) ^ (1 + ε) * ∑ z ∈ sexticRows B, ‖b z‖ ^ 2

/-- The sextic case: `χ_z = (·/z)₆`, theta multiplicity from sixth powers. -/
def SexticSpikeFree : Prop := SpikeFreeLargeSieve 1 6

/-- The cubic case: `χ_z² = (·/z)₃`, theta multiplicity from cubes. -/
def CubicSpikeFree : Prop := SpikeFreeLargeSieve 2 3

/-- The conjecture for all sources gives the same bound on the squarefree-norm subfamily of the numerics. -/
theorem spikeFree_squarefree {k q : ℕ} (h : SpikeFreeLargeSieve k q) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ b : Ideal O → ℂ,
      (∀ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B),
          rowInner (sexticRows B) b (spikeVector k B i) = 0) →
        dualForm (orderKernel k) (sexticRows B) (squarefreeSources B) b ≤
          C * (B : ℝ) ^ (1 + ε) * ∑ z ∈ sexticRows B, ‖b z‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  exact ⟨C, hC, fun B hB1 b hb =>
    (dualForm_mono_sources _ _ (Finset.filter_subset _ _) b).trans (hB B hB1 b hb)⟩

/-- The multiplicity weights `w = C B^{ε/q} (B / N m)^{1/q} 2^{−j}`: the number of dual frequencies `m j^q` up to the
dual length `B^{1+ε}`, with geometrically decaying weights in the profile degree `j` (below the cutoff the Poisson
kernel is analytic in the profile variable). -/
noncomputable def gradedWeight (q : ℕ) (C ε : ℝ) (B : ℕ) (i : Fin 3 × (ℤ × ℤ) × ℕ) : ℝ :=
  C * (B : ℝ) ^ (ε / q) * ((B : ℝ) / max 1 (twistNorm i.2.1 : ℝ)) ^ ((1 : ℝ) / q) * (1 / 2) ^ i.2.2

theorem gradedWeight_nonneg (q : ℕ) {C : ℝ} (hC : 0 ≤ C) (ε : ℝ) (B : ℕ) (i : Fin 3 × (ℤ × ℤ) × ℕ) :
    0 ≤ gradedWeight q C ε B i := by
  unfold gradedWeight
  have hm : (0 : ℝ) < max 1 (twistNorm i.2.1 : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : (0 : ℝ) ≤ (B : ℝ) ^ (ε / q) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : (0 : ℝ) ≤ ((B : ℝ) / max 1 (twistNorm i.2.1 : ℝ)) ^ ((1 : ℝ) / q) :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hm.le) _
  exact mul_nonneg (mul_nonneg (mul_nonneg hC h1) h2) (by positivity)

/-- **Conjecture (graded refinement).** The row Gram is at most `C B^{1+ε} I` plus the spike projections with the
multiplicity weights. -/
def GradedCorrectedLargeSieve (k q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B →
    CorrectedLargeSieve (orderKernel k) (sexticRows B) (sexticSources B) (C * (B : ℝ) ^ (1 + ε))
      (spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B)) (spikeVector k B) (gradedWeight q C ε B)

/-- The graded refinement implies the spike-free conjecture. -/
theorem spikeFree_of_graded (k q : ℕ) (h : GradedCorrectedLargeSieve k q) : SpikeFreeLargeSieve k q := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  exact ⟨C, hC, fun B hB1 b hb => dualForm_le_of_orthogonal (hB B hB1) b hb⟩

/-- The graded refinement gives the selected bound on any row set `W`, priced by the spike Bessel constant `Λ_W`. -/
theorem selected_of_graded (k q : ℕ) (h : GradedCorrectedLargeSieve k q) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ W : Finset (Ideal O), W ⊆ sexticRows B →
      ∀ Λ : ℝ, 0 ≤ Λ →
      SpikeBessel W (spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B)) (spikeVector k B)
        (gradedWeight q C ε B) Λ →
      ∀ a : Ideal O → ℂ,
        ∑ z ∈ W, ‖∑ n ∈ sexticSources B, a n * orderKernel k z n‖ ^ 2 ≤
          (C * (B : ℝ) ^ (1 + ε) + Λ) * ∑ n ∈ sexticSources B, ‖a n‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hB⟩ := h ε hε
  refine ⟨C, hC, fun B hB1 W hW Λ hΛ0 hΛ a => ?_⟩
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact selected_of_corrected (hB B hB1) hW hΛ (add_nonneg (mul_nonneg hC.le hpow) hΛ0) a

/-- With the union bound for the flat spikes: `Λ_W = |W| Σ_m w_m`. -/
theorem selected_of_graded_flat (k q : ℕ) (h : GradedCorrectedLargeSieve k q) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 1 ≤ B → ∀ W : Finset (Ideal O), W ⊆ sexticRows B →
      ∀ a : Ideal O → ℂ,
        ∑ z ∈ W, ‖∑ n ∈ sexticSources B, a n * orderKernel k z n‖ ^ 2 ≤
          (C * (B : ℝ) ^ (1 + ε) +
            (W.card : ℝ) * ∑ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B), gradedWeight q C ε B i) *
            ∑ n ∈ sexticSources B, ‖a n‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsel⟩ := selected_of_graded k q h ε hε
  refine ⟨C, hC, fun B hB1 W hW a => ?_⟩
  have hw : ∀ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B), 0 ≤ gradedWeight q C ε B i :=
    fun i _ => gradedWeight_nonneg q hC.le ε B i
  have hΛ0 : (0 : ℝ) ≤ (W.card : ℝ) * ∑ i ∈ spikeIndex (twistCutoff q C ε B) (profileCutoff C ε B), gradedWeight q C ε B i :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg hw)
  exact hsel B hB1 W hW _ hΛ0
    (spikeBessel_flat W _ (spikeVector k B) _ hw fun i _ z _ => norm_spikeVector_le k B i z) a

/-- The concrete kernels satisfy the corrected inequality with the trivial constant, so the conjecture's content is
the size `C B^{1+ε}` of the diagonal constant. -/
theorem orderKernel_corrected_trivial (k B L M J : ℕ) (w : Fin 3 × (ℤ × ℤ) × ℕ → ℝ)
    (hw : ∀ i ∈ spikeIndex M J, 0 ≤ w i) :
    CorrectedLargeSieve (orderKernel k) (sexticRows B) (sexticSources L)
      (((sexticRows B).card : ℝ) * (sexticSources L).card) (spikeIndex M J) (spikeVector k B) w :=
  corrected_trivial _ (norm_orderKernel_le k) _ _ _ _ _ hw

end Concrete

end QRH.ArviKWall.BalancedSieve

#print axioms QRH.ArviKWall.BalancedSieve.selected_of_corrected
#print axioms QRH.ArviKWall.BalancedSieve.spikeBessel_of_blocks
#print axioms QRH.ArviKWall.BalancedSieve.isSelected_trivial
#print axioms QRH.ArviKWall.BalancedSieve.selected_of_amplified
#print axioms QRH.ArviKWall.BalancedSieve.exists_orthogonal_of_card_lt
#print axioms QRH.ArviKWall.BalancedSieve.spikeFree_of_graded
#print axioms QRH.ArviKWall.BalancedSieve.spikeFree_squarefree
#print axioms QRH.ArviKWall.BalancedSieve.selected_of_graded_flat
#print axioms QRH.ArviKWall.BalancedSieve.orderKernel_corrected_trivial
#print axioms QRH.ArviKWall.BalancedSieve.powerGauss_one
