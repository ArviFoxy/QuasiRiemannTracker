# Round 7: beating the large sieve for P1 with signal-processing tools (2026-10-25, negative)

Question (the user's suggestion): can tools from compressed sensing, frame theory or ML signal
processing give the column branch of P1 (the quadratic large sieve for slot-twisted cubic-theta
coefficients slightly past the diagonal `N = KL`) a power saving?

Answer: no tool tried beats the large sieve. Each either uses statistics that an explicit adversary
also matches while reaching the N-term, or turns back into the same self-dual problem. The round did
produce one rigorous result, two structural facts and two clean sufficient lemmas.

## Structural facts (numerically to about 1e-15)

- **Orientation.** The paper's `χ_p` is the sextic symbol, so the slot twist is
  `χ_P(n)^{-2} = conj((n/P)_3)`. The toy in `../../atom1/toy/` uses `(n/P)_3`, the conjugate (no
  numerical difference, but it matters structurally).
- **The slot twist is a dilation.** With twisted multiplicativity
  `g(c₁c₂) = conj((c₁/c₂)_3) g(c₁) g(c₂)`, one has `β(n) χ_P(n)^{-2} = g̃(nP)/g̃(P)`: the slot space is
  spanned by prime dilates of the θ₃ coefficients. For GL(2) Hecke eigenforms prime dilation is free;
  for θ₃ only cube dilations are Hecke operators. That is exactly why marks raise the conductor and
  cube marks do not.
- **Cube roots.** `g̃³ = n/|n|` and `g̃² = conj(g̃)·n/|n|`; all the arithmetic is in which cube root
  `e(n)` is taken.
- **Smooth slots cancel the Gauss sum.** Poisson in the slot variable turns
  `g̃(n) Σ_P w(N(P)/L) N(P)^{-1/2} conj((n/P)_3)` into `(L/N)^{1/2} Σ_{N(μ) ≲ 27N/L} φ(μ)(μ/n)_3`. In the
  model (N′ = 7796 columns) 98.8–99.2% of this vector lies in a cubic-character span of 3–9% of the
  dimension (random vectors: 3–9%; the toy's orientation: 6–16%).

## Matrix concentration (rigorous)

Write the `K × L` matrix as `S = Σ_n β(n) φ_n x_nᵀ` and give `β` independent random phases per
multiplicative block `{d·m : N(m) ≤ K}`. The matrix Rademacher bound gives
`E‖S‖²_op ≪ log · max(‖X_B‖²‖Φ‖², ‖Φ_B‖²‖X‖²) ≈ K N log` at `N = KL`: the column branch is diagonal for
random coefficients, using only the quadratic and cubic large sieves as black boxes. So P1 is a
derandomization problem, and it breaks there: the moments `tr((SS*)^m)` of the actual Gauss sums contain
`Σ_P F_P^m`, which already needs the single-mark bound `F_P ≤ N^{2−η}` at its own self-dual point
`N = K·N(P)` (the fourth moment would need `F_P ≤ N²/√L`).

## Obstructions

- **Uncertainty principles / coherence** (Donoho–Stark, Elad–Bruckstein, Gershgorin, Schur): capped
  at `‖S‖_F²/N² ≈ 0.92–0.98` since `KLN = N²` at the binding. Even Lindelöf for every individual twisted
  central value implies only `N²` for arbitrary slot coefficients.
- **Algebraic-only proofs fail** (rigorous adversary): changing β only on prime columns of norm
  `> N/7` keeps unimodularity, twisted multiplicativity, `β³ = n/|n|` and all composite values, yet gives
  `‖Φc‖² ≫ (L/log²N)·diagonal` (model: 3.4–5.8× the diagonal; optimizing all prime values reaches
  9.7–13.1 of an allowance 22.6). Any proof must use the automorphy of θ₃, self-dual at `N = KL`.
- **Paving / sketching:** arithmetic pavings exist (`‖Φ|_B‖² ≤ 2K` on blocks of multiples), but the
  recombination cross terms are the original off-diagonal.
- **Dual certificates / majorants:** frame bound of a larger family, at least the N-term.
- **Type I / Type II split of prime slots:** Type I reduces to Lemma Q3; Type II (slot `= de` with
  arbitrary coefficients) is the hard core — Cauchy over `d` plus Poisson cancels the Gauss sums, but
  the diagonal of the resulting overcomplete cubic sieve is exactly the N-term.
- Numerics: `S` looks like an iid Gaussian matrix (stable rank 22.5–23.6 against 23.9; principal
  angles at the random-subspace edge 0.049 against 0.0525; single-mark ratios 0.81–1.17).

## Correction to `../../LOG.md`

Use (a) (the inverse-moment budget) only needs `(K + N^{1−η} K^η)‖c‖²` with **η ≥ 0.0085**, because
`N/K = Z^{0.129}`. The remark "K + N^{1−η}K^η never suffices" applies only to use (b) (the probe).

## Cleanest open lemmas

- **Lemma Q3 (quadratic–cubic uncertainty principle).** `E(k, μ) = Σ_{n~N} W μ²(n) (n/k)_2 (μ/n)_3`,
  nontrivial `k ≤ K`, `N(μ) ≲ 27N/L`, `N = KL`. Claim: `‖E‖_op ≤ N^{1−η}`. It implies P1 for smooth slots
  (η ≈ 6.3e-4 suffices for use (a)); it has no Gauss sums; trivial bound N, random value about
  `2√(KM)` (`M ≈ 27K`). Numerically random-like (max cos² 0.084–0.172 against random edges
  0.100–0.196). Caveat: Poisson in `n` turns it back into cubic Gauss sums twisted by sextic characters.
- **Lemma BD (block decoupling).** `‖Σ_π g̃(π) S_π‖² ≤ N^{o(1)} σ²`; true for random phases; implies P1.
- **Single-mark plus mixed second moments**: the minimal input for any moment proof.

Files: `NOTES.md` (details), `zw.py`, `build.py`, `test_gauss.py`, `test_absorb.py`, `exp_spectral.py`,
`exp_adversary.py`, `exp_prime_adversary.py`, `exp_typeI.py`, `exp_frame_nck.py` (frame bounds,
written but not run), `logs_*.txt`.
