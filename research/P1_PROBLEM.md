# P1: the one analytic input that would clear the bar (self-contained statement, 2026-10-25)

This consolidates `atom1/README.md`, `round7/signal-processing/` and `round8/README.md`. It states
exactly what would lower θ by the missing 6.1e-6 (the face family already gives 3.9e-6 of the 1e-5
milestone), what is known, and why the known tools stop.

## Setting

Work over `O = Z[ω]`, `ω = e^{2πi/3}`. For squarefree primary `n` let
`g̃(n) = g(n)/√N(n)` be the normalized cubic Gauss sum
(`g(n) = Σ_{x mod n} (x/n)₃ e(Tr(x/(n√−3)))`). Rows are quadratic residue symbols
`χ_k = (·/k)₂`, `N(k) ≤ K`. Slots are cubic symbols `conj((·/P)₃)` for primes `P` with `N(P) ~ L`,
with slot weights `a(P)` (in every application: smooth prime weights times fixed characters).

Column vector (the reflected theta coefficients times the slot sum):

  `c(n) = g̃(n) · Σ_P a(P) N(P)^{−1/2} conj((n/P)₃)`,  `N(n) ~ N = KL`.

By twisted multiplicativity `g̃(n)·conj((n/P)₃) = g̃(nP)/g̃(P)`: the slot space is spanned by
prime dilates of the theta coefficients.

## The statement needed

**Use (b), the probe's marked energy (cheapest).** For `N ≤ K^{1+δ′}` with `δ′ ≈ 1.1e-4`:

  `Σ_{N(k)≤K} |Σ_n c(n) χ_k(n) W(N(n)/N)|² ≪ K^{1+o(1)} Σ|c(n)|²`.

The large sieve (Goldmakher–Louvel over `Z[ω]`) gives `(K + N)^{1+o(1)}Σ|c|²`, which exceeds this by
`N/K = K^{δ′}`.

**Use (a), the count's marked inverse moment.** At `K = Z^{0.742}`, `N = Z^{0.871}` (`N/K = Z^{0.129}`):

  `Σ_k |Σ_n c(n)χ_k(n)W|² ≪ (K + N^{1−η}K^{η})Σ|c|²`  with `η ≥ 0.0076`.

Either one, with the stated size, gives at least 6.1e-6 in θ through the exact return.

## Equivalent forms

- **Subspace angle.** With `V = span{χ_k}` (dimension `K`) and `βW = span{g̃·conj((·/P)₃)}`
  (dimension `L`) in `C^N`, P1 for arbitrary slot weights is `‖Proj_V Proj_{βW}‖² ≤ N^{−η}`.
  Random subspaces give `≈ 1/L`.
- **Central values.** `S(k, P) = Σ_n g̃(n)χ_k(n)conj((n/P)₃)W(N(n)/N)` is the twisted theta series
  `θ₃ ⊗ χ_k ⊗ conj(·/P)₃` exactly at its critical point (conductor `≈ (kP)²`, length `KL`). P1 asks
  for a power saving in `‖S‖²_op` below the conjectured Frobenius norm `KLN = N²`, i.e. a stable rank
  of the `K × L` central-value matrix at least `N^η`.
- **What is rigorous.** The hybrid norm (quadratic sieve, then cubic sieve) proves `‖S‖²_op ≤ N^{2+ε}`.
  The best rigorous Frobenius bound is `LN²`. Entrywise Lindelöf gives only `N²`.

## Evidence that P1 is true

- Function fields (`F_q[T]`, `q ≡ 1 mod 6`): Weil gives square-root cancellation for every twist, so
  the column branch is diagonal for every `N`.
- Toy models over `Z[ω]`: `‖Φc‖²/diag = 0.6–1.1`, single-mark `F_P/diag = 0.81–1.17`, stable rank
  22.5–23.6 of `S` against 23.9 for Gaussian, principal angles at the random edge.
- Matrix concentration (non-commutative Khintchine) proves the diagonal bound when the Gauss-sum
  phases are replaced by independent random phases per multiplicative block. At `K′ = 156`,
  `N′ = 7796`, `L′ = 60` the true matrix has `‖S‖²_op` within 2% of the block-randomized one
  (`round7/signal-processing/logs_frame_nck_600_60000_400.txt`).

## Why the known tools stop

- **Any positivity step re-creates the `N` term.** After Poisson in the rows the off-diagonal is a
  bilinear form signed by reciprocity; its dual diagonal equals the original `N` term. So the target
  is an asymptotic large sieve at the critical point with a power-saving error. Conrey–Iwaniec–
  Soundararajan have only log savings even for the full family of Dirichlet characters.
- **Algebra alone is not enough.** Changing `g̃` only at primes of norm `> N/7` keeps every algebraic
  property (unimodularity, twisted multiplicativity, `g̃³ = n/|n|`) and pushes the sum to 3.4–5.8 times
  the diagonal. A proof must use the automorphy of `θ₃`.
- **The slot twist keeps the problem between two regimes.** More terms than characters (`N > K`),
  shorter than the slot-twisted critical length (`N < KL`). Voronoi/functional equations cannot
  shorten it, and the large sieve cannot see the cancellation.
- **Moment methods need the single-mark case at its own self-dual point** (`F_P ≤ N^{2−η}` at
  `N = K·N(P)`), and the fourth moment even needs `F_P ≤ N²/√L`.
- **GL(2) analogue.** Level-uniform second moments of quadratic twists are open. Li (Invent. 2024)
  removes the `ε` at the balanced point but keeps the `N` term past it.
- **Closest results.** Dunn–Radziwiłł's Type II estimate (cubic twists, inexplicit `X^{ρ}`,
  `ρ < 1e-4`, partly GRH); David–Dunn–Hamieh–Lin's quartic analogue at `u^{3/2}` (enough only for
  `K ≤ N^{2/3}`); OpenAI's unconditional cubic first moment, Prop. 4.1 (structured beats generic,
  near two narrow configurations, inexplicit).

## Cleanest sub-lemmas

- **Lemma BD (block decoupling).** `‖Σ_π g̃(π)S_π‖²_op ≤ N^{o(1)}max(‖ΣS_πS_π*‖, ‖ΣS_π*S_π‖)` for the
  blocks `{πm : N(m) ≤ M}`. True for random phases; numerically true for `g̃`; implies P1.
- **Lemmas SM + MM.** Single-mark `F_P ≤ N^{2−η}` and the mixed moments
  `Σ_{P≠P′}|Σ_k S(k,P)conj S(k,P′)|² ≤ N^{4−2η}`.
- **Smooth slots (use (a) only).** The vector inequality for
  `c_I(n) = Σ_{N(μ) ≲ 27N/L} φ(μ)(μ/n)₃` (no Gauss sum). Poisson in `μ` returns it to the original
  problem. The operator-norm version over all `φ` (round 7's Lemma Q3) has trivial bound `N^{1.118}`,
  because Heath-Brown's cubic-sieve term `(MN)^{2/3}` dominates.
