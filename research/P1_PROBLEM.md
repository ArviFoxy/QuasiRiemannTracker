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

Either one, with the stated size, is worth about 6–7e-6 in θ in the float model of the return
(`LOG.md`, "Open directions"); the exact prices on the face-family chain may differ slightly.

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

## Localization (round 9, `round9/outside_tools/NOTES.md`)

Split the columns by their largest prime factor `π`, with `c(πm) = g̃(π)e_π(m)`.
- On the columns with `N(π) ≤ K`, the column branch is at most `2K^{1+ε}·F·‖c‖²` for **any**
  values of the Gauss sums at the block primes. `F` is the frame constant of the block vectors
  (rigorous). It is numerically at Marchenko–Pastur, flat in `N/K`.
- So P1 needs arithmetic only on the **hard core**, the columns with a prime factor of norm `> K`:

  `Σ_{N(k)≤K} |Σ_{n: N(P⁺(n))>K} c(n)(n/k)₂ W(N(n)/N)|² ≪ K^{1+0.16δ′+o(1)}Σ|c|²` (use (b)).

  For use (a) the right side is `(K + N^{1−η}K^η)Σ|c|²`.
- Caveat: by Vaughan's identity the hard core is P1 modulo the frame bound, so the reduction
  localizes the difficulty but does not remove it.

## Cleanest sub-lemmas

- **Lemma BD (block decoupling).** `‖Σ_π g̃(π)S_π‖²_op ≤ N^{o(1)}max(‖ΣS_πS_π*‖, ‖ΣS_π*S_π‖)` for the
  blocks `{πm : N(m) ≤ M}`. True for random phases; numerically true for `g̃`; implies P1.
- **Lemmas SM + MM.** Single-mark `F_P ≤ N^{2−η}` and the mixed moments
  `Σ_{P≠P′}|Σ_k S(k,P)conj S(k,P′)|² ≤ N^{4−2η}`.
- **Smooth slots (use (a) only).** The vector inequality for
  `c_I(n) = Σ_{N(μ) ≲ 27N/L} φ(μ)(μ/n)₃` (no Gauss sum). Poisson in `μ` returns it to the original
  problem. The operator-norm version over all `φ` (round 7's Lemma Q3) has trivial bound `N^{1.118}`,
  because Heath-Brown's cubic-sieve term `(MN)^{2/3}` dominates.

## Companion: the long Möbius moment (atom 2), round 9

The other input of the right size is the long Möbius moment
`Σ_{u sixth-power-free, N(u)≍U} |D^{−1/2}Σ_n μ(n)(u/n)₆ W(N(n)/D)|²` at `D = U^t`, `t ∈ (1, 3/2)`.
- **Known.** Sixth-power amplification (7/8 Lemma 17.6) gives `U^{(1+5t)/6+ε}`.
- **Needed.** About 1.6e-4 less at `t ≈ 1.155` for the bar (the λ test: `λ ≥ 1/6 + 1.03e-3`).
- **Why it matters.** It is the only input that moves the unmarked zero-density exponent
  `ρ(ν) = 1 − 10ν/(15 − 6ν)`, with sensitivity `4ν/(5 − 2ν)` (`round9/README.md` §1,
  `lean-lab/ZeroDensityGame.lean`).
- **Numerics.** On the actual family (2076 rows at `U = 8000`), the moment stays at its diagonal
  (ratio 0.89–0.99) up to `t = 1.4`, where amplification allows a factor 20
  (`round9/numerics/`).
- **Where a proof would have to enter.** Square-root cancellation in the Möbius bilinear form
  `Σ_{n≠n′} μ(n)μ(n′) Σ_u χ_n(u) conj(χ_{n′}(u))`. Its kernel has conductor up to `D² ≫ U`, which
  makes this a twisted Chowla-type correlation. Even for all characters to one modulus, only
  averages over the modulus (Barban–Davenport–Halberstam) avoid such correlations.
