# Round 9, outside tools: frame theory on P1, witness design at the corner (2026-10-25)

Status labels: **[R]** rigorous (proof given or standard), **[H]** heuristic, **[N]** numerical
(Z[ω] model of `../../round7/signal-processing/`, reused through `zw.py`).

## 0. Verdict

No gain. The attempt produced one rigorous reduction, one localization and four closures.

1. **Main attempt (P1, atom 1), tool: frame/Gram matrices.**
   - Split the columns by their largest prime factor. On the columns whose largest prime factor
     has norm at most `K`, the column branch is bounded by the large sieve's *diagonal* times one
     frame constant `F`. This holds for **every** choice of the Gauss sums at the block primes
     [R].
   - Numerically `F` sits at the Marchenko–Pastur value `(1 + √(m/K))²` (ratio 0.88–0.99 in
     all 8 scan configurations, never above), independent of `N/K` (5 to 80). The best block
     phases stay at about 2.5× the diagonal, while the large-sieve allowance grows to 20× [N].
     Random cofactor data gives the same `F` as the true data.
   - So in the model the whole `N`-term excess that an adversary can reach sits on the **hard
     core**: columns with a prime factor of norm `> K`. By Dickman these are a fraction
     `log(log N/log K)` of the columns, which is 0.160 for use (a) and about `δ′ ≈ 1.1e-4` for
     use (b).
   - It does not close. A bound for `F` is *equivalent* to P1 on the smooth part for every
     choice of block multipliers, and the trivial bound for `F` is exactly the large sieve. Given
     the frame bound, the hard core is equivalent to P1, and the standard route to it (a
     combinatorial decomposition of the large prime) contains the full column vector `c` in its
     `d = 1` Type I term [R].
2. **Second attempt (count corner, items 2 and 4), tool: LP/witness design.**
   - A new witness family, Möbius blocks weighted by the number of prime factors in a band, has a
     rigorous density-hypothesis-strength mean value at every length `t ≥ 1`. That is far better
     than the long line's slope `5/6 − δ`.
   - It does not close either. By the explicit formula, prime-factor weights act on the zeros'
     residue profile as a **scale shift**, so these witnesses are saturated only when the Möbius
     block at the shifted length is. That is target 5 of `../../LOG.md` (scale transfer), and the
     lattice adversary of `../README.md` §1 defeats it [R in the model, H for real `L`-functions].
3. **Short closures.**
   - SDP combinations of aligned witnesses gain at most a factor `J` (the number of witnesses) [R].
   - Many tiny slots make `A(n)` log-normally spiky, but only by a constant [H].
   - The exchange rate 6 is the exact stabilizer [R].
   - Higher-rank metaplectic theta functions carry the sextic Gauss sums explicitly, but their
     functional equations lengthen sums [H].

## 1. Why P1, and why frame theory

P1 (`../../P1_PROBLEM.md`) needs the smallest relative change of all the atoms. Use (a) needs only
`η = 0.0076` of a saving whose true size is the whole `N/K`. Use (b) needs the excess past `N = K`
to be kept to 16%. The coefficients are specific, and every toy puts the truth at the diagonal.
Round 7 showed that a proof must use the automorphy of `θ₃`: an adversary that changes `g̃` at
primes of norm `> N/7` reaches 3.4–5.8× the diagonal. The question asked here is a frame-theoretic
one: **at which primes does the proof need arithmetic, and where is generic near-orthogonality
enough?**

## 2. The block decomposition [R]

Notation as in `P1_PROBLEM.md`: `Φ` is the `K × N` matrix `(n/k)₂`, and
`c(n) = g̃(n)A(n)` with `A(n) = Σ_P a(P)N(P)^{−1/2}conj((n/P)₃)`.

- **Blocks.** Every squarefree `n` has a unique largest prime factor `π = P⁺(n)`. Twisted
  multiplicativity gives `c(πm) = g̃(π)·e_π(m)` with
  `e_π(m) = g̃(m)conj((m/π)₃)A(πm)` (checked to `3.5e-16`). Put
  `w′_π = Φ(e_π placed on B_π)`. Then `Φ(c·1_{B_π}) = g̃(π)w′_π`.
- **Weighted Cauchy–Schwarz.** For every unimodular choice `x_π` in place of `g̃(π)`,

  `‖Σ_π x_π w′_π‖² ≤ (Σ_π ‖w′_π‖²) · F`,  `F := λ_max(Σ_π w̃_π w̃_π*)`,  `w̃_π = w′_π/‖w′_π‖`.

- **The block-diagonal factor is the diagonal.** If `L ≤ N(π) ≤ K` with `L = N/K`, block `π` has
  cofactor length `N/N(π) ≤ K`. Goldmakher–Louvel in the diagonal regime then gives
  `‖w′_π‖² ≤ (2K)^{1+ε}‖c·1_{B_π}‖²`. Hence

  **`CB(c·1_smooth) ≤ 2K^{1+ε} · F · ‖c‖²` for every choice of Gauss sums at the block primes.**

  `L`-smooth columns take as block index their least-norm divisor with norm `≥ L`. That norm is
  `< L² ≤ K`, so they are covered in the same way.
- **The trivial frame bound reproduces the large sieve.** `⟨w′_π, y⟩ = Σ_m e_π(m)Y(πm)` with
  `Y(n) = Σ_k ȳ_k(n/k)₂`. If every block is non-degenerate (`‖w′_π‖² ≥ K‖e_π‖²/C`), Cauchy–Schwarz
  in the cofactor gives `F ≤ (C/K)·sup_y Σ_n |Y(n)|²/‖y‖² ≤ C(1 + N/K)` by the dual large sieve.
  With this the inequality is `≍ (K + N)‖c‖²`, the large sieve. Any power saving in `F` is
  therefore new information.
- **Hard core.** These are the columns with `N(P⁺(n)) > K`, i.e. `n = πm` with `N(m) < N/K`. There
  are `N^{1−o(1)} > K` blocks (the primes of norm in `(K, N]`), so `F ≥ #blocks/K ≫ 1`
  (`λ_max ≥ trace/K`), and no phase-free bound can work there.

## 3. Numerics [N]

Script `block_gram.py` (logs `logs_block_gram_*.txt`). Rows are quadratic symbols with
`N(k) ≤ K`, columns are split-squarefree with `N(n) ∈ (N/2, N]`, and the slots are `14–60` prime
marks. `adv` is the best block phases found by a phase power iteration (a lower bound for the
maximum). `LS` is the large-sieve allowance `(K′ + N′)‖c‖²/diag`.

**Scan in `N` at fixed `K`** (`block_scan.py`, `logs_block_scan_K600.txt`, `logs_block_scan_K2000.txt`):

| K | N | N′/K′ | smooth: F / MP | smooth: adv/diag | smooth: LS | hard core: adv/diag | hard core: LS |
|---|---|---|---|---|---|---|---|
| 600 | 6000 | 5 | 0.99 | 2.65 | 3.5 | 4.8 | 3.9 |
| 600 | 12000 | 10 | 0.95 | 2.62 | 4.9 | 7.5 | 7.7 |
| 600 | 24000 | 20 | 0.97 | 2.72 | 7.7 | 12.7 | 15.4 |
| 600 | 48000 | 40 | 0.91 | 2.52 | 12.8 | 20.0 | 31.3 |
| 600 | 96000 | 80 | 0.88 | 2.56 | 19.8 | 31.8 | 66.4 |
| 2000 | 20000 | 5 | 0.97 | 2.45 | 3.8 | 4.6 | 3.5 |
| 2000 | 40000 | 10 | 0.97 | 2.42 | 5.8 | 7.3 | 6.8 |
| 2000 | 80000 | 20 | 0.98 | 2.56 | 9.5 | 11.8 | 13.6 |

`MP = (1 + √(m/K′))²`, where `m` is the number of blocks. With the true Gauss sums, `CB/diag` is
0.80–1.12 on both parts.

- On the smooth part, adversarial block phases gain a bounded factor (about 2.5, which is
  `(1 + √(m/K′))²` with `m/K′ ≈ 0.55–0.6` here). The factor does not grow with `N/K`.
- The weighted bound `wub = blk·F/diag` is nearly attained: the adversary reaches 82–92% of it
  on the smooth part, so the frame inequality is sharp up to about 15%.
- On the hard core the adversary reaches 61–76% of `wub`. It grows with the number of hard-core
  blocks (`F ≈ MP ≈ m/K′`), roughly like `(N/K)^{0.7}` in this range, and reaches 48–131% of the
  nominal allowance. The allowance `(K′ + N′)` is not a strict bound: the large sieve holds up to
  constants and `ε`.
- In the true problem `m/K ≈ 1/log K`, so the smooth factor tends to 1.

**What `F` depends on** (`bg_dependence.py`, logs `logs_bg_dependence_*.txt`). The cofactor data
`e_π` was replaced while the blocks were kept:

| cofactor data `e_π(m)` | F/MP (K=600, N=48000) | F/MP (K=2000, N=40000) | best block phases / diag |
|---|---|---|---|
| true `g̃(m)conj((m/π)₃)A(πm)` | 0.92 | 0.97 | 2.51 / 2.42 |
| without slots | 0.98 | 0.97 | 2.72 / 2.52 |
| `g̃(m)` only | 1.03 | 1.08 | 3.11 / 2.68 |
| random phases | 0.98 | 0.96 | 2.66 / 2.48 |
| `(m/k₀)₂` (aligned) | 2.98 | 1.71 | 10.21 / 4.99 (allowance 12.6 / 5.7) |
| aligned on half the blocks | 1.81 | 1.21 | 4.57 / 2.98 |

So `F` is a genuine property of the cofactor data. It fails for cofactors aligned with a quadratic
character, and the true data is indistinguishable from random.

## 4. What this reduction proves, and why it does not close

**Proposition [R].** P1 (use (a) or (b)) follows from two statements:
- **BG (block frame bound):** `F ≤ N^{o(1)}` (use (b)), or `F ≤ L^{1−η}/2` (use (a)), on the
  non-hard-core columns with the block indices of §2;
- **HC:** P1 for `c·1_{hard core}`.

Proof: `CB(c) ≤ 2CB(c_smooth) + 2CB(c_HC)` and §2.

**Obstructions.**
- **BG is P1 for a larger family [R].** Exactly,
  `F = sup { ‖Σ_π x_π w′_π‖² / Σ_π |x_π|²‖w′_π‖² : x ∈ ℂ^m }`. So BG is P1 on the smooth part,
  measured against the block diagonal, for **every** coefficient vector `x_π e_π(m)` (arbitrary
  block multipliers). It contains the true `c` (`x_π = g̃(π)`). Unimodular `x` give
  `sup_y (Σ_π |⟨w′_π, y⟩|)² ≤ blk·F`, and numerically they reach 82–92% of it.
  - What BG needs is non-alignment of the cofactor vectors `e_π` with quadratic polynomials
    `Y` across many blocks at once (table above: aligned cofactors break it).
  - The cofactor data still contains `g̃(m)` at primes `< N(π) ≤ K`, so BG is not free of
    arithmetic. It is free of the block phases.
  - A sufficient pointwise route (flat profiles `|Σ_m e_π(m)(m/k)₂|² ≤ L^{1−η}M`) is
    square-root cancellation for short sums of Gauss sums far below their critical length
    (`M ≤ K` against `≈ K²L`), which is out of reach.
  - The frame is phase-free but not coefficient-free.
- **HC is P1-hard [R].**
  - Given BG, HC ⟺ P1, since `c = c_smooth + c_HC` and `CB` obeys the triangle inequality.
  - The standard route to HC writes `1[π prime] = Λ(π)/log N(π)` and decomposes `Λ` (Vaughan or
    Heath-Brown).
  - The Type I term with `d = 1` replaces the prime `π > K` by an arbitrary `j` with
    `N(j) > K`. That gives `Σ_{N(m)<L} c·1_{m|n}`, i.e. `c(n)` times the number of divisors of
    norm `< L`.
  - Its `m = 1` term is `c` itself, with coefficient exactly 1. The terms `m > 1` are P1 at
    length `N/N(m) ≥ K` for `g̃·χ_m·A`, with `χ_m = conj((m/·)₃)`.
  - The Type II pieces have both factors `≥ L` and are block pieces of BG type. So the route is
    circular.
  - Without the decomposition, the hard core's prime sums `Σ_{π~X} g̃(π)conj((π/mP)₃)(π/k)₂`
    (`X ∈ (K, N]`) lie at or below their critical length, since `N(k)N(m)N(P) ≳ N ≥ X` for
    typical rows. Heath-Brown–Patterson type savings need `X` large compared to the conductor.
    This is a statement about the range of the available tools, not a proof that HC is false.
- **The density of the hard core does not help [R].** A fixed fraction (0.16, or `δ′`) of columns
  at the `N`-term still has exponent `N`. Only exponents count as `Z → ∞`.

**What is new: a localization of where the excess can live.**
- On the smooth part, the Gauss sums at the largest prime factor (the block phases, primes of
  norm `≤ K`) can be replaced by arbitrary unimodular numbers. The cost is at most `F`.
- For the true cofactor data `F` stays at the random-matrix value `(1 + √(m/K))²`, which tends
  to 1 since `m/K ≈ 1/log K`.
- So no choice of Gauss sums at primes of norm `≤ K`, made largest-prime-factor-wise, creates an
  `N`-term excess. An excess must come from one of two places:
  - alignment of the cofactor data with quadratic characters (BG fails). This is not seen: the
    true data is indistinguishable from random;
  - the hard core, where the adversary reaches the full allowance.
- For use (b) the hard core is "a prime of norm in `(K, K^{1+δ′}]` times a cofactor of norm
  `< K^{δ′}`". Round 7's algebraic adversary (`g̃` changed at primes of norm `> N/7`) lives
  entirely inside it once `N/K > 7`.

## 5. Second attempt: witness design at the corner (LP lens)

**Witness.** For a band `I = {p : N(p) ∈ (X, 2X]}`, `X = U^x`, and `D = U^t` (`t ≥ 1`), put

  `M^ω_u(D) = Σ_n μ(n) ω_I(n) ψ_u(n) N(n)^{−s₀} W(N(n)/D)`,  `ω_I(n) = #{p ∈ I : p | n}`.

**Mean value [R].** `μ(pm) = −μ(m)` for `p ∤ m`, so `M^ω = −Σ_{p∈I}ψ(p)N(p)^{−s₀}Σ_{p∤m}μ(m)ψ(m)…`.
Separate `W` by Mellin to get `M^ω = −(2πi)^{−1}∫W̃(w)D^w Q_u(I; s₀+w) M_u(V; s₀+w) dw` plus a
`p | m` correction of relative size `≪ 1/X`. Then:
- In the bin, the buffered zero-free window and the explicit formula give
  `|Q_u(I; s)|² ≪ X^{δ+O(e)}` for `|Im s − γ_u| ≤ Z^τ`. Zeros outside the window are damped by the
  decay of `Ŵ_I`.
- The inverse moment with row-dependent heights (7/8 Lemma 17.6) applies to `M_u(V)`, which has
  length `U^{t−x} ≤ U^{1−c}`.

Hence `Σ_{u∈bin}|M^ω_u(D)|² ≪ X^{δ}U^{1+ε}`. The rows with `|M^ω_u(D)|² ≥ D^δ` number at most
`U^{1−δ(t−x)+ε}`. With `x = t − 1` this is the density hypothesis `1 − δ` for every `t ≥ 1`, against
the long line's `1/6 + (5/6 − δ)t`. Even the global bound (`κ = 2β* − 1` instead of `δ`) gives
slope `κ − δ = 0.294 < 5/6 − δ = 0.378`.

**LP value if it applied.** If every corner row had a saturated `ω`-witness with `t − x = 1`, then
`R → 1 − δ`, i.e. `ΔR = −0.059` and `Δθ ≈ −7.8e-3`. This is round 5's lossless interpolation.

**Why it does not apply.**
- *Real `L`-functions [H].* By the explicit formula,
  `M^ω(D) = Σ_ρ (−Q̃(I;ρ))·Res_ρ D^{ρ−s₀} + (left integral)`, with
  `Q̃(I;ρ) ≈ −(log X)^{−1}Σ_{ρ′}Ŵ_I(ρ′−ρ)X^{ρ′−ρ}`. Summed over `ρ`, this is a superposition of
  height-localized copies of the Möbius residue profile at scale `t − x`. Prime-factor weights act
  as a **scale shift**, so a dip of the profile at `t − x` (in the whole box, which is what the
  adversary needs anyway) kills the witness.
- *Model [R].* In the one-variable model `L = P(U^{−m₁(s−a)})` this is exact: the `ω`-witness is
  the coefficient of `Y^{k_D}` in `(−L′/L)_I·(1/L)`, which is `Σ_{k∈I}π_k M_{k_D−k}`, a partial
  convolution of the log-derivative coefficients with the Möbius profile. The full convolution is
  `(1/L)′` (that is, `μ·log = −μ∗Λ`).
- In `../README.md` §1's lattice adversary, `π_k` and `M_j` vanish off `s₀ℕ`. So the witness is
  saturated only when `t − x ∈ s₀ℕ ∩ [0,1] = {s₀, 2s₀}`, where its count is
  `I(t − x) ≥ 1 − 2νs₀ = ρ`. Band versions (sums over many `x`) are partial convolutions and give
  either a count `≥ R`, when the band reaches a saturated scale `≤ r*`, or zero.
- **Closed: prime-factor transfer = scale transfer (target 5).**

## 6. Short closures

- **SDP instead of Hölder in the count [R].**
  - Take `J` witnesses with bounds `B_j`, saturation levels `T_j` at bad rows, aligned phases at
    bad rows, and arbitrary cross-moment bounds.
  - Testing the positive form `Σ_u |Σ_j α_j W_j|²` gives at best
    `#bad ≤ (Σ_j T_j/B_j)^{−1}·(1 + cross) ≥ min_j(B_j/T_j)/J`.
  - Without forced alignment it gives `min_j B_j/T_j`.
  - So the gain is at most a factor `J`. The corner offers `O(1)` saturated witnesses (a dip
    between `r*` and `t*`, and twists by other characters see other `L`-functions), so the gain
    is constants only.
- **Slot spikiness [H].** With `J` slot pools, `|A(n)|² = Π|A_i(n)|²` is roughly log-normal (each
  `|A_i|²` is roughly exponential). Its `L²` mass sits on a density about `e^{−0.82J}`. That is a
  constant independent of `Z` (fixed mesh), and the large sieve on sparse sets is not better in
  general. No power.
- **Exchange rate 6 [R].**
  - `ψ_{ua′} = ψ_u` off `a′` for all `n` forces `(a′/·)₆ = 1` at almost all primes, so `a′` is a
    sixth power (Kummer theory).
  - Units twist by fixed ray characters, conjugation moves the height, and `a³` (`a²`) twist by
    `(a/·)₂` (`(a/·)₃`). Averaged over `a`, those give the diagonal `Σ|B(u)G(u,h)|²` rather than
    `|F_b(h)|²` (they orthogonalize).
  - Exact-copy amplification therefore has rate exactly 6, and only density changes it.
- **Higher-rank theta [H].** The sextic Gauss sums produced by the second Poisson step ("Kazhdan–
  Patterson in disguise") are, by Kazhdan–Patterson uniqueness for `n = r, r+1`, Whittaker data of
  the theta representation on the 6-fold cover of `GL(5)`/`GL(6)`. So an explicit carrier exists,
  but its functional equations have conductor exponent 5–6 and lengthen the sums. This is a
  pointer, not a route.

## 7. Lemmas that would give the gain, and the assumptions

- **Lemma HC (believed true).** For use (b): with `N = K^{1+δ′}`, `δ′ ≤ 2e-4`,
  `Σ_{N(k)≤K} |Σ_{n: N(P⁺(n))>K} c(n)(n/k)₂ W|² ≪ K^{1+0.16δ′+o(1)}Σ|c|²`. For use (a) the same
  with `(K + N^{1−η}K^η)`, `η ≥ 0.0076`.
  - Evidence: true-phase ratios `CB/diag` of 0.91–1.12 on the hard core in every run (0.86–1.24
    without slots). The adversary needs
    non-Gauss values at primes `> K`.
- **Lemma BG (believed true).** `F ≤ N^{o(1)}` for the smooth blocks.
  - Evidence: `F/MP ∈ [0.88, 0.99]` in 8 configurations, flat in `N/K`. It holds for random
    cofactor phases (matrix concentration, round 7 §3.2).
  - BG + HC ⟹ P1 [R], worth 6–7e-6 in θ per `P1_PROBLEM.md`.
  - But HC ⟺ P1 modulo BG [R], so HC is the real content. It is a statement about Gauss sums at
    **primes** larger than the row count, against quadratic × slot characters, at the critical
    length.
- **Assumptions.**
  - The toy model has: split-squarefree columns; prime slots with uniform weights (no `ϑ`, `Ψ₀`,
    cube parts or S-parts); `K′ ≤ 520` rows; `N/K ≤ 80`; `log N/log K ∈ [1.24, 1.79]`, against the
    real 1.174.
  - The model's hard-core fraction is larger than Dickman's `log u`, since primes are a large
    share of small split-squarefree columns.
  - §5's mean value uses the bin's buffered zero-free window and Lemma 17.6 as stated in the
    paper.

## Files

| file | contents |
|---|---|
| `block_gram.py` | block decomposition by largest prime factor, frame constant, adversarial block phases |
| `block_scan.py` | scan in `N` at fixed `K` |
| `bg_dependence.py` | dependence of `F` on the cofactor data |
| `logs_*.txt` | verbatim outputs |
