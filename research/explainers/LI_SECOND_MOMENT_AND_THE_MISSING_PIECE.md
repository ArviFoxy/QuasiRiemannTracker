# Li's second moment, the fourth moment, and what our problem still lacks

An explainer, written 2026-10-25. Sources:
- X. Li, *Moments of quadratic twists of modular L-functions*, arXiv:2208.07343, Invent. Math.
  2024 (text in the session scratchpad).
- Q. Shen and J. Stucky, *The fourth moment of quadratic Dirichlet L-functions II*,
  arXiv:2402.01497.

## 1. Vocabulary

**Characters.**
- A *quadratic character* is `χ_d(n) = (d/n)`, the Kronecker symbol. It takes the values ±1, and 0
  when `n` shares a factor with `d`.
- `d` is a *fundamental discriminant*. Li uses `8d` with `d` odd and squarefree.
- `Σ*` means a sum over squarefree integers. `Σ♭` means a sum over fundamental discriminants.

**Modular forms and Hecke eigenvalues.**
- `f` is a *Hecke eigenform* of weight `κ` for `SL₂(Z)`. Its normalized Fourier coefficients
  are the *Hecke eigenvalues* `λ_f(n)`.
- They satisfy the *Hecke relations*, e.g. `λ_f(np) = λ_f(n)λ_f(p) − λ_f(n/p)` when `p | n`.
- Deligne's bound gives `|λ_f(p)| ≤ 2`.

**L-functions and twists.**
- `L(s, f) = Σ λ_f(n) n^{−s}`.
- The *twist* `f ⊗ χ_d` has `L(s, f ⊗ χ_d) = Σ λ_f(n)χ_d(n) n^{−s}`. It is the L-function of a
  form of level `d²`.

**Conductor and functional equation.**
- The *conductor* measures the complexity of an L-function; for `f ⊗ χ_d` it is about `d²`.
- The *functional equation* `Λ(s) = (sign)·Λ(1 − s)` relates `s` and `1 − s`. Here `Λ` is `L`
  times gamma factors and a power of the conductor.
- If the sign is −1, the central value vanishes.

**The approximate functional equation.**
- The central value is `L(½) ≈ Σ_{n ≲ √conductor} a_n n^{−½} + (sign)·(a dual sum of the same
  length)`.
- `√conductor` is the *critical length*: for `f ⊗ χ_d` it is `|d|`.
- A sum longer than the critical length can be *reflected* by the functional equation into a
  shorter dual sum.

**Moments and the conjecture.**
- The *moments* of the family are `M(k) = Σ_{0<8d<X} L(½, f ⊗ χ_{8d})^k`.
- Keating–Snaith conjecture `M(k) ∼ C·X(log X)^{k(k−1)/2}`.

**What was known before Li.**
- `k = 1`: Iwaniec.
- `k ≤ 1`, upper bounds: Radziwiłł–Soundararajan.
- `k = 2`: only `X^{1+ε}` unconditionally (Heath-Brown's large sieve), and the asymptotic under
  GRH (Soundararajan–Young).

**Li's Theorem 1.1** (unconditional): `M(2) ∼ C_f·X log X`. "Unconditional" means GRH is not
assumed.

## 2. The large sieve, and the two ways it can fail

The quadratic large sieve asks how much one signal `a_n` (`n ≤ N`) can correlate with many
characters `χ_m` (`m ≤ M`):

  `Σ_{m≤M} |Σ_{n≤N} a_n χ_m(n)|² ≤ Δ(M, N)·Σ|a_n|²`.

- **The ideal** is `Δ = M + N`.
  - `M` is the *diagonal*: every character sees the signal with mean square `Σ|a_n|²`.
  - `N` is the *N-term*. If `N > M`, the signal can be chosen to be one character, and then that
    character alone gets `N·Σ|a_n|²`.
- **Heath-Brown** proved `Δ ≪ (MN)^ε(M + N)`.
  - The factor `(MN)^ε` is the *ε-loss*. For the second moment it costs `X^ε`, which is fatal,
    since the target is `X log X`.
- So a large sieve can be weak in two ways:
  - an ε (or log) loss at the balanced point `N ≈ M`;
  - the N-term past it, `N > M`.

Li removes the first, for the special coefficients `a(n) = λ_f(n)/n^{½+it}`.

## 3. Li's key estimate (Proposition 3.2)

  `S♭(M, N, t) = Σ♭_{M≤|m|<2M} |Σ_n λ_f(n) n^{−½−it} G(n/N) (m/n)|² ≤ L^{2/3}(1+|t|)²·(M + N log(2 + N/M))`.

Here `G` is a fixed smooth cutoff (a dyadic partition of unity) and `L` a constant depending on
`f`. There is no ε: only a log, and only when `N ≫ M`. The N-term is still there.

Why that suffices for Theorem 1.1:
- The approximate functional equation reduces `M(2)` to such sums with `N ≲ X`, `M ≍ X`.
- The easy range `N ≤ X/(log X)^A` is handled by Poisson summation.
- Proposition 3.2 bounds the hard range `X/(log X)^A ≤ N ≤ X` by `O(X·loglog)`. That fits under
  the main term `X log X`.

## 4. How Li proves it

1. **Inflation by prime squares** (Lemma 3.1). For `p ∤ n`, `(mp²/n) = (m/n)`: every modulus `m`
   has *copies* `mp²`.
   - Sum over the `P(L) ≈ √L/log L` primes `p ∈ [√L, 2√L]`, and use positivity.
   - Uniqueness of `m p²` (`m₁p₁² = m₂p₂²` forces equality for squarefree `m`) avoids
     overcounting.
   - Result: the sum over `m ≍ M` is bounded by `1/P(L)` times a sum over *all* `m′ ≍ ML`, a
     longer family.
   - The terms with `p | n` are handled by the Hecke relation and are smaller instances of the
     same sum.
   - Dropping the squarefree condition on `m′` is safe only for these coefficients. For
     `a(n) = 1/√n`, the square moduli alone would give a huge main term (the pole of `ζ`). For
     `λ_f`, `L(s, f)` has no pole.
2. **Poisson summation in the long `m′`-sum.** Now there are more moduli than terms (`ML > N`),
   so Poisson in `m′` gives:
   - a diagonal main term `∝ ML`;
   - dual frequencies `k ≲ N²/(ML)` with Gauss-like sums `G_k(n₁n₂)` (eq. (2.1)).
   - Generically `G_k(n) ≈ χ_k(n)√n`. So the off-diagonal is again a large-sieve sum with the
     same coefficients, over a smaller family `k ≍ X/L`.
3. **The functional equation of `L(s, f ⊗ χ_k)`.** Its conductor is `k² ≍ (X/L)²`, so its
   critical length is `X/L`. The `n`-sum has length about `X`, which is past the critical length,
   so it reflects to a dual sum of length `(X/L)²/X = X/L²`.
   - The new problem has family `X/L` and length `X/L²`: smaller than before by a factor `L`.
4. **Nested induction on `M`, then on `N`.**
   - The statement is proved for all smaller `(M, N)` with the same constant `L^{2/3}`.
   - The factor `1/P(L)` from step 1 absorbs the constant-factor losses of each round, so the
     constant never grows.
   - For large `N`, Lemma 5.3 uses the functional equation directly.

**Shen–Stucky.** They run the same scheme for the fourth moment of quadratic Dirichlet
L-functions:
- Their large sieve is a "fourth-moment" version, with coefficients from `L(s, χ)²`.
- New cross-cancellations between diagonal and off-diagonal terms give the asymptotic
  `X·Q₁₀(log X) + O(X(log X)^{6+ε})`.
- It is unconditional, and it is the first fourth moment of a symplectic family. Its large
  sieve still has an N-term past the balanced point.

## 5. Why it worked for Li, and what is missing for us

**Li's structural luck: no dead zone.**
- For `f ⊗ χ_m`, the critical length `|m|` equals the family size `M`.
- So every length is either `N ≤ M` (the large sieve is diagonal) or `N > M` (past the critical
  length, so reflect).
- The only enemy is the log or ε at `N ≈ M`, and inflation plus induction removes it.

**Our P1 (the column branch of the probe).**
- *Rows*: quadratic characters `χ_k`, `N(k) ≤ K`.
- *Coefficients*: normalized cubic Gauss sums `g̃(n)`, times a *slot sum*
  `Σ_P a(P)(n/P)₃^{−1}` over primes `P ~ L`.
  - The `g̃(n)` are the Fourier coefficients of the Kubota–Patterson cubic theta function `θ₃` on
    the cubic cover of `GL(2)` over `Z[ω]`.
- The relevant L-function is `θ₃ ⊗ χ_k ⊗ (·/P)₃⁻¹`. Its conductor is about `(kP)²`, so its
  critical length is about `KL`.
- We need the sum at length `N = K^{1+δ′}` with `δ′ ≈ 1.1e-4`. So `K < N < KL`: the dead zone.
  - There are more terms than characters, so even an ε-free large sieve gives `K + N`, i.e. the
    N-term. That costs `K^{δ′}`, which is exactly the 6.1e-6 we are short.
  - The sum is shorter than the critical length, so the functional equation lengthens it instead
    of shortening it.
- Without the slot twist (`L = 1`) the critical length would be `K`, and Li-style reflection
  would make P1 easy. **The slot twist creates the dead zone.**

**Three further mismatches with Li's toolkit.**
1. *Twisted multiplicativity instead of Hecke relations*:
   `g̃(nm) = g̃(n)g̃(m)·(n/m)₃^{±1}`. Inflating by a prime changes the coefficients by a cubic
   character, so the copies are not exact.
2. *The Patterson bias*: `Σ_{N(n)≤X} g̃(n) ≈ c·X^{5/6}`, a main term rather than square-root
   cancellation (the cubic theta series has a pole).
   - This is Li's footnote problem: dropping primitivity creates main terms.
   - In the 7/8 paper it is why the plain fourth moment with slots must *amplify by sixth powers*
     (exchange rate 6). That gives the slot cost `6κ ≈ 3` instead of 2.
   - A fourth moment with slots that subtracts the bias exactly would be worth about 7e-4 in θ
     (`../barriers/README.md`).
3. *Uniformity in the slot twist* `P`, i.e. in a second family parameter.

**In one line.** Li and Shen–Stucky beat the ε at the balanced point, in families whose critical
length equals their size. We need to beat the N-term past the balanced point, in a family whose
critical length is pushed far beyond its size by the slot twist. Every positivity step, inflation
included, re-creates the N-term there (`../P1_PROBLEM.md`). The statement needed is
Lindelöf-on-average, or a stable-rank bound, for twisted metaplectic central values. That is open
even for `GL(2)`.

**The parallel worth remembering.** Li's prime-square inflation `m ↦ mp²` is the quadratic twin
of the 7/8 paper's sixth-power amplification `u ↦ u·a⁶` (copies of a character by its kernel
powers). The exchange rate is 2 there and 6 here; 6 is rigid (Kummer).
