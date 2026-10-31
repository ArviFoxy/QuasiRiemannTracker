# Orders: why the baseline uses sextic characters over Z[ω], and what other orders would need

The target is a zero-free half-plane for Dirichlet L-functions over ℚ. The Eisenstein field and the sextic order are
the baseline's choice of detector family. `LOG.md` ("Why order 6") derives that choice from one identity: Poisson in
the rows must turn Möbius-weighted Gauss sums into the coefficients of an automorphic object with an explicit
reflection. This directory tests that identity numerically, for order 6 (and 3) over ℤ[ω] and order 4 over ℤ[i].

## `gauss_mobius.py field X`

- **Gauss sums.** For every primary squarefree ideal c of norm ≤ X (split and inert primes, ramified prime excluded;
  for ℤ[ω] also the inert prime 2, so c is coprime to 6) it builds the normalized n-th order Gauss sum g̃(c) by
  twisted multiplicativity. Prime Gauss sums are exact O(p) sums through a primitive root, and inert primes are done in
  F_{q²}.
- **Convention.** The additive character is e(Tr(x/(δc))), with δ = √−3 for ℤ[ω] and δ = 2 for ℤ[i]. Generators are
  primary: ≡ 2 mod 3 (the baseline's convention, renormalized after each product) or ≡ 1 mod 2 + 2i.
- **Checks.** Twisted multiplicativity agrees with the definition on composite moduli to 1.6e-15.
- **Output.**
  - Per-class partial sums (classes mod 4 × mod 9, or mod 16) of several weights, with their log-log growth.
  - The identity checks: is the ratio below constant on each class?
- `α(c) = c/|c|` is the angular Grössencharacter (`angularFactor` in the baseline).

## Results at X = 3·10⁵ (logs `gauss_mobius_eis_X300000.log`, `gauss_mobius_gauss_X300000.log`)

| family | weight | RMS slope | reading |
|---|---|---|---|
| ℤ[ω] | g̃₃ | 0.824 | Heath-Brown–Patterson main term X^{5/6} |
| ℤ[ω] | μ·conj g̃₆·α | 0.824 | identical to g̃₃ class by class |
| ℤ[ω] | g̃₆ | 0.62 (max 0.72) | sextic main term X^{2/3} emerging |
| ℤ[ω] | μ·conj g̃₆, μ·conj g̃₆·conj α | 0.28–0.30 | cancellation stronger than random |
| ℤ[i] | g̃₄ | 0.739 | Kubota–Patterson main term X^{3/4} |
| ℤ[i] | μ·conj g̃₄·α | 0.739 | identical to g̃₄ class by class |
| ℤ[i] | μ·conj g̃₄, other angular powers | 0.34–0.52 | no main term |
| both | random phases | 0.50–0.53 | |

**Identities [numerical, exact to 1e-15 on every class and every squarefree modulus].**
- ℤ[ω]: μ(c)·conj g̃₆(c)·α(c) / g̃₃(c) depends only on the class of c. At primes this is the baseline's Lean identity
  `localGamma_one_two_full_signal` (γ₁γ₂ = −α·G). The numerics show it extends to every squarefree modulus. So the
  Möbius sign is absorbed into a **cubic** Gauss sum, a coefficient of Kubota–Patterson's cubic theta (Patterson).
- ℤ[i]: μ(c)·conj g̃₄(c)·α(c) / g̃₄(c) depends only on the class of c. This is the Jacobi-sum evaluation
  g(χ)² = J(χ, χ)·g(χ²), with J(χ, χ) = −χ(−1)·π and a trivial quadratic Gauss sum. The minus sign absorbs μ(p) = −1.
  So the Möbius sign is absorbed here too, but into the **quartic** Gauss sum itself.

**Reading.**
- Both families absorb the Möbius sign. The difference is where it lands.
  - The cubic Gauss sums are the cubic theta's coefficients, which have an explicit reflection.
  - The quartic Gauss sums are conjecturally the *squares* of the biquadratic theta's coefficients at primes:
    Patterson's quartic conjecture, refined by Eckhardt–Patterson (Proc. LMS 1992) and studied by Bröker–Hoffstein.
    They are not the coefficients themselves.
- This corrects the earlier wording in `LOG.md` that "the Möbius sign survives" for order 4. It is absorbed, but the
  landing object has no explicit theta reflection.
- In both families, Möbius-weighted sums without the matching angular factor cancel better than random phases.
  Möbius vectors avoid the theta spike in the quartic family as well as in the sextic one. That is the property the
  baseline's inverse moment uses.
- **What a quartic detector needs.** It would start from 1 − 1/8 = 7/8 instead of 11/12. It needs a reflection for
  sums of quartic Gauss sums, and power savings for those sums twisted by Grössencharacters.
  - The Kubota–Patterson series has a functional equation for every order.
  - Patterson (1987) gives estimates for general Gauss sums at prime arguments. David–Dunn–Hamieh–Lin (arXiv
    2306.11875) improve them for quartic Gauss sums, using the quadratic large sieve over ℚ(i) and Suzuki's
    evaluation of quartic theta coefficients at squares.
  - Whether these are strong enough for each place where the baseline uses the cubic theta is open.

## The signal identities transfer too (exact, every squarefree modulus)

The baseline's signal channel uses (4.7), `γ₁ = γ₂²G` and `γ₂³ = μα` (`barriers/README.md`, atom 4). With them, the
dual coefficient at the sixth-power frequencies becomes the target's own `1/L`. `gauss_mobius.py` checks the analogues
on every squarefree modulus; each ratio below is constant on classes.

| family | identity | status |
|---|---|---|
| ℤ[ω] | g̃₆ = g̃₃²·(class unit) | exact |
| ℤ[ω] | g̃₃³ = μ·α·(class unit) | exact: the cube of the cubic Gauss sum is Möbius times a Hecke character |
| ℤ[i] | g̃₄² = μ·α·(class unit) | exact: the quartic signal identity, a square instead of a cube |
| ℤ[i] | g̃₄⁴ = α²·(class unit) | exact |

## What a quartic detector would need (map, heuristic)

| ingredient | sextic (baseline) | quartic analogue | status |
|---|---|---|---|
| Möbius absorption | μ·conj γ₁·α ∝ γ₂ (cubic) | μ·conj γ₄·α ∝ γ₄ | both exact (numerics) |
| signal identity | γ₂³ = μα | γ₄² = μα | both exact (numerics) |
| automorphic carrier of the row | cubic theta θ₃, coefficients ∝ γ₂ (Patterson) | biquadratic theta θ₄; τ₄(p)² = 2γ̃₄(p) | Patterson's biquadratic conjecture, open |
| theta bias = signal | 1/12 | 1/8 | follows the exchange rate |
| starting bound | 11/12 | 7/8 | |
| slot cost, long line, plain descent | rate 6 | rate 4 | the chain would have to be recomputed |

- In every case known or conjectured, the n-fold theta's coefficient at a prime is an n-th root of the Hecke
  character −α(p), up to class constants:
  - n = 3: τ₃ ∝ γ₂, so τ₃³ ∝ μα (Patterson);
  - n = 4: τ₄² = 2γ₄ and γ₄² ∝ μα (Patterson's conjecture);
  - n = 6: τ₆² is related to cubic Gauss sums (Chinta–Friedberg–Hoffstein, Bröker–Hoffstein).
  - "Explicit" (n = 3) means the root is itself a Gauss sum. For n = 4 and 6 only the square of the root is one, so
    a sign stays ambiguous.
- So the quartic route needs one new theorem: the biquadratic theta conjecture, or a probe built from the 4-fold
  Eisenstein series' Gauss-sum coefficients instead of θ₄. On top of that, every analytic input of the chain would
  have to be redone at exchange rate 4. That is a new architecture, not a modification of the current proof.

## Which orders absorb the Möbius sign into a single Gauss sum (classification, derived)

For order `n = 2k`, Hasse–Davenport against the quadratic subcharacter gives
`g(χ^{n−1}) ∝ g(χ^{n−2}) / g(χ^{k−1})` up to class constants. Absorption into one Gauss sum needs the right-hand side
to collapse.
- **n = 4 (k = 2):** `g(χ²)` is quadratic, so trivial up to class, and `g(χ³) ∝ 1/g(χ)`. It lands on the quartic
  Gauss sum itself (exact numerically, above).
- **n = 6 (k = 3):** `g(χ⁴) ∝ conj g(χ²)`, so `g(χ⁵) ∝ conj g(χ²)/g(χ²)`. With `γ₂³ = μα` this is the cubic
  Gauss sum (exact numerically, above).
- **n = 8, 10, 12, …:** a ratio of two distinct Gauss sums remains: orders 4 and 8 for n = 8, two quintic ones for
  n = 10, orders 6 and 12 for n = 12. There is no single-sum absorption.
- **Odd n** (no quadratic subcharacter) and **n = 2** (no Jacobi sum carrying α): the Möbius sign stays. For n = 3,
  `μ·conj g̃₃·α = μ·g̃₃²`, and the sums of μ·g̃₃ show no main term (slope 0.45 at 3·10⁵).

So exactly two orders absorb the Möbius sign into one Gauss sum: 4 and 6. Only 6 lands on the coefficients of an
explicit theta, the cubic one. This refines `LOG.md`'s three conditions: the quadratic subcharacter and the quadratic
leftover twist hold for n = 4 as well, and only the explicit-theta condition fails there.

## Rank versus explicitness: why the baseline sits at (n, r) = (3, 2) (synthesis, literature + heuristic)

- **Kazhdan–Patterson.** On the n-fold cover of GL(r), the theta representation is generic for n ≥ r and has a
  unique Whittaker model only for n = r or n = r + 1 (the latter for special covers).
- **Bump–Hoffstein and later work.** For n = r the theta's Whittaker coefficients are n-th order Gauss sums: cubic
  on GL(3), and similarly for every n ≥ 2.
- So explicit automorphic carriers exist for every order, at rank about n. That is the "something for every n".
- **The detector also needs an efficient reflection.** The baseline's theta reflection is GL(2) duality: a sum of
  length N becomes one of length about C²/N. A GL(r) Voronoi formula gives about C^r/N, which is much weaker for
  r ≥ 3.
- Explicit **and** GL(2) means n ∈ {2, 3}. Absorbing the Möbius sign into that carrier forces the row order to be 6,
  because 6 lands on cubic Gauss sums (the classification above). So the sextic family over ℤ[ω] is the unique
  power-residue detector with an explicit GL(2) carrier.
- **Quartic options** (starting bound 7/8):
  - (a) the GL(2) biquadratic theta, which needs Patterson's conjecture;
  - (b) an explicit higher-rank carrier, the 4-fold theta on GL(3) or GL(4), which pays the weaker GL(3)/GL(4)
    reflection. The next section prices both: (a) does not help even with the conjecture, and (b) loses the
    whole head start.

## What the base step needs, and the price of rank (OpenAI, Oct 5 2026 preprint, §2 Steps 2–5)

[derived from the preprint's outline; the rank count is a heuristic, not a theorem]

The 11/12 base runs in three moves.
1. **Copies.** `χ_n(u p⁶) = χ_n(u)` puts about `H^{1/6}` copies of the target sum `A₁(D)` among the rows `A_u(D)`,
   `N(u) ≤ H`. The mean square `Σ_u |A_u(D)|² ≪ D^{1+ε} H` then gives `|A₁|² ≪ D H^{5/6}`.
2. **Poisson in the row.** The dual columns carry `μ(n)γ₋₁(n) ∝ conj α(n) γ₂(n)`, and the mean square reduces to
   `Σ_{N(h) ≪ 𝓗} |B_h(D)|² ≪ D²` with `𝓗 = D²/H` and
   `B_h(X) = Σ_n conj α(n) γ₂(n) ξ(n) χ_n(h) U(N(n)/X)`.
3. **Theta transformation.** By Patterson (Thm 8.1), `γ₂(n)` is the coefficient of Kubota's cubic theta *at
   index n*: `c_θ(nb³) = 3^{5/2}|b| conj χ_n(λ)² γ₂(n)`. Expanding the twist additively and using automorphy
   gives dual sums of length `N(h)²/X`. At each `p | h` the Fourier factor `χ_p^{−1}` and the theta multiplier
   `χ_p^{−2}` combine to `χ_p³`, a quadratic character. So the dual mean square is the quadratic large sieve
   (Heath-Brown, Goldmakher–Louvel), with the sharp factor `M + L`. That gives
   `Σ_h |B_h(X)|² ≪ (𝓗X)^ε (X𝓗 + 𝓗²)`, which is `≪ D²` at `X = D`, `𝓗 ≤ D`.

**Quartic family.** Move 1 gives `1 − 1/8 = 7/8`, and move 2 lands on `conj α(n) γ₄(n)`. Move 3 needs a GL(2)
automorphic form whose coefficient at index `n` is the quartic Gauss sum of modulus `n`.
- No such form is known. The theta on the 4-fold cover of GL(2) has no unique Whittaker model
  (Kazhdan–Patterson). Patterson's conjecture makes its prime coefficients square roots: `τ₄(p)² = 2γ̃₄(p)`.
- Even granting the conjecture, `B_h` would be a twisted sum of `τ₄(n)²`. That is a Rankin–Selberg-type object, a
  rank-4 carrier, not a GL(2) one.
- The quartic Kubota series `Σ_c g₄(h, c) N(c)^{−s}` has a functional equation, but its dual coefficients are
  again quartic Gauss sums with a quartic twist. So the dual mean square is the same quartic large-sieve problem:
  Poisson twice is the identity. De Faveri's general bound (`A + B + A^{3/4}B^{1/2} + A^{1/2}B^{3/4}`) gives
  `D^{9/4}` at `A ≈ B ≈ D`, against the needed `D²`.
- If a GL(2) realization existed, the twist arithmetic could work: a quartic multiplier gives `χ_p^{−1}χ_p^{∓1}`,
  quadratic for one conjugation (the analogue of the cubic case's `χ_p^{−3}`) and trivial for the other, which would
  be useless. Which one occurs is fixed by the conjugation of the absorbed Gauss sum. Either way, the first obstruction
  is the missing form.

**The price of rank.** Suppose the absorbed Gauss sums were the coefficients of a carrier of rank `r`, with flat
coefficients and the best possible leftover twist (quadratic, so the sharp sieve `M + L`). A GL(r) reflection
sends a sum of length `X`, twisted mod `h`, to one of length `N(h)^r/X`, so
- `Σ_h |B_h(X)|² ≈ X𝓗 + 𝓗^r`;
- `≪ D²` needs `𝓗 ≤ D^{2/r}`, i.e. `H ≥ D^{2−2/r}`, which is also the optimal choice of `H`;
- the base exponent is then `θ₀ = (1 + (2 − 2/r)(1 − 1/n))/2`, for family order `n` (copies at `n`-th powers).

| carrier rank `r` | `n = 2` | `n = 3` | `n = 4` | `n = 6` | `n = 8` |
|---|---|---|---|---|---|
| 2 | 3/4 | 5/6 | 7/8 | **11/12** | 15/16 |
| 3 | 5/6 | 17/18 | 1 | 19/18 | 13/12 |
| 4 | 7/8 | 1 | 17/16 | 9/8 | 37/32 |

- At rank 2 this is `1 − 1/(2n)`, the baseline.
- A rank-3 carrier saves something only for `n < 4`, and a rank-4 carrier only for `n < 3`. In general
  `n < (2r − 2)/(r − 2)`.
- The only orders that absorb Möbius into one Gauss sum are 4 and 6 (classification above). The explicit quartic
  carriers have rank 3 or 4, so they give `θ₀ ≥ 1`: **no saving**. The head start of 1/24 is lost entirely, not
  partly.
- So within this architecture the sextic family over ℤ[ω] with the cubic theta is optimal, not just the only
  explicit option. A quartic gain needs new mathematics of a specific kind: a GL(2)-type summation formula for
  quartic Gauss sums at index `n` that leaves a quadratic twist. Patterson's conjecture alone does not give one.
- **Larger fields.** For `K ⊇ ℚ(ζ₃)` of higher degree, the sextic argument runs the same way in norms and gives
  the same exponents. Its infinite unit group adds work and buys nothing. `ℚ(ζ₃)` is the smallest field carrying
  the sextic residue symbol. [heuristic]
