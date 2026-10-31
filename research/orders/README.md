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
