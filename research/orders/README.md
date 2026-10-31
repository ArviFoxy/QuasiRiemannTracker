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
