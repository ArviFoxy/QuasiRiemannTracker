# Where the method is pinned (2026-10-24)

This note collects, in one place, the four analytic exponents that bind the current argument at
θ ≈ 0.87472, where each one comes from, how far it would have to move for a 1e-5 gain, and the
reasons it does not move with the tools in the papers. Details and dead ends are in `../LOG.md`.
Numbers come from `../atom-targets/` (float LP model) unless marked exact.

## The four atoms

**1. Reflected-energy slot cost 2.** Paper Lemma 14.3: `T_d = 2H + 2z_a − N_*`.
- Origin: a divisibility mark `p | A` on the cubic-theta index puts `p` into the cusp denominator
  `c`. The reflection at `a/c` rescales by `c²`, and the hybrid norm already saves the whole slot
  length in the column branch.
- It binds in three places:
  - the physical probe's marked energy `x + y + ℓ ≤ 1` (`dθ/dε = −0.0628`; for −1e-5 the cost must
    fall `2 → 1.99905`);
  - the count's marked inverse moment `r + 2z ≤ 1` (for −1e-5: `2 → 1.995`);
  - the source chain's HIGH inverse cap `(Q − r)/2`.
- Why it does not move: removing the excess needs an almost diagonal quadratic large sieve at dual
  length `K^{1+η}` for reflected Gauss-sum coefficients, i.e. Lindelöf-quality bounds for twisted
  cubic theta series. Amplifying the residual rows by squares fails on the redundancy term of the
  full family. Probe redesigns either lose the sextic slot factor (cube marks) or pay more than they
  save.

**2. Sixth-power exchange rate 6.**
- Origin: `G(u, hp⁶) = G(u, h)`. Sixth powers are the full invariance group of sextic Gauss sums
  and sextic symbols, and they have density `X^{1/6}` among elements of norm `≤ X`.
- It binds in three places:
  - the long Möbius moment `(1+5r)/6` (for −1e-5: lower by `2.7e-4` at `r ≈ 1.155`);
  - the plain descent's slot cost (`Λ ≈ 6qB`);
  - the LOW amplifier denominator `1 − 6qB₀/Λ₀ ≈ 0.007`.
- Why it does not move: exact invariance cannot use a denser multiplier set. Twisted
  multipliers (`p³`, `p²`) orthogonalize rather than amplify. The long moment beyond the family is
  equivalent to zero-density input, and bootstrapping with the count itself is circular exactly at
  the binding `δ ≈ 0.45–0.5`.

**3. HIGH density floor `q ≥ 1/2`.**
- Origin: the HIGH count's gate `H_ν + G > f` at `ν = q`. Below `ν = 1/2` the gain `G` (itself
  pinned by atoms 1–2) no longer covers `H_ν`.
- The chain's fixed point is `Λ → 6qB ≈ 3B`. Lowering the floor to 0.45 gains only `5·10⁻⁷`
  (exact).

**4. Sextic theta bias `c_g = 1/12`.**
- Origin: the Gram estimate's exceptional frequencies `k = a⁶e₀`. With the exact correlation
  (Lemma 13.3) both complete column means survive iff `v_p(k) ≡ j_p − 1 (mod 6)` at the S-primes,
  so main terms exist for an S-supported `e₀`.
- Mixtures of probe characters give only positive diagonal main terms. For −1e-5 the bias term must
  become `P_a^{1/6 − 2.5e-4}`.

## What is LP-tight

Given these four inequalities, every recombination tried is no better:
- Hölder between witnesses, joint numerator × witness moments (they reproduce Cauchy–Schwarz on
  affine branches), pointwise vs fourth-moment numerators, and witness-weighted numerator bounds;
- multiple or second-order detectors, smoothed mollifiers, and covering arguments over cutoffs;
- face selection, re-feeding, `h`, `z₀`, caps and windows.

The exact pipeline with every known refinement (Lemma F, fine pivots, density floor) is at
θ* = 0.8747257, against the next milestone of 0.8747189.

## What would move it

| new input | effect |
|---|---|
| Lindelöf-quality mean values for cubic Gauss sums twisted by quadratic characters (column branch beyond the diagonal) | atom 1, all three places |
| a Möbius Type II estimate beyond the diagonal for sextic families, or any zero-density input stronger than the count itself | atom 2, long branch |
| a plain fourth moment with slots that subtracts the Patterson bias instead of amplifying | atoms 2 and 3 on the plain side; slot cost 2 there would lower the count `R` from 0.6047 to about 0.5996, worth about `7·10⁻⁴` in θ |
