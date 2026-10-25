# Literature check (2026-10-24): can any known result move the binding atoms?

Scope: published or preprint results that could strengthen the three analytic bottlenecks of the
argument:
- **B1**, the marked inverse moment's column branch (slot cost 2);
- **B2**, the long Möbius moment beyond sixth-power amplification;
- the **zero-detection/count** step (large values).

Statements were checked against the primary PDFs unless marked [secondary]. Several are 2026
preprints that have not been refereed.

Bottom line: **no known result moves B1 or B2, and no large-values theorem exists for these
families.** The existing tools are the state of the art. Xu–Sang (2610.17675) independently arrive at
exactly our unmarked three-line count (exponent 7/12 at σ = 3/4), built from the same two lemmas.

## Origin of the bottlenecks

OpenAI, "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8" (GitHub openai/math):
- Lemma 17.1 is the inverse moment (B1).
- Lemma 17.6 is the long Möbius moment by u ↦ u·a⁶ (B2): Σ_{Nv≤H} sup|M_v|² ≪ H^{1+ε} for
  H ≥ D^{1+c}, then P = (H/U)^{1/6}.

Follow-ups import both unchanged: Xu–Sang 2610.15291, and Liu 2610.12234 / 2610.26835.

## Results and verdicts

**Dunn–Radziwiłł** (arXiv 2109.07463; Ann. Math. 200 (2024)), Patterson's conjecture.
- Corrected cubic large sieve (Prop 9.1, which subtracts the Patterson bias) and Type II estimates
  for g̃(ab) (Prop 10.1). The Type II estimates are non-trivial for X^{1/3+ξ} ≤ B ≤ X^{1/2−ξ}, with
  saving w^{9/20} or X^{ρ/2}, ρ < 1e-4 not explicit.
- The coefficient class C_η and the Type I inputs need GRH-type hypotheses for Möbius-like
  sequences.
- **Not usable**: B1 averages over cubic twists by a cubic modulus; for B2 the Möbius coefficients
  would need GRH.

**Heath-Brown** (Israel J. Math. 120 (2000)).
- Σ_{Nc≤X} g̃(c)Λ(c) ≪ X^{5/6+ε} unconditionally.
- Cubic large sieve (M + N + (MN)^{2/3}) for squarefree variables; it is sharp, and the extremal
  vector is the Gauss-sum vector itself.
- **Not usable.**

**Twisted Gauss-sum mean values.**
- David–de Faveri–Dunn–Stucky, 2410.03048: cubic twists, Σ_m |ψ(hm, s)|² ≪ N(h)^{1/2}M^{1+ε}.
- David–Dunn–Hamieh–Lin, 2306.11875 (quartic, over Q(i), quadratic twists):
  Σ_{Nα≤u} μ²(α)|h(½+ε+it; α)|² ≪ u^{3/2+ε}. That is u^{1/2} below convexity; Lindelöf on average is
  not proved. This is the closest template for B1.
- A cubic analogue at u^{3/2} would give N·K^{3/2}, a saving only for K ≤ N^{2/3}. In the MI binding
  child (K = Z^{0.742}, N = Z^{0.871}) that is not enough. This matches `../lean-lab/MIBranches.lean`:
  the slot primes stay in the conductor.

**OpenAI, "An unconditional first moment for cubic Gauss sums"** (GitHub, 25 Sep 2026).
- Claims Patterson's asymptotic unconditionally.
- Prop 4.1 beats the cubic sieve for prime-convolution coefficients, but only near two narrow
  configurations, with non-explicit η. The only unconditional "structured beats generic" result
  found. Cubic, not sextic.

**De Faveri, n-th order large sieve** (2610.04045).
- Statement: A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n} (n-th-power-free variables). It is sharp
  (Xu–Sang 2610.17675, Thm 1.1).
- For B2 at (U, D) it gives U^{1/3}D^{5/6}, worse than amplification's U^{1/6}D^{5/6}.
- **Not usable**: any gain must use the Möbius structure.

**Guth–Maynard in the q-aspect.**
- Chen–Gupta–Li, 2507.08296: a single modulus q, using the full character group.
- No version exists for Σ_{q≤Q}, cubic, sextic or Hecke families.
- **Not usable**: B1 and B2 are mean values, not large values.

**Zero density for cubic/sextic families.**
- Blomer–Goldmakher–Louvel, IMRN 2014: g = 8(1−σ)/(7−6σ).
- De Faveri, Cor 1.5: 8/11 at σ = 3/4.
- Xu–Sang, Thm 1.2: (31−32σ)/(21−12σ), 7/12 at σ = 3/4. It equals our unmarked count
  R = 1 − 10δ/(15−6δ) at δ = 2σ − 1, and is built from Lemma 17.6 and the plain fourth moment.
- Our marked count (p = 1/2) is below all of these.

## Leads worth keeping

1. A cubic analogue of DDHL's quadratic-twist mean value, as a possible route to B1. Insufficient
   at the binding point even at exponent 3/2.
2. OpenAI's unconditional cubic first moment, Prop 4.1, as the only unconditional example of
   structured coefficients beating a higher-order sieve. Its sextic or Möbius analogue would bear on
   B2.

Extracted texts are in the session scratchpad (not committed): Dunn–Radziwiłł, Heath-Brown,
David–de Faveri–Dunn–Stucky, DDHL, de Faveri, Guth–Maynard, Chen–Gupta–Li, Baier–Young,
Blomer–Goldmakher–Louvel, Gao–Zhao, Louvel.

## Additional sweep (2026-10-25)

**de Faveri–Dunn–Hoffstein, 2607.07911** (Non-orthogonality of the cubic and quartic large sieves
via Rankin–Selberg).
- Thm 1.1, over `Q(ζ₃)`: the cubic large sieve's operator norm is `≫ (AB)^{−ε}(A + B + (AB)^{2/3})`
  for all `A, B`. So the `(AB)^{2/3}` term is sharp, caused by the Gauss-sum bias.
- (2.10): Lindelöf on average in the cubic twist aspect, `Σ_{N(a)≤A}|ψ^{(3)}(a, 1+ε+it)|² ≪ A^{1+ε}`,
  via Zagier's Rankin–Selberg regularization.
- **Not usable.** P1 needs quadratic twists `χ_k³` of the theta coefficients in a family of size `K`
  below the critical length `KL`, i.e. a thin family. The cubic sieve part of the hybrid norm is
  in its diagonal regime at the binding (`v ≥ 2z_a`).

**Diaconu–Ion–Paşol–Popa, 2607.27131** (Second moment of `r`-th order Hecke L-functions).
- Asymptotic first and second twisted moments of `L(1/2, χ_a)` over squarefree `a`, for fields
  containing `μ_{2r}`, `r ≥ 3`, via Weyl group multiple Dirichlet series.
- For `r = 3` over `Q(√−3)` the error is `X^{5/6+ε}` unconditionally (`X^{3/4}` under GRH),
  recovering David–de Faveri–Dunn–Stucky.
- **Not usable.** Our binding mean values are the inverse (Möbius) moment past its diagonal and
  the marked column branch. Neither is a moment of `L` itself, and the plain moments are already
  diagonal.

**QRH follow-ups.** Sang 2610.15291 (0.8748867) and Liu 2610.12234 (0.874957) are far above the
tracker record, and no newer follow-up was found.

