# Round 11 (2026-10-25): after the single-stage follow-up

Bar: unchanged. No upstream PR after #73 (checked 2026-10-25), so the milestone is ≤ 0.8747189 and
6.1e-6 is still needed below the face family's 0.874725 (0.8747252 at K = 9/2).

## 1. What binds in the return at θ* (K = 9/2 faces)

The return was run just below θ* (θ = 8747251/10^7, h = 401/500, global mode):

- **Receipts.** All positive except the guard `source_lambda_low` (`Λ_P − 3 = 3.0e-7`). That guard
  is worth at most 1e-7 (`../LOG.md`, "Last checks on the face-family return").
- **Next receipts.** `principal_z` 8.7e-5, `incumbent` 5.5e-4 (the 7/8 cap), `source_C_cap` 3.0e-3,
  `floor` 3.5e-3.
- **Covers.**
  - `old_small`, `old_peak`, `old_switch`, `new_switch` and `new_kink` cover with positive
    coefficients (min 1.2e-3).
  - **`new_top` fails** at the box `δ ∈ [0.453421, 0.453426]`, `p ∈ [0.499996, 1/2]`.

So the binding inequality is the return polynomial itself, the high-side balance
`θ ≥ R₀ + E_b + (3/4)·d·N/J`, at `d = h`, `δ ≈ 0.4534`, `p = 1/2`, with the count `N/J` from the
count face C. No receipt constant (the explicit constants of `floor`, `small_row`, `principal_*`,
…) is binding, so sharpening a lemma constant in the return cannot help. This confirms the
atom-level picture (`../STRUCTURE.md` §7).

## 2. Atom 2, fresh look (agent, done): no power saving, but a sharper localization

A fresh-perspective agent looked at atom 2 in its cleanest form: the sextic Möbius mean value past
the diagonal, with target `λ ≥ 0.16834` at `D = U^{1.155}`. Notes: `sextic_moment_notes.md`,
scripts `factor_split_mass.py` and `ls_constant_support.py` with their logs.

- **Twist averaging (proved).** Averaging over cubic or quadratic twists is easy (`λ = 1/2` and
  `1/3`). But these are twists, not copies, and at equal conductor they are worse. Exact copies
  still need `a⁶`.
- **Thickened or sparse families, `t`- and `a`-averages (proved).** Nothing beyond copies.
  Product families dualize factor by factor, and averaging over `a` is amplification itself.
- **Bootstrap + grouping (conditional).** Use the global-strip bound
  `|block|² ≤ B^{0.749}·diag` on a sub-product of size `U^s`, `s ∈ [0.0031, 0.172]`.
  - This requires (A): a diagonal mean value for general coefficients up to length `U` on the
    dyadic family.
  - Given (A), 99% of the mass gains up to `U^{0.013}`. The rest, the `U^{0.172}`-rough core
    (about 1% of the mass), gains nothing. So the total saving is a constant, not a power.
- **(A) looked true numerically, but it is false past `U^{4/5}` (correction, same day).**
  - **The numerics.** The large-sieve constant of the actual dyadic family sits at the
    random-matrix edge (0.93–1.00 of `(√R + √C)²`, at `U = 3000` and `8000`). The agent read this
    as "no bias", because a `(RC)^{2/3}` term would be 2.6–3.6× the edge.
  - **The counterexample.** The bias that survives on dyadic rows comes from the sixth-power dual
    frequencies, not from small moduli.
    - Take `b_u = conj g̃₆(1, u)` on `u ~ U` (one residue class mod 4, so that the reciprocity
      signs are constant).
    - Poisson in `n` writes the dual form's off-diagonal as `(N/U²)Σ_h |Σ_u b_u g₆(h, u)|²`.
    - At `h = a⁶` the inner sum has no cancellation: `Σ_u √N(u) ≈ U^{3/2}`.
    - There are about `(U²/N)^{1/6}` such `h`, so the large-sieve constant is at least
      `N^{5/6}U^{1/3}`. That is de Faveri's `A^{1/3}B^{5/6}` term, and it exceeds `U` for
      `N > U^{4/5}`.
  - **Why the numerics missed it.** It is the same sixth-power-frequency mechanism as the probe's
    signal channel `k = a⁶e₀`. At `U = 8000`, `N ≈ U` it is about `N·0.6·U^{1/6} ≈ 2.7N`. That is
    within the constant of the edge `(√R + √C)² ≈ 4N`, so the numerics cannot separate it.
  - So (A) for general coefficients fails at least on `(U^{4/5}, U]`. The `A^{5/6}B^{1/3}` term
    (theta coefficients at the rows) probably makes it fail past `U^{1/2}`.
- **The atom, localized.** At the binding point the rough core is round 10's adversary (three
  primes of size `U^{0.385}`). There the problem is equivalent to a sixth moment with no `μ`:
  `Σ_u |Σ_{p~P} ψ_u(p)p^{−s}|⁶ ≤ U^{1.129−η}(E|Q|²)³` with `P = U^{t/3}`.

**What (A) would have been worth.** The source chain's faces certify that the plain fourth moment
with slots is diagonal on `m₁ + m₂ + Λz ≤ B`.
- (A) for general coefficients would give `B = 1`, `Λ = 1` directly: the product `S_{m₁}S_{m₂}Q_z`
  is a Dirichlet polynomial of length `U^{m₁+m₂+z} ≤ U`.
- The chain's end face is `(B, Λ) ≈ (0.957, 2.90)`. In the return, `Λ_P = 1` would roughly
  quadruple the numerator capacity `C`, worth about −2e-3 in θ.
- The general version is false (above), so only the restricted version could hold:
  - plain sums and slots, whose coefficients are far from the Gauss-sum vectors;
  - the unconditional range is `N ≤ U^{1/2}`, which gives the useless face `(1/2, 1)`.
- That restricted version is atom 1 again, since its dead zone is exactly where the slots break
  the plain reflection.
