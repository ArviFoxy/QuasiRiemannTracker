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
    signal channel `k = a⁶e₀`. The singular value of the whole matrix is at the edge
    `(√R + √C)²`, about 4 times the diagonal at `R ≈ C`. A bias of this size hides inside that
    constant.
  - **Direct test** (`gauss_bias.py`, logs `gauss_bias_U20000*.log`).
    - Setup: rows are primary primes with `N(π) ≡ 1 (36)`, so the unit symbols are 1 and
      reciprocity has no signs. The dual form is compared for `b = conj(g̃)` and for random
      unimodular `b`.
    - Results (`U = 2·10⁴`, 326 rows):

      | `N` | `conj(g̃)` | random |
      |---|---|---|
      | 1500 | 1.11 | 0.995 ± 0.05 |
      | 5000 | 1.18 | 0.991 ± 0.03 |
      | 15000 | 1.08 | 0.998 ± 0.014 |

    - `g̃` without conjugation and the twisted versions sit at or below random. At `U = 10⁴`,
      `N = 6000` the excess is 1.13 against 0.978 ± 0.010.
    - So a Gauss-sum bias is visible, at 2–7σ, but it is 5–10 times smaller at these sizes than
      the crude constant of the heuristic.
  - **Conclusion.** (A) for general coefficients is heuristically false on `(U^{4/5}, U]`. That is
    de Faveri's sharp term, and the `A^{5/6}B^{1/3}` term probably makes it fail past `U^{1/2}`.
    The edge-level numerics do not establish (A). The asymptotic claim is a heuristic, not a
    theorem.
- **The atom, localized.** At the binding point the rough core is round 10's adversary (three
  primes of size `U^{0.385}`). The agent restated it as a sixth moment with no `μ`:
  `Σ_u |Σ_{p~P} ψ_u(p)p^{−s}|⁶ ≤ U^{1.129−η}(E|Q|²)³` with `P = U^{t/3}`.
  - **Caveat (added here).** This is harder than the Möbius moment, not equivalent to it.
    - Amplification reaches `U^{1/6}D^{5/6}` only because the full family's moment at length `D`
      is diagonal for **Möbius** vectors (the inverse moment, through theta reflection).
    - For the prime cube `Q³` the general sextic sieve has the bias term `D^{7/6}` at `V = N = D`.
      So even `U^{1.129}` is unknown for this sixth moment.
  - The Möbius structure is essential, consistent with round 10 §5.

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

## 3. Verification and the follow-up submission

- **Packed certificates.** The HIGH and sector certificates now run in packed integer arithmetic.
  The face-family certificates take about 168 s of kernel time, against about 2600 s in PR 73
  (`../verification/AUDIT_FOLLOWUP.md` §6–8).
- **The submission package.** The single-stage follow-up is packaged as
  `arvi-single-stage-20261025` on branch `submission-single-stage-20261025`. It is not posted.
  - Value: 2186813/2500000 = 0.8747252, which is 3.7e-6 below PR 73.
  - Simplification: no seed step, no intermediate return and no PR 67 re-proof (−38% export
    bytes), plus about 15× less kernel time in our certificates.

