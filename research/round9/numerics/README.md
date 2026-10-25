# Round 9 numerics: the long Möbius moment of the actual sextic family (2026-10-25)

`long_moment.py` computes, for the actual sextic family over `Z[ω]`:
- rows: primary, conservatively squarefree `u` with `N(u) ∈ [U, 2U)`, using round 7's builder;
- `M_u(D) = D^{−1/2} Σ_n μ(n)(u/n)₆ W(N(n)/D)`, over ideals `n` prime to 6 with `N(n) ∈ [D, 2D)`
  and a smooth bump `W`.

It prints the row average of `|M_u|²` divided by the diagonal `Σ_n μ(n)²W²/D`, for `D = U^t`.

**What it is for.** For `t > 1` the method's only bound is sixth-power amplification (7/8 Lemma
17.6). That bound allows the average to grow like `U^{(1+5t)/6 − 1}`, and the long line
`L(t) = 1/6 + (5/6 − ν)t` is the only input that moves the unmarked exponent `ρ(ν)` (`../README.md`
§1). Lindelöf on average predicts a ratio of about 1.

**Results** (`long_moment_U3000.log`, 778 rows):

| `t` | `D` | squarefree columns | ratio to diagonal | amplification allows | max row / diagonal |
|---|---|---|---|---|---|
| 0.600 | 122 | 35 | 1.077 | 1.00 | 5.97 |
| 0.800 | 605 | 168 | 0.909 | 1.00 | 5.75 |
| 1.000 | 3000 | 848 | 0.977 | 1.00 | 7.28 |
| 1.155 | 10377 | 2932 | 1.009 | 2.81 | 9.08 |
| 1.250 | 22202 | 6254 | 1.029 | 5.30 | 8.05 |

The long moment stays at its diagonal past `t = 1`, where amplification already allows a factor
2.8–5.3. At this scale there is no sign of the `(1 + 5t)/6` growth. So atom 2 looks like a
limitation of the method, as P1 did in round 7's toy models.

**Why a proof is hard.** Expanding,
`Σ_u |M_u|² = D^{−1} Σ_{n,n′} μ(n)μ(n′)W W′ Σ_u χ_n(u) conj(χ_{n′}(u))`.
- The off-diagonal is a Möbius bilinear form whose kernel is incomplete character sums of conductor
  up to `D² ≫ U`. Diagonal size past `D = U` needs square-root cancellation in that bilinear form.
- That is a correlation statement for `μ` twisted by the family, Chowla-type and on the wrong side
  of the parity barrier.
- Even the full family of Dirichlet characters to one modulus `q < N` needs Möbius correlations
  `Σ_{q|h} Σ_n μ(n)μ(n+h)` for this. Only averages over `q` (Barban–Davenport–Halberstam) avoid
  them, and a thin family has no such average.

**Larger run** (`long_moment_U8000.log`, 2076 rows):

| `t` | `D` | squarefree columns | ratio to diagonal | amplification allows | max row / diagonal |
|---|---|---|---|---|---|
| 0.800 | 1326 | 374 | 0.910 | 1.00 | 6.76 |
| 1.000 | 8000 | 2252 | 0.989 | 1.00 | 7.21 |
| 1.100 | 19652 | 5533 | 0.956 | 2.11 | 7.10 |
| 1.155 | 32216 | 9094 | 0.965 | 3.19 | 9.79 |
| 1.250 | 75659 | 21337 | 0.894 | 6.50 | 6.78 |
| 1.400 | 291290 | 82200 | 0.983 | 20.0 | 10.25 |

At `t = 1.4` the moment is at its diagonal (0.98) where amplification allows a factor 20. The
largest row is about 7–10 times the mean, about the maximum of 2000 exponential variables
(`log 2076 ≈ 7.6`), so no row is exceptional. The method's long line is a property of the proof,
not of the family.
