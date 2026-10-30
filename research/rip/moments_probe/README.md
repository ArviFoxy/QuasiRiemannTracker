# Moments probe: fixed-index cross-correlations (D2) and the sixth moment of short sextic sums (D4)

Two independent numerical probes over Z[ω] for `research/fresh-look/second/directions.md`, sections D2 and D4.
Everything here is new code, logs and results. No other repository file was touched, nothing was committed.
Evidence tag for all numbers below: [numerical]. Exponents carry finite-size errors; I quote the statistical error
calibrated on surrogates and recommend reading each exponent as ±0.1.

## 0. Results in short

**Probe A (D2, fixed-index cross-correlations).** For the 10 (and 20) smallest primary split primes P, with
S(k,P) = Σ_n g̃(n)(n/k)₂ conj((n/P)₃) W(N(n)/(K N(P))) and G_{PP'}(K) = Σ_{N(k)≤K} S(k,P) conj S(k,P'):

* The diagonal is the diagonal. G_PP(K) = (0.83…0.93)·R(K)·D_P(K), where R(K) = #rows (5184 at K = 2·10⁴, 12980 at
  5·10⁴) and D_P = Σ_n W²; i.e. G_PP ≈ 0.0196·K²·N(P), fitted growth K^2.02. No N-term at the self-dual point (also not
  at windows N = KN(P)/4 and 4KN(P)).
* The cross-correlations behave like independent random variables: ρ_{PP'} ≈ ζ·R(K)^{-1/2}, ζ = rms(ρ)√R = 0.94 for
  primes above different rational primes, flat in K (0.78 … 1.1). Fitted ρ ~ K^-η (K ≥ 700, up to 2·10⁴):
  **η = 0.57 [0.50, 0.64] (different norms), 0.47 [0.43, 0.56] (conjugate pair P, P̄), 0.56 [0.51, 0.63] (all pairs)**
  with 10 primes; 0.52 / 0.55 / 0.52 with 20 primes (190 pairs); K up to 5·10⁴: 0.54 / 0.52 / 0.54.
  Surrogates with i.i.d. random phases or random cube roots (same rows/columns/K-grid) give 0.49–0.52 ± 0.03–0.06.
  Random behaviour (η = 1/2) is not distinguishable from the data; η = 0 (no cancellation) is excluded by a wide margin.
* The conjugate pair (P, P̄) has ζ = 1.3…1.6, not 1: this is a trivial exact doubling (g̃(n̄) = conj g̃(n) gives
  S(k̄,P) = conj S(k,P̄), so G_{PP̄} is a sum of R/2 doubled terms and E|G_{PP̄}|² = 2·R·D_P D_P̄, ζ = √2·0.96); the
  symmetric surrogates give 1.26–1.36 ± 0.14.

**Probe B (D4, sixth moment of short plain sums in the thin sextic family).** Rows u: squarefree ideals of norm in
[B, 2B] prime to 6 (R ≈ 0.28 B), S_u = Σ_{n primary, N ≤ N(n) < 2N} (n/u)₆, N = B^m:

* **No N-term.** M₆ = Σ|S_u|⁶/(R N³) stays between 0.09 and 0.59 (typically 0.3–0.4) from B = 3000 to B = 1.5·10⁶ while N³/R grows up to
  4.4·10³ (m = 0.5), 2.2·10² (m = 0.43), 10⁷ (m = 0.8, B = 4.8·10⁴). The Dirichlet family mod a prime q ≈ R, run through the same
  code, has M₆ = N³/q + O(1) (3105 at B = 7.7·10⁵, m = 0.5); the thin family has M₆ = 0.38 (0.387 at B = 1.5·10⁶). Fitted N-term
  coefficient M₆ − M₆(mult. surrogate) = c·N³/R: c = (−1.5 ± 0.1)·10⁻⁵ (m = 0.5), (−6.5 ± 1.2)·10⁻⁵ (m = 0.43); negative, and
  10⁻⁵ of the full family's c = 1.
* **B-scaling.** Slope of log M₆ in log B (B = 1.2·10⁴ … 1.5·10⁶, 8 values) is +0.020 ± 0.006 at m = 0.5 and +0.029 ± 0.006 at
  m = 0.43, the same as for the random multiplicative surrogate (+0.031, +0.040), i.e. log-power growth of the diagonal; an N-term
  would give +0.50 and +0.29. Slope of log(actual/surrogate): −0.012 ± 0.006 (m = 0.5), +0.007 ± 0.006 (m = 0.43).
* **Relative to the surrogates.** actual/(random completely multiplicative μ₆ surrogate) = 0.98–1.00 for m ≤ 0.35, 0.95–0.98 for
  m = 0.43, 0.87–0.89 for m = 0.5 (B ≥ 1.9·10⁵), falling to 0.55 at m = 0.8. The deficit sits in the extreme tail (the real family has no
  row with |S|²/N above ≈ 4–6, the surrogate reaches 8) and in rows without small prime factors. It is the opposite sign of an N-term.
* M₄ behaves identically (M₄ = 0.30 at m = 0.5 for every B ≥ 1.2·10⁴, against N²/R = 3.54 and a full-family 5.8; actual/mult 0.96).

**Judgement.** Probe A: the weak form (X_fix) is numerically true with η₀ ≈ 1/2 and no visible dependence on N(P)N(P')
(log-slope of ζ² in N(P)N(P') = 0.10 [−0.04, 0.23] over a factor 130, so A ≈ 0); the data show nothing that makes the
problem look structurally hard, which says nothing about provability. Probe B: Lindelöf on average (ε₆ = 0 within ±0.02) holds for
the plain short sums for all m up to 0.8; the N-term of the full family is not forced in the thin family and is absent at these sizes.

## 1. Definitions (exactly what was computed)

Arithmetic and conventions are those of `research/round7/signal-processing/` (zw.py, build.py) and `research/rip/`
(zomega.py, zfamily.py); see §3 for what was reused and how it was validated.

**Probe A.** Primary = a + bω with a ≡ 2 mod 3, b ≡ 0 mod 3 (one generator per ideal prime to 3).
* Columns n: primary, split-squarefree (squarefree norm, all prime factors ≡ 1 mod 3), 1 < N(n) ≤ X (build.py columns).
* Rows k: the same set with 1 < N(k) ≤ K (build.py rows; squarefree, k = 1 excluded, never a square).
* g̃(n) = g(n)/√N(n), g(n) = Σ_{x mod n}(x/n)₃ e(Tr(x/(n√−3))); exact at primes, composites by
  g(c₁c₂) = conj((c₁/c₂)₃) g(c₁)g(c₂) (zw.GaussTable formula).
* P: the 10 smallest primary prime elements, ordered by (N, a, b): norms 7,7,13,13,19,19,31,31,37,37 (both conjugates of
  each rational prime are separate P); 20 primes: up to norm 79.
* S_K(k,P) = Σ_n g̃(n)(n/k)₂ conj((n/P)₃) W(N(n)/(c K N(P))), conj((n/P)₃) = 0 if P | n. Default c = 1 (the self-dual point
  N = K·N(P)) and W(u) = (1−u)₊; also W = (1−u)₊², W = exp(1 − 1/(1−u²)) (smooth bump), c = 1/4 and 4.
* G_{PP'}(K) = Σ_{N(k)≤K} S_K(k,P) conj S_K(k,P'), rows and window both rescaled with K (S is recomputed for every K).
  K grid: 14 (resp. 16) geometric points, 250 … 2·10⁴ (resp. 500 … 5·10⁴).
* ρ_{PP'}(K) = |G_{PP'}|/√(G_PP G_P'P'). For independent entries E ρ² = 1/R(K) (R(K) = #rows), so ζ := ρ√R = O(1) for
  random behaviour (η = 1/2) and ζ ∝ K^{1/2−η} otherwise.
* Diagonal prediction: D_P(K) = Σ_n W_P(n)² [P ∤ n], R·D_P (|g̃| = 1 so this is the n = m part of Σ_k|S|²).
* "Diag cross term": Dcross_{PP'} = Σ_n conj χ_P(n)χ_{P'}(n)W_P W_{P'}; R·Dcross is the n = m part of G_{PP'} (stored).
* Pair classes: conj = (P, P̄); diff = primes above different rational primes (G_{P̄P̄'} = conj G_{PP'}, so |ρ| depends only on
  the orbit under simultaneous conjugation); all.
* Fits: OLS of log(class-mean ρ) on log K over K ≥ 700 (≥ 1000 for the 5·10⁴ run); [lo,hi] = bootstrap over pairs
  (optimistic: pairs share primes). Alternative fits (rms ρ, ρ against R(K), dyadic-block Gram sums over K/2 < N(k) ≤ K,
  median single-pair slope) are in `logs/*.analysis.txt`.

**Probe B.** Rows u: squarefree products of distinct prime ideals of Z[ω] (split: both conjugates; inert q ≡ 2 mod 3 with
norm q²), coprime to 6 (so 2 and 1−ω are excluded), norm in [B, 2B]; this is the row set of zfamily.py (426 rows at
B = 1500, identical). χ_u(x) = Π_{π|u}(x/π)₆ with (x/π)₆ ≡ x^{(Nπ−1)/6} mod π (zomega.Prime.sym).
* S_u = Σ_{n primary, N ≤ N(n) < 2N} χ_u(n), N = B^m (real), all primary n (all ideals prime to 3 with norm in [N,2N)),
  zero when gcd(n,u) ≠ 1. Variant `--sources zfamily`: only the zfamily.py sources (odd squarefree norm prime to 3).
* M₄ = Σ_u|S_u|⁴/(R N²), M₆ = Σ_u|S_u|⁶/(R N³).
* Comparators at the same R, N and the same coprimality zeros:
  - **mult**: S_u = Σ_n f_u(n), f_u completely multiplicative on ideals with i.i.d. uniform μ₆ values at every prime
    ideal (including (2)); E|S|⁶ equals the diagonal count with coprimality mask. This is "Lindelöf on average" in its
    cleanest form. (Product of three primary elements is primary, so χ_u(n₁n₂n₃) = Πχ_u(n_i); diagonal pairs agree exactly.)
  - **iid**: i.i.d. uniform unimodular phase per (u,n).
  - **T/N^k**: exact counts T₄ = #{n₁n₂ = n₃n₄}, T₆ = #{n₁n₂n₃ = n₄n₅n₆} of ideals in the window, without the coprimality
    mask (so ≈ 10–25% above the mult surrogate).
  - **full**: the full family of Dirichlet characters mod a prime q ≈ R (q > 2N) on the integers in [N, 2N); exact count
    #{n₁n₂n₃ ≡ m₁m₂m₃ mod q}/N³ ≈ N³/q + O(1). This is the positive control of the diagnostic. It uses N terms per
    window (the ideal windows have ≈ 0.4 N), so compare via N³/q, not absolutely.
* z = (actual − mean(mult)) / √(se² + sd²/nrep), se = row-wise standard error of the actual (assumes independent rows;
  rows u and ū have S_ū = conj S_u, so true z are up to √2 smaller), sd = replica-to-replica sd of the surrogate.
* N-term coefficient c: weighted least squares of M₆(actual) − M₆(mult) = c N³/R through the origin.

## 2. Files

| file | purpose |
|---|---|
| `gauss_prime.c`, `fastgauss.py` | O(p) cubic Gauss sums at primes (C, OpenMP, compiled on first use into `$MP_BUILD`), snapped to the exact cube root of π/\|π\|; composites by the GaussTable twisted-multiplicativity formula with a one-pow cubic symbol |
| `test_fastgauss.py` | validation against `zw.gauss_direct` / `zw.GaussTable` |
| `probeA.py`, `analyzeA.py`, `summarize_A.py`, `test_probeA.py` | probe A: run, analysis, summary tables, end-to-end check |
| `probeB.py`, `tables_B.py`, `compact_B.py`, `test_probeB.py` | probe B: run (rows, symbols, surrogates, exact diagonals), tables/fits, checks |
| `diag_colcorr.py`, `diag_tail.py` | probe B diagnostics quoted in §5.4 (column correlation matrix of one window; tail/bin/row-type breakdown) |
| `run_A_batch.sh`, `run_A_batch2.sh`, `run_B_batch.sh` | the exact command lines of all runs |
| `logs/`, `results/` | verbatim logs and raw results (`.npz` G-matrices per K, `.json` moments) |

## 3. Reuse and validation

Reused unchanged: `Arith.elems` (columns/rows/primes), `quad_row`, `col_arrays`, `cubic_exp` (zw.py); `zomega.Prime.sym`
(inert primes and all validation of probe B). Replaced by faster equivalents, validated against the originals:
* prime Gauss sums: max |fast − gauss_direct| = 1.4·10⁻¹⁵ over all 768 prime ideals of norm ≤ 6000; 6 random primes near
  1.8·10⁶: ≤ 6·10⁻¹⁶; raw (unsnapped) C output has |g̃³ − π/|π|| ≤ 6.6·10⁻¹¹ (p ≤ 6000), snap distance ≤ 3.9·10⁻⁶ at
  p ≤ 1.85·10⁶ (the three cube roots are √3 = 1.73 apart, the nearest one is taken, so errors below 0.87 are harmless);
* conjugation shortcut g̃(π̄) = conj g̃(π): 1.5·10⁻¹⁵; composite columns vs `GaussTable.gt`: 1.9·10⁻¹⁵, vs `gauss_direct`:
  1.6·10⁻¹⁵; g̃(n̄) = conj g̃(n) for all 1556 columns ≤ 6000: 8·10⁻¹⁶;
* `test_probeA.py`: G_{PP'} from `probeA.py` vs a plain-loop reference using only round7 code, K = 150 and 600:
  relative difference 9·10⁻¹⁶ and 4·10⁻¹⁶; the same script checks S(k̄,P) = conj S(k,P̄) (the source of the doubling of the (P,P̄) class)
  for all rows and all 10 P at K = 300: 6·10⁻¹⁴ (max |S| = 61);
* probe B (`test_probeB.py`, B = 1500): same 426 rows as zfamily.py; vectorised symbol table = `Prime.sym` on all 422 × 38 pairs
  (0 mismatches); S_u identical to a direct computation; M₄, M₆ of `run()` identical to brute force (to 6 digits);
  χ_u(n₁n₂n₃) = Πχ_u(n_i) on 254/254 primary triples; T₄, T₆ identical to brute-force dictionaries (windows C = 5 and 22).

## 4. Probe A results (logs: `logs/A_*.log`, `logs/A_*.analysis.txt`, `logs/summarize_A.md`)

Setup of the main run (`A_true_lin_K20000_np10`): 40 s on 4 cores. At K = 2·10⁴: R = 5184 rows, X = 7.4·10⁵, 191 950
columns, Phi 5184 × 191 950.

### 4.1 Diagonal

| K | R(K) | columns (largest window) | G_PP/(R D_P): mean [min,max] over the 10 P | G_PP/(K² N(P)) mean |
|---:|---:|---:|---:|---:|
| 250 | 66 | 2406 | 0.883 [0.706, 1.002] | 0.0190 |
| 687 | 176 | 6606 | 0.829 [0.744, 0.955] | 0.0173 |
| 1889 | 486 | 18120 | 0.886 [0.825, 0.938] | 0.0186 |
| 5194 | 1348 | 49842 | 0.920 [0.878, 0.977] | 0.0195 |
| 10192 | 2656 | 97820 | 0.918 [0.902, 0.932] | 0.0195 |
| 20000 | 5184 | 191950 | 0.926 [0.911, 0.937] | 0.0196 |
| 50000 | 12980 | 479946 | 0.934 [0.928, 0.945] | 0.0198 |

Fit: mean_P G_PP ~ K^2.02, and G_PP/(R D_P) ~ K^{+0.02}: the single-column second moment is diagonal, with a constant
≈ 0.93 (i.i.d.-phase and random-cube-root surrogates give 0.957 ± 0.004: the 3% difference is the only trace of arithmetic
in G_PP). Over the 20 primes up to norm 79 the ratio is 0.88–0.93 for every P with log-slope −0.005 in N(P).
The n = m part of the cross terms, R·Dcross, is 5–14% of |G_{PP'}| (median over pairs) at K ≥ 700 and falls with K; the
off-diagonal-only version of ρ (G − R·Dcross) is the same to 2%.

### 4.2 Cross-correlations (10 primes, K ≤ 2·10⁴)

| K | R | conj: mean ρ, ζ | diff: mean ρ, ζ | all: mean ρ, ζ |
|---:|---:|---:|---:|---:|
| 250 | 66 | 0.133, 1.17 | 0.089, 0.78 | 0.094, 0.83 |
| 687 | 176 | 0.068, 1.09 | 0.070, 1.07 | 0.070, 1.07 |
| 1889 | 486 | 0.073, 1.80 | 0.040, 0.99 | 0.044, 1.11 |
| 5194 | 1348 | 0.044, 1.85 | 0.019, 0.78 | 0.022, 0.96 |
| 10192 | 2656 | 0.033, 1.72 | 0.018, 0.99 | 0.019, 1.10 |
| 20000 | 5184 | 0.015, 1.19 | 0.011, 0.86 | 0.011, 0.90 |
| 50000 (own run) | 12980 | 0.011, 1.40 | 0.0076, 0.94 | 0.0080, 1.00 |

(ζ = rms of ρ over the class times √R.)  The distribution over the 90 conjugation-independent "diff" pairs of the 20-prime run at
K = 2·10⁴ is that of an exponential variable: mean ζ² = 1.04, 4% of pairs above 3 (Exp(1): 5%), maximum 6.2 among 90
(expected ≈ 5); no outlier pair. The normalised Gram matrix D^{-1/2}GD^{-1/2} has λ_max − 1 = 0.70–0.95 × the Marchenko–Pastur
edge 2√(nP/R) + nP/R (0.54 at K = 350, 0.70–0.97 for K ≥ 700; 10 and 20 primes, and the 5·10⁴ run): no outlier eigenvalue.

### 4.3 Fitted exponents (ρ ~ K^-η)

| run | R(K_max) | η all | η diff | η conj | ζ diff | ζ conj |
|---|---:|---:|---:|---:|---:|---:|
| exact g̃, W = (1−u)₊, c = 1, 10 primes (norms 7…37) | 5184 | 0.558 [0.51, 0.63] | 0.572 [0.50, 0.64] | 0.469 [0.43, 0.56] | 0.94 | 1.56 |
| same, 20 primes (norms 7…79; 190 pairs) | 5184 | 0.519 [0.48, 0.55] | 0.516 [0.48, 0.55] | 0.549 [0.46, 0.67] | 1.04 | 1.44 |
| W = (1−u)₊² | 5184 | 0.532 [0.45, 0.60] | 0.557 [0.48, 0.64] | 0.367 [0.24, 0.57] | 0.93 | 1.52 |
| W = smooth bump | 5184 | 0.577 [0.52, 0.63] | 0.586 [0.51, 0.65] | 0.510 [0.46, 0.59] | 0.95 | 1.56 |
| window N = K N(P)/4 | 5184 | 0.517 [0.44, 0.59] | 0.550 [0.48, 0.63] | 0.320 [0.01, 0.57] | 0.92 | 1.31 |
| window N = 4 K N(P) | 5184 | 0.466 [0.39, 0.55] | 0.462 [0.38, 0.56] | 0.483 [0.18, 0.78] | 1.03 | 1.29 |
| K up to 5·10⁴ (fit K ≥ 1000) | 12980 | 0.538 [0.49, 0.58] | 0.541 [0.49, 0.59] | 0.524 [0.46, 0.60] | 0.93 | 1.54 |

Null calibration, same rows/columns/K-grid, 10 primes, 10 replicas each (mean ± sd over replicas):

| surrogate | η all | η diff | η conj | ζ diff | ζ conj | G_PP/(R D_P) at K_max |
|---|---:|---:|---:|---:|---:|---:|
| i.i.d. random phases | 0.489 ± 0.035 | 0.494 ± 0.042 | 0.447 ± 0.146 | 0.97 ± 0.04 | 0.95 ± 0.06 | 0.959 ± 0.003 |
| random cube root at every prime (g̃³ = π/\|π\|, twisted mult. kept) | 0.514 ± 0.023 | 0.514 ± 0.025 | 0.503 ± 0.170 | 1.00 ± 0.06 | 0.93 ± 0.14 | 0.957 ± 0.004 |
| i.i.d. phases with g̃(n̄) = conj g̃(n) | 0.488 ± 0.058 | 0.481 ± 0.069 | 0.524 ± 0.105 | 0.99 ± 0.04 | 1.36 ± 0.14 | 0.957 ± 0.006 |
| random cube roots with g̃(π̄) = conj g̃(π) | 0.518 ± 0.052 | 0.524 ± 0.052 | 0.475 ± 0.116 | 1.00 ± 0.07 | 1.26 ± 0.14 | 0.956 ± 0.005 |

With 10 primes the true η is 0.04–0.09 above the null means (1–2 sd of the null replicas); with 20 primes (190 pairs) it equals them.
ζ(conj) is within 1.5 sd of the symmetric nulls. Part of the excess is the slow rise of the diagonal ratio (0.83 → 0.93 over the grid,
a K^{+0.02} factor in the denominator of ρ). No true run has η(all) or η(diff) below 0.46 (the conj class, with 5 pairs,
ranges over 0.32–0.55).

### 4.4 Dependence on N(P), N(P')

20-prime run, all 190 pairs, mean ζ² over K ≥ 700 in five bins of 38 pairs ordered by N(P)N(P') (49–6241): 1.09, 0.98, 1.14, 1.23, 1.26
(log-slope 0.09). For the 180 "diff" pairs alone the log-slope of ζ² in N(P)N(P') is 0.10 (bootstrap over primes [−0.04, 0.23]); so
ρ ∝ (N(P)N(P'))^{0.05±0.07} at most.
In the notation of (X_fix): |G_{PP'}| ≈ ζ R^{-1/2}·√(G_PP G_P'P') with √(G_PP G_P'P') = 0.0196 K² √(N(P)N(P')): A ≈ 0.

### 4.5 What probe A can and cannot say

* It sees correlations only above the noise floor ρ ≈ R^{-1/2} (0.014 at K = 2·10⁴, 0.009 at 5·10⁴). A coherent component of size ρ_sys
  adds R·ρ_sys² to ζ²; ζ² (diff) is 0.74 at K = 2·10⁴ against 0.93–1.0 for the null surrogates, so ρ_sys ≲ 0.5/√R ≈ 0.007
  (K = 2·10⁴), ≲ 0.004 (5·10⁴): at most about the size of the random-walk term, never a K-independent or slowly decaying one. A weak slowly
  decaying component below that floor (e.g. ρ_sys ~ 0.003 K^{-0.1}) is invisible. For the pricing, η₀ ≈ 7·10⁻⁴ (A = 2) would be enough
  and the data show total decay with exponent ≈ 0.5, so as a statement about the truth of (X_fix) the numerics leave a factor ~700 in the
  exponent to spare; they say nothing about how to prove it.
* P ranges over norms ≤ 79 and K ≤ 5·10⁴; the (X_fix) asymptotics is K → ∞ at fixed P.
* Columns are the split-squarefree model of build.py (not all squarefree n). n = 1 is excluded.
* Exponent errors: ±0.03–0.06 statistical (null replicas, 13–14 correlated grid points), ±0.1 recommended with finite-size and the
  log corrections in R(K) ≈ 0.26 K (local slope of R^{-1/2} is −0.47, not −0.5).

## 5. Probe B results (logs: `logs/B_*.log`, `results/B_*.json`)

All runs: nrep = 12 surrogate replicas (8 for B_big, 6 for B ≥ 0.7 windows). B_main takes 6 min.

### 5.1 Required grid and beyond: M₆ (actual, mult. surrogate in parentheses, row-wise se in brackets)

| B | R | m = 0.30 | m = 0.35 | m = 0.43 | m = 0.50 |
|---:|---:|---:|---:|---:|---:|
| 3000 | 848 | 0.331 (0.351) [0.030] | 0.284 (0.311) [0.034] | 0.202 (0.197) [0.022] | 0.288 (0.325) [0.035] |
| 6000 | 1695 | 0.088 (0.092) [0.005] | 0.157 (0.149) [0.012] | 0.372 (0.398) [0.038] | 0.242 (0.295) [0.025] |
| 12000 | 3376 | 0.311 (0.291) [0.017] | 0.586 (0.568) [0.042] | 0.328 (0.389) [0.023] | 0.392 (0.420) [0.031] |
| 24000 | 6770 | 0.169 (0.159) [0.006] | 0.295 (0.319) [0.012] | 0.300 (0.314) [0.013] | 0.383 (0.403) [0.019] |
| 48000 | 13559 | 0.416 (0.425) [0.016] | 0.233 (0.235) [0.008] | 0.294 (0.290) [0.013] | 0.349 (0.373) [0.014] |
| 96000 | 27091 | 0.204 (0.196) [0.005] | 0.303 (0.310) [0.007] | 0.372 (0.379) [0.009] | 0.351 (0.395) [0.010] |
| 192000 | 54202 | 0.334 (0.341) [0.005] | 0.410 (0.409) [0.009] | 0.411 (0.434) [0.010] | 0.366 (0.411) [0.007] |
| 384000 | 108368 | 0.401 (0.405) [0.006] | 0.438 (0.440) [0.006] | 0.359 (0.378) [0.005] | 0.384 (0.435) [0.006] |
| 768000 | 216784 | 0.352 (0.353) [0.003] | 0.371 (0.376) [0.004] | 0.378 (0.395) [0.004] | 0.380 (0.436) [0.004] |
| 1536000 (`B_big`, m ≥ 0.43 only) | 433573 | | | 0.381 (0.390) [0.003] | 0.387 (0.442) [0.003] |
| N³/R at B = 768000 (1536000) | | 0.9 | 7.0 | 180 (220) | 3105 (4391) |
| N, #terms at B = 768000 | | 58, 24 | 115, 47 | 339, 136 | 876, 354 |
| exact diagonal T₆/N³ at B = 768000 | | 0.417 | 0.454 | 0.486 | 0.537 |
| full Dirichlet family mod q ≈ R, B = 768000 | | 11.3 | 19.3 | 190 | 3105 |

The non-monotone behaviour in B at fixed m is the integer-part jump of the number of terms C ≈ 0.4 N (4 terms at B = 6000, m = 0.3);
the surrogate carries the same jumps, so use the ratio.

### 5.2 M₄ = Σ|S|⁴/(R N²)

| B | R | m = 0.30 | m = 0.35 | m = 0.43 | m = 0.50 |
|---:|---:|---:|---:|---:|---:|
| 3000 | 848 | 0.323 (0.332) [0.019] | 0.278 (0.296) [0.019] | 0.219 (0.210) [0.015] | 0.274 (0.288) [0.019] |
| 6000 | 1695 | 0.138 (0.141) [0.005] | 0.189 (0.183) [0.009] | 0.315 (0.332) [0.017] | 0.231 (0.264) [0.013] |
| 12000 | 3376 | 0.300 (0.287) [0.010] | 0.411 (0.409) [0.017] | 0.295 (0.324) [0.011] | 0.315 (0.318) [0.013] |
| 24000 | 6770 | 0.199 (0.190) [0.005] | 0.281 (0.291) [0.007] | 0.271 (0.273) [0.007] | 0.312 (0.316) [0.009] |
| 48000 | 13559 | 0.328 (0.333) [0.007] | 0.236 (0.237) [0.004] | 0.258 (0.260) [0.005] | 0.293 (0.300) [0.006] |
| 96000 | 27091 | 0.214 (0.211) [0.003] | 0.281 (0.282) [0.004] | 0.311 (0.309) [0.004] | 0.295 (0.306) [0.004] |
| 192000 | 54202 | 0.300 (0.303) [0.003] | 0.326 (0.324) [0.003] | 0.317 (0.325) [0.003] | 0.301 (0.308) [0.003] |
| 384000 | 108368 | 0.317 (0.317) [0.002] | 0.339 (0.339) [0.002] | 0.296 (0.301) [0.002] | 0.304 (0.313) [0.002] |
| 768000 | 216784 | 0.304 (0.303) [0.001] | 0.306 (0.306) [0.002] | 0.299 (0.303) [0.002] | 0.303 (0.315) [0.002] |
| 1536000 (`B_big`, m ≥ 0.43 only) | 433573 | | | 0.299 (0.301) [0.001] | 0.303 (0.316) [0.001] |
| N²/R at B = 768000 | | 0.02 | 0.06 | 0.53 | 3.54 |
| exact diagonal T₄/N² | | 0.339 | 0.347 | 0.346 | 0.360 |
| full Dirichlet family mod q ≈ R | | 2.4 | 2.7 | 3.0 | 5.8 |

### 5.3 Ratios and scaling (fixed m, B ≥ 12000; 7 values of B for m ≤ 0.35, 8 values incl. B = 1.536·10⁶ for m = 0.43, 0.50)

actual/mult for M₆: m = 0.30: 0.94 … 1.07 (0.997 at B = 7.7·10⁵); m = 0.35: 0.91 … 1.05 (0.987); m = 0.43: 0.84 … 1.02 (0.957; 0.978 at
B = 1.5·10⁶); m = 0.50: 0.82 … 0.95 (0.871; 0.876 at 1.5·10⁶). Full table: `logs/B_main.log` ("=== all ===") and `logs/B_big.log`.

| m | slope of log M₆(actual) in log B | slope of log M₆(mult) | slope of log(actual/mult) | N-term slope 3m−1 |
|---:|---:|---:|---:|---:|
| 0.30 | +0.119 ± 0.006 | +0.145 ± 0.002 | −0.010 ± 0.007 | −0.10 |
| 0.35 | +0.067 ± 0.007 | +0.089 ± 0.002 | +0.004 ± 0.007 | +0.05 |
| 0.43 | +0.029 ± 0.006 | +0.040 ± 0.002 | +0.007 ± 0.006 | +0.29 |
| 0.50 | +0.020 ± 0.006 | +0.031 ± 0.002 | −0.012 ± 0.006 | +0.50 |

(M₄, slope of log(actual/mult): −0.005 ± 0.004, +0.002 ± 0.004, +0.005 ± 0.003, −0.006 ± 0.003 for m = 0.30, 0.35, 0.43, 0.50.)
The positive slopes in the first two columns come from the slow (log-power) growth of the diagonal count and from the jumps of
the number of terms; the surrogate has the same, so only the third column carries information.

N-term coefficient c in M₆ − M₆(mult) = c·N³/R (`tables_B.py results/B_main.json results/B_big.json`): m = 0.43: (−6.5 ± 1.2)·10⁻⁵;
m = 0.50: (−1.46 ± 0.07)·10⁻⁵; all 20 points with N³/R ≥ 30: (−1.48 ± 0.07)·10⁻⁵. For M₄ (m = 0.5, N²/R = 3.5 fixed): c = (−3.2 ± 0.2)·10⁻³.
Full family: c = 1 by construction.

### 5.4 Tails (max over rows of |S_u|²/N)

| B | m | N, #terms | actual | mult. surrogate (mean of 12) |
|---:|---:|---:|---:|---:|
| 192000 | 0.50 | 438, 176 | 4.06 | 6.34 |
| 384000 | 0.50 | 620, 250 | 5.70 | 7.49 |
| 768000 | 0.50 | 876, 354 | 4.46 | 8.32 |
| 768000 | 0.43 | 339, 136 | 4.74 | 6.72 |

For a complex Gaussian S with E|S|²/N = 0.38 the expected maximum over R rows is 0.38·ln R ≈ 4.7: the real family is at the Gaussian level, the
random multiplicative surrogate (multiplicative chaos tail) is heavier. At B = 192000, m = 0.5 (`diag_tail.py`, one surrogate draw) the
bin |S|²/N ∈ [4, 6) holds 1 real row and ≈ 11 surrogate rows and carries 0.7% (real) against 5.6% (surrogate) of Σ|S|⁶; most of the
deficit of M₆ (0.366 against 0.400) comes from there. By number of prime factors of u the ratio actual/mult is 0.88, 0.92, 1.00,
0.74 for 1, 2, 3, 4 factors; by the norm of the smallest prime factor 0.98, 1.03, 0.89, 0.83, 0.88 for [1,10), [10,30), [30,100),
[100,1000), ≥ 1000: the deficit lives in rows without small prime factors. The second moment is exactly diagonal: M₂ ratio 1.006, and the
column correlation matrix of the 88 sources at B = 48000, m = 0.5 (`diag_colcorr.py`) has rms off-diagonal entry 0.0079 against
R^{-1/2} = 0.0086, Σ_{n≠m} Γ(n,m)/N = −0.4% of the diagonal.

### 5.5 Longer windows (B_mext, B_mlong) and larger B

actual/mult for M₆ and the actual M₆ with N³/R in brackets (m ≥ 0.4):

| B | m = 0.40 | m = 0.45 | m = 0.55 | m = 0.60 | m = 0.70 | m = 0.80 |
|---:|---:|---:|---:|---:|---:|---:|
| 3000 | 1.20 | 0.93 | 1.38 | 0.84 | 0.62 | 0.72 |
| 12000 | 1.05 | 0.80 | 0.89 | 0.84 | 0.60 | 0.57 |
| 48000 | 0.91 | 0.99 | 0.84 | 0.87 | 0.62 | 0.55 |
| 192000 | 0.98 | 0.96 | 0.85 | 0.78 | | |
| M₆ actual at largest B [N³/R] | 0.42 [40] | 0.40 [250] | 0.38 [9.6·10³] | 0.35 [6.0·10⁴] | 0.28 [5.0·10⁵] | 0.27 [1.3·10⁷] |

M₆ never exceeds 0.67 (B = 3000, m = 0.4, one standard error 0.07), and the ratio to the surrogate is ≤ 1.05 at every (B ≥ 12000, m ≥ 0.4). The N-term coefficient
c is negative at every m: −5·10⁻⁴ (0.40, N³/R ≤ 40), −8·10⁻⁵ (0.45), −8·10⁻⁶ (0.55), −1.7·10⁻⁶ (0.60), −3.9·10⁻⁷ (0.70), −2·10⁻⁸ (0.80).
`B_big` (B = 1.536·10⁶, R = 433 573; only m = 0.43, 0.50, 8 surrogate replicas, 4.7 min): M₆ = 0.381 (mult 0.390, ratio 0.978, z = −2.5)
at m = 0.43 with N = 457, 182 terms, N³/R = 220; M₆ = 0.387 (mult 0.442, ratio 0.876, z = −16) at m = 0.50 with N = 1239, 499 terms,
N³/R = 4391; M₄ = 0.299 (0.301) and 0.303 (0.316). Exact T₆ and the full-family control were skipped there (more than 420 terms).

Source-set variants (`B_zfam`, `B_zfam_big`, `B_odd_big`, `B_nosq_big`; 12 replicas). Sources as in zfamily.py (odd squarefree norm prime to 3,
which is the split-squarefree set of probe A): actual/mult for M₆ at m = 0.50 is 1.09, 0.77, 0.88, 0.98, 0.94, 1.00 for B = 3000 … 96000
and 0.97, 0.93 at B = 1.9·10⁵, 3.8·10⁵; at m = 0.43: 0.94, 0.99. Odd norm only (B = 1.9·10⁵): 0.94 (m = 0.43), 0.94 (m = 0.50). Ideal (n)
squarefree, inert primes allowed (B = 1.9·10⁵, 3.8·10⁵): 0.93, 0.97 (m = 0.43), 0.93, 0.92 (m = 0.50). So the deficit of 5–10% relative to the
multiplicative surrogate is present for every choice of sources, and no choice shows an excess.

## 6. Caveats

1. **Sizes.** Probe A: K ≤ 5·10⁴, norms ≤ 79, 14–16 correlated grid points; ζ(conj) has only 5–10 independent pairs.
   Probe B: windows contain 4–500 terms; B ≤ 1.5·10⁶; one realisation of the actual family, noise ≈ 1% in M₆ at the largest B.
   Neither probe can see an effect with amplitude below the stated floors (probe A: ρ_sys below R^{-1/2}; probe B: N-term coefficient c above
   ≈ +10⁻⁵ of the full family's).
2. **Surrogate deficits are unexplained.** actual/mult < 1 for m ≥ 0.43 (z up to −13 with row-wise se, ≈ −9 with the √2 correction for
   conjugate rows). It is concentrated in the extreme tail and is not an N-term; I did not find its mechanism. Reading "mult" as the
   exact diagonal is therefore only right up to this ≤ 13% (m ≤ 0.5) … 45% (m = 0.8) factor.
3. **Exponent resolution.** B-slopes are ±0.01 statistically; discrete jumps of C make single points unreliable, so only ratios were fitted.
   Treat all exponents as ±0.1 (the task rule). The diagonal itself carries log-powers, visible as the positive slopes of M₆(mult).
4. **Sums, not L-values.** Probe B measures plain sums of length B^m with a sharp cutoff; the window moment ∫|L(1/2+it)|⁶ of (W) and the
   packet sixth moment μ₆ of (H) are not the same objects. A positive result for sums supports but does not imply them.
5. **Probe A models.** Columns are the split-squarefree set of build.py; n = 1 omitted; rows exclude k = 1; the window is smooth with edge
   (1−u)₊ (checked against (1−u)₊² and a C^∞ bump); G_{PP̄} carries the exact factor 2 in E|G|².

## 7. Reproduce

```
cd research/rip/moments_probe
export MP_BUILD=/tmp/moments_probe_build            # where gauss_prime.c is compiled (needs gcc with OpenMP)
python3 -I test_fastgauss.py 6000 && python3 -I test_probeA.py 600 && python3 -I test_probeB.py 1500
bash run_A_batch.sh && bash run_A_batch2.sh          # ~30 min total on 4 cores, ~8 GB RAM for the K = 5·10^4 run
bash run_B_batch.sh                                  # ~25 min (B_main 6 min, B_nosq_big 5 min, B_big 5 min)
python3 -I summarize_A.py; python3 -I analyzeA.py results/A_true_lin_K20000_np10.npz --pairs
python3 -I tables_B.py results/B_main.json results/B_mext.json results/B_mlong.json; python3 -I compact_B.py results/B_main.json
```

## Probe C (follow-up): why the thin family sits *below* the multiplicative model

Script `probeC.py`; logs and JSON in `logsC/`. Weighted sums S_u = Σ_n w(N(n)/N)χ_u(n), with smooth
w = exp(−(log t)²/(2·0.3²)) on [e^{−1}, e], or the sharp annulus [1, 2). The multiplicative surrogate has i.i.d.
μ₆ values at prime ideals and the same coprimality mask. Moments are normalized by (Σw²)^{k/2}, using 4 surrogate
replicas. Rows are split into prime, composite and inert-factor classes.

**M6 actual / multiplicative surrogate, all rows, smooth weight:**

| m | 0.2 | 0.25 | 0.3 | 0.4 | 0.45 | 0.5 | 0.55 | 0.6 | 0.7 | 0.75 | 0.8 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| B = 3·10⁴ | 2.25/2.19 | 3.61/3.48 | 4.60/4.22 | 5.09/5.15 | – | 5.16/5.97 | – | 4.64/6.85 | 4.30/7.65 | 3.89/8.73 | 3.77/9.11 |
| B = 10⁵ | – | – | – | 5.54/5.40 | 5.71/5.98 | 5.12/6.59 | 5.86/7.02 | 4.88/7.80 | – | – | – |
| B = 3·10⁵ | – | – | – | 5.59/6.00 | 6.02/6.67 | 5.72/7.31 | 6.46/8.19 | 5.55/9.07 | – | – | – |

**Findings.**
- **Mechanism: the functional equation.** The surrogate's M6 grows monotonically with the log-length. The actual
  M6 saturates near the self-dual length m = 1/2 and falls beyond it, roughly symmetric under m ↔ 1 − m on
  [0.25, 0.75] (e.g. 4.60 at 0.3 and 4.30 at 0.7).
  - For m > 1/2, Poisson summation makes S_u a dual sum of length N(u)/N, so its normalized moments follow the
    dual length: actual(0.7) = 4.30 against surrogate(0.3) = 4.22.
  - The random multiplicative model has no functional equation and overestimates for m > 1/2.
  - At m = 0.2 against 0.8 the dual weight's shape (a 2D Hankel transform with tails) breaks the exact symmetry.
- **Self-dual point:** a stable constant factor, ratio 0.865 → 0.777 → 0.782 at B = 3·10⁴, 10⁵, 3·10⁵. It is
  not an exponent effect.
- **Below 1/2** (m ≤ 0.4, the D4 packet regime): ratio ≈ 0.93–1.09, i.e. random multiplicative behaviour.
- **Sharp versus smooth cutoff:** sharp weights show a smaller deficit (0.77 against 0.56 at m = 0.7). The sharp
  annulus's dual has slowly decaying oscillatory tails, i.e. more effective terms. So the cutoff is not the cause
  (the smooth deficit is larger).
- **Row classes:**
  - Prime rows show a stronger deficit than composite rows for m ≥ 0.45, consistently at B = 10⁵ and 3·10⁵:
    0.76/0.79 and 0.72/0.82 at m = 0.5; 0.60/0.64 and 0.53/0.66 at m = 0.6. Mechanism of this difference open.
  - Rows with an inert prime factor are too few (464 at B = 3·10⁴) and too noisy to conclude, though χ_{(q)} is
    trivial on rational sources for inert q.
