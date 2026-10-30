# Prime-pool numerics: the empirical prime cost Λ of a twisted fourth moment of the sextic family

First step (b) of `research/fresh-look/second/directions.md`, D1.  Everything is in this directory
(scripts, `results/`, `logs/`); nothing else in the repository was touched.  Run with `python3 -I` (the scripts add their own
directory to `sys.path`).  Evidence tags: [numerical] = computed here, [derived] = heuristic reading of the data, not proved.

## 0. Headline [numerical]

* **No prime cost is visible for any fixed weight family.**  With `F/Dcop` (below), every variant of the task (a_P = 1, 8 random-phase
  seeds, N(P)^{-it} for t = 5, 20, both Gauss-sum normalisations, and the plain-sum control) has F/Dcop ≤ 1.009 on the whole task grid
  (m ∈ {0.25..0.40}, s ≤ 0.45, i.e. total length T = 2m+s up to 1.25) for B ≥ 10^6 (row-sampling errors 0.2-1%, at B = 10^7 0.2-0.4%);
  over B = 10^6 … 10^7 the ranges are 0.991-1.005 (random phases), 0.985-1.007 (t = 20), 0.984-1.008 / 0.977-1.009 (Gauss simple / canon), 0.977-1.007 (control),
  and the smooth weights dip further: 0.954-1.004 (a_P = 1), 0.980-1.006 (t = 5).
  Growth exponents d ln(F/Dcop)/d ln B (B = 5·10^4 … 10^7) are 0 ± 0.003 (max |e| = 0.0052, all within 2σ of 0).  So `Λ_emp` cannot be read off a "break": there is none
  inside the required window (only the one-sided bounds `Λ_emp < (1-2m)/0.45` = 1.1 / 0.9 / 0.7 / 0.4 for m = 0.25 / 0.30 / 0.35 / 0.40).
* **The only departures from 1 are small and of bounded size**, and they carry the only measurable "onsets":
  smooth weights (a_P = 1, t = 5) show a *deficit* (F < D, down to 0.959 ± 0.004 at m = 0.4, s = 0.45, B = 10^7) switching on at T ≈ 1:
  fit `ln(F/Dcop)/ln B = κ max(0, 2m + Λs − 1)` gives **Λ = 0.96 ± 0.05** (κ = −0.011 ± 0.002) for a_P = 1 and 0.99 ± 0.14 for t = 5.
  The Patterson-aligned weights (conjugate Gauss sums) give a *plateau excess* of +4 … +8% for the pool alone once P0² > B:
  **s\* = 0.52 ± 0.01 → Λ_onset = 1.92 ± 0.05** (2% threshold; 1.6 at a 4% threshold), identical from B = 2·10^4 to 10^6, no growth with B.
* **The onset does not move with m** (Gauss-aligned pool in front of plain factors: same onset s ≈ 0.55-0.6, excess +9-13% at s = 0.7, B = 3·10^4),
  so the plain-sum length is *not* added to the prime cost; no departure at all up to s = 0.45 for m ≥ 0.25.
* **Worst case over all pool weights** (sup over unimodular a, and over all complex a): F/Dcop reaches 2 at
  s = 0.93 / 0.82 / 0.73 / 0.69 for m = 0 / 0.25 / 0.35 / 0.40 (averages over B = 3·10^3 … 10^5), i.e. `Λ_adv = (1−2m)/s_break` = 1.07 / 0.61 / 0.41 / 0.29, stable to ±0.03.
  This is a random-matrix law, ≈ (1+√(n/R_eff))² (n = pool size, R_eff = participation ratio of |X|^4 over the rows), larger by up to 1.9 for m = 0.4 (heavy tails).
* **Verdict:** the data are consistent with Λ ≤ 1.82 and with Λ = 2, and cannot separate them (Sec. 6).  Everything measurable sits at Λ ≲ 1,
  except one ≤ 8% effect (Gauss-aligned pool alone, m = 0) whose onset s\* ≈ 0.52 is a "Λ ≈ 1.9" structure: P0² ≈ B.

## 1. What was computed (definitions and conventions)

* Z[ω], ω = e^{2πi/3}, elements a + bω.  **Primary** = a ≡ 2, b ≡ 0 mod 3 (one generator per ideal coprime to 3; the unit ideal is represented by
  n = −1, whose symbol is the z-dependent sign (−1/z)_6).  A product of three primary elements is primary, so X1·X2·Q is an exact Dirichlet
  series over ideals, `c_m` collected over equal ideals; checked in `ppsanity.py` against `zomega.Prime.sym` (error 4e-15).
* **Rows**: squarefree ideals z (products of distinct prime ideals, both conjugates of a split prime allowed), N(z) ∈ [B, 2B], (z,6) = 1.
  R ≈ 0.2823 B, so log_B R = 0.84 (B = 3000) … 0.92 (10^7): the row count is B^0.9, not B.  χ_z(n) = Π_{π|z} (n/π)_6 (0 if (n,z) ≠ 1).
* **X(z) = X1 = X2** = Σ_{n primary, N(n) ≤ B^m} W(N(n)/B^m) χ_z(n), all primary n (also composite and even), W = 1 ("plain") or (1 − N/N_i)_+ ("smooth").
  m ∈ {0.25, 0.30, 0.35, 0.40}.  Number of terms: 4-16 at B = 12000, 23-253 at B = 10^7.
* **Pool** Q(z) = Σ_P a_P χ_z(P): split primary primes (prime *ideals*, so both conjugates of p ≡ 1 mod 3), P0 < N(P) ≤ 2P0, P0 = B^s.
  "n pool" = number of prime ideals.  Weights a_P: `ones`; `rand0..7` (iid unimodular, seeds); `t5`, `t20`: N(P)^{−it} (t = 0 is `ones`);
  Patterson-biased `gauss_simple`: a_P = conj(g̃(P)), g̃ = p^{-1/2} Σ_{x mod p} (x/P)_6 e(x/p), x rational integers (the task's normalisation);
  `gauss_canon`: same with the Kubota character e(Tr(x/(√−3 P))) = e(−b x/p), P = a + bω primary (this is the convention of
  `round7/signal-processing/zw.py`).  They differ by the twist conj((−b/P)_6) (checked); **the two are not equivalent numerically** (Sec. 4.4).
* **Control**: Q replaced by a plain sum X3 of length N3 = P0 = B^s with the same W (F = Σ|X|^4|X3|^2, D from the triple convolution).
* **F** = Σ_z |X|^4 |Q|^2 (streamed over rows; independent check F = Σ_z |Σ_m c_m χ_z(m)|^2 over the ideals m agrees to 1e-16).
  **D** = R Σ_m |c_m|^2, c = coefficients of X·X·Q over ideals (exact collisions included, e.g. P | k).
  **Dcop** = R Σ_m |c_m|^2 ρ_m, ρ_m = Π_{π|m} N(π)/(N(π)+1): the fraction of rows coprime to m.  `Dcop` is the exact expectation of F if the
  sextic characters at distinct primes were independent (verified against exact coprime counts: ratio 0.994-1.004).  D itself is 0.83-0.90 × Dcop
  at large B (rows divisible by a small prime ideal of m kill the term), which is why the raw `F/D` of the task is ≈ 0.87 where `F/Dcop` ≈ 1.00.
  **Both ratios are tabulated**; "F/D leaves O(1)" is read on `F/Dcop`.
* **SE** = row-sampling standard error of F (std of |X|^4|Q|^2 over rows / √R).  Not an arithmetic error bar; heavy tails make it a lower bound.
* Worst-case probe (`ppadv.py`): with M = E_Q^H diag(|X|^4) E_Q and Δ = R A diag(ρ) A^H, F(a) = a^H M a, Dcop(a) = a^H Δ a;
  `sup_L2` = generalised top eigenvalue (sup over all complex a: an upper bound for *every* weight class, including zero-forced ones),
  `sup_uni` = unimodular power iteration a ← phase(Ma), 9 starts (a lower bound for the unimodular sup; 85-95% of `sup_L2`).

## 2. Files

| file | purpose | cost |
|---|---|---|
| `ppcore.py` | library: vectorised sextic symbols (validated against `../zomega.py`), row enumeration by factorisation, Gauss sums, convolution/diagonal | |
| `ppsanity.py`, `ppsanity2.py` | correctness checks, independent F, random-sign comparison | seconds |
| `ppgrid.py B` | the (m, W, s, variant) grid for one B → `results/grid_B.json` | B=10^5: 1.4 s; 10^6: 17 s; 2·10^6: 56 s; 4·10^6: 162 s; 10^7: 459 s |
| `ppadv.py B` | extended window s ≤ 0.95, m from 0, worst-case weights → `results/adv_B.json` | 7 s (3000) … 137 s (10^5) |
| `ppqalone.py B s-list` | the pool alone (X = 1), many weights incl. orientation/angular tests → `results/qalone_*.json` | 10-100 s |
| `ppanalyze.py` | all tables, exponents, fits → `results/results_tables.md` | 20 s |
| `ppshow.py` | quick look at one grid file | |
| `results/` | `grid_*.json`, `adv_*.json`, `qalone_*.json` (raw numbers), `results_tables.md` (**the tables**), `sanity_*.txt` | |
| `logs/` | stdout of every run | |

Reproduce: `for B in 3000 6000 12000 20000 50000 100000 200000 500000 1000000 2000000 4000000 10000000; do python3 -I ppgrid.py $B; done`,
`python3 -I ppadv.py B --ms 0,0.15,0.25,0.35,0.4 --ss 0.4,0.5,0.6,0.7,0.8,0.85,0.9,0.95` (B ≤ 12000; `--ss 0.5,…,0.9` at 3·10^4, `0.6,0.7,0.75,0.8,0.85` at 10^5),
`python3 -I ppqalone.py B 0.45,0.475,0.5,0.525,0.55,0.575,0.6,0.625,0.65,0.7` for B = 2·10^4, 5·10^4, 10^5, 2·10^5, 4·10^5, 10^6, plus
`python3 -I ppqalone.py B 0.75,0.8,0.85 --out results/qalone_hi_B.json` (B = 10^5; 0.75,0.8 at 2·10^4; 0.8 at 4·10^5), then `python3 -I ppanalyze.py`.
`ppshow.py FILE [smooth|plain]` prints one grid file (all columns F/Dcop).

## 3. Validation [numerical] (`results/sanity_checks.txt`, `results/sanity_randomsign.txt`)

* Vectorised symbols = `zomega.Prime.sym` on 2220 random (ideal, element) pairs; inert symbols; multiplicativity; primary generators.
* Row sets = brute-force enumeration over distinct prime ideals (zfamily style): R = 848 (B = 3000), 1695 (6000); identical norm multisets.
* X1X2Q(z) = Σ_m c_m χ_z(m) with χ_z(m) from `zomega.Prime.sym` of the product element: 4e-15.  F (product) = F (direct over ideals): 1e-16.
* **F/D ≈ 1 when T is well below log_B R**: e.g. B = 10^6, T = 0.60-0.80: F/Dcop = 0.999-1.001 for all variants (row-SE 0.5%); the task's raw F/D is 0.87-0.90 there
  only because D counts rows that a small prime ideal of m kills (Dcop removes exactly that).
* **Random-sign / random-phase vectors on the same support** (60 draws): F_rs/Dcop = 1.000 ± 0.004 (B = 2·10^5), ± 0.008 (5·10^4), ± 0.015-0.02 (12000), ± 0.03-0.04 (3000);
  the structured values (true characters, one random a_P, plain/smooth W) are 1.020/1.000 (2·10^5, m=.35,s=.4), 0.982/1.003 (5·10^4), 1.015/1.023 (12000), 1.136/1.129 (3000, X has 7 terms),
  i.e. comparable; the only ≥ 3σ departures are at B ≤ 12000 (+4σ at B = 3000, −3.5σ at B = 12000 for (m,s) = (0.4, 0.45): 0.93-0.94 vs 1.00 ± 0.018), none beyond 2σ at B ≥ 5·10^4.
* Gauss sums: |g̃| = 1, canon = conj((−b/P)_6)·simple.

## 4. Results

Full tables for every B, both W, all variants: `results/results_tables.md` (Sec. 1: required grid, 2: extended B, 3: exponents/fits, 4: extremes, 6: worst case, 7: pool alone).

### 4.1 Required grid (B = 3000 … 20000) [numerical]

Pools with ≥ 5 prime ideals exist only for s ≥ 0.40 (B = 3000, 6000), ≥ 0.35 (12000), ≥ 0.35 (20000): two or three values of s per B, so **s_break cannot be
resolved at these B**.  Row-SE is 2.6-8.4%, the seed-to-seed spread 0.8-7.5%; F/Dcop (all variants, pools ≥ 5) scatters in 0.945 … 1.209 (B = 3000), 0.861 … 1.084 (6000),
0.844 … 1.052 (12000), 0.864 … 1.096 (20000), without a trend in s or T (3σ outliers: see Sec. 3).
Typical lines (smooth W; full set in the tables):

| B | m | s | n | T | F/D (a=1) | F/Dcop a=1 | rand (8 seeds) | t=5 | t=20 | gauss simple | gauss canon | control | row-SE |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 12000 | 0.25 | 0.45 | 12 | 0.95 | 0.994 | 1.052 | 0.988 ± 0.038 | 1.027 | 1.024 | 1.001 | 0.966 | 0.999 | 3.6% |
| 12000 | 0.40 | 0.40 | 10 | 1.20 | 0.766 | 0.870 | 0.941 ± 0.075 | 1.015 | 0.955 | 0.917 | 0.844 | 0.922 | 5.1% |
| 12000 | 0.40 | 0.45 | 12 | 1.25 | 0.852 | 0.961 | 0.944 ± 0.032 | 0.917 | 1.004 | 0.969 | 0.913 | 0.916 | 5.3% |
| 20000 | 0.25 | 0.45 | 16 | 0.95 | 0.945 | 1.012 | 1.002 ± 0.017 | 0.994 | 0.985 | 1.007 | 0.908 | 1.012 | 2.8% |
| 20000 | 0.40 | 0.45 | 16 | 1.25 | 0.881 | 0.995 | 1.053 ± 0.019 | 0.994 | 1.045 | 1.096 | 0.897 | 1.021 | 4.2% |

The plain fourth moment of X alone (no pool) is 0.96-1.13 × its diagonal here (B = 3000: 1.001, 1.048, 1.108, 1.130; 12000: 1.007, 0.989, 0.968, 0.959; 20000: 0.995, 0.995, 1.016, 1.034
for m = 0.25 … 0.40), and 0.999-1.003 at B = 10^7: the sample mean of a heavy-tailed |X|^4 over R rows is only good to a few % at B ≤ 2·10^4.

### 4.2 Extended B (same grid, 5·10^4 … 10^7) [numerical]

| B | m | s | n | T | F/D (a=1) | F/Dcop a=1 | rand | t=5 | t=20 | gauss simple | gauss canon | control | row-SE |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 10^6 | 0.25 | 0.45 | 70 | 0.95 | 0.903 | 1.002 | 1.001 ± 0.003 | 1.000 | 0.999 | 0.989 | 0.990 | 1.000 | 0.6% |
| 10^6 | 0.40 | 0.45 | 70 | 1.25 | 0.842 | 0.968 | 0.995 ± 0.008 | 0.980 | 0.996 | 0.986 | 0.993 | 0.984 | 1.0% |
| 10^7 | 0.25 | 0.20 | 6 | 0.70 | 0.869 | 0.998 | 0.999 ± 0.001 | 1.000 | 0.998 | 0.999 | 0.998 | 0.999 | 0.2% |
| 10^7 | 0.25 | 0.45 | 186 | 0.95 | 0.889 | 0.999 | 1.000 ± 0.002 | 0.997 | 0.997 | 0.990 | 0.997 | 1.001 | 0.2% |
| 10^7 | 0.35 | 0.45 | 186 | 1.15 | 0.848 | 0.975 | 1.003 ± 0.001 | 0.989 | 0.999 | 0.993 | 0.997 | 1.001 | 0.3% |
| 10^7 | 0.40 | 0.30 | 24 | 1.10 | 0.860 | 0.989 | 1.003 ± 0.004 | 0.995 | 0.999 | 1.003 | 0.999 | 1.007 | 0.4% |
| 10^7 | 0.40 | 0.45 | 186 | 1.25 | 0.829 | 0.959 | 1.005 ± 0.001 | 0.984 | 1.001 | 0.996 | 0.997 | 0.985 | 0.4% |

Largest deviation of F/Dcop on the whole grid, B = 10^7: max 1.007 (control), min 0.959 (a_P = 1); `X alone`: 0.999 … 1.003.
Plain-W tables are the same within their larger noise (sharp cutoff).

### 4.3 Growth exponents and the κ-Λ fit [numerical]

* `e(m,s) = d ln(F/Dcop)/d ln B` (weighted LS over B ≥ 5·10^4): all 20 grid points × 7 variants (140 fits) lie within 2σ of 0; max |e| = 0.0052 (gauss canon, (0.40, 0.30)), typically ±0.002 ± 0.002.
  Pooled by T-bin the weighted means are in [−0.0011, +0.0019] ± 0.0009 (T < 0.9, 0.9-1.05, 1.05-1.3).  Face-model limit
  `e ≤ κ max(0, 2m+Λs−1)` ⇒ **Λ ≤ 1.12 / 0.91 / 0.68 / 0.46** for m = 0.25 / 0.30 / 0.35 / 0.40 (2σ, κ = 1; 1.15 / 0.94 / 0.71 / 0.50 for κ = 1/3).
* Signed fit of all (m,s,B ≥ 10^6) points to `ln(F/Dcop)/ln B = κ max(0, 2m+Λs−1)`:

| variant | κ | Λ | note |
|---|---|---|---|
| a_P = 1 | −0.0111 ± 0.0017 | **0.96 ± 0.05** | χ²/dof 7.3 (κ=0) → 1.07 (fit): a real, *negative* effect |
| t = 5 | −0.0032 ± 0.0014 | 0.99 ± 0.14 | |
| random phases, t = 20, gauss simple, gauss canon | 0.0004 ± 0.0049, 0.0000 ± 0.0012, −0.0003 ± 0.0029, −0.0001 ± 0.0001 | undetermined | κ consistent with 0 |
| control (plain X3) | −0.030 ± 0.013 | 0.5 ± 0.8 | one corner point only |

A negative κ means F < D: the smooth/zero-aligned classes lose a few percent beyond T ≈ 1; this is not a cost.  The onset is at T = 2m + s ≈ 1 (Λ ≈ 1: "primes cost their length").

### 4.4 Patterson-aligned weights: a bounded excess switched on by P0² > B [numerical]

Pool alone (`ppqalone.py`, X = 1).  F/(R n), B = 10^5 (R = 28210), SE 0.6%:

| s | n | P0²/B | ones | rand | t=5 | t=20 | **gauss simple** | **gauss canon** | gauss simple, *non*-conjugated | gauss canon, non-conj. | angular (P/\|P\|)^{±1,±3} |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0.50 | 50 | 1.0 | 1.002 | 1.002 | 0.994 | 0.993 | 1.003 | 1.016 | 0.990 | 0.992 | 0.99-1.00 |
| 0.60 | 136 | 10 | 0.995 | 1.001 | 0.999 | 1.004 | 1.024 | 1.005 | 0.998 | 0.998 | 0.99-1.00 |
| 0.70 | 374 | 100 | 1.009 | 0.996 | 1.000 | 1.005 | **1.070** | 1.038 | 1.005 | 0.994 | 1.00 |
| 0.80 | 1026 | 1000 | 0.995 | 0.999 | 0.998 | 0.998 | **1.069** | 1.048 | 1.002 | 1.009 | 1.00 |
| 0.85 | 1732 | 3162 | 1.005 | 0.999 | 1.002 | 1.000 | **1.077** | 1.050 | 1.005 | 1.001 | 1.00 |

* Orientation matters: conj g̃ (aligned) gives +4-8%, g̃ itself and angular Hecke characters give 1.00.  Ones, random, t = 5, 20 give 1.00 ± 0.01.
* The excess is a function of P0²/B alone (curves for B = 2·10^4 … 10^6 collapse): ≈ 0 for P0² ≤ B, +2.5-4.7% at P0²/B = 3-4, +2.3-3.7% at 7-16, +5.0-6.4% at 25-63,
  plateau +5-8% for P0²/B > 100 (plateau mean 1.058, 1.073, 1.067, 1.053 at B = 2·10^4, 10^5, 4·10^5, 10^6: no growth with B).
* Onset (isotonic fit, parametric bootstrap; `results_tables.md` Sec. 7): `gauss_simple` crosses 1.02 at s\* = 0.527 ± 0.022, 0.510 ± 0.009, 0.523 ± 0.007, 0.518 ± 0.018,
  0.522 ± 0.004, 0.517 ± 0.001 for B = 2·10^4, 5·10^4, 10^5, 2·10^5, 4·10^5, 10^6, i.e. Λ_onset = 1/s\* = 1.90 … 1.96, and crosses 1.04 at s\* = 0.61-0.65 (Λ = 1.54-1.64);
  `gauss_canon` (the Kubota character) is weaker: s\*(2%) = 0.60-0.62 for B ≥ 10^5 (Λ = 1.62-1.68; 0.705 at B = 2·10^4, not reached at 5·10^4), 4% reached only at s\* ≈ 0.76 (Λ ≈ 1.3).
  The task's simple normalisation is the *more* aligned one.  [derived] Reading: G(P,P') = Σ_z χ_z(P)\bar χ_z(P') has a coherent dual term of size B/√(pp') once pp' > B
  (Poisson in z), carried by the Gauss sums; summed over the pool it is O(n/P0) = O(1/ln P0) relative to R·n, never a power of B.
* With plain factors in front (`ppadv.py`, Sec. "Gauss-aligned excess with plain factors"): the onset stays at s ≈ 0.55-0.6 for all m ∈ [0, 0.4]; at s = 0.7 the excess grows mildly with m
  (B = 3·10^4: 1.090 / 1.091 / 1.088 / 1.130 / 1.129 for m = 0 / .15 / .25 / .35 / .40, SE 1.2-5%; B = 10^5: 1.070 / 1.081 / 1.105 / 1.111 / 1.115, SE 0.6-2.9%).
  On the required window (s ≤ 0.45), with m ≥ 0.25 it is absent (B = 4·10^6, 10^7: gauss simple 0.986-1.006).  [derived] The plain factors do not align with g̃: g̃(kP) = (k/P)_3 ε g̃(k) g̃(P) carries a cubic symbol
  that cancels when summed over P for non-cube k.

### 4.5 Smooth weights: a small deficit (F < D) [numerical]

a_P = 1 at (m,s) = (0.40, 0.45): 0.906 / 0.960 / 0.959 / 0.944 / 0.968 / 0.954 / 0.967 / 0.959 for B = 5·10^4 … 10^7 (SE 3.2% … 0.4%): constant in B, i.e. no exponent, onset T ≈ 1.
In the extended window (B = 10^5): a_P = 1 gives 0.909 ± 0.021 at (0.40, 0.80), 0.915 ± 0.019 at (0.35, 0.80); B = 3·10^4: 0.898 ± 0.023 at (0.25, 0.90); random phases and t = 20 stay at 1.00.

### 4.6 Extended window and worst-case weights (`ppadv.py`, `results_tables.md` Sec. 6) [numerical]

R_eff/R of |X|^4 (smooth): 1.0 (m = 0), 0.64 (0.15), 0.26 (0.25), 0.14 (0.35), 0.105 (0.40) at B = 10^5, falling with B for m > 0.
`sup_uni` = 0.85-1.00 × `sup_L2` (median 0.95); `sup_L2` follows (1+√(n/R_eff))² to within 2% for m ≤ 0.15, 4-15% for m = 0.25, and exceeds it by a median 1.15 (m = 0.35) / 1.19 (m = 0.40),
up to 1.8-1.9 at the largest pools: heavy tails beyond the second moment of |X|^4.  Break (sup_uni = 2) and `Λ_adv = (1−2m)/s_break`:

| m | s_break (B = 3000 / 6000 / 12000 / 30000 / 10^5) | Λ_adv (same B) |
|---|---|---|
| 0 | 0.919 / 0.938 / 0.944 / >0.90 / >0.85 | 1.09 / 1.07 / 1.06 / <1.11 / <1.18 |
| 0.15 | 0.920 / 0.938 / 0.944 / >0.90 / >0.85 | 0.76 / 0.75 / 0.74 / <0.78 / <0.82 |
| 0.25 | 0.825 / 0.820 / 0.812 / 0.821 / 0.814 | 0.61 / 0.61 / 0.62 / 0.61 / 0.61 |
| 0.35 | 0.703 / 0.734 / 0.745 / 0.707 / 0.737 | 0.43 / 0.41 / 0.40 / 0.42 / 0.41 |
| 0.40 | 0.655 / 0.702 / 0.712 / 0.677 / 0.689 | 0.31 / 0.28 / 0.28 / 0.30 / 0.29 |

(τ = 1.5: s_break 0.74 … 0.83 for m = 0, 0.48 … 0.61 for m = 0.4; τ = 3: ≥ 0.95 for m ≤ 0.15, 0.76-0.83 for m = 0.4.)  The break is at pool size ≈ 0.2 R_eff, not on a line 2m + Λs = const:
s_break falls only from 0.94 to 0.69 while (1−2m) falls from 1 to 0.2.  The alternative fit `ln(sup)/ln B = κ max(0, 2m+Λs−1)` to the whole scan gives κ = 0.11-0.14 and
**Λ_fit = 1.63 ± 0.18 (B = 3000), 1.62 ± 0.18 (6000), 1.55 ± 0.16 (12000), 1.34 ± 0.18 (3·10^4), 1.32 ± 0.22 (10^5)** (`sup_uni`; `sup_L2`: 1.65, 1.64, 1.58, 1.39, 1.42): a line fitted to a convex
crossover, drifting down with B.  Since the sup bounds every weight class, **any zero-forced pool has Λ_emp ≤ Λ_adv** at these B.

## 5. Empirical Λ per weight variant (one table)

| weight variant | observed departure of F/Dcop from 1 | Λ_emp (error) | meaning |
|---|---|---|---|
| (i) a_P = 1 (= t 0) | deficit, to 0.959 ± 0.004 (B=10^7); constant in B | onset fit **0.96 ± 0.05** (κ = −0.011 ± 0.002) | F < D; no cost |
| (iii) t = 5 | deficit to 0.984 | 0.99 ± 0.14 | F < D |
| (iii) t = 20 | none (1.000 ± 0.003) | break absent: < 1.1 / 0.9 / 0.7 / 0.5 (m = .25 / .30 / .35 / .40; s ≤ 0.45); < 0.53 / 0.21 at s ≤ 0.95 (m = .25 / .40; few-% accuracy, B ≤ 3·10^4) | |
| (ii) random phases, 8 seeds | none (1.000 ± 0.002; seed sd 0.1-0.8% at B ≥ 10^6) | same bounds | |
| (iv) gauss simple (task) | none on the task window; pool alone: +2% at s\* = 0.52 ± 0.01, plateau +5-8% | **Λ_onset(m=0) = 1.92 ± 0.05** (2% threshold), 1.6 (4%); for m ≥ 0.25: no onset for s ≤ 0.45 ⇒ < 1.1 … 0.4 | bounded, O(1/ln) excess |
| (iv) gauss canon | none on the task window; pool alone: +2% at s\* = 0.60-0.62, plateau +4-5% | 1.65 ± 0.05 (2%) | |
| control (plain X3) | none (≤ 0.7%; −1.5% at the last corner) | < (1−2m)/0.45 | |
| worst case over weights (sup_uni / sup_L2) | grows as (1+√(n/R_eff))² | **Λ_adv = 1.07 / 0.61 / 0.41 / 0.29** (m = 0 / .25 / .35 / .40), fit Λ_fit 1.3-1.65 | upper envelope of every class |

Error bars: the statistical part (row-SE, bootstrap) is quoted; systematic uncertainty from (a) the threshold (2% vs 4%: ±0.15-0.3 on Λ_onset), (b) the s-grid step (0.025-0.1: ±3-10% of Λ),
(c) B-drift (Λ_fit decreases by 0.3 from B = 3·10^3 to 10^5; Λ_adv does not), and (d) finite-size exponents (Sec. 7) is of order ±0.2 or more.

## 6. Do the data distinguish Λ ≈ 1.8 from Λ = 2?  No. [judgement]

* Every fixed-weight family has F/Dcop = 1.00 ± 0.02 (smooth weights: down to 0.95) at B ≥ 10^6 across the face boundaries of both Λ = 1.82 and Λ = 2
  (they sit at s = (1−2m)/Λ ≈ 0.27 / 0.22 / 0.16 / 0.11 resp. 0.25 / 0.20 / 0.15 / 0.10 for m = 0.25 / 0.30 / 0.35 / 0.40), and beyond them up to T = 1.25.  Neither face is approached; on the required window the region where "F ≲ D" is observed extends past both lines by a factor ≥ 1.6 (m = 0.25) to ≥ 4 (m = 0.40) in s,
  and in the extended window (s ≤ 0.9-0.95, few-% accuracy) by ≥ 3.
  A line `2m + Λs = 1` with Λ = 1.82 and one with Λ = 2 are indistinguishable when nothing happens on either.
* The single feature at Λ ≈ 2 (Gauss-aligned, m = 0, onset P0² ≈ B ⇒ s\* → 1/2) is O(1)-small and plateaus; its fitted Λ_onset is 1.92 ± 0.05 at the 2% level and 1.6 at 4%;
  the gap 2.0 − 1.82 = 0.18 is smaller than this threshold ambiguity (0.3).  Moreover finite B biases s\* upward: an onset at P0² = c·B gives Λ_eff(B) = 1/(1/2 + ln c/(2 ln B)).
  The measured crossings correspond to c ≈ 1.6 (2%, s\* = 0.517 at B = 10^6) and c ≈ 21 (4%, s\* = 0.61), i.e. Λ_eff = 1.93 resp. 1.64 at B = 10^6, and 1.97 resp. 1.80 even at B = 10^12.
  **A true Λ = 2 onset therefore looks like 1.6-1.9 at accessible B, depending on the threshold** — the same range in which 1.82 lies.
* The worst case over all weights has Λ_adv ≤ 1.1, and the fitted Λ_fit = 1.3-1.65 decreases with B.  So there is no hint that the zero-forced pool needs Λ above 1; the numerics
  support "Λ ≤ 1.82" (with a very large margin) but give no purchase on the difference between 1.82 and 2.
* What would separate them: a regime in which F/D grows as a power of B (none seen: |e| ≲ 0.003), i.e. much larger B, or rows/weights where a zero-forced structure is present (below).

## 7. Caveats

* **Scale.**  The requested window has few terms: X has 4-16 terms at B = 12000 and 23-253 at 10^7; the dyadic pool has ≥ 5 prime ideals only for s ≥ 0.35 (B ≤ 2·10^4), s ≥ 0.2-0.25 (10^6-10^7).
  R = B^{0.84…0.92}, so "T = 1" is *above* the row count at every B here; the trivial large-sieve wall (S_m ≳ R) lies at T ≈ log_B R ≈ 0.9 and nothing happens there for non-adversarial weights.
  Exponent estimates carry ±0.1 or worse; the exponent-free statements (constancy of F/Dcop in B, collapse in P0²/B) are the robust ones.
* **Zero-forcing is not reproduced.**  The theorem's weights are fixed and smooth, but the *rows* that matter are those selected by a zero of L(s, χ_z) near height t; no Dirichlet polynomial of these tiny
  lengths detects zeros of conductor ≈ B.  The worst-case probe (sup over a for the *given* X and rows) is the only part that covers row-dependent alignment, and it is a random-matrix law here.
* **D variants.**  Raw `F/D` (task) vs `F/Dcop`; sixth-power coincidences m ≡ m' (e.g. 2^6) are excluded from both (they need v_2(k) ≥ 6, rare at these lengths).  `ρ` is the analytic coprime fraction
  (exact count differs by ≤ 0.4%).  n = −1 is the first term of X (primary generator of the unit ideal).
* **Row-SE** assumes independent rows; with heavy tails it is a lower bound.  The `rand` columns average 8 seeds that share the rows; their spread is reported separately.
* **Not done:** B > 10^7; products of j ≥ 2 primes in the pool (the theorem's pools include them and are denser at small s); Voronoi/reflected variants; non-dyadic pools.
* The 200000-row random-sign check was run for (m, s) = (0.35, 0.40) only; the (0.40, 0.45) run was cut for time.
