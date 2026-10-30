# Prime rows versus composite rows in the sextic M6 deficit

This is a follow-up to probe C (README.md, last section). It asks why the ratio M6(actual)/M6(multiplicative surrogate) is
lower on rows u that are a single prime ideal than on composite rows. All code and logs are new: `primerows_*.py` and
`logsP/`. No existing file was modified and nothing was committed. Evidence tags: [numerical] means measured here,
[derived] means a short argument given here, [conjecture] means not established.

## 0. Answer in short

1. **The overall deficit comes from the functional equation, with the full conductor.** For a primary n,
   χ_u(n) = χ_u(−1)·λ_u(n), where λ_u is a Hecke character mod 3u. Its conductor is u·(1−ω)^c, where c is set by
   N(u) mod 36: c = 0 if k_u = 0, c = 1 if k_u = 3, and c = 2 otherwise, with k_u = ((N(u)−1)/6) mod 6. So the dual
   length is proportional to 3^c·N(u)/N. [derived]
   - Poisson summation over Z[ω] reproduces |S_u| from its dual sum to ≤ 1.8·10⁻³ (relative), on prime and composite rows
     with all six values of k. [numerical]
   - The deficit is ordered by c. At B = 1.6·10⁶, m = 0.45 the ratio is 0.79, 0.82, 1.00 for c = 0, 1, 2. At B = 10⁵,
     m = 0.7 it is 0.36, 0.49, 0.50. [numerical]
   - From m ≈ 0.6 on, the random multiplicative model applied to the dual sum gives the actual M6 to within about 6%
     (B = 10⁵) to 13% (B = 3·10⁴, smaller samples), class by class. [numerical]
2. **The prime/composite gap is a coprimality-mask effect, not a property of prime moduli.** [numerical]
   - Mask transplant: each prime row keeps its own character χ_π, but its sources are restricted to those coprime to the
     mask of a randomly chosen composite row. The prime row's ratio then rises to the composite value. The surrogate is the
     same in expectation for both sides.
   - Pooled over disjoint row sets, at m = 0.5: gap −0.053 ± 0.020, transplant shift +0.037 ± 0.007, residual
     −0.022 ± 0.017 (all in log of the ratio). With the mask {π₇} alone, prime rows masked artificially agree with the genuine
     rows π₇·π′ at every m (|log| ≤ 0.06 ± 0.07).
3. **Why a mask raises actual/surrogate.** [derived + numerical]
   - Removing a small prime ideal q from a random multiplicative sum lowers its normalized sixth moment M6/M2³. The
     asymptotic factor is (1+4/q+1/q²)/(1−1/q)², which is 2.17 for q = 7. At finite length this factor is only partly
     realized, and the realized part grows with the length.
   - The surrogate is evaluated at the length N. For q = 7 its shape factor goes from 0.90 (m = 0.3) to 0.80 (m = 0.6).
   - Once m > 1/2, the actual follows its shorter dual sum, where the same mask costs only about 0.90 at every m.
   - So the deficit is overestimated on unmasked rows, which are prime rows and composites without small factors. On
     composites with q = 7 or 13 (46% of the composite rows) the surrogate is discounted, and the actual does not pay
     that discount.
4. **The size of the effect is smaller than first reported.**
   - Probe C's 4-replica surrogate for the prime class at B = 3·10⁵ was 8–12% too high for m ≥ 0.5, compared with 10⁶
     draws. The prime ratios there were 0.719, 0.693, 0.530 and are really 0.775, 0.750, 0.595.
   - On disjoint rows there is no gap for m ≤ 0.45. For m = 0.5 to 0.65 the gap is −0.05 to −0.16 (in log).
   - The small-m prime deficit seen at B = 3·10⁵ (−0.12 at m = 0.3) is a tail fluctuation of the prime rows with norm in
     [3·10⁵, 8·10⁵]. It does not appear on disjoint rows (B = 8·10⁵, 1.6·10⁶).

**Confidence.**
- High that the gap is caused by the mask and not by primality. The transplant gives the same result at all six values
  of B, and the pure-{π₇} artificial mask agrees at B = 10⁵ and 3·10⁵.
- Medium-high for the dual-length explanation of why the actual is less sensitive to a mask. It is quantitative from
  m ≈ 0.6; at m = 1/2 it is qualitative.
- A residual of −0.09 ± 0.03 at m = 0.6 (three values of B) is unexplained and may be noise (§7).

## 1. Setup (same objects as probe C)

- **Rows, sources, weight, normalization.** As in probeC.py: smooth weight w(t) = exp(−(log t)²/0.18) on [e⁻¹, e], and
  M6 = mean |S_u|⁶/(Σw²)³.
- **Surrogate.** For each row, K replicas of a random completely multiplicative f with i.i.d. uniform μ₆ values at the
  prime ideals of the sources, including (2), and the same mask. Here K = 16–128, against 4 in probe C. For the
  artificial-mask runs, 10⁶ independent draws per mask.
- **Error bars.** Bootstrap over clusters {u, ū}: |S_ū| = |S_u| exactly (checked), so conjugate rows are not independent.
  The surrogate's per-row means are resampled with their rows.
- **Classes.** prime: nf = 1. composite: nf ≥ 2. min-7: the smallest factor has norm 7 (32% of composites); min-13: 14%.
- **Row sets.** B ∈ {10⁵, 2·10⁵, 4·10⁵, 8·10⁵, 1.6·10⁶} give disjoint row sets with norms in [B, 2B]. B = 3·10⁵ overlaps
  two of them and is shown but not pooled. There are 8 418 to 109 051 prime rows per B, and 451 654 rows at B = 1.6·10⁶.

## 2. The functional equation and the 3-part of the conductor [derived, checked numerically]

**The character on ideals.**
- The product of two primary elements is ≡ 1 mod 3, so n ↦ χ_u(n_primary) is multiplicative only up to the sign
  χ_u(−1). The ideal character λ_u(𝔫) = χ_u(−n_primary) is completely multiplicative and trivial on units.
- It is a character mod 3u. Its 3-component is x ↦ δ_x^{k_u}, where δ_x is the unit with δ_x·x ≡ 1 mod 3. Here k_u is
  computed from (ε/π)₆ = ε^{(Nπ−1)/6} and Π(1+6a_i) ≡ 1+6Σa_i mod 36.
- The 3-component has conductor 1, (1−ω) or (3) according as k_u ≡ 0, k_u ≡ 3, or k_u ∈ {1, 2, 4, 5}.
- N(u) mod 36 is equidistributed in both classes: 16.5/16.7/66.8% (prime) against 16.7/16.7/66.6% (composite) for
  c = 0/1/2.

**Poisson summation over Z[ω].**
- Use the trace pairing; the dual lattice is 𝔣⁻¹𝔡⁻¹, the covolume is √3/2·N𝔣, and |τ| = √N𝔣.
- Let Ĝ(ρ) = π∫w(t)J₀(2πρ√t)dt be the 2-D Fourier transform of x ↦ w(|x|²).
- For c ≥ 1: |S_u(N)| = (2N/√(3N𝔣))·|Σ_n conj χ_u(n)·Ĝ(2√(N·N(n)/(3N𝔣)))|, with N𝔣 = 3^c·N(u).
- For c = 0 the sum is imprimitive at 1−ω, and S = (T(N) − λT(N/3))/6 with λ = χ_u(1−ω). This gives a two-scale dual
  (formula in `primerows_dual.py`).
- `primerows_dual.py --B 3000` (`logsP/dualcheck_3000.txt`) checks the formulas on 6 prime and 6 composite rows (one
  per k = 0…5) at m = 0.4…0.7, 48 comparisons. The largest relative deviation is 1.8·10⁻³, limited by the Ĝ grid.
  So the dual length and the Gauss-sum normalization are the same for composite moduli. The root number is a phase and
  does not enter |S_u|.

**The deficit is ordered by c** (ratio actual/surrogate over all rows, `summary.md` T2):

| B | m | c = 0 (conductor u) | c = 1 ((1−ω)u) | c = 2 (3u) |
|---|---|---|---|---|
| 1.6·10⁶ | 0.40 | 0.903 ± 0.023 | 0.992 ± 0.026 | 0.995 ± 0.016 |
| 1.6·10⁶ | 0.45 | 0.791 ± 0.024 | 0.822 ± 0.025 | 0.999 ± 0.018 |
| 1.6·10⁶ | 0.50 | 0.725 ± 0.021 | 0.969 ± 0.032 | 0.792 ± 0.012 |
| 10⁵ | 0.60 | 0.475 ± 0.032 | 0.508 ± 0.037 | 0.683 ± 0.039 |
| 10⁵ | 0.70 | 0.356 ± 0.024 | 0.492 ± 0.036 | 0.495 ± 0.023 |

**The self-dual dip.** For c = 2 the ratio dips at exactly m = 1/2 for every B: 0.756, 0.849, 0.796, 0.780, 0.786, 0.792.
It then recovers at m = 0.55 (0.87–0.97) before the dual regime takes over. [numerical]
- m = 1/2 is the self-dual point N = √(3N𝔣)/(2π) for c = 2. For c = 1 the dip sits at m ≈ 0.45, where predicted.
- So at self-duality the actual lies below both diagonal predictions: the mixed ("partial swap") terms are negative. In
  the dual table (§5), at m = 0.5 the actual is 0.78 of the surrogate for prime rows, while the random model on the dual
  gives 0.92.

## 3. Is the gap real? (`summary.md` T1, `analyze_*.txt`)

**The gap per B.** gap = log(ratio_prime) − log(ratio_composite):

| m | 10⁵ | 2·10⁵ | 3·10⁵ (overlaps) | 4·10⁵ | 8·10⁵ | 1.6·10⁶ |
|---|---|---|---|---|---|---|
| 0.30 | +0.038 ± 0.067 | −0.067 ± 0.049 | −0.124 ± 0.044 | −0.110 ± 0.036 | −0.018 ± 0.029 | +0.014 ± 0.022 |
| 0.40 | +0.085 ± 0.086 | −0.040 ± 0.065 | −0.086 ± 0.050 | −0.028 ± 0.044 | −0.090 ± 0.037 | −0.022 ± 0.028 |
| 0.50 | −0.004 ± 0.075 | −0.037 ± 0.069 | −0.050 ± 0.060 | −0.050 ± 0.049 | −0.118 ± 0.038 | −0.022 ± 0.031 |
| 0.60 | −0.099 ± 0.115 | −0.133 ± 0.065 | −0.096 ± 0.061 | −0.183 ± 0.047 | – | – |

**Findings** [numerical]:
- **The surrogate was noisy in probe C.** At B = 3·10⁵ the prime-class surrogate M6 with 10⁶ draws (`artmask_3e5_q7.log`)
  is 8.036, 8.876, 9.944, 10.978 at m = 0.45, 0.5, 0.55, 0.6. Probe C's 4 replicas gave 8.200, 9.572, 10.761, 12.323.
  The surrogate's tail is heavy (one draw can carry 8% of the class M6), so the replica sd underestimates the error.
  With K = 32 the B = 3·10⁵, m = 0.5 entry of the probe C table becomes 0.771 against 0.810, not 0.719 against 0.818.
- **There is no gap without the functional equation.** Pooled over the disjoint sets, the gap is −0.021 ± 0.015,
  +0.028 ± 0.020, −0.036 ± 0.019, −0.023 ± 0.019 at m = 0.3, 0.35, 0.4, 0.45.
- **The B = 3·10⁵ small-m offset is a sampling fluctuation.** It comes from the prime rows with norm in [3·10⁵, 8·10⁵],
  which B = 3·10⁵ and 4·10⁵ share.
  - It sits in the extreme tail. At B = 4·10⁵, m = 0.3 there are 16 conjugate pairs with |S|²/mass ≥ 6 against 29.8
    expected (Poisson p ≈ 0.4%), and none ≥ 8 against 3.4 expected.
  - It is absent on disjoint rows: B = 8·10⁵ gives −0.018 ± 0.029 and 1.6·10⁶ gives +0.014 ± 0.022.
- **The gap is real in the functional-equation regime.** It is −0.053 ± 0.020 (m = 0.5), −0.074 ± 0.039 (0.55),
  −0.159 ± 0.036 (0.6) and −0.122 ± 0.044 (0.65). It is larger against min-7 rows: −0.09, −0.14, −0.22, −0.22.
- **It is not a normalization artefact.**
  - Prime rows have an exact diagonal of 1, since no source is divisible by u.
  - Renormalizing each composite row by its own masked diagonal raises the composite ratio by 0.005–0.018, which
    widens the gap slightly (`primerows_normcheck.py`, `logsP/normcheck.txt`).
  - The actual M2 matches the masked diagonal in both classes to within about 2%.

## 4. Decisive test: give prime rows the composite masks (`primerows_transplant.py`, `primerows_artmask.py`)

**Transplant.** For each prime row u = π, draw J = 3–4 composite rows v and compute
A_{u,v} = Σ_{n coprime to M(v)} w·χ_π(n), where M(v) is the set of factors of v that can divide a source. The surrogate
of A_{u,v} has exactly the distribution of v's surrogate. So mean|A|⁶/mean sur(v) can be compared with the composite
ratio, and with the same rows unmasked.

**Predictions.**
- If the gap were intrinsic to prime moduli (arithmetic of χ_π, reciprocity, pretentiousness), transplanted rows would
  stay at the prime value.
- If it is a mask effect, they move to the composite value.

**Result** (pooled over the disjoint B; shift = log(transplanted/prime) on the same rows, paired bootstrap;
residual = log(transplanted/composite)) [numerical]:

| m | gap (prime − composite) | shift, composite masks | residual | gap vs min-7 | shift, masks of min-7 rows | residual vs min-7 |
|---|---|---|---|---|---|---|
| 0.30 | −0.021 ± 0.015 | +0.001 ± 0.004 | −0.017 ± 0.013 | −0.013 ± 0.018 | +0.007 ± 0.008 | −0.004 ± 0.015 |
| 0.40 | −0.036 ± 0.019 | +0.003 ± 0.005 | −0.033 ± 0.017 | −0.025 ± 0.021 | +0.019 ± 0.011 | −0.005 ± 0.018 |
| 0.45 | −0.023 ± 0.019 | +0.023 ± 0.006 | −0.001 ± 0.018 | −0.061 ± 0.024 | +0.038 ± 0.013 | −0.024 ± 0.020 |
| 0.50 | −0.053 ± 0.020 | +0.037 ± 0.007 | −0.022 ± 0.017 | −0.091 ± 0.023 | +0.077 ± 0.013 | −0.019 ± 0.019 |
| 0.55 | −0.074 ± 0.039 | +0.042 ± 0.013 | −0.034 ± 0.033 | −0.139 ± 0.051 | +0.090 ± 0.025 | −0.039 ± 0.044 |
| 0.60 | −0.159 ± 0.036 | +0.070 ± 0.015 | −0.086 ± 0.033 | −0.218 ± 0.042 | +0.145 ± 0.022 | −0.074 ± 0.039 |
| 0.65 | −0.122 ± 0.044 | +0.105 ± 0.019 | −0.019 ± 0.038 | −0.215 ± 0.053 | +0.208 ± 0.030 | +0.001 ± 0.049 |
| 0.70 (10⁵ only) | −0.084 ± 0.074 | +0.130 ± 0.030 | +0.046 ± 0.068 | −0.246 ± 0.089 | +0.303 ± 0.052 | +0.057 ± 0.084 |

**What the table shows.**
- The shift is zero where there is no functional-equation deficit (m ≤ 0.4). It switches on with the deficit and grows
  with m. For masks taken from min-7 rows it is about twice the composite-average shift, because q = 7 is the strongest
  mask.
- The residuals are consistent with zero except at m = 0.6 (2.6σ; §7).
- Per B, the shift is positive at all 23 points with m ≥ 0.45 except one (B = 2·10⁵, m = 0.55: 0.000).

**Artificial mask {π₇} alone** (`artmask_3e5_q7.log`; G = all genuine rows π₇·π′ with π′ prime and N(π′) above the
largest source norm, so their mask is exactly {π₇}). P are the prime rows, A the same rows masked at π₇. The surrogate
uses 10⁶ draws per mask.

| m | P/sur₀ | A/sur₇ | G/sur₇ | log(A/G) |
|---|---|---|---|---|
| 0.30 | 0.902 | 0.932 | 0.931 | +0.002 ± 0.058 |
| 0.40 | 0.885 | 0.924 | 0.978 | −0.057 ± 0.066 |
| 0.45 | 0.836 | 0.911 | 0.953 | −0.045 ± 0.089 |
| 0.50 | 0.775 | 0.837 | 0.813 | +0.029 ± 0.070 |
| 0.55 | 0.750 | 0.868 | 0.871 | −0.003 ± 0.107 |
| 0.60 | 0.595 | 0.674 | 0.665 | +0.014 ± 0.073 |

Same characters, an artificial mask, and an imprimitive sum: A lands on the genuine composite values G.

**By conductor class** (B = 4·10⁵, 8·10⁵, 1.6·10⁶, `byc.md`).
- The shift switches on first where the dual is shortest. At m = 0.4: +0.024 ± 0.013 (c = 0) against +0.007 ± 0.007
  (c = 2). At m = 0.45: +0.039 (c = 0), +0.037 (c = 1), +0.017 (c = 2).
- At m = 0.5 the gap is −0.100 (c = 0), −0.110 (c = 1), −0.048 (c = 2).

## 5. Why a mask raises the ratio once m > 1/2

**(a) The surrogate's sensitivity to a mask grows with length.** [derived + numerical]
- For a random completely multiplicative f, the sixth-moment count Σ_{n₁n₂n₃=n₄n₅n₆} has the Dirichlet series
  Σ d₃(𝔫)² N𝔫^{−s} = ζ_K(s)⁹·A(s). Its local factor at 𝔮 is Σ_j d₃(𝔮^j)² N𝔮^{−j} = (1+4x+x²)/(1−x)⁵, with x = 1/N𝔮.
- Masking 𝔮 replaces this by 1 and multiplies M2 by (1−x). So the leading term of M6/M2³ is multiplied by
  (1−x)²/(1+4x+x²): 0.46 for N𝔮 = 7, 0.65 for 13, 0.74 for 19.
- At finite length only the powers 𝔮^j that fit into the window contribute, so only part of the factor is realized.
  The realized part grows with log N.
- Measured (`tables.md`; 10⁶ draws at B = 3·10⁵, 2·10⁵ at B = 10⁵), the factor for 𝔮 = π₇ is:
  - B = 3·10⁵: 0.903, 0.873, 0.866, 0.834, 0.812, 0.796 at m = 0.3, 0.4, 0.45, 0.5, 0.55, 0.6.
  - B = 10⁵: 0.928 at m = 0.3 down to 0.808 at m = 0.7.
- The sixth-moment diagonal is exactly ideal equality: a sixth-power coincidence would need an ideal of norm < e, which
  is only (1). So the μ₆ model here is the Steinhaus model at this order.

**(b) The actual's sensitivity does not grow.** [numerical]
- On the same prime rows, masking π₇ multiplies the actual's M6/M2³ by 0.935, 0.899, 0.921, 0.897, 0.931, 0.891
  (B = 3·10⁵, same m as above), and by 0.93–1.02 (mean 0.96) at B = 10⁵, m = 0.5…0.7.
- In the short regime (m ≤ 0.45) this matches the surrogate's factor, as it must, since there the actual equals the
  surrogate.
- Beyond m = 1/2 it stays near 0.9 while the surrogate's factor falls to 0.80. The ratio 0.891/0.796 = 1.12 at m = 0.6 is
  the shift +0.11 to +0.15 seen in §4.

**(c) Why: in the dual regime the actual is the random model of its shorter dual.** [numerical]
- `primerows_dualsurr.py` replaces conj χ_u by a random masked f in the exact dual representation of §2 (the "dual
  surrogate", dsur). Row samples are stratified by class and c; the actual is taken over all rows.
- At B = 10⁵ (`tables.md`), pooled over c with row weights:

| m | class | dsur | actual | orig. surrogate | dsur/sur | actual/sur |
|---|---|---|---|---|---|---|
| 0.5 | prime | 7.42 | 6.27 | 8.07 | 0.919 | 0.776 |
| 0.5 | min-7 | 3.77 | 3.42 | 3.90 | 0.965 | 0.876 |
| 0.6 | prime | 6.03 | 5.70 | 9.80 | 0.616 | 0.581 |
| 0.6 | min-7 | 3.14 | 3.15 | 4.51 | 0.697 | 0.700 |
| 0.7 | prime | 5.21 | 5.25 | 11.75 | 0.443 | 0.446 |
| 0.7 | min-7 | 2.77 | 2.95 | 5.17 | 0.535 | 0.571 |
| 0.7 | other composite | 4.60 | 4.56 | 9.85 | 0.467 | 0.463 |

- From m = 0.6 on, the dual surrogate reproduces the actual per class to within about 6%. At B = 3·10⁴
  (m = 0.6, 0.7, 0.8; smaller samples, so the actual carries about 10% noise) it is within 13%, and the prime/min-7
  gap is predicted as 0.11, 0.24, 0.34 against an observed 0.12, 0.17, 0.44.
- It also reproduces most of the class gap: predicted log(0.535/0.443) = 0.19 against observed 0.25 at m = 0.7, and
  0.12 against 0.19 at m = 0.6.
- The dual of a row is short. In the check run at B = 3000 the median of the dual mass sits at N(n) ≈ N/1.5–N/2.3
  (c = 2) and N/6–N/9 (c = 0, 1) at m = 0.6, and at N/6–N/10 (c = 2) and N/17–N/40 (c = 0, 1) at m = 0.7
  (`primerows_dual.py` profile column). The ratio scales as B^{1−2m}, so at B = 10⁵ the duals are a further factor 2
  (m = 0.6) to 4 (m = 0.7) shorter. At such lengths the local factor at 7 is barely realized, which is (b).
- At m = 1/2 neither diagonal is right. The actual lies below both (the dip of §2), but the transplant shows the mask
  still acts in the same direction.

**Summary of the mechanism.**
- The surrogate is a fair comparator only at a single length. With the functional equation, the actual "lives" at the
  dual length, while the surrogate is evaluated at N.
- How much the surrogate overestimates depends on how fast its M6 grows from the dual length to N. That growth includes
  the realization of the local factors of the unmasked small primes.
- A row that already lacks π₇ (or π₁₃) has less growth to overestimate, so its deficit looks smaller.
- Prime rows lack nothing, which is all there is to their "stronger deficit". [numerical for B ≤ 1.6·10⁶,
  m ≤ 0.7; the general statement is a conjecture]

## 6. Other lenses

**Composite subfamilies as twists by χ_q.**
- The transplant changes only the mask, not the character (no χ_q twist), and it reproduces the composite ratio. So the
  twist by a fixed small-conductor χ_q is irrelevant. [numerical]
- Subclass ordering follows mask strength (`subclass.txt`, m = 0.5): rows with ≥ 3 factors and rows containing a
  conjugate pair π·π̄ (two masked primes) sit above rows with two factors, which sit above prime rows. For example, at
  B = 8·10⁵: 0.905, 0.982, 0.799, 0.739.
- The smallest-factor bins of `analyze_3e5_s345.txt`: q = 7, 13 are highest; q ≥ 31 is close to prime rows.
- Composite rows without small factors (smallest norm > 200, weak masks) are not "composite-like"; they sit with the
  prime rows. At B = 3·10⁵, m = 0.5, 0.55, 0.6: 0.786, 0.733, 0.642 against prime 0.771, 0.767, 0.605. At
  B = 2·10⁵: 0.733, 0.660, 0.580 against 0.837, 0.866, 0.605.

**Reciprocity.**
- By reciprocity χ_u(π′) is a function of u modulo small moduli, equidistributed for prime and composite u alike.
- No row–source correlation is needed: the transplanted prime-modulus characters behave like composite ones. [numerical]

**Large values and pretentiousness** (`largevalues_*.log`, prime rows, value of the multiplicative character λ_u at π₇).
[numerical]
- The surrogate's M6 does not depend on f(π₇): conditional M6 for Re f(π₇) = 1, ½, −½, −1 is flat within ±5%
  (the noise level), and the share from f(π₇) = 1 is 0.16–0.175 against 1/6. Its tail at these lengths is not
  "pretending to be 1 at 7". The local factor acts through the number of representations n = π₇^j·m, not through
  alignment.
- In the functional-equation regime the actual is, if anything, anti-pretentious at 7. At B = 10⁵, m = 0.6 the
  conditional M6 is 4.16, 4.94, 6.27, 7.60 for Re λ_u(π₇) = 1 … −1, and λ_u(π₇) = 1 rows carry 12–14% of Σ|S|⁶.
  Presumably this reflects the J₀-shaped dual weight, whose first lobe changes sign. [conjecture]
- It is noisy at B = 3·10⁵ and irrelevant to the class gap.

**Inert factors.**
- Rows with an inert prime factor (5–6% of composites) have slightly higher ratios than other composites on average:
  about +0.06 in log at m = 0.5 and 0.6, with single values between −0.15 and +0.19 and se 0.06–0.13. The mask
  (q = 5, norm 25) is weak, so this is not obviously a mask effect.
- They are too few to matter for the class comparison. Not investigated further.

## 7. What remains open

- **The m = 0.6 residual.** After the transplant, prime rows remain −0.086 ± 0.033 below composites (pooled over three
  B) and −0.074 ± 0.039 below min-7 rows.
  - At m = 0.5, 0.55, 0.65, 0.7 the residuals are −0.02, −0.03, −0.02, +0.05, and the pure-{π₇} comparison at
    B = 3·10⁵, m = 0.6 gives +0.014 ± 0.073. So I read it as a fluctuation, but a small second-order effect is not excluded.
  - One candidate: the dual of a genuine composite is masked at q, while the dual of the transplanted (imprimitive) sum is
    not. I did not compute the dual surrogate of the imprimitive sum. [conjecture]
- **No analytic formula for the mixed regime.** At m ≈ 1/2 the actual lies below both the original and the dual diagonal
  (the self-dual dip). A CFKRS-type swap expansion with masked local factors, evaluated at the shifted arguments, should
  give both the dip and the mask dependence. I did not attempt it. [conjecture]
- **Asymptotics.** The mask effect should grow with log B at fixed m > 1/2, because the realized part of the local factor
  at 7 grows toward 2.17 at the original length while the dual length also grows. The present B range (10⁵ to 1.6·10⁶)
  is too short to see a trend in the gap. [conjecture]
- **Sharp weight.** Only the smooth weight was studied here.

## 8. Files and reproduction

All scripts are under `research/rip/moments_probe/` and run with `python3 -I`.

| file | what |
|---|---|
| `primerows_core.py` | rows with metadata (N(u), k_u, conjugate row, mask key), actual sums, per-row surrogate replicas, exact masked diagonal, cluster bootstrap |
| `primerows_run.py` | data run: actual S_u and K surrogate replicas per row → `logsP/run_<B>.npz` |
| `primerows_analyze.py` | class tables, conductor split, smallest-factor bins, shape, null replicas (`analyze_*.txt`) |
| `primerows_dual.py` | Poisson/dual formula with the 3-part of the conductor, checked row by row; dual mass profile |
| `primerows_dualsurr.py` | random model applied to the dual representation (`dualsurr_*.json/log`) |
| `primerows_transplant.py` | mask transplant (`transplant_*.json/log`, `transplant_rows_*.npz`) |
| `primerows_artmask.py` | artificial mask {π₇} on prime rows vs genuine π₇·π′ rows, 10⁶-draw surrogates (`artmask_*`) |
| `primerows_byc.py`, `primerows_summary.py`, `primerows_tables.py`, `primerows_subclass.py` | pooled tables (`byc.md`, `summary.md`, `tables.md`, `subclass.txt`) |
| `primerows_largevalues.py` | conditional moments on the value at π₇ (`largevalues_*`) |
| `primerows_normcheck.py` | per-row renormalization by the exact masked diagonal (`normcheck.txt`) |

**Commands** (seeds are fixed, so outputs are reproducible). The raw `run_*.npz` files total about 600 MB and were moved
out of the repository; regenerate them with:

```
python3 -I primerows_run.py --B 100000 --m 0.3 0.35 0.4 0.45 0.5 0.55 0.6 0.65 0.7 --K 64 --out logsP/run_1e5.npz   # 4 min
python3 -I primerows_run.py --B 200000 --m 0.3 0.4 0.45 0.5 0.55 0.6 0.65 --K 32 --out logsP/run_2e5.npz           # 3 min
python3 -I primerows_run.py --B 300000 --m 0.3 0.35 0.4 0.45 0.5 0.55 0.6 --K 32 --out logsP/run_3e5.npz          # 2 min
python3 -I primerows_run.py --B 400000 --m 0.3 0.4 0.45 0.5 0.55 0.6 --K 24 --out logsP/run_4e5.npz               # 4.5 min
python3 -I primerows_run.py --B 800000 --m 0.3 0.35 0.4 0.45 0.5 --K 24 --out logsP/run_8e5.npz                    # 3 min
python3 -I primerows_run.py --B 1600000 --m 0.3 0.35 0.4 0.45 0.5 --K 16 --out logsP/run_1.6e6.npz                 # 5.5 min
python3 -I primerows_run.py --B 30000 --m 0.5 0.6 0.7 0.8 --K 128 --out logsP/run_3e4.npz
for B in 1e5 2e5 3e5 4e5 8e5; do python3 -I primerows_transplant.py logsP/run_$B.npz --J 4 --out logsP/transplant_$B.json; done
python3 -I primerows_transplant.py logsP/run_1.6e6.npz --J 3 --out logsP/transplant_1.6e6.json
for B in 4e5 8e5 1.6e6; do python3 -I primerows_transplant.py logsP/run_$B.npz --J 4 --pools composite --saverows logsP/transplant_rows_$B.npz; done
python3 -I primerows_summary.py; python3 -I primerows_byc.py 4e5 8e5 1.6e6; python3 -I primerows_tables.py
python3 -I primerows_artmask.py --B 300000 --m 0.3 0.4 0.45 0.5 0.55 0.6 --q 7 --D 1000000 --out logsP/artmask_3e5_q7.json
python3 -I primerows_artmask.py --B 100000 --m 0.3 0.4 0.5 0.55 0.6 0.65 0.7 --q 7 --D 200000 --out logsP/artmask_1e5_q7.json
python3 -I primerows_dual.py --B 3000 --m 0.4 0.5 0.6 0.7 --nrows 1 --rmax 30 > logsP/dualcheck_3000.txt
python3 -I primerows_dualsurr.py --B 100000 --m 0.5 0.6 0.7 --nrow 1200 --K 128 --run logsP/run_1e5.npz --out logsP/dualsurr_1e5.json
python3 -I primerows_dualsurr.py --B 30000 --m 0.6 0.7 0.8 --nrow 1500 --K 256 --run logsP/run_3e4.npz --out logsP/dualsurr_3e4.json
python3 -I primerows_normcheck.py 2e5 4e5 8e5 1.6e6 > logsP/normcheck.txt
python3 -I primerows_largevalues.py --B 100000 --m 0.3 0.4 0.5 0.6 0.7 --D 400000 --out logsP/largevalues_1e5.json
python3 -I primerows_largevalues.py --B 300000 --m 0.3 0.4 0.5 0.55 0.6 --D 300000 --out logsP/largevalues_3e5.json
python3 -I primerows_analyze.py logsP/run_3e5.npz --sections 3 4 5 --nb 300 > logsP/analyze_3e5_s345.txt   # likewise for the other B
python3 -I primerows_subclass.py logsP/run_1e5.npz logsP/run_2e5.npz logsP/run_3e5.npz logsP/run_4e5.npz logsP/run_8e5.npz > logsP/subclass.txt
```

**Normalization check** (§3). Per-row renormalization by the exact masked diagonal (`diag` in the npz) leaves prime rows
unchanged and raises composite ratios by 0.005–0.018. For example, at B = 8·10⁵, m = 0.5: 0.831 becomes 0.839.
