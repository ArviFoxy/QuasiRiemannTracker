# R3 - New powers in the final return: ledger, re-derivation from Lean, combinations, exact prices

Date 2026-10-28. Python only (no `lake`/`lean`, nothing committed or posted). Scripts and logs: `research/newpowers/r3/` (`run_all.sh`, `logs/`).
Instruction followed: earlier notes (`REPORT.md`, `B1`, `barriers`, `P1_PROBLEM`) are **hypotheses**; every conclusion below is tagged.

* **[L]** read in Lean (path:line). **[D]** my derivation (checked exactly or numerically, script named). **[N]** numerics. **[I]** inference, not verified.
* `COL/` = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/`, `OAI/` = `.../openai_baseline/OAI/NumberTheory/DirichletL/`, `P83/` = PR 83 `sil_density_split_20261026/`, `P86/` = PR 86 `density_split_fine_chain/`.
* Scenarios (as `lemmaW.md`): **A** = floor 0.60, count step 73 / physical step 38 (theta* 0.873946275, gap to bar 0.8739358 = +1.047e-5; its faces are uncertified optimiser outputs);
  **B** = PR 86 chain, role split 46/38 (0.873954831, gap +1.903e-5).

---------------------------------------------------------------------------------------------------------------------------------

## 0. Bottom line

1. **Nothing found that closes the gap by recombining the return's existing inputs.** The return is a *consumer* of five moment statements; the only amplifier whose identity is used inside the return's own counting is the sixth-power Euler-factor identity (long line). The fourth-power transfer lives only inside the source faces (chain), not in the return. [L, section 1]
2. **Three new, checked tools** (section 3): (i) the count exponent as a series ("resistor") network, `(1-Z)/(R-(1-d)) = 1/d + A_P(1/(d A_I) + 1/(k_L-d))`, equal to the toolchain's `N/J` to 1e-16; (ii) the *plateau principle* - exact copies of any exchange rate pay only where the base moment bound is flat in the row count; (iii) a pointwise model (`pm.py`) that reproduces the exact Bernstein-cover theta* to <=1e-9 (base) and the 20 lever prices of `lemmaW.md` to <=4e-9 (<=3.6e-8 at 2e-4) - used for all prices here.
3. **One lever is shared by three places** (new, [L]+[D]+[N]): the probe's marked energy (`x+y=1-ell`), the inverse capacity (`r+2z<=1`) and the diagonal range of the Moebius moment feeding the sixth-power amplification are all the same hybrid-norm statement (`OAI/Reflection/UniformSieve.lean:14`, uniform over *arbitrary* bounded coefficients). A single power saving `e` in the column branch (dual length may exceed the critical length by `Z^e` for free) is worth, **exact-cover verified**:

   | e needed (Z-exponent) | A | B |
   |---|---|---|
   | probe only (c_E = 2 -> 1.99904) | 1.66e-4 | 3.02e-4 |
   | probe + inverse capacity | 1.30e-4 | 2.35e-4 |
   | probe + inverse + Moebius diagonal range | **8.9e-5** | **1.60e-4** |

   (P1-language: `N <= K^(1+e/(1-ell))`, i.e. delta' = 2.0e-4 / 1.57e-4 / 1.07e-4 in A.) This is the smallest demand of any candidate and the only one acting on three inputs; it is atom 1, and no library ingredient proves it.
4. **Every "new amplifier" candidate fails at a named inequality** (table in section 5): mixed 6/4 long line (needs a twist-averaged lower bound that is false by orthogonality), squares/cubes amplification of the reflected rows (redundancy term `A*N*B`, margin 0), twist-to-dilation conversion in the column branch (loses 1/3 in exponent through the sextic sieve's `(KD)^(2/3)`), amplified marked inverse (slope +0.56 .. +1.22 per unit slot, needs <0), doubled slots via `D^2` (touches only the diagonal `p=p'`, mass `1/|pool|`; needs a 0.91% discount), Holder-6 (needs `mu_6 <= 1.154`, library gives 1.52, ideal sieve amplified by sixth powers 1.23; critical exchange rate 2.29).
5. **Holder-6 is the largest prize**: a diagonal sixth moment of the numerator packet would lower E by 0.021-0.026 (>=400x the 4.9e-5 needed), and the threshold is only 15% above diagonal. It is also the farthest from the library (needs a Lemma-18.1-type induction for three plain copies).
6. **Best synthesis [I]**: B2's marked-HIGH gate (chain level, library-only count, s0 lower by 5-8.6%, theta 0.873938984, gap +3.2e-6) *plus* a column excess of about e = 4e-5 (probe+inverse) or 5e-5 (probe only) reaches the bar; every return lever is linear (superposition error <=2e-8, section 4).

---------------------------------------------------------------------------------------------------------------------------------

## 1. Ledger: every amplifier / moment power in the final return

The interface between the return and the analysis is the **moment contract** `Cycle25DetectorRawFiber.BaseMoments` / `Moments` (`COL/Cycle25/Assembly/Count/Moments.lean:14-65`) plus the two `GlobalSource` faces (`P86/Return/Endpoint.lean:22,48`). The return never touches a Gauss sum; it manipulates scalar exponents. [L]

| # | place | exact statement used [L] | identity / mechanism | power / constant |
|---|---|---|---|---|
| 1 | **long line L** `hI0` (`COL/Record1252270103Return/CountCurve.lean:60`) | `no_slot_endpoint` (`OAI/Hecke/InverseAmplificationEndpoint.lean:11-98`), `sourceExponent r = max 1 ((1+5r)/6)` (`InverseAmplificationBudget.lean:10`) | Euler-factor identity at a prime `P`: `series chi = (1 - chi(P)P^-s) series psi` when `idealCoeff psi = deletePrimes {P} (idealCoeff chi)` (`InverseAmplificationColumn.lean:12`, `prime_column_identity :47`), i.e. `psi_{uP^6}(n) = psi_u(n) 1_{(n,P)=1}`; `(u,P) -> uP^6` injective; norm `U*V^6` (`InverseAmplificationPowers.lean:8`); averaged over `typedPrimePool` (`InverseAmplificationPrimePool.lean:18,41`) | **sixth powers**, exchange rate 6, multiplicity `(H/U)^(1/6)`; base bound `RawMoment` (`InverseAmplificationRaw.lean:11`) = Lemma 17.1 at `z=0`, diagonal only for `D^(1+c) <= H`; gives slope `k_L = 5/6` |
| 2 | **inverse line I** `hI` (`CountCurve.lean:62`) | `BaseMoments.inverse_marked` (`Moments.lean:41-45`): for selected slots `r + 2*sum w < 1`, `2r + 8*sum w < 3` the second moment `sum_u ||M_r Q||^2 <= C U^(1+eps)`; baseline form `original_source_energy` (`OAI/Dictionary/InverseMarkedReferenceSourceEnergy.lean:33,58`) | no amplifier in the line; slot cost from the reflected energy `T_d` (hybrid quadratic x cubic norm, `OAI/Reflection/UniformSieve.lean:14`: `(X+Yq Bq) Bq (Yq+L+(Yq L)^(2/3))`, arbitrary coefficients `|A|,|aP|<=1`) | second moment; **c_I = 2** |
| 3 | **plain line P** `hA` | `AffineMarkedMoment` (`COL/Record12518109Count/MarkedFiber.lean:20`), `piecewise_marked_count` (`CountMoments.lean:16`): `2m + Lam*sum w <= B` => `sum_u ||S_m S_m Q||^2 <= C U^(1+eps)` | face `GlobalSource B Lam cap` from the chain (sixth-power pool + Sil's `D^4` transfer, `whole_column`) | **fourth moment**, slots weight 2, cost `Lam` per unit width with multiplicity |
| 3' | natural tail `hP` (`CountCurve.lean:64`) | `Moments.plain_marked` (`Moments.lean:17`): `2m + 6*kappa*sum w <= 1` | Collet's face | 4th moment, cost `6 kappa` |
| 4 | plain unmarked `hP0` | `plain_unmarked` (`Moments.lean:46`): `<= C U^(max 1 (2m)+eps)` | z=0 case of Lemma 18.1 | 4th moment, no restriction on length |
| 5 | **numerator Holder** | `weighted_row_holder` (`COL/Cycle25/Numerator/Holder.lean:35`), `weighted_amplitude_bin` (`AmplitudeHolder.lean:15-23`): `L^2 (sum|S|)^4 <= #^3 sum |S|^4 |Q|^2`; exponent `total - selected/2 + (3R+1+eps)/4`; `numeratorExponent` (`COL/Record1252270103Return/GenericScalar.lean:14`) | Holder (4, 4/3), pointwise `||Q||>=L` used at power 2 (docstring `Holder.lean:8`: "selected prime factors occur inside the fourth moment with exponent two, not four") | **Holder-4**, halving `delta p C / 2` |
| 6 | **numerator face** | `finite_physical_pair_affine` (`P83/ReturnD/PhysicalDirect/Input.lean:49`): `sum_u ||P1 P2 prod_i slot_i||^2 <= C U^(1+eps)` if `X1+X2+Lam*sum width <= B`, `sum width <= cap`; pools `primePool .. (U^width i)` depend only on the width, so repeated lists are inside the statement at linear cost | same face as 3 | 4th moment, weight 2 |
| 7 | **probe energy** | `Geometry.Parameters.x_add_y : x+y = 1-ell` (`COL/Record1252270103Return/Geometry.lean:16`); `compensated_reflected_exponent_with_length` (`.../Low/Detector/LowReflectedLength.lean:17`; hypothesis `hH` line 19, `hret` line 23): `T_d = 2H+2A0+2za-1-ell0-theta-N0-3B0`, `u = min{v,za,(v+za)/3}` | Lemma 14.3 + hybrid norm | **c_E = 2** (`2 za` in `T_d`) |
| 8 | shift / "dilation box" in the numerator | `scheduledCapacity`, `scheduled_capacity_damping` (`P83/ReturnD/PhysicalDirect/Geometry.lean:40,123`), `weighted_dilation_bin` (`BinBound.lean:22`) | shifted plain length `m0+v/2` costs `2t/Lam` capacity, paid by damping `delta v/4` | not an amplifier; `v=0` is the worst case [L] |
| 9' | **signal / probe Gram bound** | `compensated_gram_scale_bound` (`COL/Record1252270103Return/Low/Detector/LowGramScale.lean:21`; bound `3 (qX/L) (Y/(qX))^(1/6) Y^delta`), `source_gram_power` (`:46`), `LowGeometry.gram_power` (`COL/Record1252270103Return/Low/Geometry.lean:18`): `x + (y-x)/6 + y delta = 2 signal(theta) + y delta`, `signal(theta) = x/2 + (y-x)/12` | exceptional frequencies `k = a^6 e0` (Lemma 13.3 exact correlation) are *exact sixth-power copies* and each carries a genuine main term: the 1/6 is the density of sixth powers, here working **against** us (atom 4, `c_g = 1/12`) | sixth powers (density `X^(1/6)`), not improvable: fourth-power frequencies `D^4 e0` carry the row-dependent phase `chi_a(D)^2` and do not survive the sum over `a` |
| 9 | old rows `d<=dm` (`P83/ReturnD/Schedule.lean:51`), floor bin (`P83/.../FloorExponent.lean`), feedback `new_feedback` (`GenericFeedback.lean:10`) | natural face `6 kappa`, central cube norm `4/25` per slot, `(kappa-kappa_theta)/50` | sixth-power pool / cubes | not binding (old edges saturate ~0.87364; floor costs <=7e-8; feedback 1/50) |

Exponent identity (not trusted, re-derived [L]): `rowAt = 1/2 - h/6 - y/2 - ell/2 + z0 (h-d) + d/4 + delta/2 + delta p (ell - C/2) + 3dR/4` with `z0 = 17/50`; the `Ebase` constants of `P86/Return/Formulas.lean:86` follow from `numerator_kernel_exponent` (`GenericScalar.lean:23`) by `ring`, for arbitrary `(x,y,ell)` with `h := 1+ell-x`; I re-checked the coefficients of `x`, `ell` and the constant by hand.

---------------------------------------------------------------------------------------------------------------------------------

## 2. What the count and the numerator are, exactly (self-contained re-derivation)

Lines at `(delta, p)` with `q = delta p`, cutoff `t`, inverse length `r`, plain length `m = t-r` [L: `common_witness_count_bound`, `CountCurve.lean:48-127`; PR 86 `Formulas.lean:32-72`]:

    I(r) = 1 - delta r - (2 q/c_I)(1-r)          (c_I = 2, capacity z=(1-r)/2)
    P(m) = 1 - 2 delta m - 2 q (B-2m)/Lam        (face (B,Lam))
    L(t) = 1 - delta + (k_L - delta)(t-1)        (k_L = 5/6)
    R    = min_t max( crossing(I,P)(t), L(t) ),   numerator: Holder-4 exponent  total - selected/2 + (3R+1)/4,  theta >= Ebase + (3/4) d R.

The edge `d = h` (newTop), `p = 1/2`, branch C binds; `delta* = 0.4431 (A) / 0.4414 (B)`, `R = 0.612573 / 0.614242`, `t* = 1.1427`, `C = 0.04813`, `ell = 0.17088`, `m0 = 2 ell/h = 0.4245`.

---------------------------------------------------------------------------------------------------------------------------------

## 3. New lenses

### 3.1 Series network for R [D, `resistor.py`, exact]
With `a = k_L - d`, `A_I = 1 - 2p/c_I`, `A_P = 2 - 4p/Lam`, `Z = 2pB/Lam`:

    R - (1-d) = (1-Z) / [ 1/d + A_P ( 1/(d A_I) + 1/a ) ].

Verified against `N/J` of `cert_return.branch_affine` evaluated in Fractions at the binding point of both scenarios (difference 1e-16, `logs/resistor.log`) and against a brute-force `min_t max_r min(lines)` (0.612570). The three terms carry 22.6% / 49.4% / 28.0% (A) of the sum = the dual weights of B1 (P 0.226, I 0.495, L 0.279). Elasticities: `dR/dk_L = 0.0400`, `dR/dc_I = 0.0138`, `dR/dLam_C = 0.0039`, `dR/dB_C = -0.045`; `dtheta/dR = -0.1295`, `dtheta/dE = +0.2145`. Consequence: **the I term is the largest resistance (49%)**, so a given *relative* improvement is worth most there (c_I: 0.29% closes A), then L (0.24% of k_L).

### 3.2 Plateau principle [D]
Exact copies with exchange rate `e` (multiplicity `(H/U)^(1/e)`) turn a known bound `B(H)` for rows `<=H` into `min_{H>=U} B(H)/(H/U)^(1/e)` for rows `<=U`. This improves `B(U)` iff `B` is flatter than `H^(1/e)` somewhere. Bounds occurring in the return: diagonal Lemma 17.1/18.1 (slope 1: never); Moebius plateau `H<D` (slope 0: the sixth-power long line, where Lemma 17.1 gives the diagonal at `H>=D^(1+c)`); quadratic large sieve `N>K` (slope 0, but see 5.3: the plateau value is *attained* by aligned coefficient vectors, so copies cannot lower it for a coefficient class that contains them - and `bounded_column_hybrid_energy_extracted_type_uniform` is stated for arbitrary bounded coefficients [L]); sextic sieve `(KD)^(2/3)` (slope 2/3: pays for `e>1.5`).
So the sixth-power amplifier sits in the only place where it can pay; a different exact-copy family would have to be denser than `X^(1/6)` *and* act there.

### 3.3 Holder orders as large-values lines [D, `amplification_algebra.py` s.4]
`sum_B |S| <= max_v [ v + min(R, mu_k - k v) ]` over the moment lines `mu_k` (v = exponent of |S|). The Lean proof is the corner of the `k=4` line with slot credit: `v4 = (1-R-2 q C/d)/4 = 0.09023`, value `R+v4 = 0.70281`; pointwise cap `|S|<=U^(delta m0/2) = U^0.09404` lies just above it (lowering the cap by 4.05% would make it tie, by 4.11% would gain 4.9e-5), so it does not bind (B1's "no mixed regime" re-derived).
A `k`-th line beats the corner iff `mu_k < R + k v4`: `k=2`: 0.793 (impossible, diagonal is 1: Holder-2 worse by 0.0698 in E, [I] face `m0+z<=1/2`); **`k=6`: 1.154**; `k=8`: 1.335. Available `mu_6` for the packet (length `m0`, `S^3` has length `3 m0 = 1.2734`): large sieve `K+D`: 1.273; sextic sieve (`Lemma 9.1`, `K+D+(KD)^(2/3)`): **1.516**; amplified by sixth powers: 1.228 (ideal sieve) / 1.516 (sextic); critical exchange rate for the ideal sieve **2.29** (exchange rates 2: 1.137; 3: 1.182; 4: 1.205). Because the fourth moment is Lindelof-on-average for *every* length (Lemma 18.1, z=0, `plain_unmarked`) but the sixth is not, `k=4` is where the library stops.

### 3.4 One column-excess lever [L]+[D]+[N]
Probe: `hH` and `hret` of `compensated_reflected_exponent_with_length` say `T_d <= H - 3d` with equality at `d=0, za = ell`: the dual length equals the row count `K`. Inverse: `r + 2z <= m` is `T_d <= H + z`. Long line: `RawMoment` needs `D^(1+c) <= H`. A saving `e` in the dual-diagonal term of the hybrid norm relaxes all three by `e` (Z-units): probe `x+y = 1-ell+e` (then `ell = 11/3-4 theta + e/3`, `y = h-2ell+e`, Lean-literal `signalShift`), inverse `r+2z <= 1+e/h`, long `L(t) -> L(t) - (5/6)e/h` [I: that Lemma 17.1 at `z=0` is relaxed by the same e]. Prices in section 4.

---------------------------------------------------------------------------------------------------------------------------------

## 4. Exact prices

Model: `pm.py` (pointwise; calibration `logs/calib.log`: base 0.873954830 vs exact 0.873954831 (B), 0.873946275 vs 0.873946275 (A); lever prices differ by <=4e-9 for `dE, dR, dC, c_I, k_L` up to 2e-4). Valid while newTop/C binds (not for `Cfull`: old edges bind at ~0.87364). New levers verified in the **exact Bernstein cover** (`exact_check.py`, `exact_check_joint.py`, `logs/`): `eI` (inverse excess) and `sL` (long-line shift) with the branch polynomials re-derived (`t*J = T + sL D - d pp eI A_P`, `N = N0 - a d pp eI A_P - sL d A_I A_P`): at the PM-needed values the exact theta* is 0.873935801 (gap +1e-9, A) and exactly the bar (B). Joint (probe geometry as B1, floor receipts dropped, h scanned; free-h bonus 2.85e-7): exact gaps -2.5e-7 / -2.7e-7 / -2.9e-7 at e = 1.66e-4 / 1.30e-4 / 8.9e-5.

Needed size of each lever to reach the bar (`needed_sizes.py`):

| lever | A | B | % of the constant (A) |
|---|---|---|---|
| dE (additive) | -4.89e-5 | -8.84e-5 | - |
| dR (count lowered) | 8.09e-5 | 1.46e-4 | 0.013% of R |
| dC (capacity) | +4.41e-4 | +8.01e-4 | +0.92% |
| halving 1/2 -> 1/2+eps | eps = 0.00459 | 0.00834 | +0.92% |
| c_I (2) | 1.99414 | 1.98956 | -0.29% |
| k_L (5/6) | 0.83132 | 0.82969 | -0.24% |
| count face Lam_C / B_C | -0.92% / +1.78e-3 | -1.73% / +3.56e-3 | |
| physical face Lam_P / B_P (cap 0.09) | -0.91% / +1.30e-3 | -1.64% / +2.37e-3 | |
| plain-line shift (extra z at fixed m) | 3.59e-4 (+0.93% of z_P) | 6.72e-4 (+1.76%) | |
| probe column excess e_E (Z) | 1.66e-4 | 3.02e-4 | = c_E 1.99903 |
| inverse column excess e_I (U) | 7.39e-4 (e_Z 5.95e-4) | 1.33e-3 | |
| long-line fourth-power width w (U) | 8.65e-4 | 1.56e-3 | 0.41% of slot supply `ell/d=0.212` (2.4% of a pure fourth-power family) |
| diagonal extension of the Moebius range, e_Z (long only) | 2.79e-4 | 5.02e-4 | |
| joint e (probe + inverse) | 1.30e-4 | 2.35e-4 | |
| joint e (+ long range) | **8.86e-5** | **1.60e-4** | |
| doubled-slot discount eta (2nd copy 1 - eta/2 cheaper) | 0.0182 (0.91%) | 0.0328 (1.64%) | |

Superposition (A, half-size pairs; `more_prices.log`): `c_I/2 + k_L/2`, `c_I/2 + eps/2`, `e_E/2 + k_L/2`, `e_E/2 + c_I/2`, `e_E/3 + c_I/3 + k_L/3`, `w/2 + eps/2` all land within 2e-8 of the bar. Per-unit slopes (A): `dtheta/dE +0.2145`, `/dR -0.1295`, `/dC -0.0238`, `/dc_I +1.78e-3`, `/dk_L +5.19e-3`, `/deps -2.29e-3`, `/de_E -0.0630`, `/de_I(U) -0.0142`, `/dw -0.0121`.
Chain coupling [I, from B2's numbers, not re-run]: `k_L` enters PR 83/86's chain only through the unmarked density `rho(nu)=1-10nu/(15-6nu)` (`P83/Source/HybridGates.lean:55,62` `rhoOf`, `highJ`; `Density/StepGates.lean:152` `ds_high_aux`); `k_L = 0.8313` raises `10/(15-6q)` by 6.9e-4 at `q=0.6` (~ -1.5e-6), so the needed `k_L` is ~0.8316 not 0.8313. `c_I` and the column excess do not enter PR 86's chain (HIGH is *unmarked*); a tiny `e` moves the chain by <=2e-7 (`dq/q ~ 4e-5`). B2's marked-HIGH gate would make the chain use the count lines (c_I, Lam, k_L) - an unpriced second-order coupling.

---------------------------------------------------------------------------------------------------------------------------------

## 5. Candidates: mechanism, price, failing inequality, rescue

### 5.1 Long line: sixth powers mixed with twist-absorbed fourth powers  [D; price exact]
Formula: multipliers `a^6 b^4` with `b` limited to width `w` (units of log U): `H = U A^6 B^4`, multiplicity `A B`, bound `H/(AB)`, giving
`L(r) = (1+5r)/6 - min(w/3, (r-1)/12) - delta r` (pure fourth powers: `(1+3r)/4`). Needed `w = 8.65e-4` (A) = 0.41% of the slot supply, 2.4% of a pure fourth-power family; prices: `w=1e-3`: -1.21e-5 (A), `3e-3`: -3.6e-5, full fourth power 3.57e-2: -4.3e-4.
**Failure [L]+[D]**: `psi_{uP^4}(n) = psi_u(n) chi_n(P)^4` is a cubic twist *of the Moebius variable n*; the identity of `prime_reciprocal_identity` requires `idealCoeff psi = deletePrimes {P} (idealCoeff chi)`. `whole_column` (`arvi_..._FourthPower/GaussTransfer.lean:106`) absorbs twists sitting on the coefficient index of a polynomial in the *moduli* `a_i` as a dilation of the *frequency* `k` (`fourth_power :81`: `G_a(D^4 k) = chi_a(D)^2 G_a(k)`); the long moment has no frequency variable (Poisson in `u` against `n ~ D > U` lengthens the sum). Needed statement ("Lemma T"): for a bad row `|M_u(D)|^2 >= V` and a pool `B` of primes of norm `U^w`, `sum_b |M_{u b^4}|^2 >= c|B| V U^-o(1)`. It is false: the Gram matrix of cubic characters over the pool has diagonal `|B|` and off-diagonal controlled only when the pool exceeds the conductor `D^2`, so `sum_b|M_{ub^4}|^2 ~ |B|` independently of `V`. Rescue: none within (M)-type; the demand `w = 8.65e-4` equals the diagonal-range extension `e_Z = 2.8e-4` of 5.5.

### 5.2 Amplified marked inverse (slots kept)  [D, `amplification_algebra.py` s.2]
Amplify `r + c_I z > 1` by exchange rate `e`: exponent `1 + (e-1)/e (r + 2z - 1)_+ - delta r - 2 q z`; `d/dz = 2(e-1)/e - 2q = +1.22 (e=6), +1.06 (4), +0.89 (3), +0.56 (2)` against `2q = 0.443`; pays only for `e < 1.285`. Beyond the diagonal a partial saving pays only if the loss rate per unit excess is `< delta p = 0.2215` (a 78% saving of the large-sieve loss). Dead; this is why the K-copy lemma (`arvi_repeated_marks`, supply) is irrelevant here (supply `ell/d = 0.212 > z_M = 0.126`).

### 5.3 Squares / cubes on the reflected rows (quadratic invariance)  [D]
Rows `k a^2` carry the same quadratic character (exchange rate 2); slot indices `P b^3` the same cubic character (rate 3). Amplified column branch: `(K A + N B/A)` if the enlarged family obeyed `(K A^2 + N B)`, optimum `2 sqrt(K N B)` - the excess halves. **Failure**: the enlarged family contains the `A` copies of every aligned vector, so its large-sieve constant is `K A^2 + A N B` (non-squarefree rows; the test vector `c = chi_{k0}` gives `|S(k0 a^2)|^2 = N` for all `a`); after dividing by the multiplicity the `N B` term is untouched: margin exactly 0, loss `A` in the `K` term. Lean evidence: `bounded_column_hybrid_energy_extracted_type_uniform` holds for arbitrary bounded `A n b`, `aP`; and the paper's (14.18) `Z^(O/2+max{M-O, 2M-O+Q+V-N*})` (Lemma 14.3) is already maximal at `O=0` (powerful rows do not enlarge it) [paper, not Lean]. Rescue: an operator-norm bound for the `K x L` matrix of central values `S(k,P)` (P1) - the only statement using the Gauss-sum structure.

### 5.4 Twist-to-dilation conversion in the column branch  [D, `amplification_algebra.py` s.7]
Split `n = n1 n2`, convert `chi_{n2}(n1)^4` into `k -> k n2^4`, Cauchy in `n2`, sextic sieve on `n1` over rows `K N2^4`: exponent `a + max(1+4a, N1, (2/3)(1+4a+N1)) + N1` against `(K+N)N`; the `(KD)^(2/3)` term makes it worse by >= 1/3 for every `N2` (0.333 at `N=K^(1+1e-4)`). Dead.

### 5.5 Moebius diagonal range  [N, exact]
`RawMoment` with `D <= H Z^e` (c < 0) shifts L by `(5/6)e/h`: needs `e_Z = 2.79e-4` (A). Same atom as 5.1/5.6 (atom 2 at scale 3e-4).

### 5.6 Joint column excess (P1)  [section 4]
Lemma needed (exact Lean interface): (i) `hH` of `compensated_reflected_exponent_with_length`: `+e`; (ii) `Geometry.Parameters`: `x+y = 1-ell+e` with the Lean `signalShift` `-(5/6-x/3-ell/6)` (not `(4+y-x)/6`); (iii) `inverse_marked` / `original_source_energy`: `r + 2 sum w < 1 + e/h`, `inverse_requested_capacity`, `hI` exponent `-delta p e`; (iv) `RawMoment` for `c = -e/(d r)`, `exists_amplification_budget`, `amplified_norm_dominates`. Analytic content: for squarefree `k, n, P`, `sum_{N(k)<=K} |sum_n c(n) chi_k(n)|^2 << K^(1+o(1)) sum|c|^2` for `N <= K^(1+delta')`, `c(n) = g(n) sum_P a(P) N(P)^(-1/2) conj((n/P)_3)` uniformly in `|a|<=1`, `delta' = e/(1-ell)`. **Ingredients in the library**: quadratic sieve over Z[omega], Heath-Brown cubic sieve, twisted multiplicativity of `g`, the hybrid bound with arbitrary coefficients, K-copy/overlap adapters. **Missing**: any power saving beyond the large sieve for `g`-structured coefficients (automorphy of the cubic theta function; Dunn-Radziwill type results are inexplicit and cannot enter rational certificates).

### 5.7 Doubled slots, `D^2` identity, K copies  [L]+[D]
Lean: the face counts `Lam*sum width` with multiplicity and allows equal widths (same pool) - weight `|Q|^(2K)` costs `K Lam z`, credit `K q z/2`: **neutral for every K** (`half_price.log` reproduced by `pm.py`: eps = 0.0046 <-> eta = 0.0182). A discount `c_2 = 2 - eta`: `eps = eta/(2(2-eta))`; needed eta = 0.0182 (A), 0.0328 (B) (second copy 0.91% / 1.64% cheaper). `D^2` [coordinator, not verified by me]: the squared prime block `p^2` is the diagonal of `Q^2`, a fraction `1/|pool|` of its l^2 mass; cross terms `p p'` are products of two simple blocks and keep the `D^4` cost per block - so `D^2` cannot give a 0.91% discount for pools of any size. Need: a new source step with weight-4 slots (chain level).

### 5.8 Holder-6 / mixed Holder (4,6) / weights  [D]
Section 3.3: needs `mu_6 <= 1.154` (no slots; with slots the amplified-sieve cost `0.83/unit` exceeds the credit `0.059/unit`, so z=0); fractional or mixed weights and interpolation between orders are affine in the weights, hence endpoints (B1's claim re-derived). The pointwise route needs the packet's zero-free exponent `delta m0/2` lowered by 4.1%; the zero-free bound is attained (Prop 8.3 saturation).

### 5.9 Face-level equivalents  [N]
Same need as `Lam_C -0.92%`, `Lam_P -0.91%`, doubled copy -0.91%: all ~1% of a slot cost, while Sil's transfer moved the natural face from 4.5 to 3.7 (18%) and the density-split chain is ~20x that size - the demand is small, but the chain's inequalities (`q(6B-L)<=L`) are the source-side question, not the return's.

---------------------------------------------------------------------------------------------------------------------------------

## 6. Re-examination of `return-transfer/REPORT.md` section 3 (against Lean)

| claim | verdict |
|---|---|
| "high side never applies Poisson in the rows, no Gauss sum for `G(D^4 k)` to act on" | **True of the return's Lean text** ([L]: it manipulates scalar moments), **false of its inputs**: the marked inverse moment is a Gauss-sum object (hybrid norm). It blocks pure replacement inside the return, not a new input. The transfer cannot help the inverse side anyway: the trade slot <-> row costs 4 per unit width (`fourth_power`) against c_I = 2 (`original_source_energy`) [D]. |
| "plain and numerator moments are faces" | True [L] (`Endpoint.lean:22,48`). Role split already used (46/38). A different *kind* of face (weight 4, sixth moment) would be a new source theorem. |
| "marked inverse moment has no pointwise slot energy to pay" | Correct but misdirected: c_I = 2 is the reflection modulus squared; the tolerance that matters is the column excess e shared with the probe (3.4). |
| "long moment: fourth powers give cubic twists, not copies" | True [L] and strengthened [D]: the twisted family carries no information about the row (Gram diagonal), so no *mixture* works either (5.1). |
| "Levy's (4/3,4) Holder step is optimal given its inputs" | Re-derived [D]: corner of the 4th-moment line; beaten only by a 6th-moment line with `mu_6 <= 1.154`. |
| "a doubled slot costs 2 Lam in a face step" (listed as unverified) | Verified [L]: `hcap` of `finite_physical_pair_affine` counts widths with multiplicity. |

---------------------------------------------------------------------------------------------------------------------------------

## 7. Ranking and recommendation

1. **Column-excess lemma** (5.6): smallest demand (probe alone e = 1.66e-4; with inverse 1.30e-4; with the Moebius range 8.9e-5), three inputs, exact-verified interface. Plausibility low (atom 1/P1), Lean wiring ~300-700 lines (B1) plus regenerated rows.
2. **B2 marked-HIGH gate + small e** [I]: library-only chain change (gap -> +3.2e-6) then e ~ 4-5e-5 (or c_I 1.9982, k_L 0.8327, eps 0.0014, w 2.6e-4 by linearity).
3. **Holder-6 / sixth moment of short smooth packets** (5.8): largest payoff, needs `mu_6 <= 1.154`; a Lemma-18.1-type induction for three copies is the only route; no library piece.
4. Doubled-weight face (5.7): needs a new source step; 0.91% discount.
5. Dead: mixed 6/4 long line, squares/cubes on rows, twist-to-dilation, amplified marked inverse, pointwise cap.

## 8. Not done / caveats
* B2's marked-HIGH numbers and the chain coupling of `k_L` are taken from `B2_source_slope.md`/`B2/run_knobs.py`, not re-run. Scenario A's steps 47-74 are uncertified optimiser faces.
* The identification "column saving e = same relaxation in probe, inverse and Moebius range" is [I]; only the probe's is read in Lean literally (`hH`).
* `D^2` / `p^3` / `p^2` identities of the coordinator were not verified; Sil's mixed ledger (`MixedLedger`, `GlobalSlotSelection.lean`) was read only at the level of the `43/100` selection spec.
* Lemma 18.1's proof and Sil's `Kernel*`/`Mixed*` modules (~200 files) were not read; claims about what the chain can still give are inference.
* PM covers newTop/C only; `Cfull`-sized levers (>= ~3e-4) hit the old-branch edges.

## 9. Files
`r3/pm.py` (model + `needed`), `calib.py`, `needed_sizes.py`, `more_prices.py`, `price_tables.py`, `joint_p1.py`, `resistor.py`, `amplification_algebra.py`, `exact_check.py`, `exact_check_joint.py`, `run_all.sh`; `r3/tc/` = copy of the exact toolchain (`cert_return.py`, `gen_return_lean.py`, `pr86.py`, `best.py`, `levers_pr86.py`, `lowfloor_greedy.py`, faces `chain86.json`, `greedy_f060_dl005.jsonl`); `r3/logs/*.log` = outputs quoted above.
