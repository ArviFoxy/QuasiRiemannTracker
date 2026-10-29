# Arvi Zone probe: independent outer bound at M = 1

Window probed: M = 1, a = m1+m2 in [0.30, 1.50] (step 0.05), s in [0, 0.30] (step 0.025): 325 points, each with three splits
(m1 = m2, 3:1, (a, 0)), five mechanisms. Labels: **[rigorous]** (Lean definitions or standard theorems), **[heuristic]** (needs GRH / Lindelof for the
Hecke L-functions of Q(omega)), **[numerical]** (toy model, finite size). No face parameter was used. Read: the files named in the brief, Lean sources under
`Submissions/openai_baseline` and `Submissions/hailey_collet_1252270103/Record12518109Source/InitialMoment.lean` (whose `SourceFace` constants I ignored),
and of `research/` only `EnergyRegion.lean`, plus one directory listing and one read-only `git status --short` (path names only, no file contents; no other git command was run).

## 0. Result

**No mechanism rejects any of the 325 grid points, on any split. The outer bound is the whole window: a_out(s) >= 1.50 for every s.**
The classical "family + length" barrier a+s <= 1 (and, with the K^(1/6) perfect-sixth-power rows, a+s <= 5/6) is realised only by the *principal* rows,
and `initialKeep` removes exactly those. Every kept row has non-principal characters on all of A1, A2, S_i, so no row has a pole, and no admissible datum was found that aligns with a kept row. Acceptance is [heuristic] (GRH) + [numerical]; a rigorous rejection cannot exist unless GRH-type bounds fail. Since under GRH the Arvi Zone contains the whole window, any smaller outer bound would be false unless GRH fails: the whole window is the sharpest outer bound that can be stated without disproving GRH.
`fig/outer.png` is therefore uniform; `fig/control_nokeep.png` is a positive control (not the Lean statement): with the principal rows left in, a+s > 5/6 is rejected.

## 1. What the energy is

Paths are relative to `Submissions/openai_baseline/OAI/NumberTheory/DirichletL/` (`DL/`); `ER` = `research/lean/arvi_energy_region/EnergyRegion.lean`.

```
E = sum'_{z in O, initialKeep z}  Re Phi(N(z)/K) * |row_z|^2 ,   K = Z^M, M = 1            DL/Moments/InductionEnergy.lean:16-20
row_z = (X1 X2 prod_i D_i)^(-1/2) * A1(z) A2(z) prod_i S_i(z) ,   D_i = Z^(w_i)             DL/Moments/RetainedEnergy.lean:14-19
A_j(z) = sum'_{ideals I} eta(I) (m^6 z / I)_6 N(I)^(it) W_j(N(I)/X_j)   (ALL ideals)         DL/Moments/HeckeHeight.lean:125-128, HeckeExpansion.lean:13-25
S_i(z) = sum_{P in pool_i} beta_i(P) eta(P) (m^6 z / P)_6 N(P)^(it)                           DL/Moments/HeckeSlots.lean:11-14
beta_i(P) = chi_{theta_i eta0^-1}(P) W(N(P)/D_i) (N(P)/D_i)^(-sigma + i v_i)                  DL/Moments/NaturalFixedRaySourceCharacters.lean:20, DL/Hecke/PrimeAnnular.lean:15
```
* **Ring/rows.** O = Z[omega] = integers of Q(zeta_3), class number 1 (`DL/Hecke/Family.lean:13-14`); N(z) = ‖eisEmbedding z‖² = x²-xy+y² (`DL/Arithmetic/EisensteinEmbedding.lean:153`). Rows: all z in O, weight Re Phi(N(z)/K).
* **Symbol.** (.,.)_6 = `canonicalSextic` = cubic²·quadratic = sixth-power residue symbol, u = x^((NP-1)/6) mod P read as a unit of O (`EisensteinEmbedding.lean:461`, `DL/GaussSum/FiniteFourier.lean:801`),
  multiplicative on ideals (`DL/Eisenstein/CompactEnergyFamilies.lean:484`). m = `fixedBadMask`·`idealGenerator 1` = 2·lambda·unit, lambda = omega-1 (`DL/Moments/SecondHeightFamily.lean:15`), so
  (m^6 z/P)_6 = 1_{P∤m}(z/P)_6 (`DL/ChineseRemainder/PrimaryCompletions.lean:427`): primes above 2 and lambda drop out.
* **Lengths.** m_j = log_Z max(1,X_j) (`DL/Energy/Bands.lean:15`), s = sum w_i; W_j = `p.profile j`, Schwartz with support in [1/4, 9/4] (`DL/Moments/FiniteProfileExceptionalPair.lean:14-19`).
  Slot pool = prime ideals with N(P) <= 2D_i in the identity ray class mod rayModulus mod H (`DL/Moments/PrimeSlot.lean:14`, `DL/RayQuotient.lean:47`); W smooth on [1,2], sigma = 33/50, so
  slot coefficients are O(1) (a smooth weight, **not** N(P)^-sigma).
* **Normalisation.** Unit-size coefficients and 1/sqrt(length): the diagonal of every row is O(1) (each slot contributes ~ 1/log D), the trivial size is |row|² ~ T = Z^(a+s), and the bound says |row|² ≲ Z^eps *on average* over the K rows.
* **Kept rows.** `initialKeep η Q₀ z := z ≠ 0 ∧ ¬FixedInducingRow η Q₀ m 1 z` (`DL/Moments/DetectorEnergyInitialState.lean:21`, `DL/CenteredExceptionalProfile.lean:338`), Q₀ = `internalQ Q η₀` = Q ⊓ modulus(η₀), a multiple of 72 (`UnitRegionSource`, `ER:145-156`).
  Unfolding (`DL/Hecke/RowClosure.lean:174`, `DL/Moments/FixedRowMask.lean:29`): z is removed iff the primitive character inducing eta·(m^6 z/.)_6 has conductor dividing Q₀.
* **Bound.** C·diagonalControl(Phi)·control²·(1+|t|+height)^degree·Z^(M+eps), diagonalControl = 16(1+pi)²·max_{k<=2}‖Phi‖_{k,0} (`DL/QuadraticSieve/InitialBound.lean:200`), and sum_z|Phi(N(z)/K)| <= diagonalControl·K (`:208`).
* **Adversary.** *Outside* the exists-C and eventually-in-Z (`ER:145-160`, so Z-free): alpha (<= |alpha| slots), rayModulus, H, W, bPhi, eta, eta0, Q, eps, mesh. *Inside* (may depend on Z):
  T, theta_i (trivial on the pool: inert), w_i in [0,mesh], v_i, t, height (polynomially penalised), Phi (only its sup-norms enter; weights in [0,1] on norm values are arbitrary), profiles p (control²), X1, X2.
  Z real, M = 1 exactly. `energy_absolute` (`DL/Moments/InductionEnergy.lean:71`) gives the trivial bound E <= C·K·T.

Facts used below: (F1) for kept z the row character is non-principal on the plain sums and, for every theta, on the slot pool (`sector_nonprincipal`, `DL/Moments/NaturalFixedRaySourceCharacters.lean:65`) [rigorous];
(F2) its conductor norm is <= N(η.mod)N(m)N(72)N(rad z) ≲ K (`DL/Detector/RowRadicalConductor.lean:101`) [rigorous].

## 2. Mechanisms

**M1 degenerate rows. Rejected set: empty.**
Principal rows: for eta = 1 the rows z = w^6 (about 0.7·K^(1/6); 3,3,5,6,6,9 for K = 1e4…3e6) have row character 1_{(.,mw)=1}, a pole, hence A_j ~ 0.3 X_j, S_i ~ pi(D)/h and |row|² ≈ 0.04·T/(log D)^(2k)
(measured tau = |row|²/T = 4.2e-2, `logs/m1_degenerate.log`). They are removed: psi = trivial character (modulus (1), vacuously primitive, Q₀ ≤ (1)) induces the row character. **[rigorous, machine-checked]** `lean/PrincipalRowRemoved.lean`: for eta = trivial, `initialKeep` fails at z = w^6 for every w ≠ 0 and every Q (axioms: propext, Classical.choice, Quot.sound; `logs/lean_check.log`).
The removed set is {z: cond(eta(z/.)_6) | Q₀}, about 47·K^(1/6) rows (150…390 for K = 2e3…3e5), the rest of them non-principal of conductor | 72.
Kept degenerate classes (cubes/squares, c·w^6 with c ∤ Q₀, low conductor) have a non-principal character of conductor q: A_j is negligible once X_j >= q·Z^delta (M2) and generic otherwise; measured median tau ≲ 1e-6, max 3.5e-5 (vs 4e-2 for principal rows).
*Positive control* [numerical]: without the mask E_pr/K ~ Z^(1/6+a+s-1); measured exponents +0.14, +0.33, +0.54, +0.64 at a = 1.0, 1.2, 1.4, 1.5 (s = 0) vs predicted +0.17, +0.37, +0.57, +0.67: the toy sees such a violation, and sees none with the mask.

**M2 large-sieve sharpness / duality / alignment. Rejected set: empty.**
*Duality.* A_j(z) is a smooth sum of a non-principal Hecke character of conductor norm N(f) ≲ K (Phi is supported in N(z) <= b_Phi·K, `ER:68`, b_Phi fixed): its functional equation gives effective length min(X, N(f)/X) and |A_j| ≪_A X^-A (CK)^(A+1/2) (1+|t|)^(2A+1) for X >= K^(1+delta).
Hence **[rigorous, asymptotic, my derivation, not Lean-checked] the Arvi Zone contains every (m1,m2,s,1) with max(m1,m2) > 1, for every s**: take A >= (m_other+s+1)/(2·delta), the row energy is then <= (1+|t|)^(4A+2)·control², and E <= diagonalControl·K·(...).
*Numerics* [numerical, `logs/m2_alignment.log` (i), (i-b)]. The onset is set by the TRUE conductor N(f) = q6·4^f2·3^flam, not by q6 (the part away from 2, lambda): the 2,lambda-part N(f)/q6 (local class field theory, checked against the discriminants of Q(w,√2), Q(w,∛2), Q(ζ12), Q(w,∛3), Q(ζ9) in `selftest.py`) has median 430 and reaches N(72) = 5184, so binning by X/q6 alone looks alive (mean |A|²/X = 0.21 at X/q6 >= 30).
Against the dual length delta = 3N(f)/(4π²X) the data fall on one curve, the same for rows with trivial and with large 2,lambda-part (Z = 3e3, 2369 kept rows, Schwartz-type profile): |A|²/X = 0.29–0.43 for delta >= 0.3, 0.26 (0.1–0.3), 0.09 (0.03–0.1), 0.016 (0.003–0.01), 4e-4 (< 0.001). For all 648 kept rows at Z = 100 the Phi-weighted mean is 0.40 (X = K), 0.22 (100K), 0.024 (10³K), 8.5e-5 (3·10⁴K); median N(f) = 168K.
So the dead regime is real and visible, but at accessible Z it starts only at X ≳ 10²–10³·K (the constant N(f)/K; the dual weight of a C^infinity bump also decays like a stretched exponential). Plain-only fits with max(m1,m2) >= 1 (5 configs) give kappa in [-0.12, -0.01] (`logs/evidence_table.md`).
*Alignment.* Knob table in `logs/m2_alignment.log`: t, v are smooth phases in N(.) (t up to 1e6: flat, `logs/m4_tscan.log`); theta is inert on the pool; profiles/Phi are smooth/monotone; the only fixed finite-conductor twists (eta, eta0, Q, M, H) align with rows of conductor | Q₀, i.e. exactly the removed rows.
Single row [numerical, Z = 1e5]: best-over-data |row|² <= 3.5e-4·K (a = 1.0), 7.2e-4·K (a = 1.5), 2.9e-5·K (a = 0.8, s = 0.3). Many rows: the K^u largest row energies sum to 0.09K (u = 0.6), 0.44K (u = 0.8), 1.5K (u = 1) at a = 1.5.

**M3 diagonal term. Rejected set: empty.** [rigorous] a_n <= B·d_(k+2)(n) and sum a_n <= B·C·T give sum a_n² <= B²·C_eps·T^(1+eps), so the diagonal is <= C·K·Z^eps at every (a,s) (slot weights add a factor ~ 1/log D < 1).
[numerical] exact sum a_n²/T = 0.02–0.43 per row; actual/diagonal = 0.68–0.94 over 28 (config, Z) pairs; diagonal exponent <= +0.05 for plain-only data (slot data: noisy, pools of 2–5 primes); the diagonal itself grows like (ln Z)^beta, beta = 0.28, 0.48 at m = (0.5,0.5), (0.4,0.4), so some Z^eps in the bound is genuinely needed (`logs/m3_diagonal.log`).

**M4 small-scale numerics. Rejected set: empty.** Toy (`toy.py`, `sweep.py`): the real sum for eta = 1 (and eta = (c0/.)_6), Q₀ = (72), M = (1); R = 4000 rows sampled uniformly from N(z) <= 2K (M3, M5 and the tail study are exhaustive), Phi = smooth taper; self-tests: symbol vs
independent computation, multiplicativity, cubic reciprocity (763 pairs), ideal counts, keep predicate (`logs/selftest.log`). Quantity: mean row energy m(Z), E = K_eff·m(Z), so the bound is m(Z) <= C Z^eps.
65 fits of m ~ Z^kappa over Z = 1e3…1e12 (`logs/evidence_table.md`): **kappa in [-0.157, +0.038], max(kappa - 2 se) = +0.011**; plain-only m = 0.25–0.4, flat (kappa = +0.02, +0.01, -0.004 at a = 1.0, 0.8, 1.5); with slots m = 0.01–0.14 (0.002 for two slots), decreasing like 1/log D.
The random sextic model gives similar exponents (`logs/m4_S4*`); exhaustive tails (72k and 726k rows) equal the random model's (`logs/m4_tails.log`); adversarial search over t, v, profile shapes, X-scales: best/baseline = 1.3–3.1, kappa(best) in [-0.12, +0.016] (`logs/m4_adversary.log`);
plain/slot cross-correlation rho = 0.94–1.64 (`logs/m4_decoupling.log`). Detection limit ~ 0.05–0.1 in kappa (the positive control gives 0.14–0.64). Rule: reject if kappa - 2·se > 0.08.

**M5 frame / Welch. Rejected set: empty.** [rigorous] for K_eff unimodular rows and n columns, lambda_max(G) >= max(K_eff, n) (trace/rank): the free-coefficient large sieve is sharp. [numerical, Z = 1000, K_eff = 5297, X = Z^1.5, n = 19120]:
lambda_max >= 74775, but the admissible smooth vectors reach only r_rigid = 2318 and best r = 4306 (|t| <= 3), 5050 (|t| <= 300) ≈ K_eff; with the principal rows put back r = 32921 ≈ 1.7n. Slot columns: best admissible r <= 1.03·K_eff (`logs/m5_welch.log`).
Sharpness of the classical barrier is carried by the removed rows, not by the rigid coefficients.

**Heuristic acceptance everywhere [GRH].** For kept z, GRH gives |A_j|² ≪ X_j (q(1+|t|))^eps and |S_i|² ≪ D_i log⁴(q D_i (2+|t|+|v|)), so |row_z|² ≪ Z^eps and E ≪ K Z^eps at every (m1,m2,s): nothing in (a,s) is rejected.

## 3. Outer boundary at M = 1 (`logs/outer_table.csv`, `logs/grid.log`)

| s | a_out(s), m1 = m2 | a_out(s), any split tried | numerics at this s: worst fitted kappa | mechanism setting it | status |
|---|---|---|---|---|---|
| 0.000 | >= 1.50 | >= 1.50 | +0.029 +- 0.009 (23 configs, a = 0.3–2.0) | none | [heuristic, GRH] + [numerical] |
| 0.025 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.050 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.075 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.100 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.125 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.150 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.175 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.200 | >= 1.50 | >= 1.50 | -0.045 +- 0.027 (6 configs, a = 0.3–1.0) | none | [heuristic, GRH] + [numerical] |
| 0.225 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.250 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.275 | >= 1.50 | >= 1.50 | not run | none | [heuristic, GRH] + [numerical] |
| 0.300 | >= 1.50 | >= 1.50 | +0.038 +- 0.014 (19 configs, a = 0.3–1.5) | none | [heuristic, GRH] + [numerical] |

Rejected points per mechanism: M1 0, M2 0, M3 0, M4 0, M5 0 (of 325). Numerics were run at 21 grid points (s in {0, 0.2, 0.3}). A single slot with s <= 0.1 never has a non-degenerate pool (Z^s < 20 for Z <= 1e12); s in {0.025 … 0.175, 0.225 … 0.275} were not run (covered by the structural argument and the plain/slot decoupling).
*Asymmetry*: E is symmetric under (m1, X1, p0) <-> (m2, X2, p1), so any rejected set would be symmetric; there is none. The one-sided structure is on the accepted side: for a > 1 the split (a, 0) is **rigorously** inside (M2) whereas m1 = m2 is inside only conditionally. Toy splits (0.75,0.25), (1,0), (1,0.5), (1.1,0), (1.2,0.3): kappa in [-0.12, +0.01].

## 4. Caveats; what would move the bound

1. **Everything depends on GRH-type input.** A rigorous rejection would need an exhibited kept row with |row|² > K^(1+delta), i.e. a large value of a Hecke L-function or prime sum for a finite-order ray class character of Q(omega); that contradicts GRH.
   An exceptional (Siegel-type) zero, for a sequence of kept rows of conductor ~ Z^u, would give |A_j|² ~ X_j^(2beta-1) and restore a+s <= 1 + o(1) at those scales. The outer bound would then move to a+s <= 1.
2. **The mask is load-bearing.** Without the removal of principal rows the boundary is a+s = 5/6 (`fig/control_nokeep.png`); a weaker `keep` (removing fewer rows) moves the bound there. With the Lean `keep` there is no residual barrier.
3. **Numerics are finite-size.** Asymptotic slot regimes (pool >= 6 primes) start at Z^w >= 50 (w = 0.3: Z >= 1e5); single slots with w <= 0.1 never reach it (Z <= 1e12). Detection limit ~ 0.05–0.1; sampled means have 3–5% error, fits with few Z are noisy (chi²/dof is large for slot configurations).
   Choices: eta in {1, (c0/.)_6}, eta0 trivial, rayModulus = (1), Q₀ = (72), Phi a taper; other (M, H) change the pool density by 1/h, not the exponent.
4. The dead regime max(m1,m2) > 1 is a hand derivation (standard functional-equation argument); numerically only the collapse of single plain sums in delta is shown (§2 M2), not the energy at m_j >> 1, which is out of reach (X = Z^m_j and the constant N(f)/K ~ 10²). "Principal => removed" is machine-checked only for eta = trivial and z = w^6; "removed iff conductor | Q₀" and the general-eta statement were read from the definitions.
5. The toy removes rows with all valuations outside (2, lambda) divisible by 6, a superset of Lean's removed set (conductor | 72); the extra rows have bounded non-principal conductor and are dead for m_j > 0.
6. M other than 1, unbounded slot counts, or Z-dependent eta/eta0 are outside this statement and not probed.

## 5. Files

`toy.py` (faithful toy), `sweep.py`, `m1_degenerate.py`, `m2_alignment.py`, `m3_diagonal.py`, `m4_scaling.py` (S1–S5), `m4_adversary.py`, `m4_decoupling.py`, `m4_tails.py`, `m4_tscan.py`, `m5_welch.py`,
`mechanisms.py` (rejection rules), `grid.py` (grid search, figures), `postprocess.py`, `summarize.py`, `selftest.py`, `lean/PrincipalRowRemoved.lean`; `logs/` (all outputs; `m4_summary.txt` and `evidence_table.md` hold the final de-duplicated fits, the per-experiment `m4_S*.log` tables predate de-duplication; `outer_table.csv`); `fig/outer.png`, `fig/control_nokeep.png`.
Reproduce: `python3 selftest.py; python3 m4_scaling.py S1 S2 S3 S4 S4b S5; python3 postprocess.py; python3 m1_degenerate.py; …; python3 summarize.py; python3 grid.py` (about 1–1.5 h on 4 cores).
