# The theta span V of the sextic large sieve (Arvi's "replace M by an operator with the RIP we need")

The reduction is in Lean (`../../lean/arvi_kwall/FlatDilution.lean`). If M = (flat low-rank part on V) +
(I − P_V)M, then RIP of M on every thin row set follows from a **full-family** bound for (I − P_V)M, and the V
part is diluted by k·|W|/R. That needs k = dim V small. This directory measures what V is, and finds that k cannot
be small.

## Synthesis (2026-10-31): what the sextic large sieve's excess is

[numerical, with the mechanism heuristic; details in `../../journal/JOURNAL.md`, entries of 2026-10-31]

- **Prior work.** de Faveri–Dunn–Hoffstein (arXiv 2607.07911, 2026) prove the cubic and quartic large-sieve lower
  bounds by this mechanism and conjecture the order-n operator norm, whose n = 6 extremal term at A = B is the
  `B^{7/6}` measured here. The items below are the sextic numerics and their structure.
- **The excess is the residue of a Kubota series.** For a source vector built from Gauss sums,
  `E f(z) = Σ_x f(x)(x/z)₆` is, by reciprocity and twisted multiplicativity, a partial sum of the sextic Kubota series
  `ψ₆(z, s) = Σ_x g̃(z, x) N(x)^{−s}` at the index z. Its pole gives a main term proportional to `L^{1/3}` times the
  sextic theta coefficients at z.
  - The outlier's row vector is the same for every source length.
  - Disjoint source windows point the same way.
  - The main energy grows like about `L^{1/3}`.
  - The strength at L = B is `B^{1/q}` for order q: `B^{1/6}` for the sextic matrix, `B^{1/3}` for the cubic one.
- **One theta or two.** For q = 3 the residue is Patterson's Gauss-sum vector, the row theta itself: one spike seen
  from both sides. For q = 6 the theta coefficients are not Gauss sums (Kazhdan–Patterson), so the source theta and
  the row theta are different vectors.
- **Why the source theta dominates.** The sources fill every scale 1 … L and the residue builds up coherently across
  them; the rows fill one dyadic window. This gives the source theta about ten times the row theta's energy at
  3·10⁴.
- **The residue has components.** At small rows the source classes mod 4 give about eight independent residue
  vectors, consistent with the components of the sextic theta over Bröker–Hoffstein's representatives. The large-B
  outlier is one combination of them.
- **Every twist carries a copy.** Twisting the source theta by `(x/m)₆` gives the residue at `zm`. The twisted copies
  weaken only like `N(m)^{−1/6}`, so they matter up to `N(m)` of order B.
- **Removing them works at 3·10⁴.** Against the right null (random phases on E's zero pattern, about 4.5% below the
  Marchenko–Pastur formula), E off twisted thetas on both sides (row twists to 300, source twists to 100) sits at the
  null for the sextic and the cubic matrix alike. Random spans of the same dimensions do not. At 10⁵ the same families
  are relatively smaller and leave a few percent (`theta_twosided_grow`).
- **For the K-wall.** The twisted source spikes are flat on slot-selected rows (`theta_src_twisted_selected`). Beyond
  the two-sided spike-free conjecture itself, the new arithmetic input is a shifted-convolution bound for sextic
  theta coefficients at products (`../../frontier/README.md`).

| script | measures |
|---|---|
| `theta_span.py B L` | dual energy ratio r = ‖Eᵀc‖²/(S‖c‖²) of theta row vectors conj G(z,1)·profile against random phases; profile Gram (rank one?); detectors' projections; top singular values with V removed |
| `theta_profile.py B L` | is the excess rank one in the radial profile? Compares profiles with I(U) = ∫U t^{−5/6} ≠ 0 and = 0 |
| `theta_blocks.py B L` | small-modulus row vectors χ_z(m), and twisted theta vectors conj G·χ_z(m)·χ_z(u) |
| `theta_top.py B L` | structure of the top singular vectors (radial, small primes, characters, units) |
| `theta_topspan.py B L` | overlap of the top singular vectors with the twisted-theta and block spans; compressed spectra |
| `theta_twists.py B L [per_bin] [bins]` | excess of twisted thetas conj G·χ_z(u)·χ_z(m) as a function of N(m), against conjugate and plain twists and random phases |
| `theta_powers.py B L` | which row vectors carry the excess: plain, conj G, G, and Gauss-sum powers |
| `theta_mask.py B L [seeds]` | top singular values of E against random phases with E's exact zero pattern (the right baseline) |
| `theta_models.py B L [seeds] [P0,...]` | top singular values of E against models with the same zero pattern: random symbols (RSYM), random multiplicative rows (RMM), exact small primes (EXACT), randomly conjugated row characters (RCHAR, reciprocity broken) |
| `theta_locate.py B L` | top of E after projecting the rows off the block span or the twisted-theta span, or dropping small/large sources |
| `theta_reciprocity.py B L [seed]` | theta excess in RCHAR, with its own Gauss sums |
| `theta_top_free.py B L [k]` | matrix-free top of E (int8 codes, chunked Lanczos) against masked random phases and RCHAR, for B up to 10⁵ |
| `theta_top_free2.py B L [--k] [--threads] [--nrandom] [--nrchar]` | `theta_top_free.py` through the compiled kernel `theta_ckernel.py` (E rebuilt row by row from the int8 symbol table, EᴴE v accumulated in the same pass; AVX-512 + OpenMP): 40× faster per product, B up to 3·10⁵ (table 2.4 GB). Several seeds of the masked random phases and several RCHAR draws; prints the excess and the implied spike strength θ |
| `theta_ckernel.py` | the kernel as a library: EᴴE v, the same on a row subset with unit-norm rows (the unit-diagonal Gram), E v, top eigenpairs by ARPACK |
| `theta_growth.py [log ...]` | growth table from the `theta_top_free*` logs: excess over the masked random edge, θ, adjacent, grid and least-squares slopes d log θ / d log B |
| `theta_outliers.py B L [--k]` | how many eigenvalues of EᴴE/S sit above the masked random edge, and how far |
| `theta_selected.py B L P0,... [rho,...]` | slot-selected rows W (top ρR by \|Σ χ_z(π)\|, N(π) ∈ [P0, 2P0]) against random rows and against RCHAR: top of the unit-diagonal Gram on W, and the concentration of the top singular vectors on W (dense, B ≤ 3·10⁴) |
| `theta_selected_free.py B L P0,... [rho,...]` | the same matrix-free (B up to 3·10⁵), with a positive control (rows aligned with the outlier) and a dilution check on random row sets |
| `theta_dualframe.py B L [P0] [rho,...] [M,...]` | dual-frame bound Σ_W \|Ea\|² ≤ λ_max((Q⁻¹)_WW)·λ_max(EᴴQE)·‖a‖² for slot-selected W: Q from the theta and block spans (both conjugations), the wide ReLU kernel (as Q and as Q⁻¹), a low-pass metric, and the spectral metrics Q = f(EEᴴ) as references |
| `theta_srcspike.py B L` | source-side theta vectors G(x)χ_x(u)N(x)^{−1/2}: energy, overlap with the top right vectors, twisted source-theta span |
| `theta_primepool.py B L` | prime-pool row vectors: energy and overlap with the top left vector |
| `theta_classes.py B L [sample]` | reciprocity sign s(z, z′) and χ_z(−1) by row class mod 4; per-class spectra and theta excess (no anti-self-dual class) |
| `theta_offspan.py B L [M,...] [J]` | in the Lean statement's convention b* E E^H b (`../../lean/arvi_kwall/SexticSpikeFree.lean`): the theta G·conj χ(u)·profile against its conjugate; the top of E off the theta span (each conjugation), the block span (both conjugations), all of them, and a random span of the same dimension |
| `theta_cubic.py B L [M] [J]` | the cubic family E3 = E² (agent test T5): cubic theta G3·conj χ³(u) against its conjugate; the top of E3 off the theta span, the block span, both, and a random span (twists coprime to 6) |
| `theta_cubic_struct.py B L [k]` | structure of the top cubic vectors: flatness, mass in the span of class indicators (z mod 9, z mod 2) × {1, G3, conj G3} × profile, and the single supplementary twists χ³(λ^e 2^f u) × {1, G3, conj G3} |
| `theta_suptwist.py B L k [top]` | r_H of every supplementary twist λ^e 2^f ω^g (−1)^h for the theta (Lean conjugation), the other conjugation and the plain character, in the sextic (k = 1) or cubic (k = 2) family |
| `theta_classtwist.py B L k [M]` | the top of E^k off the class-twisted span (classes mod 9 and mod 4 × {G_k, conj G_k, 1} × profiles), alone and together with the twists coprime to 6, against random spans |
| `theta_cubic_top.py B L [M,...]` | mass of the top cubic vectors in V(M) and in the source-side theta span (the 10⁴ run was stopped after V(100); superseded by `theta_cubic_struct`) |
| `theta_cubic_vm.py B L [M,...] [J] [kinds]` | the cubic family off the Lean statement's spike family V(M): 27 supplementary twists × the twists with N(m) ≤ M × profiles (theta kind, or all kinds), against a random span of the same dimension |
| `theta_ampframe.py B L [rho] [P0,...] [model]` | Q1 (`../../frontier/README.md`): dual-frame bounds c_W(Q)·λ_max(EᴴQE) for diagonal metrics built from slot sums (amplifier, mixes, powers, caps), the oracle and the truth; model `rand` = independent sixth roots of unity on E's zero pattern |
| `theta_ampfree.py B L [rho] [P0] [model]` | the same metrics against the free-probability edge of their weights and against the single-row lower bound |
| `theta_blockcover.py B L [M] [J]` | is the block outlier inside the Lean spike family? Energy of u0…u3 and of the source theta's row image E f in the row spans of `SexticSpikeFree`'s shapes × classes mod 36; the source theta restricted to large sources and projected off the family; flatness of E f and its share on slot-selected rows |
| `theta_dualcore.py` | library: the exact Poisson formula for the Gaussian primary-n Gram, and symbols at arbitrary a + bω |
| `theta_poisson.py B [nrows] [seed]` | entrywise check of the exact Poisson self-duality of the Gaussian Gram: the three unit types a/b/c and the phase ε on classes mod 36 |
| `theta_dual.py B [wf] [Lmul] [dil]` | the same at matrix level in a narrow row window: errors of the dual predictions, spectra, eigenvector overlaps |
| `theta_util.py` | library for the mechanism probes: source Gauss sums, row and source class data, cached top singular triples, the class-signed source theta |
| `theta_mech_rows.py B L` | row side of the block outlier: energy in plain-character spans, coefficient law in N(m), class functions, the row image of the source theta |
| `theta_mech_src.py B L` | source side: profile of v0 by norm, global overlaps, cell coherence of the class-signed conj g̃ |
| `theta_mech_corner.py B L` | candidate vectors for the outlier: the literal candidates, the build-up of the class-signed source theta, the cubic-character scan, the profile exponent |
| `theta_mech_restrict.py B L [core\|full]` | the outlier on row and source subsets (unit classes, primes, windows, norm ranges), with BBP predictions after refitting |
| `theta_mech_growth.py` | growth law θ ≈ 0.378 B^{1/6} of the source-theta spike from the kernel fit, against the measured tops |
| `theta_mech_free.py B L [threads]` | matrix-free source-theta checks at B = 10⁵ and 2·10⁵ |
| `theta_mech_cluster.py B L` | second tier: twisted copies χ_x(m)·f, and the row split by χ_z(−1) |
| `theta_cubic_twosided.py B L [M] [J] [beta,...]` | the cubic family with both thetas removed: row thetas V(M) and the source-theta span (cubic Gauss sums of the sources on cells mod 4 × mod 9 × parity × N^{−β}); one-sided, two-sided and random-span tops; energies of the top pairs |
| `theta_pairs.py B L k [ntop]` | one theta or two? Energies of the top singular pairs of E^k in the row-theta span (left) and the source-theta span (right), same spans for k = 1 and k = 2 |
| `theta_cfh.py B L` | is the sextic outlier's row vector the sextic theta function? Modulus law of u₀ on prime rows, and its squared phase against cubic and sextic Gauss sums × classes (a Chinta–Friedberg–Hoffstein-type test) |
| `theta_twosided.py B L [M] [J] [beta,...]` | the sextic family with both thetas removed (dense): row family V (thetas and plain characters on classes mod 36, twists N(m) ≤ M, J profiles) and source family P (conj g̃, g̃ times N^{−β} on cells mod 36 × parity); one-sided, two-sided and random-span tops |
| `theta_twosided_free.py B L [M] [J] [beta,...] [threads]` | the same matrix-free (compiled kernel, E^H Q_V by a chunked pass), B up to 2·10⁵ |
| `theta_src_residue.py B L1,L2,... [k] [threads]` | rows fixed, sources up to each L: top of E and of the masked null, and overlaps of the top left vectors across L (rows matched by factorization) |
| `theta_src_windows.py B L nwin [k] [threads]` | E restricted to disjoint dyadic source windows: top against the masked null, and overlaps of the windows' top row vectors |
| `theta_src_coherence.py B L nwin` | row images of the fixed class-signed source theta on disjoint source windows: their mutual correlation, against the masked null and random class phases |
| `theta_src_lscale.py B L1,L2,...` | main energy of the class-signed source theta (\|Ef\|² minus the masked null) against L at fixed B |
| `theta_twosided_grow.py B L CONFIGS [J] [threads]` | two-sided test with growing families (row twists N(m) ≤ M, twisted source thetas N(m) ≤ M′, several β), matrix-free through the kernel's forward and adjoint products; compared with the masked null on the same spans and with random spans |

All scripts build E and the row Gauss sums through `theta_core.py`. The matrix-free scripts (`theta_top_free2`,
`theta_selected_free`, `theta_outliers`) use `theta_core.build_tables`, which stops before the dense matrix and returns
the rows, the sources and the int8 symbol table (`build` starts from it and gives the same E as before).

**Findings** (logs `theta_*B*.log`):
- **Theta excess.** +16%, +18%, +24% at B = L = 3000, 10⁴, 3·10⁴ (6, 11, 23 sd), against the random-phase
  baseline.
  - It is rank one in the profile: +18–20% when I(U) ≠ 0, and −5%…+3% when I(U) = 0. This matches Xu–Sang's
    Gauss-Gram main term, arXiv 2610.17675.
  - It is not the top of the spectrum: removing V changes the top singular value by < 0.1%.
- **Block structure = reciprocity.** Against the right baseline (random phases with E's zero pattern), the top of
  the spectrum is +3.4%, +7.8% and +14% at B = 3·10³, 10⁴ and 3·10⁴.
  - It lives on low-frequency rows: projecting off the block span χ_z(m)χ_z(u), N(m) ≤ 100, removes it. The top
    block combination is a short prime pool Σ_m χ_z(m).
  - Every model without reciprocity sits at the random level: random symbols, random multiplicative rows, exact
    small primes, and randomly conjugated row characters (whose rows are still characters).
  - Breaking reciprocity also removes most of the theta spike (`theta_reciprocity_B10000.log`).
  - It grows like a B^{1/6} spike: +24% at B = 10⁵, with implied spike strength 1.44, 1.74, 2.08, 2.57 at
    3·10³, 10⁴, 3·10⁴, 10⁵. RCHAR stays at the random level at 10⁵ (`theta_top_free_B100000.log`). It is neither
    the row theta, the source theta nor a prime pool (`theta_srcspike`, `theta_primepool`).
- **The block outlier is the source-side theta (correction to the previous bullet).**
  - Its source vector is f(x) = A(x mod 4)·(3/x)₃·ε(x)·conj g̃(x)·N(x)^{−1/3}. Here A is a twelfth root of unity per class
    mod 4, (3/x)₃ a cubic character mod 9, and ε(x) = −1 on odd-class sources with an odd number of prime factors.
  - A spiked-Wishart (BBP) fit with this spike reproduces the top eigenvalue within 3% from 3·10³ to 3·10⁵. The
    strength is θ ≈ 0.378 B^{1/6} (`theta_mech_*`).
  - `theta_srcspike` had tested G(x)χ_x(u)N(x)^{−1/2}, which lacks the class phases, the cubic character, the parity
    sign and the profile.
  - The row image E f has no component along the row thetas: energy 0.170 and 0.067 against random 0.153 and 0.051 at
    10⁴ and 3·10⁴. It lives at large N(x): restricted to N(x) > 3000 and projected off the low-twist family, it keeps
    a growing excess (`theta_blockcover`).
  - So the one-sided Lean conjecture misses it; see `../../lean/arvi_kwall/SourceSpike.lean`.
  - E f is flat on rows (exponential law), and its share on slot-selected rows equals their density.
- **One theta for the cubic family, two for the sextic** (`theta_pairs`, `theta_cubic_twosided`). Cubic top pairs are
  row thetas on the left and source thetas on the right, with matching energies (0.89/0.90 at 3·10⁴). Removing the
  row thetas removes the cubic source theta too. The sextic top pair is a source theta (0.46) whose row vector has no
  row-theta content (0.06 against 0.05). That row vector looks random, and it is not visibly the sextic theta
  function (`theta_cfh`). Patterson's Gauss-sum theta for n = 3 against Kazhdan–Patterson non-uniqueness for n = 6;
  see the journal.
- **Both thetas removed, fixed families** (`theta_twosided`, `theta_twosided_free`; V of dimension 1080 with twists
  N(m) ≤ 30, P of dimension 432). Top s²/S off both families: 3.773 at 3·10⁴, 4.442 at 10⁵, 4.756 at 2·10⁵. Random
  spans of the same dimensions: 4.016, 4.746, 5.171.
  - **Null (correction).** Compare with the masked random matrix projected off the same spans, not with the
    Marchenko–Pastur formula. E's zero pattern puts its edge about 4.5% lower: 3.616 at 3·10⁴ and 3.879 at 10⁵. So
    the remainder is 4.3% and 14.5% above the null, not "at the edge" at 3·10⁴.
  - Both families carry signal at every size, but fixed families leave a growing excess, as expected from one spike
    per twist (below).
- **Growing families** (`theta_twosided_grow`, matrix-free through the kernel's forward and adjoint products).
  Excess over the masked null with the same spans:
  - 3·10⁴: +4.3%, +2.1%, +1.1%, −0.4%, −1.7% for (M, M′) = (30, 0), (100, 0), (100, 30), (300, 0), (300, 100).
    Random spans of the same dimensions stay at +10% … +2%.
  - 10⁵: +14.5%, +13.4%, +10.3% for (30, 0), (100, 0), (300, 0), where V is 4–13% of the rows against 13–42% at
    3·10⁴.
  - So families that grow reach the null at 3·10⁴. At 10⁵ the same families are relatively three times smaller and
    remove less; see the journal for the follow-up.
- **The block outlier is a residue** (`theta_src_residue`, `theta_src_windows`, `theta_src_coherence`,
  `theta_src_lscale`). With the rows fixed, the top row vector is the same for every source length (overlaps 0.56–0.74
  at 10⁴). The row images of the class-signed source theta on disjoint dyadic source windows are correlated (mean
  |corr|² 0.046 at 10⁴, 0.052 at 3·10⁴; masked null 0.0003 and 0.0001). Its main energy grows roughly like L^{1/3} at
  fixed B. This fits the residue of the sextic Kubota series in the source variable, `L^{1/3} conj τ₆(z)`, which gives
  B^{1/6} at L = B. For q = 3 the residue is Patterson's Gauss-sum vector, the row theta itself, which explains one
  theta (cubic) against two (sextic). See the journal. [identification with τ₆ heuristic]
- **Exact Poisson self-duality** of the Gaussian primary-n Gram, to the 10⁻⁹ truncation level (`theta_poisson`).
  - The dual is the same family at a pair-dependent length 27 N(z)N(z′)/(4L), dilated by the unit type.
  - It carries a twelfth-root phase that is constant on classes mod 36, not mod 4.
  - The off-diagonal Gram in a narrow row window has no outlier (`theta_dual`). The block outlier needs the full row
    range.
- **Both parts are flat** (unimodular on coprime rows), so both dilute on thin row sets.
- **Convention (correction to three scripts).** r = ‖Eᵀc‖²/(S‖c‖²) is the row Gram form b* E E^H b at b = conj c.
  - So in the Lean form the excess is carried by G·conj χ(u), not conj G·χ(u): r_H = 1.09–1.13 against 0.93–0.98
    (`theta_offspan_B10000.log`).
  - `theta_span`, `theta_locate` and `theta_topspan` projected conj G·χ out of E E^H, the conjugation without the
    excess.
  - Re-run in the right convention, the findings above stand. The top vector's mass in the theta span is at the
    random level (0.040 against 0.046), and the top outlier sits in the block span.
  - The thetas are far below the bulk edge at these sizes, so removing either conjugation barely moves the top.
- **Only conj G carries the excess.** Plain rows show a deficit (r = 0.85–0.93 against 0.946). G and the Gauss-sum
  powers conj G², G², conj G³ are neutral (0.90–0.98) (`theta_powers_B30000.log`).
- **One spike per twist.** Every twisted theta conj G·χ_z(m) carries the same excess, +0.084 ± 0.005 for
  34 ≤ N(m) ≤ 2200 at B = 3·10⁴. It ends near N(m) ≈ B²/L. m = 1 carries +0.221 ≈ 2.6 copies
  (`theta_twists_B30000.log`). Mechanism: in the Poisson dual, the frequencies h = m·j⁶ all repeat atom m.
- **What the K-wall needs (corrected).** V is not low-dimensional. Asymptotically every twist with
  N(m) ≤ B^{1−6γ} keeps an excess ≥ B^γ. Two statements remain:
  - (LS off V) for that B^{1−6γ}-dimensional V, at the balanced point;
  - a detector condition ‖P_V M a‖² ≲ L·B^γ‖a‖², which is an unbalanced twist sieve.
  See the journal, "Where the theta excess lives".
- **The outlier to B = L = 3·10⁵** (`theta_top_free2.py`, logs `theta_top_free2_B*.log`, `theta_top_free_B200000.log`,
  `theta_top_free_B300000.log`; table and slopes by `theta_growth.py`). Top of EᴴE/S for the sextic matrix, for random
  phases on E's zero pattern (mean of 3–6 seeds) and for RCHAR (2–3 draws), and the implied spike strength θ from
  λ/λ_edge = (√θ + 1/√θ)²/4:

  | B = L | 3·10³ | 10⁴ | 3·10⁴ | 10⁵ | 2·10⁵ | 3·10⁵ |
  |---|---|---|---|---|---|---|
  | rows R / sources S | 848 / 778 | 2816 / 2610 | 8474 / 7768 | 28210 / 25936 | 56470 / 51852 | 84672 / 77808 |
  | sextic top λ₁ | 4.061 | 4.261 | 4.550 | 4.949 | 5.279 | 5.470 |
  | λ₂, λ₃, λ₄ | 3.995, 3.942, 3.898 | 4.109, 4.093, 4.025 | 4.334, 4.292, 4.205 | 4.751, 4.623, 4.427 | 4.975, 4.912, 4.648 | 5.110, 5.072, 4.768 |
  | masked random | 3.965 ± 0.028 | 3.950 ± 0.008 | 3.987 ± 0.005 | 3.988 ± 0.001 | 3.993 ± 0.002 | 3.995 ± 0.0002 |
  | RCHAR | 3.917 | 3.956 | 3.998 | 3.993 | 4.000 | 3.999 |
  | excess | +2.4% | +7.9% | +14.1% | +24.1% | +32.2% | +36.9% |
  | θ | 1.36 | 1.74 | 2.09 | 2.58 | 2.95 | 3.16 |

  The sizes 6·10³, 2·10⁴, 5·10⁴, 7·10⁴ give θ = 1.51, 1.84, 2.17, 2.41. The 3·10³ edge is now a 6-seed mean, which moves
  θ there from 1.44 to 1.36; the 10⁵ column reproduces the numpy-chunk run (`theta_top_free_B100000.log`).
  - The matrix is never stored: an EᴴE product costs 0.12 s at 10⁵ and about 1–3.6 s at 3·10⁵ (3 threads, shared
    machine), 40× less than the numpy chunks.
  - RCHAR sits between +0.0% and +0.3% above the masked random edge at every size from 6·10³ on, against +4…+37% for the sextic.
    The offset is structure and not alphabet: i.i.d. sixth-root phases give 3.9516 and continuous phases 3.9501 ± 0.0012
    at 10⁴ (60 seeds each).
  - Slopes d log θ / d log B between neighbouring sizes are noisy (0.08 … 0.31): the sextic top is one deterministic
    matrix per size and moves by a few percent with the arithmetic of B. On the grid 3·10³, 10⁴, 3·10⁴, 10⁵, 3·10⁵ they
    are 0.20, 0.165, 0.175, 0.186. The least-squares slope over the ten sizes is 0.183 ± 0.005 (0.187 ± 0.006 for
    10⁵ … 3·10⁵). θ = 0.31·B^{0.183} and θ = 0.41·B^{1/6} − 0.24 fit equally well (rms 0.045 in θ), so the data
    do not separate B^{1/6} with an offset from a slightly larger exponent.
  - The top is a cluster, not one spike (`theta_outliers_B*.log`). Eigenvalues above 1.05 × the masked random edge:
    1, 5, 18, 37, ≥ 48 at B = 10⁴, 3·10⁴, 10⁵, 2·10⁵, 3·10⁵ (about 6·10⁻⁴·R); above 1.10 ×: 0, 1, 4, 14, 22. At 10⁵ the
    top 48 and at 2·10⁵ the top 64 are all above 1.01 ×. The dimension of the excess space grows in proportion to R, so
    a single spike does not describe it.
- **The outlier does not sit on slot-selected rows** (`theta_selected.py`, B = 3·10⁴; `theta_selected_free.py`,
  B = 3·10⁴, 10⁵, 2·10⁵; logs `theta_selected_B30000.log`, `theta_selected_free_B*.log`). W = the top ρR rows by
  |Σ_{N(π)∈[P0,2P0]} χ_z(π)|, ρ = 0.1, 0.03, 0.01, P0 = 25 … 250 (40 and 100 at 3·10⁴); the sextic matrix and RCHAR,
  each with its own slot sums; top eigenvalue of the unit-diagonal Gram on W against random row sets of the same size.
  - Slot-selected W exceeds random W by +0.02 … +0.10 (more for small P0 and large ρ: the slot spike), and by the same
    amount for RCHAR. The difference (sextic − RCHAR) of (W − random) is +0.001 ± 0.008 over the 18 settings at 10⁵,
    −0.002 ± 0.006 over 6 at 3·10⁴ and −0.004 ± 0.006 over 9 at 2·10⁵ (mean ± rms; the random-set noise is
    0.002 … 0.006).
  - The energy of the top four left singular vectors on W is 0.98 ± 0.01 (10⁵, ρ = 0.1) and 1.005 ± 0.008 (2·10⁵) times
    the flat value ρ; RCHAR's bulk vectors 1.00.
  - Positive control: W = the rows carrying most of the top-four subspace (2.7 × the flat energy at ρ = 0.1) gives
    sextic − RCHAR = +0.35, +0.49, +0.71 at B = 3·10⁴, 10⁵, 2·10⁵ for ρ = 0.1 (+0.13 … +0.31 at 0.03, +0.09 … +0.13
    at 0.01). The test sees an aligned W at ≥ 15 sd and the slot selection is not aligned.
  - Dilution: on random row sets of a fraction ρ the sextic-over-RCHAR ratio of the top eigenvalue is 1.010, 1.032, 1.090
    at ρ = 0.2, 0.3, 0.5 (B = 10⁵), against 1.005, 1.029, 1.091 for a flat rank-one spike of strength θ√ρ (θ = 2.56),
    and 1.056 against 1.058 at ρ = 0.3, B = 2·10⁵. The flat part dilutes as the FlatDilution reduction says; the top
    spike re-emerges on a random W only for ρ > 1/θ² (0.15 at 10⁵, 0.12 at 2·10⁵, 0.10 at 3·10⁵).
- **Dual-frame (Q-metric) certificates at B = L = 10⁴** (`theta_dualframe.py`, log `theta_dualframe_B10000.log`).
  Σ_{z∈W} |(Ea)(z)|² ≤ f₁·f₂·‖a‖² with f₁ = λ_max((Q⁻¹)_WW), f₂ = λ_max(EᴴQE). For slot-selected W (P0 = 40) the truth
  ‖E_W‖²/S is 1.768 (ρ = 0.1, |W| = 281) and 1.374 (ρ = 0.03, |W| = 84), against the trivial bound ‖E‖²/S = 4.261
  (2.41× and 3.10× above). Products f₁f₂/S as multiples of the truth; random W of the same size gives the same picture:

  | Q | ρ = 0.1 | ρ = 0.03 |
  |---|---|---|
  | I (trivial) | 2.41 | 3.10 |
  | P_W + εI, ε = 0.1 / 0.01 (depends on W) | 1.05 / 1.01 | 1.07 / 1.01 |
  | I − (1−ε)P_V, V = theta, block or both, N(m) ≤ 30 … 300, either conjugation, ε = 0.3 … 0.01 | 3.3 … 126 | 3.6 … 129 |
  | wide ReLU kernel as Q, degrees ≥ 2 / ≥ 1 / ≥ 0 | 2.44 / 7.4 … 22 / 329 … 1600 | 3.1 / 8.8 … 24 / 399 … 1800 |
  | low-pass P_low + εI, low = block span | 7.8 … 161 | 10 … 201 |
  | top-k singular subspace of E, best ε (k ≈ 400 / 500) | 1.77 | 1.99 |
  | best Q = f(EEᴴ) with f₂ = 2S / S | 1.37 / 1.12 | 1.61 / 1.20 |
  | (Ĝ + 0.1)⁻¹ (Tikhonov inverse of the row Gram) | 1.06 | 1.09 |
  | wide kernel as Q⁻¹, degrees ≥ 2 / ≥ 1 | 2.45 / 1.12 … 1.39 | 3.1 / 1.18 … 1.59 |

  - No Q built from the arithmetic spans, the wide kernel or the low-pass metric beats the trivial bound. The best is
    1.16–1.36 × trivial (block span N(m) ≤ 30, ε = 0.3), and the product increases monotonically as ε falls from 1
    (checked at ε = 0.97 … 0.5 for the spans with N(m) ≤ 30 and ≤ 100: 1.0005 … 1.35 ×).
  - Reason: f₁ ≈ 1 + (1/ε − 1)·λ_max((P_V)_WW), and λ_max((P_V)_WW) = 0.17 … 0.69 for dim V = 36 … 912, the Haar value
    (√(a(1−b)) + √(b(1−a)))² with a = |W|/R, b = dim V/R. The exception is the spans that contain the slot primes
    (N(m) ≤ 100): 0.39 on slot-selected W against 0.28 on random W. Theta and block spans have identical λ_max((P_V)_WW)
    (the Gauss sums are a diagonal unitary). Meanwhile f₂ falls only from 4.26 to 3.9 (N(m) ≤ 100) …3.2 (dim 912).
  - Positive Hadamard coefficients make Q grow with EEᴴ, which amplifies the top directions (f₂ = 781 with the
    all-ones term); degrees ≥ 2 give Q ≈ (b₂+b₄)I, i.e. the trivial bound ×1.01.
  - What helps is damping the upper part of E's singular spectrum. Q = I − (1−ε)P_k with the top k left singular vectors
    gives 0.73 (ρ = 0.1) and 0.64 (ρ = 0.03) of the trivial bound; the best Q that is a function of the singular
    values gives 0.57 / 0.52 at f₂ = 2S and → the truth as f₂ → 0, where f₁ = ‖E_W‖²/f₂ is the Gram on W again
    (Q = (EEᴴ)⁺ is exact for every W and circular). λ_max((P_k)_WW) is within 5% of the Haar value, so these numbers
    are the Marchenko–Pastur spectrum plus delocalization of the top singular subspace on W, with no arithmetic input.
  - Benchmark for a structured Q (e.g. the product RKHS of `../../frontier/README.md`, Q1): it has to bring f₂ from
    4.26 to about 2–2.5 at f₁ ≲ 1.3, which is 0.6 × trivial.
