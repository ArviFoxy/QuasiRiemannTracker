# Continuous tuning of the final return: slack and a reflective redesign

Date 2026-10-29. Question: replace the hand-partitioned return (31 windows, a fixed branch per window, 15
Bernstein guards per window, 47 Bernstein rows) by a detector whose parameters are computed per patch, and
certify it with parametric lemmas plus small reflective certificates. (a) Is there θ slack? (b) Is the proof
smaller and simpler?

Tags: **[Lean]** read in a built Lean file (path:line, paths relative to `Submissions/`); **[derived]** my
derivation or an exact rational computation (script named); **[numerical]** floating point or 40-digit
`mpmath` (script named). Scripts are in this directory and run with `python3 <script>`; outputs in `logs/`.

## 0. Bottom line

* **No θ gain.** The least θ that this return can certify lies in **(0.873872338, 0.87387234]**, for every
  choice of windows, branch assignment, cover, reserve ≥ `rowFee`, face restriction (any of the 131 proven
  chain faces, either piece of the plain curve) and any `h` allowed by `BoundsN.floor_margin`
  [derived, exact rationals, `exact_bracket.py`]. The merged θ = 43693617/50000000 is within 2·10⁻⁹ of
  that optimum; the continuous optimum is about 0.8738723380 (reserve = `rowFee`) or 0.8738723399 (reserve
  10⁻⁸) [numerical, `theta_star.py`]. The reason: the per-patch detector is *already* continuous. For a
  fixed face, the cutoff, inverse length and plain length are closed-form rational functions of (δ, p), and
  the branch value is the exact optimum of Collet's bound for that face. The binding point is an interior
  optimum of branch `C`, with all 15 guards slack.
* **Large simplification.** A proof of concept builds end to end
  (`Submissions/arvi_return_tuning/`, theorem `QRH.ArviReturnTuning.dirichlet_nonvanishing_f50`, axioms
  `propext, Classical.choice, Quot.sound`). It proves the same statement as the merged theorem (checked by
  `rfl`) without `Rows/*`, the cover trees or the 31 windows. The 39 replaced certificate files
  (796,295 bytes) become 8 files (45,466 bytes): a constant-free library of 41,462 bytes plus 4,004 bytes of
  instance data (five windows, four one-line edge checks). Check time is in §4.

## 1. What the return computes

### 1.1 Chain of statements [Lean]

* `FinalF50.lean:12` `dirichlet_nonvanishing_f50` ← `Return/Endpoint.lean:69` `dirichlet_of_sources`
  (count source = chain end `ChainF50.final_source`, `ChainF50/Chain.lean:1310`; physical source = step 64,
  `Chain.lean:716`) ← `Return/EndpointFromSources.lean:42` `Final.beta_of_global_sources` ← the physical
  schedule `Return/FinalSchedule.lean:18`. Its fields `old_rows`, `new_rows` (`ReturnD/Schedule.lean:52-56`)
  require

      rowAt(d, C, δ, p) = Ebase(d, C, δ, p) + (3/4)·d·envelope(δ, p)  ≤  θ − rowFee     (rowFee = 10⁻⁹)

  for all δ ∈ [0, 3/4], p ∈ [0, 1/2], and d ∈ [d0, dm] with the old capacity C, or d ∈ [dm, dp] with the
  new capacity C (`ReturnD/Schedule.lean:28-33`; `Ebase` at `Return/Formulas.lean:88`).
* `rowAt` is affine in d on each capacity piece, so four conductor edges suffice: oldSmall (d0 = 1/200),
  oldSwitch and newSwitch (dm = 19/25), newTop (dp = h + 10⁻¹⁰) (`Return/Conductor.lean:69`
  `new_interval_bound`, `:111` `old_interval_bound`; `Return/Constants.lean:34-36,43-50`).
* `envelope(δ, p)` = min of Collet's old count `countingR κ` and the values of the windows *available* at
  (δ, p) (`hailey_collet_1252270103/Record12518109Return/FiniteEnvelope.lean:20`,
  `Record1252270103Return/CountScheme.lean:16-17`).

### 1.2 Rows, windows, branches

* **47 rows** [Lean]: `Return/EdgeCertificates.lean:51ff` `envelope_row001..047`. Each row is a box of one edge
  with a count choice (old, or the branch of one window) and a Bernstein certificate `rowNNN_pos` in
  `Rows/Edge_*.lean`. The cover trees `cover_node_000..089` assemble them into
  `closed_envelope_return_cover`. By edge: newTop 42 (31 of them through a window), oldSmall 1,
  oldSwitch 2, newSwitch 2 (old count only) [derived, `windows.py`].
* **31 windows** [Lean]: `Return/Windows.lean`, 20 `C`, 6 `capP`, 3 `capC`, 2 `weakC7`. A window is
  `ReturnCountWindow` (`Return/CountWindow.lean:14`): a branch, δ ∈ [deltaLo, deltaHi], p ∈ [pLo, 1/2], and a
  certificate that the 15 guards are positive there (`:22`). Each window is the δ-range × [p₀, 1/2] of one
  newTop row leaf (`research/density/gen_return86.py:426` `window_of`) [derived].
* **Branches.** `CountBranch` has **five** constructors, not six: `old | C | capC | weakC7 | capP`
  (`Return/Formulas.lean:15`). There is no uncapped physical branch `P` in this return. Faces:
  `C`, `capC` = (96232839/10⁸, 3853/2000, 9999/10⁵); `weakC7` = `C` with B − 7/4000; `capP` =
  (49283557/50000000, 4503/2000, 31/500) (`Formulas.lean:17-29`, `Constants.lean:16-21`). Uncapped
  branches read the plain curve on its sloped piece z = (B − 2m)/Λ; capped ones on its cap piece
  z = cap − 10⁻⁷ (`Formulas.lean:35-42`) [Lean].
* **Branch value** [Lean]: `branchCount = countN/countJ` (`Return/CountAdmission.lean:17`). This is the
  common value of three lines, the inverse line `I(r) = 1 − δ(p + (1−p)r)`, the long line
  `L(t) = 1 − δ + (5/6 − δ)(t − 1)` and the plain line `P(m) = 1 − 2δm − 2δp·z(m)`, at the witnesses
  t = countT/countJ, r = RN/DJ, m = MN/DJ (`CountAdmission.lean:14-16`; equalities `:42`, `:49`,
  `Return/CountDecode.lean:30`). Collet's `common_witness_count_bound`
  (`Record1252270103Return/CountCurve.lean:48`) bounds the count by max(I(r), L(t)) given
  plainCurve(t − r) ≤ I(r). For a fixed face and piece, the three-line crossing is the minimum of that
  bound [derived: I decreases in r, L increases in t, and the plain constraint is monotone].
* **δ and p** [Lean]: Collet counts rows with exponent `rowCount (2*a-1) (q/(2*a-1)) κ` for a zero of
  real part a, 51/100 < a, 2a − 1 ≤ 3/4. Here q is the row mean of the slot profile at threshold
  (2a − 1)/2 (`hailey_collet_1252270103/Cycle25/Assembly/Count/Parameters.lean:23,28,34`). So
  **δ = 2a − 1, i.e. a = (1 + δ)/2 is the real part of the bad row's zero (verified)**, and p = q/δ ∈ [0, 1/2]
  is the normalized mean slot amplitude. δ ≤ 3/4 is β ≤ 7/8 (`Return/Endpoint.lean:41`
  `natural_cap_return`).

### 1.3 The 15 guards (`Return/Formulas.lean:75-86`) and who uses them [Lean]

| j | guard | meaning | consumed at |
|---|---|---|---|
| 0 | D > 0 | denominator | `CountAdmission.lean:72` |
| 1 | A > 0 | — | **never** |
| 2 | C0 = 1 − Z > 0 | — | **never** |
| 3 | J > 0 | denominator | `CountAdmission.lean:74` |
| 4, 5 | 1 < t < 12499/10000 | cutoff range | `:76`, `:78` (the window interface needs only t ≤ 3/2, `Record1252270103Return/AdmittedWindow.lean:31-32`) |
| 6, 7 | 23/37 < r < 1 | inverse-length range (hypothesis `hrN` of `CountCurve.lean:57`) | `:80`, `:82` |
| 8, 9 | lowerM < m < upperM | plain length: m ≥ m₋ = 377/1000; the right piece of the plain curve is active; m < 11/25, m < naturalM, z(m) > s₋ | `:84`, `:86` |
| 10 | count ≥ 1 − 2δ naturalM − 2δp s₋ | natural tail | `Return/CountDecode.lean:66` |
| 11 | U·J′ − U′·J > 0 | count antitone in p (`Branch.antitone`) | `Return/CountMonotonicity.lean:88` |
| 12 | 11/25 − naturalM − 10⁻⁷ > 0 | constant | **never** |
| 13 | B − 2 naturalM − Λ(s₋ + 10⁻⁷) − 2·10⁻⁷ > 0 | constant; slot widths | `Return/CountWidth.lean:43` |
| 14 | capped: (Zc − s₋ − 10⁻⁷)·DJ > 0 | constant | **never** |

Guards 1, 2, 12 and 14 are proved 31 times but never used. No `hg 1`, `hg 2`, `hg 12`, `hg 14` occurs in
`arvi_density` [Lean, grep].

### 1.4 θ, h and what binds

* θ = 1 − c, c = 6306383/50000000 (`Constants.lean:14,26`), so θ = 43693617/50000000 (`:51`). Also
  ell = 4c − 1/3 = 11/3 − 4θ, y = h − 2·ell, x = 1 + ell − h and κ = 2θ − 1 (`:27-30`) [Lean].
* h = 8044451/10⁷ (`Constants.lean:15`) is the 7-digit floor of the largest h allowed by the transport box,
  `BoundsN.floor_margin` (`ReturnD/TransportGeometry.lean:29`). That ceiling is 0.804445102199 at this θ
  [derived; `gen_return86.py:1063` `hceiling`]. θ is the least value on an 8-digit grid for which the
  generator's greedy cover exists (`gen_return86.py --find-theta`) [derived from the generator; the exact
  invocation is not recorded].
* **Binding** [numerical, `analyze1.py`, `analyze2.py`, `analyze5.py`]:
  1. the newTop row at p = 1/2, δ* = 0.44878938, branch `C` (rows 26–35). The exponent there is
     0.8738723295496 against θ − reserve = 0.87387233, a slack of 4.5·10⁻¹⁰;
  2. `floor_margin`: h sits at its ceiling. ∂E/∂h = −0.0107 at the binding point, so a larger h would help.
     Past h ≈ 0.805 the numerator cap 3/50 binds and the slope turns positive;
  3. the reserve 10⁻⁸ (`FinalRows.reserve_le` needs reserve ≥ rowFee = 10⁻⁹).
* Not binding [numerical]. The other three edges have slack ≥ 1.18·10⁻². At the binding point every guard
  of `C` is slack: normalized margins are m > lowerM 0.69%, 11/25 > naturalM 0.75%, natural tail 0.84%,
  t < 1.2499 10.5%, r > 23/37 13.1%. Capped faces would count lower there (capC 0.62623 vs C 0.60672 in
  value, but **inadmissible**: m < upperM fails), and `capP`/`weakC7`/`old` count higher (`analyze2.py`).

## 2. Slack of a continuous choice

| family | max newTop exponent − (θ − reserve) | source |
|---|---|---|
| Lean envelope (31 windows) | −4.5·10⁻¹⁰ (certified) | `analyze1.py` |
| pointwise best admissible branch of the five | same point, same value | `analyze2.py` |
| envelope over all 131 chain faces × both pieces | same (the chain end is best at the binding point) | `analyze3.py` |
| physical face for the newTop capacity | step 64 is the best chain face (63/65 lose 1.7·10⁻¹⁰ / 5.6·10⁻¹⁰ of capacity) | `analyze4.py` |

* **Exact bracket** [derived, exact rationals, `exact_bracket.py`]. Take θ_t = 0.873872338 with the
  most favourable h (the exact ceiling). At (δ, p) = (0.4487894, 1/2), every chain face gives a newTop
  exponent above θ_t − rowFee (+1.17·10⁻¹⁰ for the best, the chain end), and so does the old count. The
  face's *uncapped three-line crossing* is a lower bound for any window of that face or of a restriction
  (smaller B or cap, larger Λ), admissible or not, because the window value must satisfy
  plainCurve(t − r) ≤ value with plainCurve the max of both pieces (`AdmittedWindow.lean:39`, `CountCurve.lean:8-9`). The exponent is
  convex and piecewise affine in h with slope −0.0107 at the ceiling, so smaller h is worse. Hence θ_t
  cannot be certified by any envelope built from these sources.
* **θ\* by bisection** [numerical, `theta_star.py`]: 0.873872339901 (reserve 10⁻⁸, gain 9.9·10⁻¹¹),
  0.873872338024 (reserve = rowFee, gain 1.98·10⁻⁹). The problem is stiff: along the h-ceiling,
  d(maxE − θ)/dθ = −4.80, so a row margin of 10⁻⁸ is worth only 2.1·10⁻⁹ of θ (`analyze5.py`).
* **Why there is no slack.** The idea assumes that the discrete branch choice forces a suboptimal detector
  somewhere that binds. At the binding point the detector parameters (t, r, m) are already the closed-form
  optimum of the best proven face, and no guard is active. Interpolating between faces is not a valid
  input. With two faces, the plain constraint for their union is the min of the two plain curves, so the
  union count is the min of the two counts, which is what the envelope already takes [derived].
  Per-window natural join and plain floor (`AdmittedWindow.mLo/mHi`) or a looser cutoff bound would only
  help where those guards bind, and they do not bind at δ*.
* What would move θ is outside this idea: a better count face from the chain, relaxing `floor_margin`
  (worth about 10⁻⁶ before the 3/50 cap takes over; `logs/analyze5.log`), or new moment inputs (see
  `newpowers/R3_return.md`).

## 3. Simplified certificate design

1. **Constant-free library** (`Poly2.lean`, `GuardsQ.lean`, `Guards.lean`, `RowsQ.lean`, `CoverQ.lean`):
   * `Q1`/`Q2` rational polynomials with `ev` homomorphism lemmas.
   * `bernCheck P a b c e`: the kernel *computes* the tensor Bernstein coefficients of P on the box and the
     candidate certificate `P = m + Σ g_ij (δ−a)^i (b−δ)^(n−i) (p−c)^j (e−p)^(m−j)`, then *checks* the
     polynomial identity, m > 0 and g ≥ 0. No Bernstein theory is trusted; soundness is
     `checkCert_sound`, about 15 lines. `posBox` adds kernel-computed bisection.
   * **One parametric admission lemma** `ev_guard` (`Guards.lean`): for every rational face (B, Λ, cap)
     and either piece, the computable guard polynomial evaluates to `Formulas.lean`'s `admissionGuard`
     (`admissionGuard_eq` is definitional).
   * `ev_rowBrQ`, `ev_rowOldQ` do the same for the row margins.
   * `coverOK e ws k`: the kernel covers an edge itself. On each box it tries the old count, then every
     window containing the box (first fit), and otherwise bisects. `coverOK_sound` holds for any envelope
     bounded by the old count and by every window's count. There is no tree, branch assignment or
     coefficient data.
2. **Instance data** (`Data.lean`, `Windows.lean`, `EdgeCertificates.lean`):
   * Base constants: c, h, reserve, the two faces, numeratorCap, dm. θ, ell, y, κ, the four edges, their
     capacities and the branch data are computed and identified with `Constants.lean` by cast lemmas.
   * Five windows, chosen as maximal admissible rectangles (`winsearch.py`, `coversim.py`), with
     `windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel`.
   * One `decide +kernel` per edge.
3. **Downstream unchanged**: `FinalWindows`, `FinalScheme`, `FinalEnvelopeBounds`, `FinalRows`,
   `FinalSchedule`, `EndpointFromSources`, `Endpoint` are verbatim forks (namespace
   `QRH.ArviDensity.Return.Tuning`). `ReturnD/` (119 modules) is untouched; it is generic in the windows.

Regenerating for new faces or θ: edit the base constants (here and in `Constants.lean`), and re-pick
windows only if the admissible regions move (`coversim.py` predicts the kernel run exactly; its polynomials
equal `gen_return86.py`'s on all guards and rows, `mirror.py`). No certificate generator is needed.

## 4. Proof of concept (built)

`Submissions/arvi_return_tuning/` (Lean 4.34.1). Build with `lake build Submissions.arvi_return_tuning.FinalF50`.

* `QRH.ArviReturnTuning.dirichlet_nonvanishing_f50 : (43693617/50000000 : ℝ) < s.re → … → LFunction χ s ≠ 0`.
  It depends on axioms **[propext, Classical.choice, Quot.sound]** [Lean, `FinalF50.lean:22`]. No `sorry`,
  `native_decide` or new axioms; the kernel checks are `decide +kernel`.
* Its import closure contains none of `Return/Rows/*`, `Return/EdgeCertificates`, `Return/Windows` or the
  window-dependent tail; it keeps 14 constant/static modules of `arvi_density/Return` [derived,
  import-graph script in the session].
* Same statement: `example : @QRH.ArviReturnTuning.dirichlet_nonvanishing_f50 =
  @QRH.ArviDensity.dirichlet_nonvanishing_f50 := rfl` compiles [Lean, test file in `$SCRATCH/return-tuning/lean/Same.lean`].
* `Compat.lean` re-certifies all 31 merged windows with the kernel check (all pass without subdivision) and
  proves `returnWindowNN' = returnWindowNN` and the list equality `returnWindows' = returnWindows` by `rfl`.
  The reflective windows are drop-in replacements [Lean].
* Kernel work [derived, `coversim.py`]: 5 windows × 15 guards = 75 Bernstein tests. The four edges take
  1 + 3 + 3 + 142 tests; newTop has 42 leaves at depth up to 23 (as in the merged cover) and uses all five
  windows. With the 31 merged windows the kernel cover uses only 9 of them.

### Check time [numerical, `time_modules.sh`, `logs/times.tsv`]

CPU seconds (user+sys) of `lake env lean FILE`, one file at a time, each including its own import loading
(2.7–5 s). The machine was shared (load average 2–3 during the run).

| replaced (merged `arvi_density/Return`) | files | bytes | CPU s |
|---|---|---|---|
| `Rows/Admission01..31` | 31 | 630,573 | 866 (25–31 each) |
| `Rows/Edge_*` | 6 | 84,504 | 154 |
| `EdgeCertificates.lean` | 1 | 70,881 | 39 |
| `Windows.lean` | 1 | 10,337 | 8 |
| **total** | **39** | **796,295** | **1067** |

| new (`arvi_return_tuning`) | files | bytes | CPU s |
|---|---|---|---|
| library (`Poly2, GuardsQ, Guards, Data, RowsQ, CoverQ`) | 6 | 41,462 | 42 (mostly imports) |
| `Windows.lean` (5 windows, one `decide +kernel`) | 1 | 1,402 | 18 |
| `EdgeCertificates.lean` (4 kernel covers) | 1 | 2,602 | 33 |
| **total** | **8** | **45,466** | **94** |

The ratio is about 11× in CPU and 17× in bytes; the slowest new module takes 33 s. The seven forks cost the
same as their originals (for example `FinalWindows` 7.9 s vs 6.6 s). `Compat.lean` (31 merged
windows re-certified, plus `rfl`) takes 66 s, against 866 s for the 31 Admission files. Once the new files are in place,
`Return/` would hold 13 modules and about 124 KB (now 44 modules, 875 KB). Together with `ReturnD/` (unchanged, 970 KB) the total goes from
1.84 MB to 1.09 MB.

### State of the proof of concept

* **Rebuilt by the lead after hand-off** (2026-10-29): `lake build Submissions.arvi_return_tuning.SameStatement
  Submissions.arvi_return_tuning.FinalF50` succeeds (13880 jobs, about 2.4 min wall). The in-tree test
  `SameStatement.lean` compiles the `rfl` same-statement check, and `#print axioms` gives
  `[propext, Classical.choice, Quot.sound]` for `dirichlet_nonvanishing_f50`, `closed_envelope_return_cover`,
  `windows_ok`, `ev_guard`, `coverOK_sound` and `Compat.returnWindows_eq` [Lean]. A grep finds no `sorry`,
  `admit`, `native_decide` or `axiom` in the module.
* A copy of the Lean sources is in `research/lean/arvi_return_tuning/` (the build tree is outside the repository).

## 5. Hard-coded constants that become computed

* **Computed in the PoC**:
  * the 465 guard polynomials and the row polynomials (each was re-expanded by `norm_num … <;> ring` in a
    per-certificate identity);
  * all Bernstein coefficient matrices;
  * the cover trees and the branch of every leaf;
  * the edge capacities (literals in `Constants.lean:58-69`; computed in `Data.lean` from c, h, the
    physical face and numeratorCap).
* **Removable**: guards 1, 2, 12 and 14 (unused; they need a one-line change to `ReturnCountWindow` and
  `CountAdmission`); the cutoff bound 12499/10000 (only 3/2 is needed); 26 of the 31 windows.
* **Could become definitions**: h := floor ceiling of θ (linear in θ). The windows could be found by a
  Lean search, but they are 5 × 4 rationals.
* **Remain inputs**: c (θ), the two faces, numeratorCap, dm, reserve. Per-window m₋/natural join could be
  tuned, but they give no θ (§2).

## 6. Caveats

* "Least certifiable θ" is relative to the present interfaces: Collet's count lemma, `rowAt`, the transport
  box, the chain's faces and their restrictions. The bracket checks one point exactly; the bisection value
  of θ\* is numerical.
* Timings were taken on a shared machine with a load average of 2–12; CPU seconds include each file's import
  loading (2.7–5 s).
* The kernel arithmetic is in ℚ, not integers; integer scaling as in `Faceless/TreeZ.lean` would be faster.
  It is not needed at this size.
* `Data.lean` repeats the base literals of `Constants.lean` and proves them equal. A full replacement would
  generate `Constants.lean` from them.

## 7. Files

`model.py` (float/Fraction model of `Formulas.lean`), `windows.py` (parses the merged windows and rows),
`chainfaces.py` (the 131 proven faces), `analyze1..6.py`, `theta_star.py`, `exact_bracket.py`, `mirror.py`
(exact mirror of the Lean checker), `winsearch.py`, `coversim.py`, `gen_compat.py` (emits `Compat.lean`),
`fork_tail.py` (emits the seven forks), `time_modules.sh` (CPU timings), `logs/`.
