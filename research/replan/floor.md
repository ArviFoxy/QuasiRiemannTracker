# The density floor `q >= 13/20` (= `a >= 33/40`): proof artefact or real limit?

Read-only analysis. No `lake`/`lean` was run; nothing was committed, pushed or posted; no repo file was touched
(replica scripts and logs live in `.../scratchpad/analysis/floor/`, see Appendix C).
Tags: **[V]** verified by reading Lean source or by a text diff; **[R]** float replica of Lean gates / return (not a proof);
**[I]** inference.

Path shorthand
* `HC/`  = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/` (Collet, PR 69)
* `BL/`  = `/home/user/lean-env/qrh/Submissions/openai_baseline/` (OAI baseline)
* `S83/` = `$SCRATCH/upstream/submissions/2026-10-26-sil-density-split/src/Submissions/sil_density_split_20261026/`
* `S86/` = `.../upstream/submissions/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/`
* `Q/`   = `/home/user/QuasiRiemannTracker/submissions/` (the repo's accepted submissions; PR 67 = `two-level-affine-20261019`)

---------------------------------------------------------------------------------------------------

## 0. Bottom line

1. **[V] Relation.** `q = nu = 2a - 1`, i.e. `a = (1+q)/2` is the real part of a zero. `13/20 <-> 33/40`, `3/4 <-> 7/8`, `3/5 <-> 4/5`,
   `1/2 <-> 3/4`. PR 83 states the HIGH range as `b in [(q+1)/2, 7/8]` (`S83/Density/LeafHighEnergy.lean:109,148`) and derives
   `33/40 <= b` from `13/20 <= q` by one `linarith` (`:153`, `hc.1 : (q+1)/2 <= bufferValue`).
2. **[V] The only theorem in PR 83's chain that actually stops at `33/40` is one Collet lemma**, `fixed_natural_dictionary_raw_density`
   (`HC/Cycle61/Density/NaturalEndpoint.lean:91`), called once at `S83/Density/LeafHigh.lean:112`. Every other Collet theorem PR 83 calls
   (`actual_high_retained_row`, `actual_high_slots`, `physical_family_maximum_to_fixed_dictionary`, `retained_zero_bin_low`, ...) is stated for
   `51/100 <= a <= 1` or `51/100 < a`, and PR 83's own LOW branch is stated for `1/50 <= q <= 1` (`S83/Density/LeafLow.lean:60`;
   `(q+1)/2 >= 51/100 <=> q >= 1/50`).
3. **[V] Inside the Lean proof `33/40 <= a` is never used for anything except positivity-type facts** (`0 < s.re`, `51/100 <= s.re`, `51/100 < a`,
   `0 <= 2a-1`). The tightest one is `HC/Cycle61/Density/SmallHeight.lean:74-76` (`51/100 < bufferValue e p` from `bufferValue > a - e`,
   `e < 1/1000`), which needs `a >= 0.511`. So the existing proof supports `a >= 0.511` (`q >= 0.022`) with no change of any tactic block.
4. **[V] It is a convenience constant that has been lowered by successive submissions with identical proofs.** The same wrapper chain exists in this
   repo with floor `167/200, 33/40, 81/100, 4/5, 3/4`. In particular, Collet's own tree contains
   (a) `HC/Record1252270103Bootstrap/PR67Source/Cycle63/Density/*` = the same lemma at **`4/5 <= a`** (including the exact lemma PR 83 needs,
   `.../NaturalEndpoint.lean:94`), and (b) `HC/Record1252270103Source/High/OrdinaryRange*.lean` = the wrapper chain "extended to a >= 3/4"
   with the docstring "the actual maxima count already has lower boundary 51/100; every extended wrapper body below is checked at the literal
   boundary 3/4". In six of seven compared Density files the `linarith` lines of the 4/5 and 33/40 vintages are textually identical (0 differing
   lines); the seventh (`FixedDensity`) differs only by two lines belonging to a theorem that the 4/5 vintage lacks.
5. **[R] Lowering the floor does let the chain continue, and nothing else binds first.** With the floor removed the only gate that sets the
   crossing slope is `J(w,q(v)) > 0` (`high_at_q`); `H >= 9/10`, `principal`, `second_ref`, `second_diag`, `ref_upper`, `q_upper`, `q>1/2` have
   reserves 0.009 - 0.15 down to L = 2.12. Greedy chains from PR 86's end face (ΔL = 0.005, gates >= 1e-6):

   | floor q0 (a0) | useful steps | chain end (L, B) | theta, count/physical role split | vs same-model PR 86 end 0.873954811 |
   |---|---|---|---|---|
   | 0.65 (33/40, now) | 0 | (2.3415, 0.98882) | 0.873954811 | 0 |
   | 0.64 (0.82)  | 6  | (2.3115, 0.98673) | 0.873952103 | -2.7e-6 |
   | 0.62 (81/100)| 16 | (2.2615, 0.98314) | 0.873948059 | -6.8e-6 |
   | **0.60 (4/5)** | 27 | (2.2065, 0.97872) | **0.873946037** | **-8.8e-6** |
   | none (>= 0.5)| 30-32 | (2.19-2.18, 0.9774-0.9766) | 0.873945885 | -8.9e-6 (only -1.5e-7 beyond 0.60) |

   So a floor of exactly `q0 = 3/5` (`a0 = 4/5`, already proved in PR 67's Lean) captures essentially the whole benefit. A coarse chain
   (7 steps of ΔL = 0.02) already gives 0.873946838 (-8.0e-6).
6. **[R] Two side conditions the floor does not remove:** (i) the benefit exists only with a *role split* (count face = deep chain end, physical
   face stays near L = 2.37); with a single face theta gets worse (0.873962669 at L = 2.2065). (ii) Sil's return window 03 (branch C) fails its
   guard 8 for faces below L ~ 2.27 (margin 2.9e-3 -> 1.6e-3 -> -5.4e-4 -> -2.1e-3 at L = 2.3415/2.3115/2.2615/2.2065); lowering `mMinus` to 0.33
   does not repair it, a PR 84-style re-tile of window 03 would be needed.

---------------------------------------------------------------------------------------------------

## 1. Where `33/40` and `13/20` enter

### 1.1 The relation between `a` and `q`

* `a` (or `b`) is a lower bound for the real part of a zero. `HC/LocalMoment/RawSixthDensity.lean:16-20`:
  `rawZeroBin data a b T u := exists hn, a <= zeroMaximum (fun i => (data i).character u) hn T /\ zeroMaximum ... T <= b`.
  `zeroMaximum` (`BL/OAI/NumberTheory/DirichletL/Hecke/DetectorZeros.lean:66`) is the maximum real part, over `|Im s| <= T`, of the zeros of the
  family's L-functions with `Re s >= 51/100` (`realParts := insert (51/100) ...`, :60-61).
* `nu = 2a - 1` is the density parameter; the count exponent is `unmarkedDensity nu = 1 - 10 nu/(3(5-2nu)) = 1 - 10nu/(15-6nu) = rho(nu)`
  (`HC/LocalMoment/UnmarkedDensity.lean:21`; PR 83's `rhoOf`, `S83/Source/HybridGates.lean:55`).
* PR 83 cuts the energy at `q`: a row is LOW if some retained zero bin lies strictly below `(q+1)/2` (`S83/Density/LeafRows.lean:259-265`),
  HIGH otherwise, so a HIGH row has `b >= (q+1)/2` and `nu = 2b - 1 in [q, 3/4]` (`S83/Density/LeafHigh.lean:5-6`).
  Hence **`q >= 13/20  <=>  b >= (1 + 13/20)/2 = 33/40`**, and `b <= 7/8 <=> nu <= 3/4` (the incumbent `beta <= 7/8`,
  `HC/Cycle61/Density/FixedDensity.lean:17`, `densQ <= 3/4` at `S83/Density/Price.lean:27`).

### 1.2 Statements carrying `33/40` (all in `HC/`, 33 statement hits + 1 docstring; false positives such as `Finite/Source128.lean:6` excluded)

| group | file:line |
|---|---|
| `Cycle61/Density` | `ActualZeros.lean:24,43,78,121`; `NaturalEndpoint.lean:67,91,107`; `NaturalMaskTransport.lean:67`; `SmallHeight.lean:25`; `FixedDensity.lean:25,57,64`; `UniformFree.lean:20`; `BufferedPartition.lean:58` |
| `Cycle61/Moment` | `ActualRowDensity.lean:61`; `JointHighDensity.lean:40,139`; `PhysicalHighRows.lean:110,155,199`; `HighSourceEnergy.lean:208`; `ProfileHighEnergy.lean:65`; `WholeSourceFamily.lean:125`; `JointShellEnergy.lean:130`; `ProfileJointShellEnergy.lean:29,159` |
| `Cycle61/Physical/InitialMass` | `GeometryHighShell.lean:56`; `SecondSelectedHighShell.lean:36`; `SecondChildHighShell.lean:42`; `SecondHighShell.lean:37` |
| `Record12518109Gain` | `ActualRootOrdinary.lean:53,85,129` (docstring :1: "Reuses existing checked Cycle61 density at its exact lower boundary 33/40; the endpoint HIGH range lies inside this boundary") |

(The earlier suspicion that `33/40` comes from `BL/OAI/NumberTheory/DirichletL/Detector/EulerRegion.lean:37` (`||K|| <= Q^(-(33/40))`) is wrong [V]:
there `coordK_norm_le` (`.../Detector/EulerCoordinates.lean:67`) gives `||K|| <= Q^(1 - x.re - w.re)` and the hypotheses `x.re >= 7/8, w.re >= 19/20`
make the exponent `<= -(7/8 + 19/20 - 1) = -33/40`; a numerical coincidence in a local Euler-factor error bound, unrelated to the density range.)

Which of these PR 83 can reach [V]: the closure of PR 83 contains all 14 `Cycle61.Density.*`, `Moment.{PhysicalHighRows, JointHighDensity,
ActualRowDensity, HighSourceEnergy, WholeSourceFamily}` but **not** `ProfileHighEnergy`, `ProfileJointShellEnergy`, `JointShellEnergy`, any `*HighShell`
(`analysis/closure_modules.txt`). The only call in PR 83 whose hypothesis is above ~0.51 is `fixed_natural_dictionary_raw_density` (33/40) at
`S83/Density/LeafHigh.lean:112`; the neighbouring call `physical_family_maximum_to_fixed_dictionary` (`51/100 < a`, `HC/Cycle61/Moment/PhysicalHighRows.lean:73`) at `:144` needs only `51/100 < a`.
`actual_high_slots` (`HC/Cycle61/Moment/HighSlots.lean:34,100`) and `actual_high_retained_row` (`HighRetainedRows.lean:40`) are stated for `51/100 <= a <= 1`.

### 1.3 Every place the hypothesis `33/40 <= a` is consumed in a proof [V]

Everything else just forwards `ha ha'` to the next theorem (e.g. `JointHighDensity.lean:~100-110`, `PhysicalHighRows.lean:~141,188`, `ActualRowDensity.lean:~70`).

| site | what is derived | arithmetic | needs |
|---|---|---|---|
| `ActualZeros.lean:31` | `51/100 <= s.re` for `zero_re_le_maximum` (`BL/.../DetectorZeros.lean:83`) | `s.re >= a >= 33/40` | `a >= 0.51` |
| `ActualZeros.lean:34-35` | `0 < s.re` for `zero_re_le_beta`; then `51/100 <= beta` | `beta >= s.re >= a` | `a >= 0.51` |
| `ActualZeros.lean:69`, `NaturalEndpoint.lean:82`, `NaturalMaskTransport.lean:76`, `JointHighDensity.lean:167`, `PhysicalHighRows.lean:145` | `0 < s.re` / `0 < a` | trivial | `a > 0` |
| `BufferedPartition.lean:78`, `UniformFree.lean:101`, `PhysicalHighRows.lean:192` (PR 83: `LeafHigh.lean:154`) | `51/100 < a` for `beta_lower_of_nonempty_bin` / `physical_family_maximum_to_fixed_dictionary` | strict | `a > 0.51` |
| **`SmallHeight.lean:74-76`** | `hb0 : 51/100 < bufferValue e p` from `bufferValue > a - e`, `e < 1/1000` (`he'`) | `33/40 - 1/1000 = 0.824 > 0.51` | **`a >= 0.511` (tightest)** |
| `FixedDensity.lean:47` (`unmarkedDensity_le_one (delta := 2a-1) (by linarith) (by linarith)`) | first goal `0 <= 2a-1` (second goal `2a-1 <= 3/4` uses `a <= 7/8`) | `2a-1 >= 13/20` | `a >= 1/2` |
| `HighSourceEnergy.lean:249-251`, `ProfileHighEnergy.lean:46`, `JointShellEnergy.lean:205`, `ProfileJointShellEnergy.lean:114` | `51/100 <= a`, `a <= 1`, `1/2 <= a` | trivial | `a >= 0.51` |
| `Physical/InitialMass/SecondChildHighShell.lean:159-160`, `SecondHighShell.lean:133,146` (not on PR 83's path; glanced, not traced in full) | `0 <= 2a-1`, `2a-1 <= 1`-type side goals | trivial | `a >= 1/2` |

Contrast with the *upper* hypothesis `a <= 7/8`, which is real: it gives `nu <= 3/4`, hence `rho(nu) >= 2/7 > 1/6`
(`unmarkedDensity_ge_two_sevenths`; `HC/Cycle61/Density/FixedDensity.lean:73-82` feeds `2/7` to `raw_density_weighted_from_eventual_free` whose
summability hypothesis is `1/6 < rho`, `HC/LocalMoment/UniformDensity.lean:54`, `RawSixthDensity.lean:119`), plus the rounding lemma
`unmarkedDensity_rounding` (`HC/Cycle61/Density/Rounding.lean:6`, uses `a <= 7/8, b <= 7/8`).

The deeper layers have no `33/40` at all [V]: `actual_maxima_bin_count` is stated for `51/100 < b <= 7/8`
(`HC/Cycle61/Density/ActualMaximaCount.lean:32`) and `DensityCountingSetup.actual_batch_count` for `1/2 <= a`, `2a-1 <= 5/6`
(`ActualBatchCount.lean:49,90`; same in the baseline moment bound `HC/LocalMoment/UnmarkedDensity.lean:176`).

### 1.4 Where the floor sits on PR 83's side [V]

| site | content |
|---|---|
| `S83/Density/Price.lean:25-29,36-41` | `densQ := max (13/20) (min (3/4) dens)`, `densQ_ge`, `densQ_eq (h1 : 13/20 <= dens ...)` - clip is the identity on the certified range |
| `S83/Density/Leaf.lean:293` | `hq0 : 13/20 <= q := densQ_ge ...` feeding `high_branch` |
| `S83/Density/LeafHighEnergy.lean:52` | `high_branch` hypothesis `13/20 <= q -> q <= 3/4`; `:153` `(by linarith [hc.1])` proves `33/40 <= bufferValue`; `:191` `hnuq : q <= nu` |
| `S83/Density/LeafHigh.lean:107,112` | `high_row_count` states `33/40 <= b` and calls Collet's lemma; `:154` `(by linarith)` gives `51/100 < b` |
| `S83/Density/StepGates.lean:221,242-243` | `h.dens_floor` makes `densQ = dens` in the ledger |
| `S83/Source/HybridGates.lean:73-74,120,276-282,549-554` | gate `gQFloor = dens - 13/20`, field `q_floor`, cleared form `gQFloor_mul`, lemma `dens_floor` |
| every certificate (`HybridCertificatesFirst/Second`, PR 84-86 files, 46 in PR 86) | one `q_floor` block each (`nQFloor/dQFloor` numerals derived from `13/20`; e.g. `S86/Source/HybridK15_01.lean:112-135`), `q_floor :=` in the assembly (:836) |

Independent PR 83 floors: LOW branch `q >= 1/50` (`LeafLow.lean:60`); Sil's gate `q > 1/2` (`HybridGates.lean:71,118`), used because
`150/((15-6nu1)(15-6nu2)) >= 25/24` only for `nu_i >= 1/2` (`density_slope_ge`, `:167`; `highJ_mono_quant`, `:179`; gate field `high_density_derivative`, `:131`). Neither binds near 0.60.

---------------------------------------------------------------------------------------------------

## 2. Mathematical role

* **What `a` measures.** The real part of a zero of a (Hecke, sextic, over `Z[omega]`) L-function of a row `u`; the "bin" of a row is the
  maximum zero real part in the window `|Im s| <= T`. `nu = 2a-1` measures the distance from the critical line (`Re s = (1+nu)/2`).
* **What the lemma ("Lemma 2.1", docstring at `HC/Cycle61/Density/NaturalEndpoint.lean:85`) is.** A zero-density estimate for the fixed natural
  dictionary: `#{rows of norm <= H : some L(s, chi_{j,row}) has a zero with Re s >= a, |Im s| <= T} <= C (1+T)^J H^(rho(2a-1)+loss)`.
  The exponent comes from `unmarked_count_bound` (`HC/LocalMoment/UnmarkedDensity.lean:71`): inverse Moebius moment `max(1,(1+5r)/6) - nu r`
  against plain 4th moment `1 - 2 nu m`, balanced at `unmarkedCutoff nu = 5/(5-2nu)` (`:62`: `1 <= cutoff <= 3/2` iff `0 <= nu <= 5/6`). The
  hypotheses are exactly `1/2 <= a`, `2a-1 <= 5/6` (`:176`). The repo's own notes (`research/round9/README.md` s.1) derive the same `rho`.
* **Why the lower bound is not mathematical.** No inequality in the proof involves a lower threshold above `51/100` (Section 1.3). The *lower*
  end of the stated range does not enter summability (that needs `rho > 1/6`, i.e. an upper bound on `nu`), nor positivity of a kernel.
  In PR 83, rows with bins below `(q+1)/2` are paid by LOW erasure at cost `q` per unit width (no density estimate needed), rows above by the
  lemma; `q` is a free design parameter (the optimal `q(w) = dens(v) -> q_inf = 0.999 L0/(6B0-L0)`, which *decreases* as `L` decreases:
  0.6513 at PR 86's end, 0.5989 at L = 2.2). The Lean statement's lower end is therefore the HIGH range of whichever construction first
  needed the lemma: Collet's own docstring says so (`HC/Record12518109Gain/ActualRootOrdinary.lean:1`), and PR 67 builds its returned-count bin
  value as `max (4/5) (exponentBinLower ...)` (`Q/two-level-affine-20261019/src/Candidate/Cycle63/Physical/InitialMass/DepthTwoReturnedCount.lean:249`), i.e. 4/5 is a
  design cut of that construction, not a number the density proof produced.
* **History of the constant [V, git + grep].** Same wrapper chain, floor by submission: `167/200` (10-13 `affine-local`, `certb-local`, `local44`,
  `reserve-local`, `gao-asymmetric-reserves`) -> `33/40` (10-13 Collet `cycle61-c0125139`, "extends the density range", commit 170037c8; Gao 752fd195;
  kept by `radical-asymmetric-count`, `detector-affine`, `gao-affine-asymmetric`, `gao-directional-affine`, `no-hardcoding`) ->
  `81/100` (10-16 Gao ee7be4e7, `gao-balanced-marked`; 10-19 Sil `sil-uneven-normalization`) -> `4/5` (10-20 `two-level-affine` = PR 67, commit 0db497ed,
  whose metadata has first junction 0.638012 < 0.65 [I: the reason]; then Gao `five-step-affine`, Collet PR 69 `PR67Source/Cycle63`) -> `3/4` (PR 69
  `Record1252270103Source/High/OrdinaryRange*`, used by `PositiveRadius/NaturalRaw.lean:~56`, `OrdinaryRoots.lean:20,52`).

---------------------------------------------------------------------------------------------------

## 3. Does the same proof go through with a weaker bound?

### 3.1 Evidence [V]

1. **Text diff of the two vintages.** `HC/Record1252270103Bootstrap/PR67Source/Cycle63/Density/{ActualZeros,FixedDensity,UniformFree,SmallHeight,
   BufferedPartition,NaturalEndpoint,ActualMaximaCount,...}.lean` (floor `4/5`) vs `HC/Cycle61/Density/*` (floor `33/40`), after replacing both numerals by
   a placeholder, differ only in (i) quantifier order (`exists J, forall D, exists C` vs `forall D, exists J C`), (ii) extra lemmas in the Cycle61 vintage
   (`fixed_dictionary_raw_density`, `fixed_natural_dictionary_free_density`, masked-row transport), (iii) the `namespace Record1252270103Bootstrap.PR67` wrapper.
   Counting `linarith` lines: ActualZeros 9/9, UniformFree 15/15, SmallHeight 3/3, BufferedPartition 7/7, NaturalEndpoint 1/1, ActualMaximaCount 5/5 identical;
   FixedDensity 2 vs 4 (the 2 extra belong to the extra theorem).
   Reproduce: `diff <(sed 's/4\/5/A/g;s/33\/40/A/g' PR67Source/Cycle63/Density/UniformFree.lean) <(sed 's/33\/40/A/g' Cycle61/Density/UniformFree.lean)`.
2. **The 3/4 vintage** `HC/Record1252270103Source/High/OrdinaryRangeDensity.lean:20,52,55,74,109` / `OrdinaryRangeUniform.lean:23` /
   `OrdinaryRangeSmallHeight.lean:28` / `OrdinaryRangePartition.lean:22` re-states `fixed_dictionary_eventual_free_density`, `actual_zero_regular_bin`,
   `oriented_zero_core_predicate`, `fixed_dictionary_eventual_with_exceptions`, `actual_uniform_free_density_normalized`, `actual_buffered_partition` with
   `3/4 <= a` and *verbatim the same proof bodies* (compare the body of `actual_uniform_free_density_normalized` in `OrdinaryRangeUniform.lean` with `Cycle61/Density/UniformFree.lean`).
3. **PR 67's lemma is exactly what PR 83 calls.** `PR67Source/Cycle63/Density/NaturalEndpoint.lean:91-96`:
   `exists J, forall base, exists C, 0 < C /\ forall reverse a T, 4/5 <= a -> a <= 7/8 -> 0 <= T -> forall H > 0, forall rows : Finset NonzeroFrequency, (forall u in rows, rawFrequencyNorm u <= H /\ naturalActualZeroRow base reverse a T u) -> rows.card <= C*(1+T)^J*H^(unmarkedDensity (2a-1)+loss)`.
   It is stronger than Cycle61's (weaker hypothesis on `a`, and `J` independent of `base`). The same file is in `Q/two-level-affine-20261019` and `Q/gao-five-step-affine-20261020`
   (accepted PRs), so it compiled there. [I: build status inferred from acceptance, not re-run.]

### 3.2 Tightest consumer and minimal `a`

* Collet's count as written: **`a >= 0.511`** (`SmallHeight.lean:74-76`; `ActualZeros.lean:31` and `BufferedPartition.lean:78`/`UniformFree.lean:101` need `a >= 0.51`/`a > 0.51`).
  Underlying baseline floor: `zeroMaximum` is defined with the point `51/100` (`BL/.../Hecke/DetectorZeros.lean:60-61`; `zero_re_le_maximum` :83 needs `51/100 <= s.re`, `maximum_attained` :93 needs `51/100 < zeroMaximum`).
* PR 83's HIGH reduction as written: `q >= 1/2` (Sil's own `q_lower`/`25/24`), PR 83's LOW branch `q >= 1/50`.
* So the architecture needs nothing above `q = 1/2`; the target `q ~ 0.60` is above every genuine floor [V].
* No `norm_num` step is involved; there is no arithmetic slack argument; the number is a pure domain restriction [V].

### 3.3 What changing it costs (Lean lines) [I from the sites above]

* **Option A (import PR 67's 4/5 lemma).** `S83/Density/LeafHigh.lean`: change `33/40` -> `4/5` (:107) and the call at :112 to
  `Record1252270103Bootstrap.PR67.OAI.SevenEighths.LocalMoment.fixed_natural_dictionary_raw_density` + `obtain ... := hJ base`; the PR67 copies of
  `naturalActualZeroRow`, `rawFrequencyNorm`, `unmarkedDensity` are different constants with identical bodies (defeq by unfolding): ~10-30 lines of glue.
  Adds the 15 PR67 `Cycle63/Density` modules (1,476 lines) to the import closure (none of them is in PR 83's closure today; its 10 `PR67Source...Marked.*`
  modules are).
* **Option B (fork Collet's six files).** `BufferedPartition, SmallHeight, UniformFree, FixedDensity, ActualZeros, NaturalEndpoint` = 731 lines, 13
  numerals (`BufferedPartition:58, SmallHeight:25, UniformFree:20, FixedDensity:25,57,64, ActualZeros:24,43,78,121, NaturalEndpoint:67,91,107`) to change.
  `ActualMaximaCount`, `ActualBatchCount`, `Rounding`, `CountingSetup`, `ExceptionalLift` have no numeral and can stay imported.
* **PR 83 side** (must be forked, not edited, in a descendant of PR 86): `Density/{Price 201, LeafHigh 158, LeafHighEnergy 246, Leaf 552, StepGates 360}` and
  `Source/HybridGates 602` = ~2.1k lines, ~10 numeral edits (`Price:27,29,39`; `Leaf:293`; `LeafHighEnergy:52`; `LeafHigh:107`; `HybridGates:74,120,280,552`).
  The generic `cubefree_step`/`contrary_raw_side_provider` are parametrised by `price`, so the cascade stops there. The 46 old PR 86 certificates stay valid if the
  old `gQFloor` (13/20) is kept for them (an adapter `13/20-floor => q0-floor`, ~25 lines); new steps need new certificates (generator not shipped; PR 86
  files are ~835 lines each, so 7 steps ~ 5.8k lines, 27 steps ~ 22k lines).

---------------------------------------------------------------------------------------------------

## 4. Would lowering the floor let the chain continue? (replica numerics [R])

Method: `scratchpad/analysis/floor/floor_chain.py` re-implements `HybridGates` (`S83/Source/HybridGates.lean:62-95,114-138`: 14 gates incl. `q_floor`
with a parameter) exactly as `analysis/model/gates.py`, then from PR 86's end face `G(0.9888151, 2.3415, 0.1)` takes steps of fixed ΔL (c = 1/10 as in
PR 86), optimising `(A,D)` (Nelder-Mead) for the smallest crossing slope `s0` with every gate >= 1e-6. It reproduces the earlier finding that with the
floor at 0.65 only one more step exists (`s0 = 0.0853`, then infeasible).

### 4.1 Reach vs floor (ΔL = 0.005)

Last feasible step / last step on the J-ODE:
`0.64` -> 6 steps, L=2.3115 (step 6 needs a slope jump 0.0686 -> 0.0811, `q_floor` + `principal` tight); `0.63` -> 11, L=2.2865;
`0.62` -> 17, L=2.2565; `0.61` -> 22, L=2.2315; `0.60` -> 28, L=2.2015 (step 28 slope jump 0.0837 -> 0.0883); `0.55`, `0.50`, none -> identical chains, 44 steps
to L = 2.1215 tested (q(0) = 0.573 there), `high_at_q` binding at every step.

### 4.2 Which gate binds (per-gate minimal slope at the chain's (A,D); `gate_thresholds.py`)

Steps k = 1, 8, 16, 24, 32, 40, 44 (L = 2.3365 ... 2.1215, no floor): `high_at_q` = the chain slope (0.0658, 0.0707, 0.0762, 0.0816, 0.0870, 0.0924, 0.0951);
every other gate is satisfied at any slope except `principal` at k=1 (needs >= 0.0106) and `q_lower` at k=44 (needs >= 0.0139).
Reserves (`gate_table.py`, min over v):

| gate | floor 0.60, k=27 (L=2.2065) | no floor, k=44 (L=2.1215) |
|---|---|---|
| `H_lower` (H - 9/10) | 0.072 | 0.096 |
| `principal` | 0.021 | 0.038 |
| `second_ref` / `second_diag` / `ref_upper` | 0.142 / 0.120 / 0.119 | 0.157 / 0.135 / 0.131 |
| `q_lower` (q - 1/2) / `q_upper` | 0.100 / 0.149 | 0.068 / 0.177 |
| `high_deriv` | 0.158 | 0.176 |
| `retained_cap`, `low`, `sel_deriv` (scale-free, positive) | 1.9e-3, 6.3e-4, 0.17 | 2.6e-4, 2.8e-4, 0.024 |
| `q_floor` | 2.0e-4 (binding next) | n/a |
| `high_at_q` | 1e-6 (by construction) | 1e-6 |

(`principal` only becomes active when `q_floor` forces the optimiser to a large `A`, as at floor 0.65 step 47 / floor 0.64 step 6 - then `q_floor` and `principal` are tight together.)
So: the HIGH reserve `J(w,q(v)) > 0` at `v ~ 0` is the single binder (the ODE `dB/dL = (B - 10/(15-6q))/(L-1)`, `q = 0.999 L/(6B-L)`), and the floor is the only
*extra* wall; `q_inf = 0.6513` at PR 86's end explains why 0.65 stops it.

### 4.3 theta (return replica, Sil windows, `analysis/model/fast.py`)

Role split = count face `C` at the chain face, physical/`capP` face fixed at PR 86's step-40 child `(0.9907142, 2.3715)`; `h`, `c` re-optimised.
Baseline (PR 86 end, same solver): role split 0.873954811, single face 0.873955574 (matches the earlier model optimum 0.87395555).

| floor | step (L) | role split | single face |
|---|---|---|---|
| 0.64 | 6 (2.3115) | 0.873952103 | 0.873955116 |
| 0.62 | 16 (2.2615) | 0.873948059 | 0.873955765 |
| 0.60 | 24 / 25 / 26 / **27** / 28 (2.2215 ... 2.2015) | 0.873946342 / .228 / .114 / **.037** / .075 | 0.873960228 ... 0.873963890 |
| none | 26 / 28 / 30 / 32 / 34 / 36 (2.2115 ... 2.1615) | 0.873946114 / .961 / **.885** / **.885** / .961 / 0.873946152 | - |
| 0.60, ΔL = 0.02 | 7 steps, end (2.2015, 0.978156) | 0.873946838 | 0.873965645 |

* Discretisation: 7 steps already give -8.0e-6, 28 steps -8.8e-6 (cost of the extension at fixed floor: the end faces differ by 1.2e-4 in B).
* Without role split the deep faces *hurt* (single-face theta rises past L ~ 2.34), so this lever presupposes the role-split return (earlier note:
  `analysis/pr84_86.md` s.4.2 rows b and h).
* Window 03 (branch C) of `S83/Return/Windows.lean` fails guard 8 below L ~ 2.27 (`win3.py`: margin 2.9e-3 at 2.3415 -> 1.6e-3 -> -5.4e-4 -> -2.1e-3 at 2.2065;
  window 15/16 stay positive). `mminus_scan.py`: mMinus 0.377 ... 0.33 does not fix it; a re-tile (PR 84 shrank window 03 to `[43/128, 3/8]`) is required.
  The float theta is unchanged by the tiling (equal to the "pointwise" evaluation in `analysis/model/nofloor2.log`).

---------------------------------------------------------------------------------------------------

## 5. Verified vs inferred; not done

* **Verified (reading/diff):** the a<->q relation; every statement site and every consumption site of `33/40`; PR 83's `13/20`/`33/40` sites; that PR 83 calls only one
  floor-bearing Collet theorem; that the 4/5 and 3/4 vintages are the same proofs; the history in git.
* **Replica only:** all gate reserves, chain reaches, theta values, window margins.
* **Inferred:** that PR 67's lemma can be glued into `LeafHigh` in ~10-30 lines (the two constants named `naturalActualZeroRow` etc. are defeq but I did not elaborate);
  that no hidden universe/instance clash arises when importing the PR 67 `Density` modules next to the Cycle61 ones (the 10 PR 67 `Marked` modules already co-exist);
  why PR 67 chose 4/5 (junction 0.638 < 0.65); line counts for new certificates (PR 86 file size).
* **Not done:** no Lean elaboration/build; no check of the verifier's build scope (whole dependency tree vs import closure); no generation of any new certificate.

---------------------------------------------------------------------------------------------------

## Appendix A - quick list of the edits for "floor -> 3/5"

1. Count: `S83/Density/LeafHigh.lean:107` (`33/40 -> 4/5`) and :112 (call PR 67's `fixed_natural_dictionary_raw_density`, or fork Option B).
2. Clip/gates: `S83/Density/Price.lean:27,29,39`; `Leaf.lean:293`; `LeafHighEnergy.lean:52`; `Source/HybridGates.lean:74,120,280,552` (`13/20 -> 3/5`, or add a floor parameter).
3. New step certificates for L < 2.3415 (`(A,D)` from `floor/chain_floor_0.60.log`, e.g. 7 steps of ΔL = 0.02: (2.3215,0.987458) (2.3015,0.986046) (2.2815,0.984580) (2.2615,0.983058) (2.2415,0.981482) (2.2215,0.979853) (2.2015,0.978156), A~0.51-0.54, D~32-64 except the last D=6.06 [R]).
4. Return: role-split source hypothesis (template `analysis/pr84_86.md` s.4.4), re-tile window 03.

## Appendix B - occurrences of `13/20` / `33/40` in PR 83 outside certificates

`Density/Leaf.lean:6,293`; `LeafHigh.lean:6,107`; `LeafHighEnergy.lean:37,52`; `Price.lean:5,25,27,29,39`; `Source/HybridGates.lean:9,73,74,278,550` (grep `13/20` over `S83/` minus `Source/HybridCertificates*`, `Return/Rows`, `ReturnD`).

## Appendix C - scripts and logs (`$SCRATCH/analysis/floor/`)

`floor_chain.py` (greedy chain with floor parameter), `gate_thresholds.py` (per-gate minimal slope), `gate_table.py` (all gate minima), `theta_floor.py`, `theta_base.py`,
`theta_nofloor.py` (return replica via `../model/fast.py`), `win3.py` (window margins), `mminus_scan.py`; logs `chain_floor_{0.50,0.55,0.60,0.61,0.62,0.63,0.64,-1.0}.log`,
`chain_dL0.01_floor_0.60.log`, `chain_dL0.02_floor_0.60.log`, `theta_*.log`, `mminus_scan.log`.
