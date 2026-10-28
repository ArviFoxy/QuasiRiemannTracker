# B2 - The density-step slope s0: what fixes it, and can it be made 5-6 % smaller?

Read-only research. No `lake`/`lean` was run, nothing was committed or posted. Python models and logs are in
`$SCRATCH/analysis/B2/` (`$SCRATCH` = `$SCRATCH`).
Tags: **[V]** verified by reading Lean (or by a text comparison); **[R]** replica numerics (float gate replica or the exact-cover
return toolchain of `lemmaW.md`; not a proof); **[I]** inference / judgement.

Path shorthand
* `S83/` = `$SCRATCH/upstream/submissions/2026-10-26-sil-density-split/src/Submissions/sil_density_split_20261026/` (PR 83)
* `HC/` = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/` (Collet), `BL/` = `.../openai_baseline/` (OAI baseline, `OAI/NumberTheory/DirichletL/`)
* `G(B,L,c)` = `GlobalSource B L c`; parent `(B0,L0,c0)`, child `(B,L,c)`, `dL = L0 - L`, `s0 = (B0-B)/dL`.

---------------------------------------------------------------------------------------------------

## 0. Bottom line

1. **No constant in the density step can be changed to give -5 %.** In the continuum the slope is `s0 = (B - 10/(15 - 6q))/(L - 1)` at `q = q_inf = 0.999 L/(6B - L)`,
   the largest LOW threshold the descent condition `q(6B - L) <= L` allows: the zero-density function `10 nu/(15 - 6 nu)`, the packed-envelope rate `6`, the face term `L - 1` and
   the slack `0.999` are the only inputs. The only slack constant is `0.999` (worth -0.3 % of s0, -0.8e-6 in theta). The `6` (= 4 from the D^4 transfer + 2 from column removal) and the `L - 1` are forced by the
   architecture; the `-5.3 %` would need `6 -> 5.93..5.95` (-1.0 %) or `10/(15-6q)` up by +0.5..0.6 % (i.e. `rho(0.6)` lower by 0.0032) or `L-1 -> L-0.93`. Everything else
   (`H >= 9/10`, retained cap, the four reference gates, the selection law, the `J` reserve, the 25/24 monotonicity gate) is not binding at L = 2.34 ... 2.2.
2. **The mixed fourth/sixth idea cannot act inside the density steps**: the density step already *is* the mixed step (identical LOW payment form,
   `1 + q - 6 q B0/L0`); the ADVERSARIAL_REVIEW verdict c = 6 applies verbatim (Section 4).
3. **One structural slack exists, and the stronger lemma is already in Collet's/the baseline's tree (the precedent pattern):** PR 83's HIGH branch uses the
   *unmarked* zero-density count `rho(nu)` for every HIGH row, although its pointwise bound `Z^{nu(P+s)}` is only attained by rows whose prime-slot sums have
   *maximal amplitude*, and the library already counts exactly those rows better (the amplitude-class count `Cycle25DetectorRowCount.rowCount nu p kappa`, used by the
   final return, Section 3). A (nu, x)-resolved HIGH gate lowers s0 by **5-8.6 %** with the library's count as a black box (zero-amplitude padding of the detector
   supply to 7/37), **8-14 %** if the supply condition 7/37 is relaxed to ~0.12 (or top-bin selection is used), up to **21-27 %** idealised [R].
   Exact-return theta (role split, floor 3/5, regenerated Delta L = 0.005 chain, [R]): PR 83 gate 0.873946262 -> black box **0.873938984 (+3.2e-6 above the bar)**,
   supply 0.12 **0.873934359 (-1.4e-6, passes)**, supply 0.09 0.873929714, idealised (continuum) 0.8739167 (limited by the `ell < 0.171` box). With the floor at 0.55 the black
   box reaches 0.873936435 (+6e-7; with `0.999 -> 1` as well 0.873935628, -1.7e-7) and the 0.12 variant 0.873927422 (-8.4e-6). It is **not** drop-in: it is a new HIGH leaf + a two-parameter HIGH gate + new
   step certificates; I estimate 35-45 % that it can be completed at all, ~4-7k hand-written Lean lines and 50-150k generated lines. Nothing else I found on the
   source side is plausible. **Recommendation:** do not start Lean work on it before the 1-2 day bridge audit of Section 6 (row/slot conventions, zero-predicate bridge, `dmax`/supply parameters, moments for the leaf's weights).

---------------------------------------------------------------------------------------------------

## 1. The ODE, derived from the gates (Question 1)

### 1.1 Chain of Lean statements [V]

| step | statement | location |
|---|---|---|
| scalar defs | `cross`, `sel A D v = A v/(1+D v)`, `dens = 999/1000 L0 A/((L0-L)(1+D v)+(6 B0-L0)A)`, `rhoOf nu = 1 - 10 nu/(15-6 nu)`, `packed = 1 - 6 sel`, `highJ B L w u nu = 1 - rho - nu B + nu (L-1) w - (6(1-rho) - nu - 1) u` | `S83/Source/HybridGates.lean:32,38,41-49,55,58,62-63` |
| the 14 gates + LOW identity | `HybridGates` (`q_floor :120`, `low_identity :125`, `high_at_q :130`, `high_density_derivative :131`) | `HybridGates.lean:114-138` |
| envelope `H = 1 + t - 6u` | `SideGeometry.H`; the 6 is `2a - k + q_C` with `a = A-c-u` (u leaves the columns, counted twice: -2u) and `k = K + 4u` (D^4 dilation: -4u) | `CubeFree/StepData.lean:84`; `CubeFree/Second/Side.lean:36-41` (`envelope_identity`, proved by `ring`); `CubeFree/Second/FourthTransfer.lean:35,64` (`selected_row_fourth_one`, `fourth_scale`) |
| LOW defect | `F := P_C + L0 s - B0 H <= dL v + (6 B0 - L0) u`: from root face `P_C + L S <= B`, `s <= S-f-u`, `B0 - B = dL s0` | `S83/Density/StepGates.lean:122-132` (`ds_defect_aux`) |
| LOW payment | `q F <= L0 (u + eps/16)` from the identity `L0 u - q(dL v + (6B0-L0) u) = (1/1000) L0 u` and `q (6B0-L0) <= L0` | `StepGates.lean:134-150` (`ds_low_aux`; used `:250-270`), `:89` (`dsDens_overshoot`), identity `HybridGates.lean:66-67,240` |
| HIGH payment | `nu (P_C+s) - (1-rho(nu)) H <= u` from `P_C + s <= B - (L-1) W - u` and `J >= r` | `StepGates.lean:152-165` (`ds_high_aux`; used `:271-283`), `hPS` derivation `:227-231`; `J` reserve on `[q,3/4]`: `HybridGates.lean:592` (`high_reserve`), monotone in nu: `:179` (`highJ_mono_quant`) |
| HIGH price | `highTerm nu P s M = nu (P+s) - 10nu/(15-6nu) M`, `price = max(q * deletionNeed, sup_{nu in [q,3/4]} highTerm)`, `q` clipped to `[13/20, 3/4]` | `S83/Density/Price.lean:26-29,45,52,123` |
| the count behind `1-rho` | `high_row_count` -> Collet `fixed_natural_dictionary_raw_density` (`a >= 33/40`) -> `unmarkedDensity nu = 1 - 10nu/(3(5-2nu))` | `S83/Density/LeafHigh.lean:102-158` (call `:112`), `HC/Cycle61/Density/NaturalEndpoint.lean:88-96`, `HC/LocalMoment/UnmarkedDensity.lean:21,71` |

### 1.2 The formula

At v = 0 (u = 0, w = s0), with `B = B0 - s0 dL`, `L - 1 = L0 - 1 - dL`:

    J(0, q0) = q0 [ 10/(15 - 6 q0) - B0 + (L0 - 1) s0 ]
    J(0) = 0  <=>  s0 = ( B0 - 10/(15 - 6 q0) ) / ( L0 - 1 ),        q0 = 0.999 L0 A / ( dL + (6 B0 - L0) A ).

*Correction to the ODE as quoted:* at finite dL it is the **parent's** `B0`, `L0 - 1` (the quoted `B`, `L - 1` differ by O(dL)). As dL -> 0, `q0 -> q_inf = 0.999 L/(6B - L)`
independent of (A, D) and the ODE is exactly `dB/dL = (B - 10/(15-6 q))/(L-1)`, `q = 0.999 L/(6B-L)` [V algebra; checked numerically].

Checks [R]: the formula reproduces the actual slope of PR 86's steps to 0.06-0.6 % (`s0 = 0.06510` vs `0.06501` at step 46, `0.03136` vs `0.03116` at step 1; the true minimum of `J` sits at v = 7e-4..2e-3 with
reserve ~1e-5); my own greedy per-step optimiser (all 14 gates >= 1e-6, `B2/dchain.py`, mode `pr83`) regenerates PR 86's chain from the boot face
(`B(2.3415) = 0.988817` vs 0.9888151; step 30: `s0 = 0.05358`, `B = 0.993594` = PR 86's table), and with the exact return reproduces the floor-3/5 result of `lemmaW.md` s4.1
(count step 73 / physical step ~38: 0.873946262 vs 0.873946275).

### 1.3 Which constants are where

* `10/(15 - 6 q)` and `10 nu`: the unmarked zero-density exponent (Collet Lemma 2.1; baseline balance of the inverse moment `(1+5r)/6 - delta r` against the plain 4th moment `1 - 2 delta m`,
  cutoff `5/(5-2 delta)`: `HC/LocalMoment/UnmarkedDensity.lean:62-71`, `BL/.../Hecke/DetectorRowCountEndpoint.lean`). It is the `x = 0` (no prime slot) case of the amplitude-class count.
* `6` in `6 B0 - L0`: the packed-envelope shrink `H = 1 - 6u`, `6 = 4 + 2` (above). `-L0`: the selected slots leave the row. The pair gives the descent condition
  `q (6B0 - L0) <= L0`, i.e. `L0 >= 6 q B0/(1+q)`: for `q = 3/4` this is the native barrier `18B/7`, and the chain tracks the barrier curve `L = 6 q B/(1+q)` as q falls (q = 0.65 at L = 2.34, 0.60 at 2.2).
* `0.999`: only the slack in the LOW identity (`HybridGates.lean:41,49`). `ds_low_aux` needs only `RHS >= 0`, so `1` would do [V]; the field `low_per_excess_width` (`:129`) is the only place that wants it strictly positive and is unused by `Density/StepGates` (grep).
* `L - 1`: the pointwise row bound charges every marked slot at `nu` (cost 1 per unit) while the face charges it L: `P + s <= B - (L-1) S` (`StepData.lean:72`, `StepGates.lean:227-231`).
* `13/20`: `densQ` clip and `q_floor` gate (`Price.lean:26-29`, `HybridGates.lean:74,120`); the only extra wall (floor.md).

---------------------------------------------------------------------------------------------------

## 2. Constant by constant (Question 2)

Instantaneous sensitivity of the ODE slope at the baseline-chain faces `(B_ode(L), L)`; "-5.3 %" row = change that alone gives `s0 -> 0.947 s0` [R, `B2/sens_inst.py`]:

| L (B, s0) | `6` needed | `0.999` needed | `thr(q)=10/(15-6q)` needed (rel.) | equivalent `rho(q)` change | `L-1` needed | `0.999 -> 1.0` gives |
|---|---|---|---|---|---|---|
| 2.3415 (0.98889, 0.0651) | 5.948 (-0.87 %) | 1.0135 (impossible) | +0.0046 (+0.51 %) | -0.0030 | L-0.925 | -0.36 % |
| 2.30 (0.98607, 0.0710) | 5.942 (-0.96 %) | 1.0149 | +0.0049 (+0.55 %) | -0.0031 | L-0.927 | -0.33 % |
| 2.25 (0.98235, 0.0779) | 5.936 (-1.07 %) | 1.0167 | +0.0052 (+0.58 %) | -0.0032 | L-0.930 | -0.30 % |
| 2.20 (0.97828, 0.0847) | 5.929 (-1.19 %) | 1.0184 | +0.0054 (+0.61 %) | -0.0032 | L-0.933 | -0.27 % |

Cumulative effect on exact theta (continuum ODE from (0.99999, 2.5715), floor 3/5, role split count-at-wall / physical-at-best, `B2/run_knobs.py`) [R]:

| change | theta | gap to 0.8739358 |
|---|---|---|
| none (PR 83 gates, floor 3/5) | 0.873945041 | +9.24e-6 |
| `0.999 -> 1` | 0.873944250 | +8.45e-6 |
| `6 -> 5.95` / `5.90` | 0.873933396 / 0.873922213 | -2.4e-6 / -1.36e-5 |
| thr `+0.003` / `+0.005` / `+0.010` | 0.873938297 / 0.873933688 / 0.873923264 | +2.5e-6 / -2.1e-6 / -1.25e-5 |
| `L-1 -> L-1+0.05` / `+0.10` | 0.873939055 / 0.873933285 | +3.25e-6 / -2.5e-6 |
| `s0 x (1-0.053)` / `x (1-0.06)` | 0.873935836 / 0.873934592 | +3.6e-8 / -1.2e-6 |

(about 1.7e-6 of theta per 1 % of s0; the discrete Delta L = 0.005 chain is +1.1-1.2e-6 above its continuum.)

Per constant [V = reading, R = numbers]:

| constant | role | verdict |
|---|---|---|
| `6` | descent `q(6B0-L0) <= L0` | **forced.** 4 = the exponent of the proved transfer identity `sum_v A B_v G(D n_v; k) = sum c(chi,xi) (A chi(D) G(D;k)) P_xi(D^4 k)` with `N(D^4 k) = N(D)^4 N(k)` (`FourthTransfer.lean:35,64`) [I: it is the exponent that makes the residual polynomial D-independent for sextic symbols], 2 = column removal counted twice in the large-sieve envelope (`Side.lean:36`, `a = A-c-u`). The mixed-step review (`research/mixed-step/ADVERSARIAL_REVIEW.md` O1) shows the 2 sits in the same coordinate as the parent's scale, so c = 4 is refuted. A sparse-set large sieve for `{D^4 k}` would remove the dilation cost but is not available (conductor-limited) [I]. |
| `0.999` | slack in LOW identity | **slack but tiny**: `1.0` is admissible in `ds_low_aux` [V]; -0.3 % s0 = -0.8e-6 theta [R: continuum 0.873945041 -> 0.873944250; with the improved HIGH gate -7e-7..-9e-7 in the discrete chains]. Cost: change the numeral in `dens`/`densK`/`gLowPerWidth` (`HybridGates.lean:41,49,80`), drop/relax `low_per_excess_width` (`:129`), regenerate certificates. |
| `10 nu/(15-6nu)` | HIGH count exponent | baseline moments; **the unmarked case.** The marked count is stronger (Section 3). No better *unmarked* exponent exists in the library: a grep over `HC/` and `BL/` for `shortExponent`/`longExponent`/`rowCount`/`countingR`/`unmarkedDensity`/`balancedRowCount` finds only the unmarked family (`UnmarkedDensity`, PR 67's `Cycle63` copy at `a >= 4/5`) and the marked family (`Cycle25`, `Cycle61.Arithmetic`, the baseline `Endpoint`); `RawSixthDensity`/`SixthRowMask` only concern sixth-power raw frequencies (summability `rho > 1/6`); there is no sixth-moment or improved large-values version [V grep]. |
| `L - 1` | face geometry | forced for the unresolved bound; changes to `L - 2x` in the (nu,x)-resolved bound (Section 3). |
| `13/20 -> 3/5` | floor | done in floor.md; below 0.60 worth only -1.5e-7 with PR 83's HIGH, but **-2.5e-6 (black box) .. -6.9e-6 (supply 0.12) once HIGH is improved** (Section 3.3) because the count break-even slope 0.0857 is no longer reached at L = 2.2. Needs the 3/4-vintage `NaturalEndpoint` fork for q < 0.6. |
| selection law `A v/(1+D v)` | u(v) | irrelevant in the limit dL -> 0 (q_inf independent of (A,D)); at dL = 0.005 it only moves the first-order deficit (0.0152 dL in B, ~1.2e-6 in theta). `sel_spec` allows any monotone `0 <= sel <= w`, no 5 % there. |
| `J` reserve / 25/24 gate | monotonicity in nu | `J` is increasing in nu (checked on the whole grid, also for the joint gate), so the sup is at `nu = q`; `J >= r` is the binding gate itself, but PR 86's reserves (~1e-5) cost `r/(q (L-1) s0) ~ 0.02 %` of s0 (~5e-10 in theta). |
| `H >= 9/10` | envelope range of the leaf contract | reserve 0.056-0.096 [R]; not a lever. |
| retained cap `c0 H - (w-u)` | parent cap | reserve 4.6e-4..2.3e-3, scale-free (proportional to u); binds only if c is raised. |
| principal / second_ref / second_diag / ref_upper | reference gates (9/2, 4, 3 are the natural-cost constants) | reserves 0.009-0.034 / 0.13-0.14 / 0.10-0.12 / 0.11-0.13 at L = 2.34 ... 2.2 [R, `floor/gate_table.py`]; irrelevant. |
| `q_lower` 1/2, `q_upper` 3/4 | | reserves 0.10-0.15 / 0.10-0.15. |

---------------------------------------------------------------------------------------------------

## 3. The one structural slack: HIGH is unmarked, the library has the marked count (Question 3)

### 3.1 What the leaf does today [V]

`Density/LeafHighEnergy.lean` (`high_branch`) classifies the HIGH rows only by their zero bin `c` (`selectBin`), bounds each row by
`|row|^2 <= K ctl^2 Z^{nu (P + s) + small}` (`LeafHighRow.lean:58`, from `HC/Cycle61/Moment/HighRetainedRows.lean` = plain-factor bound times `actual_high_slot_product`, i.e.
every slot is bounded by the zero-free region, amplitude `Z^{nu w/2}`), and counts each class by `rho(nu)` (`LeafHigh.lean:102-158`). `energy_le_classes` takes `R c * N c <= G` per class
(`LeafHighEnergy.lean:~145-200`). The pointwise bound is attained only by rows whose normalised prime-slot sums are at the maximum amplitude `Z^{nu w/2}` (bin value `nu/2`, "x = 1/2");
the count `rho(nu)` is the worst case over rows with *no* slot amplitude (x = 0).

### 3.2 What the library proves, unused here [V]

* `positiveSlotRow` is literally `plain factors x prod_i rowSlot_i` (`BL/.../Moments/RetainedEnergy.lean:14`).
* Amplitude bins: `HeckePrimeAmplitudeBins.amplitude`, `amplitude_upper` (`BL/.../Hecke/PrimeAmplitudeBins.lean:11,21`), `amplitudeRows`, `classMean` (`.../Hecke/DetectorAmplitudeFirst.lean:12,21`),
  `physical` (`.../Hecke/DetectorPhysicalSelection.lean:12`), `select_physical_product` (`:32`): rows of a class satisfy `U^{2 mean z - delta mesh} <= |prod_{selected} phys|^2`.
* The marked count: `Cycle25DetectorRowCount.rowCount delta p kappa = 1 - delta + delta C V/(2(V + delta C))`, `V = 5/6 - delta`, `C = 2(1-p)(1-p/3kappa)/(3 - p - 2p/3kappa)`
  (`HC/Cycle25/Assembly/Count/Crossing.lean:6-17`, `Endpoint.lean:6-9`; = `Cycle61.Arithmetic.Bernstein.countingR`, `Cycle61/Arithmetic/Bernstein/Feedback.lean:17`). At p = 0 it equals `unmarkedDensity` [V by algebra
  and by the `old` branch of `S83/Return/Formulas.lean:42-52`]. Conclusion form of the amplitude-class count: `Cycle61/Assembly/Count/SourceCount.lean:17` (`physical_source_amplitude_count`:
  `rows'.card <= C C0 Z^{3t} (Z^d)^{countingR kappa (2a-1) (q/(2a-1)) + ...}`), generic version `Cycle25/Assembly/Count/FromMoments.lean:14`, with the two-guard row hypotheses
  (`a <= detectorMaximum`, `detectorMaximum < a + 2e`) that match the leaf's HIGH bins.
* Uniformity in the slot data is exactly what the leaf needs: `Cycle25/Assembly/Count/SourceAmplitudeClasses.lean:22` quantifies `N, ell, W, upper, z` **after** `forall^f Z`, with
  `dmin, dmax` parameters (supply `(7/37) dmax <= sum ell`, `ell j <= dmin mesh`). The moment inputs are `Cycle25/Assembly/Count/PlainInput.lean:14,37` (`terminal_plain_input`, `terminal_zero_input`),
  assembled in `CertifiedMoments.lean:20`, under `51/100 <= beta`, `2 beta - 1 <= kappa_plain` (both available in the cube-free chain, `FourthPower.IncumbentInput`).
* The leaf's slot data look like the count's (`sigma = 33/50` vs `z.re = 17/50`, `primePool`, `annularWeight`; `LeafHighRow.lean:58-` vs `Cycle25/Assembly/Count/SourceMomentInput.lean:16`, `.../Hecke/PrimeRow.lean:69` `canonicalPrimeAmplitude` = a prime sum of an actual Hecke character by `exists_amplitude_character :77`) [I: conventions not matched line by line].
* The baseline's own 7/8 criterion is of this joint form: `balancedExponent delta y = -1/48 + (2/3) delta + delta x/6 - (13/16)(1 - balancedRowCount delta y)` with `y = 1/2 - x`
  (`BL/OAI/NumberTheory/DirichletL/Endpoint.lean:26-31`; margin `49/440640`, `balanced_endpoint_margin`), tight in (delta, x) - the density step simply collapsed x.

### 3.3 The joint (nu, x) HIGH gate [I: bookkeeping; R: numbers]

For a HIGH row in the class (nu, x) (x = mean slot amplitude fraction, x in [0, 1/2]; the class mean is exactly `classMean/(2a-1)`):

    exponent <= nu P + 2 x nu s + R(nu, x) H,        R = rowCount (marked count),
    ledger:  J_x(w, nu) = (1 - R) H + u - nu ( B - (L - 2x) w - 2 x u ) >= 0  for all nu >= q, x in [0, 1/2]     (H = 1 - 6u),

which for `x = 1/2, R = rho` is exactly PR 83's `highJ`. `J_x` is increasing in nu (checked on [q, 3/4] for x = 0 ... 1/2) and among the x-classes only x = 1/2 binds
(the pointwise term grows by `2 nu s ~ 0.08-0.1` per unit x, the count falls by `~0.03`). At v = 0 the continuum slope becomes

    s0 = max_x ( B - (1 - R(q, x))/q ) / (L - 2x),

i.e. thr(q) -> (1 - R(q,1/2))/q (+0.018 at q = 0.65 in the undiluted case) and `L - 1` unchanged at x = 1/2.

The count saving is `2 z q_mean` with `q_mean` the mean bin over **all** fibre slots and the library's supply condition forces `sum widths >= (7/37) d` (`DetectorRawFiber.lean:46`); the leaf has only
`s = w - u <= 0.1`. Black-box application therefore pads the supply with zero-amplitude dummy pools (legitimate: dummy bins only help), so `q_mean = x s/((7/37) d)`.
I re-derived the count optimisation with a limited supply (`B2/markedcount.py`): it reproduces `rowCount` exactly for supply 7/37 and shows that supply 0.12 already gives the full benefit
(`rowCount(0.6, 0.5) = 0.45753`; supply 0.12: 0.45755; 0.09: 0.45958; 0.07: 0.46711): the 7/37 is the worst case over cutoffs `t`, the leaf's regime (nu >= 0.6) needs ~0.11-0.13 [R/I: my scalar re-derivation, not the Lean proof].

Numbers (all [R]; `B2/{highjoint2,fastjoint,run_scen*,dchain,eval_chain*}.py`):

Instantaneous s0 change vs PR 83's gate at the baseline-chain faces ("supply" = total detector slot width the count theorem is assumed to need, padded with zero-amplitude dummy pools; 7/37 = 0.189 is the library's value, `x_mean = x s/supply`):

| scenario | L = 2.3415 | 2.30 | 2.25 | 2.20 |
|---|---|---|---|---|
| black box (supply 7/37, mean dilution) | -5.0 % | -6.0 % | -7.2 % | -8.6 % |
| supply 0.12 | -8.1 % | -9.7 % | -11.6 % | -13.7 % |
| supply 0.09 | -11.2 % | -13.2 % | -15.8 % | -18.4 % |
| undiluted (detector slots = the leaf's slots) | -20.7 % | -22.5 % | -24.6 % | -26.7 % |

(The gain is back-loaded: it grows as q falls, so a uniform "-5.3 %" is not comparable with the black-box row.)

Exact return (role split: count face at the chain end, physical face at its best L, Lemma-W/Collet windows, `B2/exacttheta.py` = `lemmaW/tc`):

| HIGH gate | continuum, floor 3/5 | discrete dL = 0.005, floor 3/5 (73 regenerated steps) | + `0.999 -> 1` | discrete, floor 0.55 (102 steps) |
|---|---|---|---|---|
| PR 83 (reference) | 0.873945041 (+9.2e-6) | 0.873946262 (+1.05e-5) | 0.873944250 (cont.) | - |
| black box, supply 7/37 | 0.873937874 (+2.1e-6) | 0.873938984 (+3.2e-6) | 0.873938270 (+2.5e-6) | 0.873936435 (+6.4e-7) |
| supply 0.12 | 0.873933205 (-2.6e-6) | 0.873934359 (-1.4e-6) | 0.873933493 (-2.3e-6) | 0.873927422 (-8.4e-6) |
| supply 0.09 | 0.873928533 (-7.3e-6) | 0.873929714 (-6.1e-6) | - | - |
| undiluted | 0.873916667 (box-limited) | - | - | - |

Weakest combined variant (black box + floor 0.55 + `0.999 -> 1`, 102 steps, count at L = 2.1065, physical at L = 2.3615): **0.873935628 (-1.7e-7, passes with no margin)**; PR 83's own gate with `0.999 -> 1` at floor 3/5: 0.873945429 (+9.6e-6).
Floor dependence (continuum): with floor 0.65 nothing passes (black box +1.4e-5; supply 0.12: +1.2e-5; supply 0.09: +1.0e-5; undiluted-ideal +4.4e-6), so the floor 3/5 (floor.md) stays a prerequisite; lowering it to 0.55 adds -2.5e-6 (black box) / -6.9e-6 (supply 0.12) in the discrete chains.
Chains regenerated by `B2/dchain.py` use the same gate replica as `model/gates.py` (validated in 1.2) with the joint gate replacing `high_at_q`; `physical` face re-optimised over L_P in 2.30-2.42 (best 2.34-2.37).

### 3.4 Obstacles and open items [I]

1. **Row bridge.** The library's count is stated for `FreeRow` with `sourceDetectorFamily ... rayCubeFamily` and `physical ... canonicalPrimeAmplitude`; the leaf has `z : O`,
   `NaturalState`, `geometryRowMaximum`, `rowSlot`. Needs: `rowSlot` = `sqrt(P) * physical` up to the conjugation/twist conventions, and the transfer of the zero predicate
   (`physical_family_maximum_to_fixed_dictionary` is the unmarked analogue). Not checked in Lean.
2. **Supply.** Black box needs dummy pools to reach `(7/37) dmax`; the cheaper route is to relax the numerals 7/37, 23/37 in the capacity lemmas (`DetectorRowCount*`/`Cycle25.Assembly.Count`) to the leaf's range (nu >= 0.5) or select the top bins instead of the mean in `select_physical_product`/`common_bin_selection` (`DetectorPhysicalSelection.lean:32`). Each is 1-2k lines of forked baseline/Collet files.
3. **d range.** The return calls the batches with `dmax = 7/8`; the lemma itself has `dmax` as a parameter, but the leaf's envelope is `H >= 9/10`. For `H >= ~1.01` the *unmarked* gate already holds (violation 0.0036 / (1-rho) = 0.008), so `dmax ~ 1.01` suffices [R].
4. **Moments for the leaf's slot weights** (`WeightedSourceData`/`MomentData`), **price contract** (`CubeFree/Price.lean:29`: monotone in P, s, Lipschitz; the x-sup price with `R(nu, x s/sigma)` is monotone in s because `2 x nu >> |dR/ds|`, checked), **certificates** (the gate becomes a rational function in (v, x); `R` has degree ~5 in x; cleared form needs 2-D or per-x Bernstein boxes).
5. Window 03 of the return must be re-tiled for L < 2.27 (floor.md) - common to every lowered-floor plan.

### 3.5 Lean cost [I]

* New leaf (class refinement of `energy_le_classes`, bin-resolved pointwise bound replacing `actual_high_slot_product` by `amplitude_upper`, instantiation of the amplitude-class count for the leaf with dummy pools, row/slot bridge): 2.0-3.5k lines. (The return's analogous wiring `HC/Record1252270103Return/PhysicalDirect/` is 5.6k lines in 53 files; the leaf needs a fraction.)
* Simplification: a **two-class** version (rows with mean amplitude fraction x >= x* = 0.45 are counted by the marked count at x*, the others by the unmarked count with the pointwise slot exponent `2 x* nu s`) keeps ~90 % of the gain (black-box supply: s0 -4.5 / -6.5 / -7.7 % at L = 2.34 / 2.25 / 2.20 vs -5.0 / -7.2 / -8.6 % for the full x-family; x* = 0.30: -2.9 .. -5.1 %) and needs `R` at a single x - one extra gate, one extra count call [R, `B2/twoclass.py`].
* Fork of `Density/{Price, LeafHighEnergy, Leaf, StepGates}` + `Source/HybridGates` with the joint gate: ~2.1k lines (as in floor.md) + ~0.8k new gate algebra.
* New step certificates: generator A1 extended to the joint gate; 73 steps at dL = 0.005 (floor 3/5), 102 at floor 0.55; roughly 1-2x PR 86's 850 lines each: 60-200k generated lines (compile budget 12 h; PR 86's 46 files already 38k lines). A family theorem (gates proved once for all dL) would remove both the 1.2e-6 discretisation loss and most of this.
* The new gate must be used from the first density step: re-using PR 86's first 30 certificate files (L down to 2.4215) and switching afterwards costs +1.7e-6 (black box: 0.873940651) / +2.7e-6 (supply 0.12: 0.873937026, which then fails the bar by +1.2e-6) [R, `B2/dchain_from.py`], because the gain accumulates along the whole chain.
* Probability that all of it closes: 35-45 % [I]. Probability that, if it closes, it reaches the bar: ~50 % for the pure black-box variant (it needs floor 0.55 **and** `0.999 -> 1` and passes with zero margin), ~85-90 % with the supply relaxation / top-bin selection (passes at floor 3/5 with -1.4e-6, -2.3e-6 with `0.999 -> 1`).

---------------------------------------------------------------------------------------------------

## 4. Can the mixed fourth/sixth idea act in the density step's LOW/HIGH branches? (Question 3, second part)

No [V reading, I judgement].

* **LOW.** The density step's LOW payment is the mixed-step payment: `L0 u - q (dL v + (6B0-L0) u) >= 0` is `u (1 + q - 6 q B0/L0) >= q dL v/L0` (cf. `MIXED_STEP_LEMMA.md` s.1: `a(1-6q beta) + d(1+q-6q beta)`, here `a = 0`). The transferred block already leaves the width passed to the parent (the `+q`), saves 1 (`price <= u`) and costs 6 of scale. Descent is `L0 > 6 q B0/(1+q)`; at the chain's operating point `1 + q - 6qB0/L0 ~ 0.001` (it is the 0.999 slack), so both the barrier and the capacity are saturated: more selected width does not help, a smaller coefficient than 6 would, and `ADVERSARIAL_REVIEW.md` O1 refutes c = 4. Collet's sixth-power pool coefficient `1 - 6 q B0/L0` is negative here (`6 q B0/L0 = 1.6`), so adding a pool is useless.
* **HIGH.** The binding HIGH condition is at v = 0 where u = 0: the selection is irrelevant (it only appears in `J(v) - J(0) = q (L-1) v - (6(1-rho) - nu - 1) u(v)`, the bracket being 1.6-1.9 here). A branch-dependent selection (no transfer for HIGH rows, large for LOW rows) would only remove the `O(dL)` loss of q from q_inf (~0.3 %), and looks impossible anyway because the selection is made on the slot widths before the rows are classified [I].
* **Refinements of the 6.** A transfer exponent smaller than 4 would need the residual Gauss polynomial `P(D^4 k)` bounded on the sparse set `{D^4 k}`; the available large sieve is range-limited (cost `N(D)^4`), and for sextic symbols the character in n is `(D/n)_6^{-4}`, which is not a bounded-conductor ray character, so the leaf (finite ray twists `theta`) cannot absorb it. No such lemma exists in `FourthPower/`, `CubeFree/`, or Collet's tree [V grep].

---------------------------------------------------------------------------------------------------

## 5. Things looked at and discarded

* Replacing LOW erasure by per-nu rates or per-bin choices of LOW vs HIGH: the price is already `max_nu min(LOW_nu, HIGH_nu)` at the single threshold `q` that saturates the LOW budget; LOW is increasing and HIGH decreasing in nu, so no gain.
* Applying the parent at an enlarged envelope for near-boundary rows: costs `F/B0 > u` (needs `L0/B0 > 5`).
* LOW erasure resolved by amplitude (cost `2 x nu` per unit): the binding class stays x = 1/2.
* Face-based count branches `C`/`Ccap` in HIGH: their 15 admission guards fail for nu >= 0.6 (the return's windows stop at delta = 0.54); only the `old` marked branch applies (`B2/cbranch.py`). Gain over `old` would be only ~0.001-0.002 in R anyway.
* Bootstrapping the incumbent (kappa = 2 theta - 1 = 0.7479 instead of 3/4): changes nothing at 1e-9 (`rowCount` and the HIGH range nu <= kappa are not binding).
* Richer face families (unions of previous faces as the LOW target; steeper child boundary beyond s0): the HIGH slack beyond the crossing cannot be used because `GlobalSource` is a single linear face; older faces (larger L, larger B) do not contain the rows outside the parent for s > s0 (checked algebraically); lemmaW already finds 0 for extra count faces.
* Handling near-boundary rows with nu >= q_inf by LOW (any selection u > 0): impossible, the net payoff per selected unit is `L0 - nu (6B0-L0) < 0` for nu > q_inf, and u = 0 pays nothing; so HIGH must carry nu in [q_inf, 3/4] down to v -> 0+.

---------------------------------------------------------------------------------------------------

## 6. Ranking (plausibility x payoff, rough Lean cost)

| # | candidate | payoff (theta, [R]) | plausibility | Lean cost | note |
|---|---|---|---|---|---|
| 1 | **(nu,x)-resolved HIGH leaf via the amplitude-class count** | black box 0.8739390 (+3.2e-6; +floor 0.55 and `0.999->1`: 0.8739356, -1.7e-7); with supply 0.12: 0.8739344 (-1.4e-6); idealised 0.8739167 | 35-45 % that it can be completed; payoff if so decisive | 4-7k hand + 60-200k generated lines, multi-week | only candidate with the right size; shares window re-tile and A1 with track A |
| 2 | floor below 3/5 (q >= 1/2; fork `NaturalEndpoint` etc. at the 3/4 vintage) | only with #1: -2.5e-6 (black box) .. -6.9e-6 (supply 0.12) extra | high (same proof bodies) | ~0.8-1k lines + 25-30 more steps | needed to make the black-box variant pass |
| 3 | `0.999 -> 1` in `dens` | -0.8e-6 | high | small + regenerate certificates | free add-on |
| 4 | family theorem / smaller dL | -1.2e-6 (ODE limit) | medium | 1-2k lines, removes 73+ files | add-on |
| 5 | supply relaxation / top-bin selection in the count | turns #1 from marginal to comfortable (+3.2e-6 -> -1.4e-6) | medium | 1-2k lines of forks | part of #1 |
| - | change of `6`, `L-1`, selection law, `9/10`, caps, reference gates, mixed step | none | none | - | forced or non-binding |

Decision tree: (i) bridge audit fails -> stop, best reachable stays 0.8739463 (floor 3/5 + role split, track A); (ii) audit passes but only the black-box count is usable -> the bar is reached only with floor 0.55 **and** `0.999 -> 1`
(0.873935628, a 7-digit declaration 0.8739357 passes by 1e-7: no safety margin, 102 step files); (iii) audit passes and the supply condition can be relaxed (or the top bins selected) -> 0.873934 at floor 3/5 (-1.4e-6; -2.3e-6 with
`0.999 -> 1`), -8e-6 at floor 0.55.

Recommended next step before any Lean: a 1-2 day paper/grep audit of items 3.4.1-3.4.4 (the row bridge `rowSlot` vs `physical`, the zero predicate bridge, `dmax`/supply parameters of
`Cycle25/Assembly/Count/SourceAmplitudeClasses.lean:22`, instantiability of `weighted_source_moments` for the leaf's weights, and `common_bin_selection`'s mean-vs-top selection). If the bridge fails, the source side
cannot reach the bar and the remaining 1.05e-5 must come from the return (B1).

---------------------------------------------------------------------------------------------------

## 7. Verified / inferred / not done

* **Verified [V]:** the gate chain of Section 1.1 (every line cited was read); `6 = 4 + 2` from `envelope_identity` (proved by `ring`); the unmarked count is `x = 0` of the marked one; the leaf classifies HIGH rows by zero bin only; the amplitude-class count and its inputs exist in `HC/` and `BL/` and are uniform in the slot data; `0.999` enters only through `dens`/`low_identity`.
* **Replica numerics [R]:** all sensitivities, chains and thetas (float gate replica validated against PR 86's 46 steps; exact Bernstein-cover return of `lemmaW/tc` validated there against PR 86's 32 rows / 240 admissions; this note adds no new return code).
* **Inference [I]:** that the joint (nu, x) bookkeeping is the right ledger for the leaf (it is the same bookkeeping as the baseline's 7/8 criterion and the return's `Ebase`/`rowAt`, but the leaf's version is not written anywhere), the dilation model for the 7/37 supply, the Lean cost and probability estimates.
* **Not done:** no Lean elaboration of anything; no check that the leaf's `rowSlot` sums match `canonicalPrimeAmplitude` in all conventions; no certificate generation for the joint gate; the discrete chains use the replica's gate tolerance (1e-6) rather than the 1e-5 reserves of the Lean certificates (effect ~5e-10 in theta); window 03 re-tiling not checked for the new faces (exact-cover model used).

## Appendix - files (`$SCRATCH/analysis/B2/`)

`odemod.py`, `odegen.py` (ODE with knobs / arbitrary slope), `sens_inst.py` (Section 2 table), `run_knobs.py`, `rowcount.py`, `markedcount.py` (count optimisation with limited supply, validated against `rowCount`), `highjoint.py`, `highjoint2.py`, `fastjoint.py` (joint gate),
`cbranch.py` (face-based branches at HIGH densities), `dchain.py` (discrete greedy chain with plug-in HIGH gate, `DFAC` env for 0.999), `run_scen*.py`, `eval_chain*.py`, `exacttheta.py` (+ `tc/`: copy of `lemmaW/tc`), logs `dch_*.log/json`.
