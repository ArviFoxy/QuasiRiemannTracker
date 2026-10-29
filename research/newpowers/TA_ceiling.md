# TA ceiling: density route with the marked HIGH leaf (K = 8), floors 3/5 ... 1/2, role split, widened transport box

Date 2026-10-29. Python only (no `lake`/`lean`), nothing committed or pushed. Resumes the interrupted study in `research/newpowers/ta/`
(scripts, `results/e2_*.json`, `logs/`; section 8). Bar = 0.8739058, PR 86 = 0.8739558. "gap" = theta* - bar in units of 1e-6 (negative = clears the bar).
Tags: **[X]** exact rational arithmetic, **[F]** float, **[XF]** exact computation on float-generated inputs (faces).

## 0. Bottom line

1. **The marked gate (Lean `gainC`, K = 8) clears the bar once the floor is <= 0.59, with large margin at 0.55 and 1/2.** Best role split, box widened, discrete chain Delta L = 0.005 [XF]:

   | | floor 3/5 | floor 0.55 | floor 1/2 |
   |---|---|---|---|
   | base (native 3/4, `0.999`) | 0.873910822 (**+5.0**) | 0.873886758 (**-19.0**) | 0.873872341 (**-33.5**) |
   | + bootstrap + `0.999 -> 1` | 0.873909421 (**+3.6**) | 0.873884702 (**-21.1**) | 0.873870352 (**-35.4**) |
   | density steps (boot face -> wall) | 71-72 | 99 | 129 (PR 86: 46) |
   | ODE limit, all-on | 0.873908202 (+2.4) | 0.873883297 (-22.5) | 0.873868954 (-36.8) |

   Floor 3/5 is **short by 3.6e-6 (all-on) / 5.0e-6 (base)**; the floor at which it clears (discrete) is **0.593 all-on / 0.591 base** (0.59: -1.8e-6 / -0.6e-6; 0.58: -5.8e-6 base).
   Bootstrap and `0.999 -> 1` are worth only 1.1e-6 and 0.8e-6 (2.0e-6 together): **not needed** at floor <= 0.55. Without marks nothing below floor 0.60 helps (0.873946, +40e-6).
2. **Binding.** Chain: stops at the density wall `q_floor` (floor 1/2: `q_lower`, the edge of the Lean-proved range), in the last step with `principal` co-binding (floors 3/5, 0.55) or `high` (1/2); every earlier step is bound by `high` alone, at nu = q, class p = 1/2, facet "cap-inverse x face-plain" (section 4). Return: edge `newTop`, p -> 1/2, delta* = 0.4435 ... 0.4489, **branch C**; count face at (or next to) the chain end (wall), physical face L_P ~ 2.247 (s0 = 0.0598 = its break-even slope); at 3/5 the physical role is not binding at all. **ell needed: 0.171023 ... 0.171185** (`ell < 0.1712` suffices; the polygon floor 0.873644 is 2.3e-4 below the best theta*).
3. **Hidden dependency: PR 86's three return branches {old, C, capP} cannot certify the new faces** (fail outright at floors 0.55 and 1/2, +8.9e-5 worse at 3/5). The return must be regenerated with the six-branch set of PR 76 `FinalReturn` (old, C, capC, weakC7, P, capP; `P` is never used); `capC` and `weakC7` are both needed (section 5.5).
4. **K is saturated at 2.** K = 8 gives exactly the face-based undiluted count (B2's "idealised" model). K = 1 costs +6.1e-6 / +14.4e-6 / +21.4e-6 at 3/5 / 0.55 / 1/2. More copies cannot help (section 6.1).
5. **Q3 passes**: with the gain off the replica reproduces PR 86's chain (B at step 46 within 2.3e-6) and the exact return gives 0.8739558 (0.873955786 at h = 8051/10000), 0.873954831 with the 46/38 split (section 2).
6. **Recommendation.** Floor 0.55 (99 steps) clears the bar by 1.9-2.1e-5 without any rider and without the role split being critical (a single face still gives -1.1e-5); floor 0.58 (82 steps) is the cheapest with >= 5e-6 margin (base -5.8e-6); floor 3/5 needs one more lever of the size in section 5.1. Floor 1/2 buys 1.5e-5 more but sits at the `q_lower` wall (end face 0.0056 above the `B0 >= 22/23` range edge of `gainC`).

## 1. What was computed, and what is exact

**Gate** (`chain2.py`; 14 gates of PR 83 `Source/HybridGates.lean`, reserve eps = 1e-6 each; child cap 0.1; first-step parent cap 0.1397): `high_at_q` is replaced by

    min_{nu in [dens(v), 3/4]} [ highJ(B, L, W, u, nu) + gainC(nu, B0, L0, c0, W - u, 1 - 6u) ] >= eps,   v in [0, c - s0],

`highJ` = HybridGates.lean:62 verbatim, `dens` with 0.999 (or 1), parent face (B0, L0, c0). `gainC` (`gainc.py`) is the Lean definition (`Gain/Gain.lean`, `Source/GainC.lean`): six branch roots
`(5Q - offset)/slope`, `xiP` = least root, `gainP = (1-2p) nu S + nu (xiP - baseXi Q)`, `gainK = inf_{p in [0,1/2]}`, `gainC` = 0 outside `ParentParams` (22/23 <= B0 <= 1, 1 < L0, 0 <= c0 <= 1, nu <= 3/4), K = 8.
Checks: [X] `gainP` in Fractions equals the float code to 1e-16 (random points); [F] the inf over p (hierarchical grid, 131 points) equals a 20001-point brute force to 8e-12 on 2000 random points; the previous agent's 5-point class grid (`variants.py` `d2`) gave the same chain (s0 identical to 5 digits at 8 steps, theta* identical to 1e-8 at all six headline cells), because the binding class is p = 1/2.
The ledger reading (MARKED_LEAF.md section 5; `PriceMarked.lean`: `highTermM = highTerm - gainC`, sup over nu in [q, 3/4], monotone in the retained width) was re-read in Lean and used as stated.

**Chain** [F]: per step a pattern search over (A, D) minimises s0 (child B = B0 - s0 Delta L) subject to all gates on a 90-point cubic v-grid; nu-mode `q` (nu = dens(v) only) for generation, **re-checked** with nu in six points of [q, 3/4], 600 v-points and a finer p-search: no real violation (max s0 shortfall 8.4e-7 against the 1e-6 reserve, i.e. true margin >= 3e-7; sum shortfall*Delta L <= 2.1e-7 in B, <= 1.3e-9 in theta). A reserve of 1e-5 (PR 86 level) instead of 1e-6 moves theta* by +5.2e-8 (floor 0.55) / +6.8e-8 (floor 1/2). The minimiser is nu = q at the eight steps inspected (1, 21, 41, 63, 81, 101, 121, 129).
**ODE** [F]: dB/dL = s0(B, L) with the v = 0 gate (DOP853, rtol 1e-10), nu-range of 7 points.
**Return** [X]: Fraction Bernstein covers of `tc/` (copies of the lemmaW toolchain; reproduces PR 86's 32 rows and 240 admission certificates exactly). PR 86's constants and four edges (dm = 19/25, mMinus = 377/1000, sMinus = 3/100, numeratorCap = 3/50, physical cap 31/500, count cap = chain cap 9999/100000, reserve 1e-8),
`BoundsN` with `ell < 0.171` replaced by `ell < 0.18`, everything else kept (theta > 873/1000, h < 806/1000, y in (0.458, 0.467), `small_saving`, `floor_margin`; h = largest 1e-6-grid value allowed by `floor_margin`), **six branches**, Collet windows (Lemma W windows give the identical theta* at all six headline faces, difference 0.0e+00).
theta* bisected at 1e-9. Faces are float chain outputs rounded to 1e-10, so every theta* below is an exact value for hypothetical faces ([XF], "Ef" of lemmaW.md); the replica is optimistic by ~2e-6 in B at the end of PR 86's chain (<= 1.4e-8 in theta).
**Role split**: count face and physical face scanned independently over the chain (about 40 count and 14 physical candidates, then a joint +-3-index refinement at 1e-9).

## 2. Q3 sanity: gain switched off [X]+[F]  (`sanity_q3.py`, `logs/sanity_q3.log`)

| check | result |
|---|---|
| PR 86 declared theta 0.8739558 with its own constants (box ell<0.171, Collet windows, old/C/capP, step-46 faces) | certifiable; least theta at h = 8051/10000: **0.8739557853** (7 digits: 0.8739558); floor-coupled h: 0.873955712 |
| same with six branches and ell < 0.18 | 0.873955712 (identical) |
| role split 46/38 on PR 86's Lean faces | **0.873954831** (both return configurations) |
| replica chain (gain 0, floor 13/20, dens 0.999, boot face (0.99999, 2.5715, 0.1397)), 46 steps | B_46 = 0.9888174 vs Lean 0.9888151 (+2.3e-6); max over steps of abs(dB) 2.3e-6 and abs(ds0) 2.8e-5; `high` binds every step |
| exact return on the replica faces | single face 46: 0.873955681; split 46/38: 0.873954804; new-code run (floor 0.65, 47 steps, count = step 47): 0.873954796 |

## 3. Q1: theta* tables [XF]

Gap in units of 1e-6 (negative clears the bar). All rows: best role split, six-branch return, box ell < 0.18.

**Explicit chain, Delta L = 0.005, marked gate (K = 8)**

| setting | floor 3/5 | floor 0.55 | floor 1/2 |
|---|---|---|---|
| base | 0.8739108 (+5.0) | 0.8738868 (-19.0) | 0.8738723 (-33.5) |
| + bootstrap (kappa' = 2 theta_rec - 1, boot face (0.99999, 2.56738, 0.1397)) | 0.8739102 (+4.4) | 0.8738856 (-20.2) | 0.8738712 (-34.6) |
| + `0.999 -> 1` | 0.8739101 (+4.3) | 0.8738858 (-20.0) | 0.8738715 (-34.3) |
| all-on | 0.8739094 (+3.6) | 0.8738847 (-21.1) | 0.8738704 (-35.4) |

**ODE limit (Delta L -> 0), marked gate**

| setting | floor 3/5 | floor 0.55 | floor 1/2 |
|---|---|---|---|
| base | 0.8739094 (+3.6) | 0.8738853 (-20.5) | 0.8738710 (-34.8) |
| + bootstrap | 0.8739089 (+3.1) | 0.8738842 (-21.6) | 0.8738699 (-35.9) |
| + `0.999 -> 1` | 0.8739088 (+3.0) | 0.8738844 (-21.4) | 0.8738701 (-35.7) |
| all-on | 0.8739082 (+2.4) | 0.8738833 (-22.5) | 0.8738690 (-36.8) |

The discrete chain sits 1.2-1.5e-6 above its continuum (first-order deficit). **Gain off (PR 83 gate, same machinery)**, discrete: floor 0.65: 0.873954796 (+49.0); 3/5: 0.873946250 (+40.5); 0.55 and 1/2: 0.873946114 (+40.3); all-on 0.873944104 / 0.873944002 / 0.873944002. ODE: 0.873953523 (0.65), 0.873945041 (3/5), 0.873944990 (0.55), 0.873944922 (1/2).

**Floor scan with marks** (base / all-on; ODE | discrete):

| floor | ODE base | ODE all-on | discrete base | discrete all-on | steps |
|---|---|---|---|---|---|
| 0.65 | | | 0.873940352 (+34.6) | | 46 |
| 0.62 | | | 0.873922151 (+16.4) | | 61 |
| 0.60 | +3.6 | +2.4 | +5.0 | +3.6 | 71-72 |
| 0.59 | -1.8 | -3.1 | -0.6 | -1.8 | 76-77 |
| 0.58 | -7.1 | -8.4 | -5.8 | | 82 |
| 0.57 | -12.2 | -13.5 | -11.1 | | 88 |
| 0.56 | -17.0 | -18.4 | | | |
| 0.55 | -20.5 | -22.5 | -19.0 | -21.1 | 99 |
| 1/2 | -34.8 | -36.8 | -33.5 | -35.4 | 129 |

**Ladder (base, discrete)**: PR 86 as submitted 0.8739558 -> role split on its faces 0.873954831 (-1.0e-6) -> floor lowered, no marks 0.873946250 at 3/5, saturating at 0.873946114 (-8.7e-6; the unmarked slope reaches the count break-even 0.0857 at L = 2.19) ->
**marks**: -1.44e-5 at floor 0.65, -3.54e-5 at 3/5, -5.94e-5 at 0.55, **-7.38e-5 at 1/2** (relative to the same floor without marks) -> riders -2.0e-6.
Why the floor now pays: with marks the slope stays below 0.0857 down to L ~ 1.97 (unmarked: 0.0846 at L = 2.20, 0.121 at 1.93; marked: 0.0636 / 0.0829; B gain at L = 1.93: +0.0122; s0 ratio 0.88 at L = 2.55 -> 0.685 at 1.93).

**Role split**: floor 3/5: none (single face = split = 0.873909421; the physical role is not binding: theta* is flat for L_P in [2.22, 2.36]); floors <= 0.55: best single face is chain face 97 (L = 2.0774) with 0.873894817 (-11.0), the split gives 0.873884702 / 0.873870352: worth **1.0e-5 (0.55) and 2.4e-5 (1/2)**. A single face already clears the bar at floors <= 0.55.

## 4. Binding constraints at the optimum

| floor / setting | steps | chain end (L, B) | stopped by | count face L_C (s0) | physical face L_P (s0) | return: failing edge at theta* - 1e-9 | ell needed |
|---|---|---|---|---|---|---|---|
| 3/5 base | 72 | 2.2115, 0.983042 | `q_floor` + `principal` (last step) | 2.2165 (0.0709) | 2.3615 (plateau) | `newTop`, delta* 0.4435, p* 0.5, C | 0.171023 |
| 3/5 all-on | 71 | 2.2124, 0.983306 | same | 2.2124 (0.0820) | 2.3674 (plateau) | `newTop`, 0.4436, 0.5, C | 0.171029 |
| 0.55 base | 99 | 2.0765, 0.974027 | `q_floor` + `principal` | 2.0765 (0.0765) | 2.2465 (0.0598) | `newTop`, 0.4459, 0.5, C | 0.171120 |
| 0.55 all-on | 99 | 2.0724, 0.973804 | same | 2.0724 (0.0866) | 2.2474 (0.0598) | `newTop`, 0.4460, 0.5, C | 0.171128 |
| 1/2 base | 129 | 1.9265, 0.962328 | `q_lower` (= `q_floor`) | 1.9265 (0.0834) | 2.2515 (0.0594) | `newTop`, 0.4488, 0.5, C | 0.171177 |
| 1/2 all-on | 129 | 1.9224, 0.962072 | `q_lower`; `high` still binding | 1.9224 (0.0908) | 2.2474 (0.0598) | `newTop`, 0.4489, 0.5, C | 0.171185 |

* **Chain.** Every step is bound by `high` (fine-settings binding counts, all-on: `high` 129/129 at 1/2; 98 + 1 `principal` of 99 at 0.55; 69 + 2 `principal` of 71 at 3/5), at v ~ 4e-4 (1 % of the range), nu = q, class p = 1/2, facet 5 = (cap-inverse, face-plain): at (nu, B0, L0) = (0.6, 0.98, 2.2) the root is 0.9074 vs baseXi 0.8772, gain 0.0181. The unmarked J is -0.004 (step 1) ... -0.025 (end) and the gain covers it exactly. The gain is saturated in S (S >= 0.06-0.08), so it depends on nu only (0.0048 at L = 2.55, 0.0151 at 2.30, 0.0244 at 2.00, 0.0259 at 1.93) and hardly on the parent face.
  Last-step reserves (x - eps): floor 1/2 all-on: `q_floor` 1.7e-6, `principal` 5.7e-4, `retained_cap` 2.6e-3, `H_lower` 6.1e-2; floors 3/5 and 0.55: `principal` = 0 and `q_floor` 2e-7 ... 1e-5 (A trade-off between them makes the last step expensive, s0 = 0.082-0.09).
* **Behind the wall.** With `q_floor` and `q_lower` removed (hypothetical) the floor-1/2 chain continues 13 more steps with `high` the only binding gate (principal 2.7e-2, second_ref 0.14, retained_cap 2e-4) and then ends at (L, B) = (1.857, 0.9565) = **B0 < 22/23, the parent range of `gainC`** (q = 0.479). So the Lean-proved range qf >= 1/2 and the gain's range B0 >= 22/23 are the two walls; the floor-1/2 end face (B = 0.9621) is 0.0056 above 22/23.
* **Return.** `newTop` (d = h + 1e-10), p -> 1/2, branch C (affine count, face line); delta* rises 0.4415 (PR 86) -> 0.4489 as the count face improves. Cover at theta*: floor 1/2 `newTop` 42 leaves = C 20, old 11, capP 5, capC 3, weakC7 3 (smallest Bernstein minimum 3.9e-10 on a C leaf at delta in [0.44879, 0.44897], p in [0.49976, 0.5]); the other three edges are slack (old branch only, minima 3.7e-3 ... 8.4e-2).
  Box margins at floor 1/2 all-on: ell < 0.18 8.8e-3 (ell = 0.171185), theta > 873/1000 8.7e-4, `small_saving` 1.6e-3, y 4.1e-3 / 4.9e-3, h < 0.806 1.6e-3, `floor_margin` 1.6e-7 (by construction). The stock-constant polygon closes at theta = 0.873644 (TB report), 2.3e-4 below the best theta*; the `ell` numeral is the only box edit (TB: 3 lines, numeral-only for theta >= 0.8737917).
* **Count-face cap** needed (six branches, Collet = Lemma W windows, `cap_check.py`): 0.096-0.097 at floor 1/2, 0.092-0.095 at 0.55, 0.091-0.092 at 3/5, against 0.09999 available (slack >= 3e-3).

## 5. Q2: what closes a shortfall, and how much slack the passing cells have

### 5.1 Floor 3/5 all-on (ODE gap +2.40e-6; the discrete chain is 1.5x worse: +3.62e-6, so multiply the sizes by ~1.5). Single improvements, each alone [XF], ODE-limit sensitivities with the role split re-optimised:

| lever | sensitivity | size that closes the ODE gap | ~ discrete |
|---|---|---|---|
| **floor 3/5 -> 0.59** (no new mathematics; +5 steps) | -5.5e-6 per 0.01 | 0.595 (ODE) | **0.593** |
| count exponent R lowered everywhere in the HIGH gate (= better gain at nu = q, p = 1/2) | 2.23e-3 per unit R | **dR = 1.08e-3** (6 % of the gain 0.018-0.021) | 1.6e-3 (9 %) |
| gain scaled (needs a count theorem beyond the K -> infinity face-based count) | | x1.088 | x1.13 |
| step slope s0 | 1.02e-6 per 1 % | **-2.4 %** | -3.6 % |
| envelope rate 6 | 1.85e-6 per 0.01 | 6 -> 5.987 | 5.98 |
| native barrier / boot-face L0 (bootstrap already included, -0.0041) | 1.49e-7 per 0.001 | **-0.0163** (0.63 %) | -0.025 |
| count face B_C at the wall | -7.6e-3 per unit | **+3.1e-4** | +4.7e-4 |
| physical face B_P | 0 (not binding; theta* flat) | none | none |
| numerator cap / physical cap (capP 0.07) | | theta -3.3e-7 at most | |
| copies K | 0 beyond K = 2 | none | none |
| finer chain Delta L = 0.0025 (142 steps) | | theta -5.9e-7 (ODE limit -1.2e-6) | not enough |
| return exponent E (exact) | +0.281 per unit | **dE = -8.5e-6** | -1.3e-5 |
| return count R on non-old branches | +0.170 per unit | **-1.4e-5** | -2.1e-5 |
| capacity C_N at the new edges | -0.0279 per unit | **+8.6e-5** | +1.3e-4 |

The cheapest by far is the floor (already a Lean theorem on [1/2, 3/4]); the cheapest *new* one is the count face (B_C + 3e-4 .. 5e-4, e.g. a refined last step or cap/geometry gain at the count role) or 0.6 %-1 % of the native barrier. Sizes in the last column are scaled, not recomputed (the discrete gap is first-order Delta L).

### 5.2 Slack of the passing cells (ODE, all-on; the lever may worsen by this much before the bar is lost)

| lever | floor 0.55 (gap -22.5e-6) | floor 1/2 (gap -36.8e-6) |
|---|---|---|
| gain needed (fraction of the Lean gain) | **0.684** | **0.665** |
| count exponent R everywhere may worsen by | 4.3e-3 (4.26e-3 per unit) | 5.2e-3 (6.79e-3 per unit) |
| step slope s0 may be larger by | 10.1 % | 12.5 % |
| envelope rate 6 may rise to | 6.098 | 6.165 |
| boot-face L0 may be higher by | 0.089 (3.5 %) | 0.151 (5.9 %) |
| count face B_C may be lower by | 3.5e-3 (slope 6.4e-3) | 4.4e-3 (7.3e-3) |
| physical face B_P | at most 5.8e-7 to gain (saturates at +1e-4: the clip s_P d binds) | lowering by 4.4e-3 tolerated (slope 8.4e-3) |
| return exponent E may worsen by | 1.07e-4 | 1.77e-4 |
| return count R may worsen by | 1.8e-4 | 2.9e-4 |
| capacity C_N may fall by | 9.6e-4 | 1.6e-3 |
| gate reserve 1e-5 instead of 1e-6 (discrete, base: cost in theta) | +5.2e-8 | +6.8e-8 |

### 5.3 Reading
At floor 3/5 the gate is count-limited: the physical role is slack and only count-face quantities matter (R, s0, B_C, native barrier). From about 0.57 downwards both roles bind (V-shaped P scan, minimum at L_P = 2.247 where s0 = 0.0598 is the physical break-even slope; ODE optimum L_P = 2.308 at floors 0.58-0.60, 2.278 at 0.57, 2.248 at <= 0.56) and the count face sits at the wall.

### 5.4 Smaller items
* Finer chain (floor 3/5, all-on): Delta L = 0.0025 (142 steps) gives 0.873908833 (+3.03e-6) against 0.873909421 (+3.62e-6) at Delta L = 0.005 and +2.40e-6 in the ODE limit: only 0.6e-6 of the 1.2e-6 discretisation loss, not enough to close 3/5.
* Declaration: 7-digit values that pass: floor 3/5 all-on 0.8739095, 0.55 all-on 0.8738848 / base 0.8738868, 1/2 all-on 0.8738704.

### 5.5 Return branches needed (`branch_sets.py`, Collet windows, box ell < 0.18)

| faces of | {old, C, capP} (PR 86) | + capC | + weakC7 | + capC, weakC7 | six |
|---|---|---|---|---|---|
| 3/5 all-on | fails | fails | 0.873921205 | 0.873909421 | 0.873909421 |
| 3/5 base | 0.873999393 | 0.873999393 | 0.873910822 | 0.873910822 | 0.873910822 |
| 0.55 (both) | fails | fails | fails | = six | 0.873884702 / 0.873886758 |
| 1/2 (both) | fails | fails | fails | = six | 0.873870352 / 0.873872341 |

`P` is never needed. These are the branches of PR 76 `FinalReturn` (`.capC`, `.weakC7`), generated by the same `gen_return_lean.py`; PR 86's return has only three.

## 6. Questions asked in the task, short answers

### 6.1 "More copies K?"
`gainK` at the binding is the facet (cap-inverse, face-plain) at p = 1/2, which contains neither K nor S: K = 8 equals K = infinity. On the K = 8 chain the gate with K = 1.5 fails at 52 of 129 steps, with K = 1 at all (-5.2e-3), with K = 2, 3, 8, 50 the minimum margin is the same (1.000e-6 = eps at four digits). Re-optimised K = 1 chains: +9.7 / -6.7 / -14.1 (3/5 / 0.55 / 1/2, all-on), i.e. +6.1 / +14.4 / +21.4 e-6 worse than K >= 2.

### 6.2 "A better count exponent at the binding"
R(nu = q, p = 1/2, s0) along the floor-1/2 chain: L = 2.56: rho = 0.2885 -> R = 0.2844; 2.26: 0.4496 -> 0.4333; 2.02: 0.5472 -> 0.5234; 1.96: 0.5686 -> 0.5435 (gain 0.0042 ... 0.0251). Black-box / limited-supply variants of MARKED_LEAF reach rho - R = 0.0003-0.0078 (a) and 0.0025-0.0164 (b+) over the same range; the Lean K = 8 gain equals the face-based undiluted count (`cu`) to 5 digits. Any further R gain is a new count theorem, priced by the dR rows above.

## 7. What must exist for these numbers to be real (Lean side, not checked here)
1. Marked step certificates (one `HybridGates`-marked file per step: 71 / 99 / 129 vs PR 86's 46), the new gate being six facet families x p in [0, 1/2] x v; the binding family is facet 5 at p = 1/2, nu = q. Floor 1/2 uses the full proved range (`q_lower` = `q_floor`).
2. Six-branch return (capC, weakC7) for the new count face + the new physical face (two `GlobalSource` constants), numerals `ell < 0.1712` in `ReturnD/TransportGeometry` (fork of `ReturnD`).
3. `gainC` parent range: all faces keep B0 >= 22/23 (end face 0.962 at floor 1/2).
4. Riders (optional, worth 2e-6): `kappa'`-priced native step; `0.999 -> 1` (drop `low_per_excess_width` strict positivity).

## 8. Files (`research/newpowers/ta/`)
`gainc.py` (Lean gain, exact + float), `chain2.py` (marked-gate greedy chain), `ode2.py`, `run2.py` / `batch3.py` (discrete scenarios, `results/e2_g*`), `run_ode2.py` / `batch4.py` (ODE, `results/e2_ode2_*`), `verify2.py` (fine re-check), `diag2.py` / `diag_all2.py` (return binding), `levers2.py`, `levers2c.py` (pricing), `branch_sets.py`, `windows_check.py`, `cap_check.py`, `numcap_scan.py`, `single_face.py`, `sanity_q3.py`, `binding_R.py`, `ode_table.py`, `tc/` (exact return toolchain), `logs/`.

