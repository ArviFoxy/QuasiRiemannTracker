# Lemma W on the PR 86 return, chain re-optimisation, and the distance to the 0.8739358 bar

Date 2026-10-28. Python only (no `lake`/`lean`, nothing committed, nothing under `research/` edited). All scripts and logs are in
`$SCRATCH/analysis/lemmaW/` (`tc/` = scripts and copies of our generator modules, `logs/` = outputs; short key below).

Conventions. `bar` = 0.8739358 (coordinator's target). `gap` = θ* − bar (positive = still missing). "Collet-structure" = the PR 83/86 return
(`Return/Formulas.lean`: windows `[mMinus, min(11/25, naturalM, …)]`, window caps = face caps, 3 branches) with its constants; "Lemma W" = our
`QRH_WINDOWS=lemmaW` admissions (`cert_return.admission_polys_W`: no lower plain window, caps = face caps, crossover join), with all six of our branches
`old, C, Ccap, C-7, P, Pcap` (a superset of PR 86's `old, C, capP`).
**Exact** = rational faces from the Lean chain files and an exact Bernstein cover (Fractions), θ* bisected at 1e-9. **Ef** = same exact cover, but on faces that
are float outputs of the ODE or the greedy step optimiser (hypothetical faces: nobody has certified those steps). **M** = numerical derivative/model.
θ* is always the *floor-coupled* optimum: h is taken on the 1e-6 grid at the largest value that BoundsN.`floor_margin` allows (see §1.4).

---------------------------------------------------------------------------------------------------------------------------------

## 0. Bottom line

1. **Q1 reproduced exactly.** Our generator, with PR 86's constants, gives the same Bernstein minimum `m` as PR 86 for **all 32 certified rows and all 240
   admission-guard certificates (exact rational equality)**. θ* = 0.873955786 at PR 86's h = 8051/10000 (0.8739558 on the 1e-7 grid, `8739557` fails on `newTop`),
   0.873955712 at the largest h the transport box allows. PR 86 is the least 7-digit θ for its faces.
2. **Lemma W gives exactly 0 on PR 86** (θ* 0.873955712 = 0.873955712 to 1e-9), for every h, every branch set, every chain face k = 0…46, the whole ODE frontier down to
   L = 2.14, and the lowered-floor chain. Reason: PR 83/86's constants (window caps = face caps, mMinus 0.377, sMinus 3/100) *are* Lemma W's three relaxations in
   practice. On our flat faces the same constants alone reproduce Lemma W to the digit (0.8741356 both; ramp faces 0.8740728 both).
3. **The economic stopping point does not move**; best configuration on the real PR 86 chain is the role split (count = step 46, physical = step 38):
   θ* = 0.873954831 (Collet = Lemma W), 0.8739549 as a 7-digit declaration (−9e-7 vs PR 86). **gap to bar +1.90e-5.**
4. **Lowered density floor (q ≥ 0.60), Lemma W, best role split: θ* = 0.873946275 (greedy ΔL = 0.005 chain, count step 73 at L = 2.2065, physical step 38), gap +1.05e-5;
   ideal continuum (ODE faces, floor 0.59): 0.873944977, gap +9.2e-6.** Lemma W adds nothing here either. So the floor delivers 9.5e-6 (47 %) of the 2.0e-5 needed (continuum 1.08e-5, 54 %); 1.05e-5 (continuum 9.2e-6) is still missing.
5. **Closest remaining lever** (after floor + split): a new analytic improvement of ≈ 5e-5 in the return exponent E, or ≈ 8e-5 in the count R at (δ ≈ 0.443, p = 1/2), or
   ≈ 0.3 % in the inverse slot cost (c_I 2 → 1.994), or ≈ 0.2 % in the long-line slope (5/6 → 0.8313), or a ≈ 5–6 % smaller density-step slope s0. Every cheap return-side
   lever (caps, physical face/cap, numerator cap, dm, mMinus, reserve, h) is exhausted (≤ 1e-7).
6. Corrections to the earlier float model (`pr84_86.md`): it ignored `BoundsN.floor_margin` (h ≤ 0.80523), so its "exact c + h = 0.8055: −2.5e-7" is really −0.9e-7 (0 at 7 digits);
   dθ/dR is 0.13, not 0.6 (θ feeds back through ell), so "1e-5 on the count = 6e-6" is 1.3e-6.

---------------------------------------------------------------------------------------------------------------------------------

## 1. Q1 — validation of the toolchain against PR 86

### 1.1 Constants of `Return/Constants.lean` (PR 86) versus our env variables

| PR 86 constant | value | our knob | status |
|---|---|---|---|
| `c`, `theta = 1 − c` | 630221/5000000 → 4369779/5000000 | `QRH_THETA` | direct |
| `h` | 8051/10000 | `QRH_H` | direct |
| `countCB, countCL, countCap` | 9888151/10^7, 4683001/2·10^6, 9999/100000 | faces file `C` | direct; **but** Collet-window cap of C is `QRH_SC` (default 11/250), PR 86 uses the face cap → patched |
| `physicalB, physicalLambda, physicalCap` | same B, L; cap 31/500 | faces file `P` | direct; **but** `gen_return_lean.py` hard-codes the P window cap 43/1000 (`FORMULAS`, `faces`) → patched |
| `naturalK` | 9/2 | `QRH_K=9/2` | same |
| `numeratorCap` | 3/50 | `QRH_SP` (ours 29/500) | set 3/50 |
| `sMinus` | 3/100 | none (`S_MINUS=17/500` in `cert_return.py`; literal `17/500` in `FORMULAS`) | patched |
| `mMinus` | 377/1000 | none (`M_MINUS=2/5`; literal `2/5`; Lemma W sets 0) | patched |
| 11/25 (`m_+`), `naturalM = (1−K sMinus)/2` | 0.44, 0.4325 | `M_PLUS`, `M_H` | same formula, new sMinus |
| `dm` (fixed switch) | 19/25 | none: ours uses the capacity join `ds = 2y/(1+6κ·sP)` (0.7303) and QRH_DMINUS only as lower bound | structural: 4 edges (oldSmall, oldSwitch, newSwitch, newTop) instead of our 6 (+oldPeak, newKink) → patched; θ* identical (convexity in d) |
| `d0, dp = h + 1e-10` | 1/200 | same | same |
| `reserve` | 1e-8 | `rowFee`/`R0` = 1e-9 | patched; effect −2e-9 |
| transport box | `BoundsN`: 873/1000 < θ, h < 806/1000, y < 467/1000, ell < 171/1000, small_saving, floor_margin | `QRH_RELAXED=H,Y,E` + hard-coded `874/1000 < θ` in `theta_star.bounds_r` | θ lower end patched (PR 86's θ = 0.8739558 violates 874/1000: unpatched `theta_star.py` rejects the declared θ with `theta>874/1000: −4.4e-5`, and `source_C_cap` if QRH_SC equals the cap) |
| `PhysicalSchedule.dMinus_lower` | 3/4 < dm | `QRH_DMINUS` (ours 1/2) | dm = 0.76 satisfies it |
| branches | `old, C, capP` | six branches in `ALLOWED` | restricted; all six give the same θ* |

### 1.2 What the formulas diff shows (`Return/Formulas.lean` vs our `FinalReturn/ReturnFormulas.lean`, design (b))
Identical `Ebase`, `rowMargin`, `D, A, C0, Z, U, countJ/N/T, RN, MN, DJ`, guards 0–9 and 11; the differences are only (i) branch list (3 vs 6), (ii) literals 2/5, 17/500 → constants
mMinus, sMinus, (iii) `branchCap` = countCap / physicalCap vs our face caps (same idea), (iv) `reserve` vs `rowFee`, (v) our Lemma W edits (`crossM, crossW`, `lowerM` without mMinus, `upperM`, guard 10, guards 12–14).
`ReturnD`: PR 83's is ours with `BoundsN` for `BoundsR`, the physical cap as schedule field, `3/4 < dMinus` instead of our `1/2 < dMinus` (diff in `lemmaW/diff/`).

### 1.3 Results (exact)
* Row check (`tc/rows_check.py`): the Bernstein minimum `m` of every row in `Rows/Edge_*.lean` (32 rows) equals ours as a rational; tightest: row023b 5.411e-08, row023a 6.233e-08,
  row024 1.219e-07, row021 7.960e-07, row025 1.881e-06. Admission check (`tc/adm_check.py`): 16 windows × 15 guards = 240/240 exact.
* θ*: **0.873955786 at h = 8051/10000** (fine bisection, 1e-9); continuous optimum of the binding branch alone (float, C branch, newTop, p = 1/2): 0.8739557852 at δ* = 0.44173, so
  the Bernstein cover loses < 1e-9. On the 1e-7 grid: 0.8739558 = PR 86's declared value.
* Binding at θ* − 1e-7 (and at the 1e-9 scale): **edge `newTop`, p → 1/2, δ ≈ 0.4395–0.4424, branch C (affine, count face)**, count R = 0.614155 at (0.4415, 0.5); old count 0.617052, capP 0.615593.
* Variants all give 0.8739558: our 6 edges (needs `dMinus > 1/2`), all six branches, reserve 1e-9. dm in [0.7501, 0.79] identical; dm = 0.80 is worse (θ* = 0.874005836, +5.0e-5).
* h scan (exact, 1e-9; Collet-structure and Lemma W identical at every h, `logs/hscan_both.log`): h = 0.8030 → 0.873958069; 0.8035 → 0.873957346; 0.8040 → 0.873956735; 0.8045 → 0.873956236;
  0.8050 → 0.873955849; 0.8051 → 0.873955786; 0.8052 → 0.873955727; floor line h = 0.805226 → 0.873955712; h ≥ 0.80525: `floor_margin` fails. θ*(h) falls by ≈ 9e-4 per unit h.

### 1.4 The h ceiling (affects every number of the earlier float model)
`BoundsN.floor_margin` is linear in h with the h-terms cancelling in the bracket: it reads **h ≤ 9.36 θ − 7.375** (0.805226 at θ = 0.8739558; 0.805039 at the bar).
Without that field the optimum is h ≈ 0.8054 and θ* is only 7e-8 lower (0.873954762 vs 0.873954831 on the role split) — the field costs almost nothing, but the float model's h = 0.8056 is not admissible.
Other box margins at the bar (θ = 0.8739358, h = 0.80504): ell < 0.171 has 7.7e-5 left (θ ≥ 0.8739167 is the hard floor of this box), y 3.8e-3, small_saving 2.1e-3, prime_supply 1.2e-2 — no box change is needed to *reach* the bar.

---------------------------------------------------------------------------------------------------------------------------------

## 2. Q2 — Lemma W on PR 86 (the key number)

**θ*(Lemma W) = θ*(Collet-structure) = 0.873955712 (floor-coupled h) / 0.873955786 (h = 8051/10000): Δ = 0.0e+00 at 1e-9 resolution; binding unchanged; gap to bar +1.99e-5.**

Why (guards at the binding point, `tc/q2_guards.py`, `tc/bind_report.py`):

| branch at (δ, p) = (0.4415, 1/2) | crossing m* | lower window slack | upper window slack | N-tail test /J |
|---|---|---|---|---|
| C, Collet-structure (window [0.3773, 0.4325]) | 0.39416 | 0.0168 | 0.0383 | 0.0093 |
| C, Lemma W (window [0.3773, m_X = 0.4883]) | 0.39416 | 0.0168 | 0.0942 | 0.0476 |
| capP (z* = 0.062) | 0.40434 | 0.0273 (W: 0.404) | 0.0175 | 0.0107 (W 0.0491) |
| Ccap (z* = cap − 1e-7 = 0.0999), Lemma W | 0.38793 | — | **−0.0106 (inadmissible)** | 0.0468 |

The capped branch at the full cap would be better by 8.7e-4 in the count (0.613909 vs 0.614778), but it is excluded by the face line, not by a window: its crossing 0.3879 lies above
(B − Λ z*)/2 = 0.3773, i.e. in the region where the face width is below z*. Lemma W keeps that condition, so it cannot admit it. The affine C branch uses the face line exactly; no extra freedom is left.
Raising the physical cap of capP (0.062 … 0.09999) or the count cap above 0.0999 (up to 0.18): 0 (exact, both window systems). Adding every branch (six): 0.

**Where Lemma W's content went (attribution ladder, PR 86 faces, `tc/ladder.py`, exact):**

| step | θ* |
|---|---|
| L0 our Collet constants: m_- = 2/5, s_- = 17/500, window caps 29/500 and 43/1000 | 0.874256814 |
| L1 + s_- = 3/100 | 0.874256814 (neutral) |
| L2 + m_- = 377/1000 | 0.874231359 (−2.5e-5) |
| L3 + window caps = face caps (0.09999, 31/500) | 0.873955711 (**−2.76e-4**) |
| L4 + PR 86 edges, 3 branches, reserve 1e-8 | 0.873955712 |
| L3 with Lemma W windows | 0.873955711 |
| L0 with Lemma W windows (caps still 29/500, 43/1000) | 0.874231359 (= L2) |

Cross-check on our own flat faces (`tc/xcheck_ours.py`, reproduces `return-transfer/REPORT.md` to the digit): `faces_k92`, caps 3/40: Collet 0.8742701; Lemma W (caps − 1e-4) 0.8741364 (report 0.8741364);
Lemma W (face caps) 0.8741356; **Collet structure with PR 83/86's constants only: 0.8741356**. Ramp faces (design b): Lemma W 0.8740728 = PR-86-constants 0.8740728.
So PR 83 captured Lemma W (the window caps = face caps, the lower m_-, and a join that is not binding). Also, mMinus is θ-neutral on PR 86's faces under an adaptive tiling (19/50, 0.379, 0.378, 0.377, 0 all give 0.873955712): PR 86's 19/50 → 377/1000 was a tiling repair.

**The one thing Lemma W still buys: a lower requirement on the count-face cap** (role split 46/38; θ* unchanged = no loss):

| count cap | Collet-structure | Lemma W |
|---|---|---|
| ≥ 0.096 | 0.873954831 | 0.873954831 |
| 0.095 / 0.094 / 0.093 | +5.7e-5 / +1.1e-4 / +1.5e-4 | 0 |
| ≤ 0.092 | fails (> 0.87404) | 0 down to 0.088 |
| 0.086 / 0.084 / 0.082 / 0.080 | fails | +9.1e-6 / +2.4e-5 / +4.6e-5 / +6.7e-5 |

Required cap along the ODE frontier (`tc/capreq.py`): Collet-structure 0.096 (L = 2.34), 0.097 (2.30), 0.098 (2.25), **0.099 (2.20, 2.15, 2.10)** against the available c = 1/10 (0.09999);
Lemma W 0.088–0.090 throughout. So on a chain continued past the wall Collet-structure sits 0.001 from failing, Lemma W has ≈ 0.01 of slack: insurance, worth 0 in θ.
Using the slack on the source side (child cap c < 1/10) does not move the frontier (greedy chain B(L) identical up to step 46 for c = 0.09/0.088/0.085); only step 47 gets cheaper (s0 0.0853 → 0.0764 at c = 0.09),
worth −2.6e-7 (c = 0.09) / −3.1e-7 (c = 0.088) on the role split, and c = 0.085 loses 1.4e-5 (below the Lemma W cap requirement). Not worth 47 regenerated step files.

---------------------------------------------------------------------------------------------------------------------------------

## 3. Q3 — chain re-optimisation (floor 13/20 as in PR 86)

### 3.1 Sensitivities of the exact θ* at the PR 86 faces (central/one-sided differences, `tc/sens2.py`, M)
| role | dθ/dB | dθ/dL | break-even chain slope s0* |
|---|---|---|---|
| count face (C branch) | −5.33e-3 | +4.57e-4 | 0.0857 |
| physical face (newCapacity at newTop) | −8.14e-3 | +4.87e-4 | 0.0598 |
| both (shared face) | −1.347e-2 | +9.44e-4 | 0.0701 |
(The physical-face derivative is one-sided if `numeratorCap` is 0.06: the clip `sP·d = 0.04831` is 1.7e-4 above the affine capacity 0.04814 at newTop, so B_P may rise by only ≈ 5e-4 before it saturates; at the chain's step 38 the margin is larger.)
Same for Collet-structure and Lemma W. dθ/dR (count lowered by R) = −0.130, dθ/dE = +0.215, dθ/dC_N = −0.0238.

### 3.2 Single face along the PR 86 chain (exact; `logs/chain_single_all.log`)
Collet = Lemma W to 1e-9 at every k. θ*: k = 0: 0.874015873; 10: 0.873995219; 20: 0.873978704; 30: 0.873966398; 38: 0.873959644; 40: 0.873958394; 43: 0.873956850; 45: 0.873956045;
**46: 0.873955712**. Marginal gain at the end 3.3e-7 per step (k = 45 → 46), consistent with `pr84_86.md`.

### 3.3 Role split on the real chain (exact; grid in `logs/`/`pairs_*.log`, separable: θ*(i, j) = f(i) + g(j) to 2e-9)
| count k_C \ physical k_P | 46 | 42 | 40 | 39 | **38** | 37 | 36 | 34 | 30 |
|---|---|---|---|---|---|---|---|---|---|
| **46** | 0.873955712 | 0.873955038 | 0.873954877 | 0.873954839 | **0.873954831** | 0.873954851 | 0.873954900 | 0.873955084 | 0.873955793 |
| 45 | 0.873956258 | | | | 0.873955379 | | | | |
| 44 | 0.873956820 | | | | 0.873955943 | | | | |
| 40 | 0.873959219 | | | | 0.873958351 | | | | |
Identical for Lemma W. Best: **(46, 38) = 0.873954831** (7-digit declaration 0.8739549, i.e. c = 1260451/10^7, h = 8052/10000 passes (largest allowed 0.805218); 0.8739548 fails), gap +1.90e-5.
Physical step 38 = G(2478297/2500000, 5953751/2500000, 1/10), count step 46 = PR 86's final face.

### 3.4 Extending the chain at floor 13/20 (Ef; `logs/ext_configs.log`, `tc/ext_configs.py`)
| configuration | faces | θ* (Collet = Lemma W) | gap |
|---|---|---|---|
| greedy ΔL = 0.005, step 47 (s0 = 0.0853) as count, step 38 physical | float | 0.873954810 | +1.90e-5 |
| ΔL = 0.0025 (92/93 steps): count k = 92 (L = 2.3415) / k = 93 (L = 2.339, s0 = 0.0716), physical k = 76 | float | 0.873954342 / 0.873954154 | +1.85e-5 / +1.84e-5 |
| ΔL = 0.00125: count k = 184 / k = 186 (L = 2.339) / k = 187 (s0 = 0.0872), physical k = 152 | float | 0.873954110 / 0.873953840 / 0.873953850 | +1.83e-5 / +1.80e-5 / +1.80e-5 |
| ODE continuum single face at L = 2.3415 / at the wall 2.33831 | ODE | 0.873954658 / 0.873954455 | +1.89e-5 / +1.87e-5 |
| ODE continuum split, count at wall, physical at L = 2.3865 | ODE | 0.873953561 | +1.76e-5 |
**Lemma W does not move the stopping point: the first-order conditions are the break-even slopes of §3.1 (count 0.0857, physical 0.0599), which Lemma W does not touch. With the floor at 13/20 the wall (L = 2.3383) comes first, so the count face stops at the wall and nothing is gained from stopping elsewhere.**

---------------------------------------------------------------------------------------------------------------------------------

## 4. Coordinator's added scenario: density floor lowered to q ≥ 0.60 (and below), Lemma W, best role split

Method: (i) greedy per-step optimiser of `analysis/model/flow.py` with the floor as parameter (`tc/flow_floor.py`, `tc/greedy_ext.py`, `tc/greedy_full.py`), started from the exact step 46 and, separately, from the boot face;
(ii) ODE `dB/dL = (B − 10/(15 − 6q))/(L − 1)`, q = 0.999 L/(6B − L); (iii) exact return on those faces, six branches, Lemma W and Collet-structure, floor-coupled h.

* The floor never binds before the wall: the floor-0.60 greedy chain is identical to the floor-0.65 chain for k ≤ 46 (ΔB ≤ 6e-10), so PR 86's 46 steps stay optimal and the extension simply continues.
  With ΔL = 0.005 it runs 28 more steps (k = 47 … 74); step 75 is infeasible (q at L = 2.1965 < 0.60). Last steps are floor-limited (min q = 0.6000 from k ≈ 62).
* **Lemma W = Collet-structure to 1e-9 at every face of the extension and of the ODE down to L = 2.14** (binding unchanged: newTop, p → 1/2, δ* ≈ 0.443–0.445, C branch, m* = 0.394, count 0.61193).

### 4.1 Discrete chain (ΔL = 0.005, floor 0.60; Ef; `logs/lowfloor_greedy.log`, `logs/floor_table.log`), physical = step 38, Lemma W
| count step k (L, B, s0) | floor needed (min q) | θ* | gap to bar |
|---|---|---|---|
| 46 (2.3415, 0.9888151, 0.0651) — PR 86 | 0.650 | 0.873954831 | +1.90e-5 |
| 47 (2.3365, 0.9884863, 0.0658) | 0.647 | 0.873954297 | +1.85e-5 |
| 51 (2.3165, 0.9871361, 0.0686) | 0.633 | 0.873952319 | +1.65e-5 |
| 55 (2.2965, 0.9857301, 0.0713) | 0.617 | 0.873950597 | +1.48e-5 |
| 59 (2.2765, 0.9842687, 0.0741) | 0.608 | 0.873949141 | +1.33e-5 |
| 63 (2.2565, 0.9827523, 0.0769) | 0.600 | 0.873947960 | +1.22e-5 |
| 69 (2.2265, 0.9803752, 0.0809) | 0.600 | 0.873946725 | +1.09e-5 |
| **73 (2.2065, 0.9787225, 0.0837)** | 0.600 | **0.873946275** | **+1.05e-5** |
| 74 (2.2015, 0.9782811, 0.0883) | 0.600 | 0.873946328 | +1.05e-5 |
Best declaration 0.8739463 (c = 1260537/10^7, h = 80513/10^5 passes; 0.8739462 fails). Single face (no split) at its best (floor 0.64, wall 2.312): 0.873953492, gap +1.77e-5 — the lowered floor only pays *with* the role split (the count role wants s0 up to 0.0857, the physical role stops at 0.0599).

### 4.2 Continuum (ODE faces; Ef; floor sweep `logs/floor_sweep.log`), count at the wall, physical ODE face at L = 2.38
| floor | wall L | B_ode | θ* split | gap | θ* single face | gap |
|---|---|---|---|---|---|---|
| 0.65 | 2.3383 | 0.98868 | 0.873953524 | +1.77e-5 | 0.873954455 | +1.87e-5 |
| 0.64 | 2.3123 | 0.98693 | 0.873950925 | +1.51e-5 | 0.873953492 | +1.77e-5 |
| 0.62 | 2.2587 | 0.98302 | 0.873946980 | +1.12e-5 | 0.873955512 | +1.97e-5 |
| 0.60 | 2.2031 | 0.97855 | 0.873945041 | +9.2e-6 | 0.873963550 | +2.8e-5 |
| **0.59** | 2.1745 | 0.97609 | **0.873944977** | **+9.2e-6** (minimum) | 0.873970154 | +3.4e-5 |
| 0.58 | 2.1455 | 0.97347 | 0.873945613 | +9.8e-6 | 0.873978684 | +4.3e-5 |
| 0.56 | 2.0857 | 0.96772 | 0.873949346 | +1.35e-5 | 0.874002230 | +6.6e-5 |
Lowering the floor below ≈ 0.59 hurts (s0 passes the count break-even 0.0857). The discrete ΔL = 0.005 chain is 1.3e-6 above the continuum (as in `pr84_86.md`: first-order deficit).

### 4.3 What would still close the remaining gap (all hypothetical, Ef/M)
Source side: scaling the density-step slope by (1 − ε) on the ODE: ε = 5 % → 0.873936387 (gap +5.9e-7, L = 2.20); 7 % → 0.873932907 (passes). **Needed ε ≈ 5.3 % in the continuum (≈ 6 % with ΔL = 0.005) and only with the floor at 0.60 or below**
(with the floor at 0.65 even ε = 10 % gives 0.873943734).
Return side, needed size to clear the bar from the lowered-floor split (gap 1.05e-5) / from the real-chain split (gap 1.90e-5); exact-cover pricing under modified formulas (`tc/levers_price.py`, `logs/levers_price.log`; the ell-box widened for pricing only):

| lever (not provable today) | slope | needed from 73/38 + floor 0.60 | needed from 46/38 + floor 0.65 |
|---|---|---|---|
| additive change of the return exponent E | +0.2143 per unit | ΔE ≈ −4.9e-5 | −8.8e-5 |
| count R lowered at the binding point | −0.1294 per unit | ΔR ≈ −8.1e-5 (0.013 % of R = 0.6119) | −1.46e-4 |
| capacity C_N at the new edges | −0.0238 per unit | ΔC ≈ +4.4e-4 (0.9 %) | +8.0e-4 |
| inverse slot cost c_I (2) | +1.79e-3 per unit (θ falls as c_I falls) | ≈ 1.9941 (−0.3 %) | 1.9896 |
| long-line slope k_L (5/6) | +5.2e-3 per unit (θ falls as k_L falls) | ≈ 0.8313 (−0.2 %) | 0.8297 |
| class fourth-moment saving η4 | −4.3e-2 per unit | ≈ 2.4e-4 | 4.4e-4 |
| selected slots save δpC instead of δpC/2 | — | −3.0e-4 (beyond the bar; saturates at the old-branch edges 0.87364) | same |
(For scale: the reports' CI = 1.9: −1.9e-4, KL = 0.80: −1.8e-4.)

---------------------------------------------------------------------------------------------------------------------------------

## 5. Q4 — further return-side levers that are now cheap (all exact, on the role split 46/38 unless noted)

| lever | result |
|---|---|
| count-face cap | useless above 0.096 (Collet) / 0.088 (Lemma W); raising to 0.12, 0.14, 0.18: 0.0. Lowering is what costs (§2). |
| physical cap (capP) 0.062 → 0.07 … 0.09999, with `numeratorCap` 0.06 | 0.0 (the capped branch is never the binder) |
| `numeratorCap` 0.0605, 0.07 (cap 0.071), 0.09 | 0.0 (clip not binding at step 38); 0.05: fails |
| physical face (step 38 instead of 46) | −8.8e-7 (§3.3); beyond that only the frontier moves |
| better physical face off the chain | dθ/dB_P = −8.14e-3, dθ/dL_P = +4.87e-4 at s0 ≥ 0.06 — already harvested |
| `dm` 0.7501 … 0.79 | 0.0 (0.80: +5.0e-5) |
| `mMinus` 0 … 0.38 (adaptive tiling) | 0.0 |
| `reserve` 1e-8 → 1e-9 | −2e-9 |
| exact c and h (floor line) | −0.9e-7 vs the submitted 0.8739558; 0 at 7 digits |
| h without the `floor_margin` field | −7e-8 (optimum h ≈ 0.8054) |
| extra count faces from the chain | 0 (count at the binding point falls monotonically along the flow) |
| smaller child cap (c = 0.088) + step 47 | −3.1e-7, needs the whole 47-step chain regenerated |
So nothing cheap remains in the return: the binder is the C branch's count at (newTop, p = 1/2, δ ≈ 0.443) given the face line and the three-moment structure.

---------------------------------------------------------------------------------------------------------------------------------

## 6. Master table (θ* in Lemma W / Collet-structure; identical in every row)

| # | configuration | θ* | binding | gap to bar | basis | Lean change beyond regenerating certificates |
|---|---|---|---|---|---|---|
| 1 | PR 86 as submitted (declared 0.8739558, h = 0.8051); exact optimum at h = 0.8051 / at the floor line | 0.873955786 / 0.873955712 | newTop, p→½, δ≈0.4415, C | +2.0e-5 | exact | none |
| 2 | 1 + Lemma W | same | same | +2.0e-5 | exact | would need `Formulas/CountWidth/CountDecode/FinalWindows` edits (~100–150 lines) for 0 gain: **do not** |
| 3 | 1 + role split 46/38 (declare 0.8739549) | 0.873954831 | same | +1.90e-5 | exact | `Return/Endpoint.lean` (two `GlobalSource` hypotheses), `Theorem.lean`, `Source/ChainK15.lean` (export step 38 and 46), `Constants` physicalB/Λ := step 38; no new analytic Lean |
| 4 | 3 + one more step at floor 13/20 (k = 47, s0 = 0.0853) | 0.873954810 | same | +1.90e-5 | Ef | +1 step file; useless |
| 5 | finer chains (ΔL 0.0025 / 0.00125), split | 0.873954154 / 0.873953840 | same | +1.84e-5 / +1.80e-5 | Ef | +46 / +138 step files |
| 6 | ODE continuum, floor 13/20, split | 0.873953561 | same | +1.76e-5 | Ef | needs a family theorem |
| 7 | floor 0.60, ΔL = 0.005, split (count 73, physical 38; declare 0.8739463) | 0.873946275 | same | **+1.05e-5** | Ef | density floor theorem (13/20 → 0.60: HybridGates `q_floor`, Sil's clip in `Density/*`, the 33/40 zero-density range), 28 new step files (k = 47 … 74), plus item 3 |
| 8 | floor 0.59, ODE continuum, split | 0.873944977 | same | **+9.2e-6** | Ef | as 7 plus a family theorem |
| 9 | 8 with the step slope s0 smaller by 5.0–5.3 % (5.0 % at L = 2.18, 5.3 % at L = 2.20) | 0.8739358 | same | 0 | Ef/M | new step theorem |
| 10 | 7 + any of ΔE −4.9e-5, ΔR −8.1e-5, ΔC +4.4e-4, c_I 1.9941, k_L 0.8313 | ≈ bar | same | 0 | exact-cover pricing | new return/count theorems |
All rows are on `Ef` or `exact` covers; binding is always `newTop`, p → 1/2, δ* = 0.4395 … 0.4453 (rises with the face), C affine branch (count 0.6142 at PR 86 → 0.6119 at step 73).

**Which lever is closest?** The lowered floor (+ split): it delivers 9.5e-6 of the 2.0e-5 needed (discrete) / 1.08e-5 (continuum); Lemma W delivers 0. Still missing: **1.05e-5 (discrete), 9.2e-6 (continuum)**. After that the cheapest
independent steps are the ones in §4.3 (a 0.01 % improvement of the count R at the critical point, 0.3 % of c_I, 0.2 % of k_L, or 5–6 % of s0).

---------------------------------------------------------------------------------------------------------------------------------

## 7. Caveats

* "Exact" = exact for the stated faces and formulas, with the Lean cover model (dyadic Bernstein cover, depth ≤ 34, strict positivity): the continuous optimum of the binding branch is 0.8739557852 vs the cover's 0.873955786.
  The earlier float model (`pr84_86.md`) agrees within 3e-7 once `floor_margin` is respected (k = 46: 0.873955555 vs 0.873955712; split: 0.873954738 vs 0.873954831; lowered-floor C@2.20: 0.873944740 vs 0.873945002).
  Independent re-run of that model's code (pointwise branches, h free, no `floor_margin`) on our faces: split 46/38 → 0.87395477 (exact without the floor field: 0.873954762); lowered floor 73/38 → 0.87394600 (exact, floor-coupled: 0.873946275).
* Faces beyond step 46 are outputs of the greedy optimiser (gate tolerance 1e-6, 300-point v-grid) or of the ODE; no step certificate exists. The authors' reserves are ≈ 1e-5, so real steps could be marginally worse (ΔB ~ 1e-7 per step, Δθ ~ 5e-10).
* Side conditions: the scalar receipts are our `cert_return.receipt` (Lemma D mode) with `BoundsN` and PR 83's `PhysicalSchedule` fields (`3/4 < dm`, `y < dm < 2y`, `dm ≤ dp`, `2 ≤ Λ_P ≤ 9/2`, `small_plain_global`, `prime_supply`, `incumbent`); at the bar every one has margin ≥ 7.7e-5 except `floor_margin` (used as the h ceiling), so none of them limits the numbers above. I found no further numeric side condition in PR 86's `FinalSchedule/Geometry/TransportInstances`.
* Lemma W's formal content (§2 proof) is not tested by Lean here; its numerical effect on PR 86 is zero, so it was not ported to PR 86's layout.
* Hypothetical levers (§4.3) are priced by modifying `cert_return` formulas as `return-transfer/levers.py` does; their admission polynomials are not re-derived.

## 8. Files (`…/analysis/lemmaW/`)
`tc/pr86.py` (PR 86 return in our exact toolchain: `Cfg`, `certifiable`, `theta_star`), `tc/best.py` (floor-coupled θ*), `tc/rows_check.py`, `tc/adm_check.py` (exact equality with PR 86's Lean),
`tc/q1_*.py`, `tc/q2_*.py`, `tc/ladder.py`, `tc/xcheck_ours.py`, `tc/cap_scan.py`, `tc/capreq.py`, `tc/chain_single.py`, `tc/chain_pairs.py`, `tc/ext_configs.py`, `tc/lowfloor_ode.py`, `tc/lowfloor_greedy.py`, `tc/floor_sweep.py`, `tc/floor_table.py`,
`tc/greedy_*.py`, `tc/flow_floor.py`, `tc/s0_scale.py`, `tc/levers_pr86.py`, `tc/levers_price.py`, `tc/cheap_levers.py`, `tc/sens2.py`, `tc/continuous_check.py`; copies of `cert_return.py`, `gen_return_lean.py`, `theta_star.py` are unmodified except the import path.
Logs in `logs/` and `lowfloor_*.log`, `ext_configs.log`, `pairs_*.log`, `chain_single_all.log`. Rerun all: `tc/run_logged.sh`.
