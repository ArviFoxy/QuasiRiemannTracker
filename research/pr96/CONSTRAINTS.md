# Two-slot probe at GT: constraint list, binding chain, and what the new theorems buy

Source: /home/user/ext/zero-free-1049-1250 (paper/chapters/*.tex, agents/*).  Read-only; nothing outside this folder written; no lake/lean.
Tags: **[Q]** quoted from the paper/its scripts; **[D]** derived by me (script named); **[U]** unverified / extrapolation.
Notation: Bm = 1049/1250 = 0.8392; ΔB = B − Bm; "closes B≥" = value of B at which the row's margin reaches 0 at GT, using the paper's own
rule that every P-side margin moves by 2ΔB and every Poisson-side slack by ΔB (checked on the two certificates at 0.8392 / 0.8291).
Excess normalisation of Ch. 6/7: an e-tail cell with excess E (at B = 4/5) closes iff 2(B − 4/5) ≥ E.

Files of mine in this folder (other files here — lean_inventory.md, final_report_draft.md, decls.tsv, graph.json, idx.py, … — belong to another agent):
ladder2.py (trivial branch + charts, any block, any rung), cross.py (crossings), cells.py (single-prime non-core cells), exact_L0.py (exact rationals),
table.py (margins), np_direct.py (non-polar direct chart), ghost.py, layered.py, q1scan.py, w389/ (copy of the repo's referee ladder).

## 0. Geometry GT [Q]
lx1=ly1=2540749/4e6=.63518725, lx2=.11114401, ly2=1.05028889, θ=.073; q1=1.2703745, q2=1.1614329, n=q1+q2−1=1.4318074, h=2q1−1=1.540749,
t2=ly2−lx2=.93914488, D20=1/2+q1/12+q2/6=.79943669 (s=B−D20=.0397633), D1=1/2+h1/3+h2/6=1−lx1/3−lx2/6=.7697469.
κ0=7q1/6−14/15=.54877025, C0=4q1/3−16/15=.627166, x*=q1/2−2/5=.23518725, E_bind=κ0/7=q1/6−2/15=.07839575, closure 11/15+q1/12=.839197875.

## 1. Every condition (GT, B = Bm) with margin, B-scaling and dependencies
Dependency code: C = classical (de Faveri, Heath-Brown, Goldmakher–Louvel, Kazhdan–Patterson FE, Poisson, Hecke); E = elementary, proved in the paper from C only
(Schur test, twisted Lindelöf on average, AFE, Montgomery detector); N = NEW theorem of the paper; I = imported from OpenAI 30 Sep 2026 (7/8).

### 1A. Poisson side (Prop poisson-rows / Lemma zls; certs frame-rows, det-classrows, frame-rows-8291) [Q]
Rows, for classes S={1},{2},{1,2} (types: one type; class {1,2}: D, N1, N2), with E_S(x)=Σ_{i∈S}[h_i(x+c_i) − x·ly_i], c1=1/3, c2=1/6,
Γ_τ(x)=E_S(x) − Σ h_i(1−r_{τ,i}(x)), σ_m=11/20:
 (G) E_S(σ_m) < B − σ_m.  Slacks at Bm: {2} .2298454, {1} .3163017, {1,2} .2569472.  Slope 1 in B.
 (I) Γ_τ(σ) ≤ (B−σ)_+ on [σ_m,1];  (T) Γ_τ(σ) ≤ −η_B on [B,1], η_B ≥ 349137/3274904 = .1066098.
 Copy-sieve (ϑ=.073) versions Γ_τ + ϑκ_j, κ1=3x+3r_{τ,2}(x)−7/2, κ2=3x−2, E_S(σ_m)+ϑ(3σ_m−1/2): min slacks κ1: .145895, .144959 ({2}); .172997, **.039201 (type D)**, .106118, .198730 ({1,2});
 κ2: .221043, .167003, .215680, .289428.  Type-D κ1 slack was .029101 at B=.8291, i.e. exactly 1:1 in B → closes B ≳ .8000 [D].
 Extraction: needs σ0 ≥ 2/3+2d (d=1/100); δ_ex = d·h1 = .0036481; worst monomial exponent −1.769 <−1.   Principal signal c'_S>0.
 Inputs: de Faveri zero density (g3 = BGL's, g6 only dF), pair-family sieve Lemma pair-sieve (dF sextic+cubic), Lemma density-from-ls.  → C/E.  Holds for B ≥ .8291 (certified) and, by slack accounting, ≳ .800 [D].
### 1B. Identities
 D20 + s = B (margin 0 by definition of s; requires s ≥ 0, i.e. B ≥ D20 = .79944).  True-size row D1 ≤ B: margin B−D1 = C(B) = 13890617/2e8 = .0694531 (closes .76975).  No theorem.
 Split of the cubic slot (Thm vac-split): t2/2 = q2/2−lx2 = .4695724 > 0, t2 = .9391449 > 0.  B-free.  Voronoi decomposition of the cubic Kubota series: C (KP FE) + local S-inversion (E).
### 1C. Hypothesis (D), remainder (Ch. 4, Thm d-all) — margins B-free except the last [Q]
 completeness ly2−1 .0502889; special columns lx1−1/3−2lx2/3 .2277579; column layers (sixth) 1/3−q1/6−(1−lx1)/5 .0486417, (cube) .0971160; variable layers (2/3)(q1−1) .1802497, (q2−1)/3 .0538110;
 energy (2/3)ly2−q2/2 .1194761, t2/3 .3130483; **all blocks .1109244 + 2ΔB (closes B ≥ .7837)**.  Inputs: dF (dF=1/3+5q1/6 is load-bearing vs BGL: loses 1/3−q1/6=.1216), HB, Poisson, masks.  All C/E.
 [D] Remark d0-rel: plain Cauchy–Schwarz already closes (D) for B > 1 − t2/6 = .84348, so at B=.86/.87 the special-column / complete-sum / PV machinery of §4.3–4.5 is not needed (Lemma a-layers, ml, slot1-energy, vac-split, vac-energy still are).
### 1D. Hypothesis (P) (Table tab:links) [Q], closing B at GT [D]
 | row | margin Bm | at .87 | at .86 | closes B≥ | theorems |
 | non-polar vanishing n−q1=q2−1; q1−1 | .1614329; .2703745 | – | – | B-free | N: thm:nonpolar-vanishing (+tree form, normaliser levels) |
 | non-polar layers (5q1+2)/6 form | .1193553 | .1810 | .1610 | .7795 | N structure (min of direct/image chart); inputs dF+HB; **uses vanishing when image empty (Step 2)** |
 | direct-tree window | .0880632 | (formula not located in text) | | | N (dt_τ, Prop dt-cuts) |
 | cube-full cells | absorbed | | | | N: thm:cube-full (cube periodicity of Patterson residues, KGD) |
 | polar cells e=1 (MAIN, JDUAL, F3) | .0703788 | .1320 | .1120 | .8040 (=4/3−5q1/12) | C/E only: (S1)+(PF) |
 | copy & tail-copy | .0348037 | .0964 | .0764 | .8218 | I: needs zero-free half-plane θ0 for 4 L(s,ψ) mod 12; θ0 ≤ 7/8+margin/2 = .8924 (Bm), **.9232 (B=.87), .9132 (B=.86)** → 7/8 suffices; classical (no power saving) does not |
 | square-factor tail, every block | 17/4e6 | .0616 (full design) | .0416 | .8392 | N: etail (see §2) |
 | other polar tails (ghost, square, mixed, JDUAL) | ≥ 17/4e6 | | | | N: thm:gt, st, mt, domination |
 | non-core polar cells | ≥ 17/4e6 | | | | N: thm:tt, cc, tcc, g2-mix, gh, strips …; heavy certificates R1,R3,R4,R5,R10,R11 (rung L5) |

## 2. Binding chain: square-factor tail (Thm etail, Ch. 6) [Q formulas, D numbers]
Cell: need(B;dn)=need0+2(B−4/5)−(2/3)dn+2(1−ε0)dn, ε0=1/2.  Top block dn=0: k=1, ℓ0=1−q1/2, pref0=2h−y1−1.
**Voronoi (K-)chart, DPX:** T_K=4x+A+max(y1,13x/6)+max(A,R_e)+R_e, A=q1−2x, R_e=h−2x ⇒ excess κ0−2x on [x*,6y1/13] (then κ0−y1+x/6 ≤ .0194).  Uses KGD (root number cancels the probe's Gauss sum), N1, sq-class, GL quadratic sieve, **Thm dpx** (X1 mean value on e²a′: Q^ε A′ max(Y,E^{13/6})).
 [D] same chart with de Faveri's slot-1 factor (tK♯): excess κ0 − (5/3)x near the crossing  (DPX gains x/3).
**Trivial branch:** T(c,x)−need = KC − 10x/3 − c/3 + S(c,x) + Λ(c,x), c∈[0,ℓ0+2x], KC=pref0+y1+1+ℓ0/3−need0.  The sup is at c=ℓ0+2x.  With S at its floor c+x (GS1 = Cor GS1) and Λ at its floor c+2x:
 excess = 3x − C0 (C0=need0−pref0−y1−1−2ℓ0=4q1/3−16/15 is purely geometric).
**Role of the block large sieve:** Λ ≤ R1 = k−(c+x)+Ω, Ω ⊇ Dual_4 = constant of {χ_{l e³}} on squarefree vectors, floor Y+x (Y=2(c+x)−k).  Only Thm block-ls (+ r1ext, GS1 on its layers) puts Ω on the floor on the corner cells (m=0 exactly, Lemma omega-lp (iii)).  Otherwise Λ = floor + μ and the line is 3x − C0 + μ_S + μ_Λ.
[D] at the corner x*, c=ℓ0+2x*=.8352, Y+x*=1.37594: dual bound PF-only 1.46421 (m=.0883), min(PF,GS1) 1.42501 (m=.0491, layered version identical), block LS 1.37594 (m=0).  μ_Λ at x*: PF option = 11/10 − 5q1/6 = .0414 (L1/L3), JLT-option larger.

### 2.1 Ladder at GT, top block, main cell (excess E; closure B = 4/5+E/2) [D; the DPX column of L0,L1,L3,L5 = repo script w389_ladder.py re-run (identical to my code to 7 digits)]
Rungs: L0 S∈{S1=x+D6(c,(c+x)/2), S2=c+D3(x,(c+x)/2)}, Λ∈{PF=min(x+D6(c,k),c+D3(x,k)), JLT (Schur/Poisson)}  [de Faveri + elementary only];
 L1 = L0 + S3 (GS1 ← thm:D6SF/thm:R2); L2 = L0 + R1 with dual by PF only (= L0: useless); L3 = L1 + R1 (thm:r1ext) with dual min(PF,GS1); L5 = L3 + block LS (paper).
 | rung | K = DPX: x_c, E, B | K = dF (no thm:dpx): x_c, E, B | no functional-equation chart (trivial+tA) | trivial only (x=q1/2) |
 | L0 | .20881, .131141, **.865571** | .23432, .158229, .879115 | .322 → B .9608 | .8095 |
 | L1 | .21968, .109412, **.854706** | .25106, .130334, .865167 | .315 → .9575 | .7262 |
 | L3 | .22428, .100206, .850103 | .25106, .130334, .865167 | .315 | .7262 |
 | L5 | .23519, .078396, **.839198** (= paper) | .25199, .128793, .864397 | .315 | .7262 |
 L0 without JLT (PF only): DPX .135260 → .867630.  Closed forms (exact, checked in rationals, exact_L0.py): L0+DPX E=(23/174)q1−16/435 (B=200812409/232000000), crossing x=(15q1−13)/29 on the JLT line (17/6)x+1/6−C0;
 L0+tK: PF line (5/6)x+5/6+KC+ℓ0 = κ0−(5/3)x, x=.234325; L1: E≈83/120−11q1/24 (PF line (2/3)x+37/30−q1, x=(13/16)(q1−1)).
 At x*: trivial excess L0 .15895, L1=L3 .11975, L5 .07840 (=3x*−C0).
 Marginal cost of removing a theorem from the full design: −blockLS +.0109; −blockLS−r1ext(L1) +.0155; −GS1 also (L0) +.0264; −thm:dpx alone (L5+tK) +.0252; −dpx−GS1…(L0+tK) +.0399; no FE chart ≥ +.12.
 Patterson part by plain Cauchy–Schwarz + large sieves (Lemma ml, a-layers; E_CS=dF+HB−1−n=1−q1/6−q2/3): requires B ≥ D20+E_CS/2 = **1 exactly** (identity in q1,q2).

### 2.2 Other places in the e-tail checked at reduced rungs [D, float, not certificates]
 * non-coprime pieces (gk,δ): strictly below the main cell at the top block for L0/L1 (e.g. L0 x=.2088: piece −.028 vs main .131).
 * other blocks: crossing excess falls ≈1.5 per unit dn; L0 at dn=.1 already −.016.  Top block is the unique binding block for every rung.
 * single-prime non-core cells, sub mode, 17 types, L∈[.002,.2], dn∈{0..1.2}, rungs L0/L1, charts with/without DPX: all ≤ core crossing excess (max → core as L→0), corr mode (0,3),(4,1),(6,0),(0,6) likewise.
 * ghost layers of the core (Thm gt: pieces (ℓ+g,tw+g,pref−2g), primal charts −2g): L0 sup decreases from .1308 (g=0) to .087 (g=.04).  Square/mixed: dominated (Lemma domination, rung-free).
 * (2,0) stratum: Thm cc / tcc (+ Prop routes) merge a (2,0) prime p into the square-factor variable (e'=pe), so the stratum is bounded by the host's e-tail at x'=x+L.  Paper [Q]: priced per prime by Thm tt the bare (2,0) cell reaches "about .1329 near L+x≈.21", i.e. would close only at ≈ .8664; "the identity is load-bearing".
   [D] my float model of that cell (type (2,0), sub mode): max .13518 at L=.2067, x=0 (DPX line meets the trivial branch), identical for L0, L1, L5 ⇒ B ≈ .8676 (0.002 above the paper's figure, unexplained [U]).
   Consequence: at B=.87 (E ≤ .14) per-prime pricing of the bare stratum would still close (margin ≈ .005), at B=.86 (E ≤ .12) it does not ⇒ thm:cc/tcc (and the route-(B) ghost bounds) are needed at .86.
 * Sound-box confirmation of the main-cell trivial branch using the repo's own box machinery (w406_tail_cert.certify_xbox, R1 and floor mode switched off; GS1 also off for L0; copy in cert/l1_cert.py) [D]:
   L0: excess ≤ .13125 on x∈[0,.2088], dn=0 and dn=.01 — CERTIFIED;  L1: ≤ .1095 on x∈[0,.2197], dn=0, .02 — CERTIFIED; negative controls (targets .1300 / .1085) fail at x≈.209 / .219 as they must.
   With the exact K-lines (κ0−2x) this gives, soundly for the top-block main cell: L0+DPX E ≤ .1313 (B ≤ .86565), L1+DPX E ≤ .1095 (B ≤ .85475).
   Crossing excess vs dn (float): L0+DPX .1311 (dn=0), .1168 (.01), .0593 (.05), −.013 (.1); L1+DPX .1094, .1022, .0460, −.024; the dF-chart variants decay likewise ⇒ dn=0 is the binding block.
 * NOT re-done [U]: multi-prime configurations, hosted (2,0) strata with ghosts (Thm gh, R5 search of 520M leaves), high types, strips certificates; they are tied to the L5 option set but all have excess →core as masses→0.

## 3. Non-polar part [D with quoted formulas]
Thm nonpolar-layers: min(direct,image) ≤ G_m=D6(q1−2a−γ,C0)+φ(min(q2−γ−2δ,(C0+γ)/2),C0)−(n+2s)−2(1−ε0)dn+a/3, C0=1−δ+dn, max at the origin: (5q1+2)/6−n−2s = −.040955−2(B−4/5).
 At the origin the minimum is the **image chart** and the image is EMPTY (Λ=q1−n+dn=dn−(q2−1)<0 for dn<n−q1=.1614): that is thm:nonpolar-vanishing (the proof of the uniform bound, Step 2, invokes it).  The uniform bound is not an independent classical estimate.
 Direct chart only (Thm tree-bound + Lemma short = dF + HB; excess D6(q1,1+dn)+φ(q2,1+dn)−(n+2s)−dn):
 | B | dn=0 | dn=.1 | dn=.1614 | closes (≤0) only for dn ≥ |
 | .8392 | +.3754 | +.2421 | +.1602 | .373 |
 | .87 | +.3138 | +.1805 | +.0986 | .260 |
 | .86 | +.3338 | +.2005 | +.1186 | .290 |
 | .85 | +.3538 | | | .330 |
 With the image chart (uniform bound) the same cell has excess −.181 (B=.87), −.161 (B=.86).  Direct-only needs B ≥ 1.027 at dn=0.  So the vanishing theorem is indispensable at 0.86/0.87; the "uniform bound alone" is not available without it for dn<.1614 (core), and for layers/sub-kernels with Λ<0.

## 4. What is needed for B = .87 and .86 (GT) [D unless stated]
Thresholds: B=.87 ⇒ E ≤ .14; B=.86 ⇒ E ≤ .12; B=.8733 ⇒ E ≤ .1466.
 * Fully classical (L0 + tK): E=.1582 ⇒ B=.8791 > .8733 (and > .87396): NOT reachable.  No FE chart: B ≥ .96.  Plain CS on the Patterson part: B=1.
 * B=.87: needs the K-chart infrastructure (KGD/N1/sq-class) AND at least one of {thm:dpx [L0+DPX .8656], thm:D6SF→R2→GS1 [L1+tK .8652]}; thm:block-ls and thm:r1ext are NOT needed (nor, in (D), the special-column machinery).
 * B=.86: needs thm:dpx AND GS1 (L1+DPX .8547, margin .0106) AND the (2,0) merging identity thm:cc/tcc (per-prime pricing .8664–.8676 > .86); tK-based charts fail even with block LS (.8644); L0+DPX .8656 fails.  thm:block-ls, thm:r1ext still not needed.
 * Always needed (no classical substitute found in the design): nonpolar-vanishing (+tree form), the FE/K-chart, cube-full + layer/transplant calculus (gt, st, mt) + non-core cell calculus (tt, strips, g2-mix) (structure; rung-free), COPY via a zero-free region ≤ .92.
 * What block-LS + r1ext + (GS1 in dual) buy: .8547 → .8392 (the whole gap between the L1 rung and the headline).
Confidence: high (≥90%) for §2.1 numbers (my code reproduces E_bind, x* and the repo ladder; exact rational check for L0); ~75% that no other cell binds at L0/L1 (pieces, 17 single-prime types, ghosts, other blocks checked);
 low for multi-prime/(2,0)-ghost families and for any re-tuned geometry (q1 scan: e-tail-only closure is non-monotone in q1, e.g. L0+DPX .8576 at q1=1.15 vs .8656 at GT, other rows not re-checked) [U].

## 5. Remarks and reproduction
 * BGL instead of de Faveri in (D) [Q Remark after Thm d-all; D arithmetic]: slot-1 exponent 2(1+q1)/3 is larger by 1/3−q1/6 = .1216, (D) margin .1109+2ΔB−.1216 ⇒ (D) closes only for B ≥ .8446 (fine at .86/.87).
 * Margins at the target exponents (slack = E_target − E_rung): B=.87 (E ≤ .14): L0+DPX .0089, L1+tK .0097; B=.86 (E ≤ .12): L1+DPX .0106; B=.8733 (E ≤ .1466): L0+tK fails (.1582).
 * Per-prime bare (2,0) cell: .1352 (mine) / ≈.1329 (paper) ≤ .14 ⇒ at B=.87 thm:cc is not needed for the bare stratum; multi-prime/hosted (2,0) strata and their ghosts [U].
 * Geometry is GT throughout.  e-tail-only scan in q1 (q1scan.py): closures are non-monotone in q1 (e.g. L0+DPX: .8576 at q1=1.15, .8609 at 1.20, .8656 at GT, .8532 at 1.35; L5 at q1=1.10 gives .859, not 11/15+q1/12), because the "floor" is only a lower bound inside the GT region;
   MAIN needs B ≥ 4/3−5q1/12 (decreasing in q1) and COPY ≥ 4/5+((7/48)q1−17/120)/2 (increasing).  Re-tuning is therefore not a free lunch and no other row was re-certified [U].
 * Reproduction (python3 -I; floats unless stated): ladder2.py (library), cross.py L0,L1,L3,L5 (crossings), exact_L0.py (Fractions), cells_scan.py L0|L1 0.0 [dpx|nodpx] (single-prime sub cells), cells_scan2.py (corr), cells_blocks.py, ghost.py, multi.py (random 2–3 prime),
   twozero*.py ((2,0) cell), np_direct.py (non-polar direct chart), table.py (margins), cert/l1_cert.py L0|L1 TARGET XMAX DN (repo box machinery; negative controls in the log), w389/w389_ladder.py ladder (≈6 min).
