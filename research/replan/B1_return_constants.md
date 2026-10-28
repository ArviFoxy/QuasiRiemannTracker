# B1 — Return constants: Lean source, slack search, exact pricing (2026-10-28)

Read-only plus Python (no `lake`/`lean`, nothing committed, nothing under `research/` edited except this file).
Scratch (scripts, logs): `$SCRATCH/analysis/B1/` (`$SCRATCH` = `$SCRATCH`).
All prices use the validated exact toolchain `$SCRATCH/analysis/lemmaW/tc/` (`pr86.py`, `best.py`, `levers_pr86.py`; Lemma W six-branch set, floor-coupled h unless stated).

Path shorthand. `COL/` = `submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/` (symlinked as `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103`;
**`grep -r` does not follow that symlink, use `grep -R`**). `OAI/` = `submissions/openai-baseline/src/Submissions/openai_baseline/`.
`PR86/` = `$SCRATCH/upstream/submissions/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/`.
`paper` = `$SCRATCH/qrh_paper.txt` (OpenAI 7/8 paper text; line numbers).

Scenarios (θ* exact, bar 0.8739358):
* **A** = lowered floor 0.60, count face step 73, physical face step 38: θ* = 0.873946275, gap **+1.047e-5**.
* **B** = PR 86 chain, role split 46/38: θ* = 0.873954831, gap **+1.903e-5**.

---------------------------------------------------------------------------------------------------------------------------------

## 0. Verdict

1. **No lever can be moved by the needed amount with the current library, with a standard argument, or with a stronger variant already proved.** I found no slack of the `33/40` kind.
   Every constant in the return is the exact output of an analytic input (not a rounded or domain-restricted version of it); the cheap algebraic variants (other Hölder orders,
   the pointwise numerator, the joint numerator, mixing count branches, `z₀`, the `p`-range, caps) are tied or strictly worse, and each is closed below by an identity or a number.
2. **Three table levers are one lever.** `C_N`, the halving `1/2 → 1/2+ε`, and the physical face `(B_P, Λ_P)` all enter `E` only through the product `δp·C/2`.
   Needed (A | B): `ε = 0.0046 | 0.0084`, i.e. `ΔC = 2εC = 4.4e-4 | 8.0e-4`, i.e. `B_P +1.30e-3 | +2.4e-3` or `Λ_P −0.91 % | −1.7 %` (§4).
   `C_N` is flat along the source chain (max at step 38, within 0.1 % for steps 30–45, 0.4 % over the whole chain 21–46), so no existing chain face gives it; only a better source frontier at the point `(2m₀, z) = (0.849, 0.0598)` can.
3. **The other levers each sit on a named barrier:** `c_I` and the probe's marked-energy slot cost `c_E` are atom 1 (P1); `k_L` is atom 2 (sextic Möbius mean value past the diagonal, `λ ≥ 0.16834`);
   `η4` is excluded by Cauchy–Schwarz (the fourth-moment diagonal is a lower bound); additive `E` has no free constant.
4. **Smallest relative demand** (not in the original table, priced here): the probe's marked-energy slot cost `c_E` `2 → 1.99904` (−0.048 %), then `c_I` −0.29 %, `k_L` −0.24 %. All three are open research problems (P1, atom 2). Plausibility of a proof in this project: ≪ 1 % each.
5. Lean cost of wiring a hypothetical improved constant into the return is small (≈ 300–700 hand-edited lines + regenerated rows, §6); the cost of the analytic theorem is unbounded. **Recommendation: put no Lean effort into return-side constants.**

---------------------------------------------------------------------------------------------------------------------------------

## 1. The exponent at the binding point (verified: closed form reproduces the exact cover)

Binding: edge `newTop` (`d = h = 0.80513`), `p = 1/2`, branch C (affine count face), `δ* = 0.44311` (scenario A). Z-exponents:

| term | value | origin (Lean) |
|---|---|---|
| `1/2` | 0.500000 | with `δ/2`: contour `Re s = a+16e`, `a=(1+δ)/2` (`COL/Record1252270103Return/GenericScalar.lean:18-19` `kernelExponent`) |
| `h/12` | +0.067094 | `13h/75 − 9d/100` at `d=h`; `=(z₀−1/6)h+(1/4−z₀)d`, `z₀=17/50`; **independent of `z₀` at `d=h`** (checked symbolically: coefficient of `z₀` is `z₀(h−d)`) |
| `−y/2` | −0.231683 | `Y^{-1/2}` normalization, `(U^(y/d))^(-1/2)` in `COL/.../PhysicalDirect/AmplitudeClass.lean:53` |
| `−ℓ/2` | −0.085441 | `(z₀−1/2)ℓ` slot normalization `GenericScalar.lean:14-16` (after `z₀` terms cancel) |
| `δ/2` | +0.221557 | contour at the row's zero |
| `δpℓ` | +0.037860 | full slot product `‖P‖ ≤ U^{qℓ/d}` (`hfull`, `AmplitudeClass.lean`; `AmplitudeHolder.lean:15`) |
| `−δpC/2` | −0.005331 | selected slots, §4 |
| `(3/4)hR` | +0.369891 | Hölder `#class^{3/4}`, `R = 0.612556` |
| **Σ** | **0.873946** | θ* = 0.873946275 (model − exact = 1.3e-8) |

`Ebase` is `PR86/Return/Formulas.lean:86-87` (= `COL/Record1252270103Return/Schedule.lean:23-24`; also `PR83` `ReturnD/Schedule.lean`); the `1/4` of `d/4` (the fourth-moment exponent `1`) is hidden inside the `9d/100`.
Exact algebra: `rowAt = 1/2 − h/6 − y/2 − ℓ/2 + z₀(h−d) + d/4 + δ/2 + δp(ℓ − C/2) + 3dR/4` (derived from `numerator_kernel_exponent`, `GenericScalar.lean:23-30`, using only `x = 1+ℓ−h`; verified numerically).
`E(δ)` is very flat at the maximum: `E(δ*±0.01) − E(δ*) = −1.5e-5`, `±0.02: −6.2e-5` — a mechanism that helps only on a δ-band must cover `a ∈ [0.7125, 0.7305]` to gain 4.9e-5.

Count at the binding point (exact lines, `duals.py`, `branches.py`): `r* = 0.748, m* = 0.3937, t* = 1.1419`; plain slot width used `z_P(m*) = 0.0867` (< cap 0.09999), inverse slot width `z_M(r*) = (1−r*)/2 = 0.126`.
Dual weights of `R` on the three lines: **I 0.495, P 0.226, L 0.279** (`R=0.61409` at δ=0.4415). So `ΔR = −8.1e-5` needs `ΔI = −1.6e-4` or `ΔP = −3.6e-4` or `ΔL = −2.9e-4`;
`dR/dc_I = 0.0138`, `dR/dk_L = 0.0396`.
Other branches at δ*: C(73) 0.612560, **P(38 face as count branch) 0.612662**, capP 0.614053, old 0.615519, Ccap (inadmissible) 0.611738.

---------------------------------------------------------------------------------------------------------------------------------

## 2. Lever table: Lean source, origin, needed amount

Slopes are exact-cover prices (`levers_price.log`, `half_price.log`, `energy_price_*.log`, `pmax_price.log`, `faces_*_price.log`).

| lever | Lean definition / theorem | mathematical origin | slope dθ*/d(lever) | needed A | needed B |
|---|---|---|---|---|---|
| additive `E` | `Ebase` `PR86/Return/Formulas.lean:86`; `GenericScalar.lean:14-30`; margin `rowMargin :88` | sum of normalizations + contour + Hölder (§1) | +0.2143 | **−4.9e-5** | −8.8e-5 |
| count `R` | `countJ/countN` `PR86/Return/Formulas.lean:44-52`; `common_witness_count_bound` `COL/Record1252270103Return/CountCurve.lean:48-127`; old closed form `COL/Cycle25/Assembly/Count/Endpoint.lean:7-9` | Chebyshev on the saturated pair `(M_r,S_m)` (paper Prop 8.3 `:3556`, Prop 19.2 `:11137`); three lines I, P, L | +0.1294 | −8.1e-5 | −1.46e-4 |
| capacity `C_N` | `newCapacity` `PR86/Return/Constants.lean:37`, `COL/.../Schedule.lean:57`; `affineCapacity` `COL/.../PhysicalDirect/Geometry.lean:27-35`, `affineCapacity_budget :83` | face `n₁+n₂+Λz ≤ B` at `n₁=n₂=m₀=1−y/d=2ℓ/h`; `C = (Bd−4ℓ)/Λ` at `d=h` | −0.0238 | **+4.4e-4 (0.91 %)** | +8.0e-4 (1.7 %) |
| halving `1/2` | `Cycle25/Numerator/Holder.lean:3-9,35,55`; `AmplitudeHolder.lean:15-66`; `PhysicalDirect/BinBound.lean:15-45`; `AmplitudeClass.lean:54` (`-q*zeroCapacity d/2`) | face weight is `‖Q‖²` (`PhysicalDirect/Input.lean:42-70`, `Active.lean:89-91`) and Hölder-4 | −2.28e-3 per unit of `1/2` | `ε = 0.0046` | 0.0084 |
| `c_I = 2` | `inverseExponent` `COL/Cycle25/Assembly/Count/Crossing.lean:13`; `hI` `CountCurve.lean:62`; capacity `(1−r)/2−ν`: `Count/Budget.lean:51-53`; MI hyps `OAI/.../Dictionary/InverseMarkedReferenceSourceEnergy.lean:57-58` | MI column branch, dual length `≤` joint critical length: `r+2z ≤ m` (paper Lemma 17.1 `:6957`) | +1.79e-3 | **1.9941** | 1.9896 |
| `k_L = 5/6` | `V δ = 5/6−δ` `PR86/.../Formulas.lean:32`, `Endpoint.lean:5`; `longExponent` `OAI/.../Hecke/DetectorRowCountCrossing.lean:20`; `hI0` `CountCurve.lean:60`; `sourceExponent r = max 1 ((1+5r)/6)` `OAI/.../Hecke/InverseAmplificationBudget.lean:9-10`; `no_slot_endpoint` `InverseAmplificationEndpoint.lean:12-98` | density `X^{1/6}` of sixth powers, `u ↦ ua⁶` (paper Lemma 17.6 `:9249`) | +5.2e-3 | **0.8313** | 0.8297 |
| `η4` | the literal `1` in `U^(1+ε)`: `AmplitudeHolder.lean:15` (`henergy`), `Input.lean:70` conclusion `U^(1+ε)` | diagonal of the fourth moment `Σ|N²Q|² ≈ U‖b‖²` | −4.3e-2 | 2.4e-4 | 4.4e-4 |
| **not in the original table** | | | | | |
| probe marked energy `c_E` | `x_add_y : x+y = 1−ell` `COL/Record1252270103Return/Geometry.lean:16`; `signal_boundary :19`; `PR86/.../Constants.lean:27-28` | Collet foundations Thm 7.1 `M+cz ≤ N_*` (cited in `atom-targets/README.md`); `c_E=2` is `T_d = 2H+2z_a−N_*` of paper Lemma 14.3 (`:5861`) | +1.07e-2 | **1.99904** (−0.048 %) | 1.99823 |
| amplitude range `p ≤ 1/2` | `∀p ∈ Icc 0 (1/2)` in `PhysicalSchedule.new_rows` (`PR83/ReturnD/Schedule.lean:53`); `hqtop : q ≤ (2a-1)/2` `AmplitudeClass.lean:76` (`hqmax` `Mask.lean:115`) | zero-free bound `|Q_i| ≤ P_i^{δ/2}` | +4.6e-3 per unit | 0.4977 | 0.4958 |
| count face `B_C` / `Λ_C` | chain end (`Source/HybridK15_NN.lean`) | source frontier | −5.9e-3 / +5.2e-4 | `+1.8e-3` / `−0.0203 (−0.92 %)` | `+3.6e-3` / `−0.0405 (−1.7 %)` |
| physical face `B_P` / `Λ_P` (numerator cap raised) | same | source frontier at `2m₀ = 0.849` | −8.0e-3 / +4.8e-4 | `+1.30e-3` / `−0.0217 (−0.91 %)` | `+2.4e-3` / `−0.039 (−1.7 %)` |

Sensitivities are additive to ~5 % (older compound runs); scenario B numbers are ≈1.8× scenario A.
(With the numerator cap `3/50` unchanged, `B_P` saturates after +5e-4 because the clip `s_P·d = 0.04831` is 1.7e-4 above the affine capacity; raise `numeratorCap` to ≥ 0.07 — `PhysicalSchedule.cap_lt_fifth` allows it — to price the rest.)

---------------------------------------------------------------------------------------------------------------------------------

## 3. Slack search, lever by lever

Searched: `COL/` and `OAI/` (read), the `arvi_*`, `sil_*`, `density_split_*` trees under `/home/user/lean-env/qrh/Submissions` (`grep -R`), and `git grep` over all 37 folders of `upstream/main`
(identifiers `weighted_row_holder`, `(1+5*r)/6`, `(5/6-δ)`, `r+2*(∑…)`, `zeroCapacity d/2`). Every submission carries the same lemmas; none has another exponent.

**Additive E.** No free constant. `rowFee`/`reserve` are 1e-9/1e-8 (price 2e-9). `z₀ = 17/50` cancels at `d=h` (the only binding edge). The ε-losses (`16e`, `L.slack`, `mesh`, `loss`) are paid from `(β−θ)/4` and tend to 0.
`h` is at its flat optimum (the unconstrained `h≈0.8054` is worth 7e-8; `floor_margin` costs nothing). **Verdict: none.**

**Count R.** Three closed facts.
* *Mixing branches is exact, not lossy.* For fixed cutoff `t`, `max_r min(I(r), min_b P_b(t−r))` equals `min_b` of the per-branch crossings (I decreasing, `g_b` increasing; checked on 2000 random line sets, 0 mismatches), and `min_t max(L, ·)` commutes with `min_b`.
  So `envelope` (`GenericCount.envelope`, `COL/Record1252270103Return/CountScheme.lean:17`) loses nothing.
* *The capped corner is worth 10× the need but is a source statement.* `Ccap` (z*=0.09999) would give `R=0.611738`, i.e. `−8.2e-4`, about 1.1e-4 in θ. It needs `(2m, z) = (0.7762, 0.09999)` in the proved region; the chain envelope there is `B−0.09999Λ = 0.7581` (step 73), i.e. 0.018 short.
  The envelope at `z=cap` rises monotonically along the chain (0.7429 at step 0 → 0.7547 at step 46); nothing nearby.
* *Lemma W and windows:* 0 (`lemmaW.md` §2).

**C_N.** `C = min(s_P d, (2y−(2−B)d)/Λ)` is exactly the face budget (`affineCapacity_budget`). `m₀ = 2ℓ/h` is forced by `y = h−2ℓ` (§5). Along the chain `C̃=C/d` is: k=21 0.05955, 30 0.05971, **38 0.05976**, 45 0.05973, 54 0.05957, 72 0.05885.
The shifted-conductor rows (`scheduledCapacity`, `Geometry.lean:33`; `scheduled_amplitude_damping`, `ClippedCapacityDamping.lean`) are strictly better than the unshifted ones (damping `δ·2t/4` against the capacity loss `≤ 2t/Λ`), so the unshifted capacity is the binding one and there is no slack there. **Verdict: needs a new source frontier (+0.9 %); see §4.**

**c_I.** The Lean MI hypotheses are exactly `r+2Σℓ ≤ m−2gap` and `2r+8Σℓ ≤ 3m−2gap` (`InverseMarkedReferenceSourceEnergy.lean:57-58`; the same in all 20+ copies). At the binding `r*=0.748` the second condition allows `z ≤ 0.188`, the first `z ≤ 0.126`: only the column branch binds (`T_d ≤ F_c`). `gap`, `ν` are arbitrary and go to 0.
The only variant in the history is the K-copy version (`arvi_repeated_marks*/Source/FiberK.lean:152`, `hzS : z ≤ copies*S`): it enlarges the *supply* `S`, not the cost. Supply is not binding here (`ℓ/d = 0.212 > 0.126`).
Count slots need not come from the probe's pool at all (a zero saturates every prime band), so there is no hidden supply lever either. **Verdict: P1.**

**k_L.** `no_slot_endpoint` proves exponent `1+5p` with `p = ((1+c)r−1)/6` and `c` arbitrary; `5/6` is the density of sixth powers. Round 11 (`research/round11/sextic_moment_notes.md`) shows any bootstrap/grouping gains only a constant, and that the general-coefficient diagonal is false past `U^{4/5}` (de Faveri). **Verdict: atom 2.**

**η4 and the numerator structure (closed).**
* Fourth-moment diagonal is a lower bound for the full family: `Σ_u|N²Q|² ≥ U‖b‖²`; a class-restricted saving needs large-values input for the sextic family (none; `research/LOG.md` 2026-10-24 Halász/Huxley entry).
* *Hölder order 2* (second moment, capacity `m₀+z ≤ 1/2`, i.e. `C₂ = d(1/2−m₀) = 0.0608`): worse by **+0.0698** in Z-exponent (`(d/4)(1−R) − δp(C₂−C/2)`); interpolation in `b` is linear in `b` with positive slope, optimum at `b=0`.
* *Pointwise numerator* (`|S'| ≤ U^{δλ/2}`, `λ=2ℓ/d`): `dR+δℓ+δpℓ = 0.60677` against Hölder `0.60370`, worse by **+3.07e-3** (65× the need); the Hölder extremal level `|N|≈U^{0.0902}` sits below the pointwise ceiling `U^{0.0940}`, so the Hölder extremal configuration is admissible and there is no mixed regime.
* *Joint numerator* (plain witness inside the moment): `levy − joint = (R − P(m))/4` exactly (`research/lean-lab/JointNumerator.lean`, re-derived symbolically); it ties at the crossing and loses for `m < m*`.
* *Higher Hölder (6):* sixth moment of the dual (length `3m₀ = 1.27 > 1`) is off-diagonal; worse.

**z₀, h, caps, windows, `dm`, `mMinus`, reserve:** `lemmaW.md` §5 (all ≤ 1e-7).

---------------------------------------------------------------------------------------------------------------------------------

## 4. The halving `δpC/2` (question 3)

**What it is.** `Cycle25/Numerator/Holder.lean:3-9` says it in words: "the selected prime factors occur inside the fourth moment with exponent two, not four". Mechanically:
* the face (source theorem) is `Σ_u ‖P₁P₂∏Q_i‖² ≤ U^{1+ε}` (`PhysicalDirect/Input.lean:42-70`): weight `‖Q‖²`, slot width counted in `n₁+n₂+Λz ≤ B`;
* `weighted_row_holder` (`Holder.lean:35`): `L²(Σ‖S‖)⁴ ≤ #³ Σ‖S‖⁴‖Q‖²` from `‖Q‖ ≥ L`; so after the fourth root the lower bound on `‖Q‖` is used at power `L^{1/2}`;
* `weighted_amplitude_bin` (`AmplitudeHolder.lean:15-66`): `Σ‖SP‖ ≤ U^{total − selected/2 + (3R+1+ε)/4}`, with `total = qℓ/d`, `selected = qC̃`.
So the full slot product costs `qℓ` and the selected part is refunded only `qC/2`.

**Neutrality (proved, symbolic check `checks.py`).** Using `K` copies of a slot set (weights `‖Q‖^{2K}`, list width `Kz ≤ C`, faces charge multiplicity) gives cost
`q(ℓ−z)+qz(1−K/2) = q(ℓ − C/2)` for every `K`, and the same for a fractional weight `s` with `sz ≤ C`. Mixed weights are therefore the same. Saving `δpC` instead of `δpC/2`
requires a face with weight `‖Q‖⁴` *at the same capacity* — an object that does not exist (`research/mixed-slots/README.md`, `research/round11/README.md` §2: a diagonal moment with a third factor is the Patterson-bias atom).

**It is the capacity lever.** `E` contains `−(1/2+ε)δpC`; `ε` is equivalent to `ΔC = 2εC`. Exact prices (`half_price.log`; scenario A, linear: `dθ*/dε = −2.28e-3`):

| ε (saving `(1/2+ε)δpC`) | 0.001 | 0.002 | 0.003 | 0.004 | 0.0045 | **0.0046** | 0.005 | 0.01 | 0.05 | 0.5 (`Cfull`) |
|---|---|---|---|---|---|---|---|---|---|---|
| gap to bar (A) | +8.2e-6 | +5.9e-6 | +3.6e-6 | +1.3e-6 | +2.1e-7 | **−2e-8** | −9e-7 | −1.2e-5 | −1.0e-4 | −2.9e-4 |

Scenario B: ε = 0.01 → −3.8e-6; so `ε_B ≈ 0.0084`. Scenario 46/46 (single face): 0.0088.
Equivalent forms of the same demand: `ΔC = +4.4e-4`; `B_P +1.30e-3`; `Λ_P −0.91 %`; envelope at `2m₀ = 0.849` up by 0.9 % of its slot width. For comparison the whole chain moves `C̃` by 0.4 %.
**Is any ε available?** I found no mechanism: no weight between `‖Q‖²` and `‖Q‖⁴` is cheaper than its multiplicity (above), no second source face helps (envelope = min of crossings, the chain is the envelope), and class information
cannot be carried into the face (bin-restricted faces do not exist, `barriers/README.md`). `p`-structure does not help either: at `p = 1/2` every slot is saturated (all slots have `g_i = δ/2`), so selecting the best subset gains nothing.

---------------------------------------------------------------------------------------------------------------------------------

## 5. Other return inputs

* **Probe geometry (`c_E`).** Lean fixes `x+y = 1−ℓ` (`COL/Record1252270103Return/Geometry.lean:16`), `h := 1+ℓ−x`, `y = h−2ℓ`, `θ = 11/12−ℓ/4` (`signal_boundary`). With marked-energy cost `c` (paper `M+cz ≤ N_*`, `N_*=1+ℓ`): `x+y = 1−(c−1)ℓ`, `ℓ = (11−12θ)/(c+1)`, `y = h−cℓ`;
  the return polynomial is unchanged (`rowAt` depends only on `ℓ,h,y`; `c_E` enters the numerator capacity through `y = h−cℓ`, i.e. `m₀ = cℓ/h`, and that effect is inside the price). Priced exactly (`energy_price_*.log`, `h` free, floor receipts dropped; base 0.873946101 at h=0.8054):
  A: c = 1.9995 → +4.9e-6 gap, 1.999 → −4.3e-7, 1.998 → −1.1e-5; **needed 1.99904**. B: 1.999 → +8.2e-6, 1.998 → −2.5e-6; needed 1.99823. Equivalent to `x+y+ℓ ≤ 1+1.6e-4`. This matches `atom-targets/README.md` (2 → 1.99905) and `P1_PROBLEM.md` use (b).
  The Pareto statement (x+y=1−ℓ) is confirmed by `LOG.md` 2026-10-24 item 7; no decoupling gain.
* **`p`-range.** Rows with a zero at depth δ have all slots saturated (explicit formula), so `p = 1/2` is the truth for them, not an artefact (inference). `p ≤ 0.4977` would be needed.
* **Caps, windows, switch, reserve, h:** nothing (`lemmaW.md` §5).

---------------------------------------------------------------------------------------------------------------------------------

## 6. Ranking (question 4)

Plausibility = my estimate that a rigorous proof appears inside this project's horizon.

| # | candidate | needed (A) | what a proof needs | plausibility | return-side Lean wiring | analytic Lean cost |
|---|---|---|---|---|---|---|
| 1 | `c_E` probe marked energy | 2 → 1.99904 | K^{1.1e-4} saving in the quadratic large sieve over slot-twisted reflected cubic-theta coefficients just past critical length (P1(b)) | ≪ 1 % | `Geometry.lean:16-19`, `Constants.lean:27-28`, receipts: ~100 lines + regenerate | open problem (GL(2)-metaplectic Lindelöf on average); ≫ 10⁴ lines |
| 2 | `c_I` | 2 → 1.9941 | same estimate, count-side form | ≪ 1 % | `Formulas.lean:33-52` (`p→2p/c_I`), `CountWidth/CountDecode/CountAdmission` (~230 lines), regenerate rows (3.5k generated lines) | same |
| 3 | `k_L` | 5/6 → 0.8313 | sextic Möbius mean value `λ ≥ 0.16834` (zero density in disguise) | ≪ 1 % | `V δ` and 5/6 literals + same files | open |
| 4 | capacity / `ε` / `B_P`,`Λ_P` | +0.91 % of `C` | plain fourth moment with slot cost lowered by 0.9 % at `(2m₀, z)=(0.849,0.0598)`, or `‖Q‖⁴`-weight face | ≪ 1 % | `Holder.lean`, `AmplitudeHolder.lean`, `BinBound.lean`, `AmplitudeClass.lean`, `GenericScalar.lean` (~300 lines) | new moment theorem + chain regeneration |
| 5 | additive `E`, `η4`, direct `R`, `p`-range | −4.9e-5 / 2.4e-4 / −8.1e-5 / 0.4977 | no mechanism (Cauchy–Schwarz, explicit formula, or combination of 1–4) | ≈ 0 | — | — |

Hand-edit footprint reference: PR 86 `Return/` is 1971 lines (hand-written core ≈ 700: `Formulas 92`, `CountWidth 61`, `CountDecode 71`, `CountAdmission 96`, `CountMonotonicity 101`, `Windows 173`, `FinalWindows 72`, `Constants 72`); generated `Rows/` 3508 lines in 21 files; `Source/` 38,852 lines in 48 files; PR 83 `ReturnD/` 15,080 lines in 119 files.

Not a lever but relevant: if the bar were 1e-5 below the record (0.8739458), scenario A (0.8739463) misses by 5e-7 and a finer chain (continuum 0.873945) would pass.

What would change this verdict: (i) any explicit power saving in the column-branch quadratic large sieve at `N ∈ [K, K^{1+10⁻⁴}]` for `g̃(n)·Σ_P a(P)conj((n/P)₃)`; (ii) a diagonal moment `Σ|S_m²Q_z|² ≪ U^{1+ε}` for `2m + c z ≤ B` with `c` 1 % below the chain's `Λ`; (iii) `λ ≥ 0.1683` for the sextic Möbius moment.

---------------------------------------------------------------------------------------------------------------------------------

## 7. Verified vs inferred

**Verified (read in Lean/paper or computed here):** all Lean statements and line references above; the exponent algebra and numeric breakdown (§1); `z₀` cancellation; neutrality of slot multiplicity and fractional weights; envelope-crossing identity; `levy − joint` identity;
the Hölder-2, pointwise and flatness numbers; chain capacity table; all exact prices (§2, §4, §5); that the same identifiers and exponents (`(1+5*r)/6`, `(5/6-δ)`, `r+2*(∑…)<1`, `zeroCapacity d/2`) occur in every submission that contains these parts (`git grep`).
**Inferred (from earlier reports, not re-derived):** that atoms 1 and 2 are open problems and the specific statements P1/λ≥0.16834 (`barriers/README.md`, `atom1/README.md`, `P1_PROBLEM.md`, `round11`); that bin-restricted faces do not exist; that p=1/2 is forced for rows with a zero at depth δ; that no earlier submission has a stronger variant (I read the lemma in Collet's tree and the baseline; the other copies were located by `git grep`, not diffed one by one).

## 8. Files

`$SCRATCH/analysis/B1/`: `half_price.py` (ε), `energy_price.py` (c_E), `pmax_price.py` (p-range, B_C/Λ_C), `faces_phys.py` (B_P/Λ_P), `duals.py` + `branches.py` + `point.py` (count lines), `ebreak.py` (exponent breakdown, E(δ) profile), `checks.py` (identities); logs `*.log`.
