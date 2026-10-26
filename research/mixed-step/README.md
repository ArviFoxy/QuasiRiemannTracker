# A mixed fourth/sixth-power source step: pricing and structure (2026-10-25)

**Question.** Our face family descends with slope `Λ = 6q*·B`, where `q*` is the HIGH threshold
and 6 is the LOW branch's exchange rate. The 6 comes from Collet's sixth-power pool amplifier.
Sil's fourth-power transfer (PR 74) replaces the exchange rate 6 on the initial face. Can it
replace it inside a source step, and what would that be worth?

Scripts: `qeff_models.py` (flow with a modified LOW exchange rate, scored by the exact return),
`sillow_envelope.py`, `sillow_theta.py`. Lean: `../lean-lab/MixedStepLedger.lean` (proved).
Earlier design notes: `../combined/MIXED_STEP_DESIGN.md`, `../combined/BARRIER_REVISITED.md`.

## 1. The two amplifiers

**Collet's pool** (paper69 `sources.tex`, (CA1)–(CA6)). On the MAIN polynomial
`F_b(h) = Σ_u b(u)·g(u, h)`, whose columns `u` may contain retained slot primes:
- for a pool prime `p` (avoiding all slots), `g(u, p⁶h) = 1_{p∤u}·g(u, h)`, hence the exact
  identity `F_b(h) = (1/P)·Σ_p F_b̃(p⁶h)`;
- Cauchy–Schwarz and the pushforward `(h, p) ↦ p⁶h` (bounded fibres) give the MAIN norm at the
  dilated radius with the density factor `1/P = U^{−a}`;
- the parent is then applied at scale `Q = 1 − 6a − δ`; excess slots beyond its capacity are erased
  at rate `q` on LOW rows ((G9)–(G13)).

So the pool saves `a` and costs `6a` of row scale. The LOW regress (the pool's own cost creates
more excess) closes iff `1 − 6qB₀/Λ₀ > 0`. In the faceless chain this is saturated (`den = 2⁻¹⁵`),
so `Λ = 6q*B` is the descent law.

**Sil's transfer** (verified in the vendored Lean, `FourthPower/`).
- **The CRT step.** The selected product `D` sits in the column modulus. The CRT step
  `MixedSupplierKernel.fixed_supplier_row_fourth` rewrites the Gauss sum at modulus `f·D·n` as a
  Gauss polynomial of the common residual coefficient at frequency `D⁴k`.
- **The average over D.** `MixedSupplierPositive.actual_grouped_average` gives
  `Σ_D groupedWeight(D)·Σ_k‖P(D⁴k)‖²/W ≤ (C(2W)^δ(16KW⁴)^ε/W)·Σ_r‖P(r)‖²`, a `1/W` average
  with bounded fibres.
- **Gates** (`MixedFirstPaidCosts.Gates`):
  - mixed: `P + 2S + 4d < R`, with `S` the live unselected width and `R = log(K·N(η))`;
  - native: `(3/4)·S < d`;
  - `Z^d ≤ W`.
- **The −2d.** `OuterFreshMixedCapacity.actual_allocated_large_gate` derives the gate from the
  root capacity `P + (93/25)(S + d) ≤ Q` and `hdeclared`, which is `Q − 2d − … ≤ R`.
- **Net ledger per unit.** Plain costs 1. Live costs 2 of row scale plus native `κ`. Selected
  costs 6 of row scale (4 for the dilation, 2 for the reference) and saves 1. The infimum is
  `(2 + 6κ)/(1 + κ) = 26/7` (`MixedStepLedger.sil_face_floor`); Sil's selection fraction 43/100
  gives 93/25.

## 2. Readings of a mixed step and their prices

A mixed step selects width `d` of the LOW excess and transfers it instead of (or with) the pool.
In `MixedStepLedger`, per unit of `d` the energy saving is `e`, the avoided erasure is `q`, and
the row cost is `c`. The payment condition is
`a(1 − 6qβ) + d(e + q − cqβ) ≥ qX₀ + r`, with `β = B₀/Λ₀` (`pays_iff`: savings cover the erasure
of the unselected excess).

Prices: the flow from Sil's tangency with the LOW exchange rate replaced, scored by the exact
return (`theta_eval.theta_star`, `h = 401/500`).

| reading | exchange rate `Q_eff(q)` | θ* | vs PR 76 (0.8746075) |
|---|---|---|---|
| pure (Collet; calibration) | `6q` | 0.8746073 | −2e-7 (model error) |
| live excess kept at 2, native `q` paid by selected (Sil's ledger on the excess) | `min(6q, (2+6q)/(1+q))` | **0.8745898** | **−1.75e-5** |
| transfer with no saving (`e = 0`, `c = 4`) | `min(6q, 4)` | 0.8746073 | 0 (`no_saving_useless`) |
| `e = 1`, `c = 6`: unselected excess erased at `q` | `6q/(1+q)` | **0.8745804**[^1] | **−2.7e-5** (the return floor) |
| `e = 1`, `c = 4` | `4q/(1+q)` | at least as good | −2.7e-5 (floor) |
| Sil-LOW: Sil's argument as the LOW branch at native rate `q`, no parent | LOW region `t + (2+6q)/(1+q)·b ≤ 1` | **0.8745804** | **−2.7e-5** |

[^1]: The flow never reaches the HIGH floor `q* = 1/2` before the cap 0.06. Every face after the
start has slope below 3, which the current return's physical receipt `source_lambda_low` needs.
Lemma D makes that receipt unnecessary (`../barriers/README.md`). `optimistic_theta.py` drops it
(hypothetical; our Lean return would need the same change) and scans P. Every P from `s = 0.03` to
0.055, with `C = (0.98269, 2.2260)` at `s = 0.06`, gives the floor 0.8745804.

**Sil-LOW.** `E(s) = max{E : E + (2+6q*)/(1+q*)·s ≤ 1}`. It gives P = (0.98094, 3.0) at
`s = 0.0403`, against our (0.97187, 3.0). θ* is flat in C, so the return's other atoms bind
there.

## 3. The return caps every source-side gain at 2.7e-5

`return_ceiling.py` scores the exact return with idealized faces (slope of P just above 3, which
the physical receipt needs):

| C | P | θ* |
|---|---|---|
| ours (0.96775, 2.9112) | ours (0.97187, 3.0) | 0.8746074 |
| ours | (0.98094, 3.0): +0.009 | 0.8745903 (−1.7e-5) |
| (0.99, 2.5) | ours | 0.8745986 (−8.8e-6) |
| (0.99, 2.5) | (0.99, 3.0) | 0.8745804 |
| (0.9999, 2.0) | (0.9999, 3.0) | **0.8745804** |

- **The floor is the return's own.** With perfect faces the return still fails just below
  0.8745804. The cover breaks at `δ ≈ 0.44122`, `p → 1/2` on the `new_top` edge. There the
  uncapped branch C has a positive return polynomial (0.002) but fails the FR8 admission
  `Mn − mL·DJ` (−0.084), because `mL = (B − L·s₊)/2` grows with the face. The capped branch is
  admitted, but its return polynomial is not positive there. So the floor is a cap/admission
  trade-off inside the return (FR8 windows), not a face.
- **What the source side can give.** At most −2.7e-5, of which P is worth about two thirds.
- **The readings against the cap.**
  - Sil-LOW reaches the cap, which is why its θ* is flat in C.
  - The mixed step's cautious reading already takes −1.75e-5 of it.
- **Sil-LOW is probably not real.** Its selected block is large (`d ≈ 0.35·b`), and the HIGH gate
  charges a first-layer amplifier (`a(5 − 6ρ)` for the pool). The pricing above ignores that
  charge. The parentless pool step fails for the same reason; that is why the face chain exists.
  The mixed step has no such charge: in the faceless family the excess, and so `d`, is
  infinitesimal at each pivot. Only the regress condition `c·qβ < e + q` matters there.

## 4. Sil's ledger, traced exactly (`SIL_LEDGER_TRACE.md`)

- **No net W factor.** The original energy carries `#active ≈ 256^#J·W` (Cauchy over selected
  assignments) and `scale = W` (regrouping). The reference is quadratic in the volume, and its
  `selectedVolume²` cancels both. That cancellation is the `−2d` in the declared width.
- **The saving d is used once,** in the nonexceptional (native) component:
  `Z^{κS}/W ≤ Z^{κS − d}`, under `Gates.Wlower`. That component sees no K4 dilation.
- **The dilation is paid in the other components** of the second Poisson:

  | component | how W enters | exponent ≤ 0 |
  |---|---|---|
  | zero frequency | `16·K·W³` | `P + S − R + 3d` |
  | nonexceptional | `1/W` | `κS − d` |
  | exceptional | `W^{7/3}` | `P + S − 5R/6 + 7d/3 − 2l/3` |
  | short reference | conductor `R + d` | `R + d + 2l − P + S − R/2` |

  The gate `P + 2S + 4d < R` is "the reference interval for `l` is nonempty"
  (`2S = 3/2 + 1/2`, `4d = 7/2 + 1/2`).
- **The native deletion is pointwise per row.** The rows are the non-fixed-inducing dual
  frequencies, with exponent `κ·w` per slot and κ from the global β. A smaller rate on a
  subfamily of rows needs a per-row slot bound at that rate. None exists, so Sil-LOW needs new
  input as well as new plumbing.

**Consequence for the step.** Collet's pool has the same shape:
- its saving `a` is used in the RAW LOW branch, against erasure at rate `q`;
- its costs land on the other components (centered `9a`, true diagonal `5a`, reference `7a`,
  HIGH `a(5 − 6ρ)`) and on the RAW scale `Q = 1 − 6a`.

In the faceless family every amplifier width is infinitesimal at the pivot. Only the RAW LOW
regress counts, so what decides the mixed step is: does the selected transfer's dilation land on
the scale of the parent call, the way the pool's `6a` does? Collet's side is traced in
`COLLET_LOW_TRACE.md` (pending).

## 5. Collet's side traced (`COLLET_LOW_TRACE.md`) and the combined ledger

**Collet (verified).**
- In the RAW excess (RC3) the MAIN radius cancels exactly (`actual_raw_coordinate_identity`).
  The pool's dilation reaches LOW only through the scale `Q = 1 − 6a − δ`, i.e. the capacity `z`.
  Per unit of `a`: RC3 −1, `Q` −6, MAIN +6, centered +4.
- Columns are `u = (one prime per live slot)·v₀·v₁`, and a slot enters both as a factor of the
  Gauss modulus and through its coefficient.
- One volume `V = X₁X₂∏Pᵢ` serves as the normalization, the column size and the `X` of the MAIN
  radius. RC3 responds as `2κ − ν₁ − ν₂`, where `κ` is the change in column size and `ν` the
  change in normalization; a slot in the columns is therefore RC3-neutral.
- The LOW erasure is pointwise per LOW row (`ActualLow`: zero maximum `< a + 2e`), at rate `q`,
  and comes before the parent call. The capacity is `cap = min((B·Q − Pcap)/Λ, hQ)`.

**Combined (inferred; to be checked adversarially).** A selected block of width `d` moved from the
columns to the frequency, with the original normalization kept (`ν = 0`, since the target is
fixed):

| term | change |
|---|---|
| RC3: column size `2κ` | −2d |
| RC3: Cauchy–Schwarz over `#D ≈ W = Z^d` selected products (`|pair coeff| ≤ 1`) | +d |
| RC3 net (the saving `e = 1`) | **−d** |
| `Q` (dilation `D⁴`; the bounded-fibre pushforward to the enlarged radius) | −4d (capacity −4dβ) |
| width passed to the parent | −d (avoids `q·d` of erasure) |
| MAIN radius | −2d + 4d = +2d (cancels in RC3) |

- **Mixed LOW payment.** `a(1 − 6qβ) + d(1 + q − 4qβ) ≥ qX₀ + r`. This is the `e = 1, c = 4`
  reading (`erase4`, exchange rate `4q/(1+q)`).
- **The −2d in Sil's `Rdecl`** is the same column-size `−2d`. In Sil's chain it cancels the
  `#active·scale ≈ W²` of Cauchy–Schwarz plus regrouping; the D-average's `1/W` is the saving `d`.
- **The other gates.** The centered, true-diagonal, reference and HIGH gates get `O(d)` terms. In
  the faceless family `d` is infinitesimal at each pivot, so only the regress counts, as for the
  pool's `a` now.
- **The agent's own figure** `qd(4β − 1)` is the same ledger without the Cauchy–Schwarz and
  normalization saving.

**Value if it holds.** The family flattens to the return floor: −2.7e-5. Widening the count window
`sC` from 13/250 to 0.054 lowers the floor to 0.8745760, i.e. −3.15e-5
(`../strip-mine/floor_scan.py`).

## 6. Full-gate check (`continuum_mixed.py`, `score_continuum.py`)

The float models above use only the HIGH gate and the LOW limit. Flatter faces could wake up the
other gates (centered G5, true diagonal, reference, sectors, HIGH-parent floor). So I reran the
full-gate continuum solver, the float mirror of every Lean gate (`../faceless-chain/gates.py`),
with:
- the mixed LOW payment, with `q` searched over `[1/2, 3/4)`;
- `d` charged like the pool in every other gate (conservative); `d` is tiny at the pivots anyway.

| run | faces | θ* (slope receipt dropped, `sC = 27/500`) |
|---|---|---|
| pure (calibration) | ends at (0.96733, 2.902), `q = 1/2`; matches our C | 0.8746075 (Lean) |
| `e = 1, c = 6` | from `s = 0.016`: `L ≈ 2.52 → 2.17`, `B ≈ 0.98 → 0.968`, `q ≈ 0.75 → 0.60` | **0.8745760** |
| `e = 1, c = 4` | `L ≈ 1.66 → 1.57`, `B ≈ 0.967 → 0.964`, `q ≈ 0.75 → 0.69` | **0.8745760** |

Both reach the return floor (−3.15e-5 against PR 76). With the full gate set, every value hinges
on `e`, the selected block's energy saving in the step's LOW branch: `e = 1` gives the floor,
`e = 0` gives nothing.

**Red flag (under adversarial review, `ADVERSARIAL_REVIEW.md`).**
- **The comparison.** At `q = κ = 3/4` the same induction would put the natural slot cost at
  `cκ/(1+κ) ≈ 1.7–2.6`, against 6κ = 4.5. Sil's direct (non-inductive) argument with the same
  transfer gets only 3.72.
- **Sil's costs.** Live slots cost 2 in Sil's exceptional and short-reference components, against
  about 1 through `T` in Collet's step gates; the dilation costs `W³` and `W^{7/3}` there.
- **Possible resolution.** The induction amortizes: `d` is infinitesimal per step, so those costs
  vanish.
- **Open question.** Whether that resolution is real, or Collet's exceptional handling hides the
  same cost.

## 7. Adversarial review: CONFIRMED with e = 1, c = 6 (`ADVERSARIAL_REVIEW.md`)

- **c = 4 is refuted.** The column term `−2d` sits in the RAW-scale coordinate `x2`, which is
  also the scale handed to the parent (`modified_deficit_and_coordinate`). So the parent is called
  at `Q′ = 1 − 6a − 6d − δ − ρ`.
- **Second-transform coordinates of the residual:** `(x0 + 5d, x1, x2 − 6d, x3 − d)`, and RC3 is
  −d. So the transfer prices exactly like a pool (saves 1, costs 6). Its gain is that the selected
  slots leave the width passed to the parent: payment `a(1−6qβ) + d(1+q−6qβ) ≥ qX₀ + r`, descent
  `Λ > 6qB/(1+q)`.
- **Keep a pool `a ≥ r`.** With `f ≈ b` a pure transfer leaves no reserve for the scheduled
  losses. Also required: (G11) at `F′`, i.e. `6Bd < (Λ−1)b` at the pivot.
- **Other gates.** Per unit of `d`: zero frequency 4, centered 3, HIGH `5 − 6ρ − ν`; each is no
  more than the pool's, so `continuum_mixed.py`'s convention is conservative.
- **The residual is an admissible Collet instance.** Common coefficient
  (`fixedCommonCoefficient`); twists `χ_n(f)²ξ` covered by ActualLow's quantifier over ray labels;
  seeds, holes, fifth-freeness. Non-coprime `n, D` vanish on both sides.
- **Red flag explained.**
  - The natural induction would close at `Λ ≥ 18/7` but has a separate wall at `Λ = 3` (centered
    comparison MF3.49, `q_κ = Λ − 1 > 2`). Collet's step has no such wall.
  - Sil's 3.72 is a direct face: its terminal gates are first-order in `d = 0.43(S + d)`, but only
    `O(d)` per step in an induction.
- **Open: the analytic lemma.**
  - The transfer at Collet's first MAIN layer, with a literal residual source.
  - Collet's step run on that residual, with `x2 := 1 − 6a − 6d − δ − ρ`.
  - Certificate gates with the O3 charges.

**Value.** `cont_c6` is the relevant run (slopes 2.52 → 2.17). With the return's physical window
`s_P = 0.052` (a generator parameter, capped by the receipt `d_s ≥ 3/4`) it certifies
**θ* = 0.8744022**, about −2.05e-4 against PR 76.

## 8. What decides it (open)

The readings differ in one fact: whether the transfer saves energy (`e = 1`) or only moves the
selected block from the modulus to the frequency (`e = 0`).
- **The volume normalization looks neutral.** `original_normalization` divides by the volume,
  selected primes included. Cauchy–Schwarz over selected products gives a factor `≈ W`, and the
  D-average gives `1/W`. So relative to the coefficient norm the transfer is neutral, unless the
  dilated moment is evaluated in a regime where the selected block's removal from the length
  counts.
- **Where the saving would come from.** In a large sieve `(range + length)·‖c‖²`, moving `W` from
  the length to the range saves `W` exactly when the length dominates the dilated range. Sil's gate
  `P + 2S + 4d < R` has that shape, read in the dual variable.
- **What the step would need.**
  - The step's RAW norm is evaluated by the parent at scale `Q`, not by a direct diagonal bound.
  - Whether the saving survives there is the question.
  - It also matters whether the step's centered geometry (G5) charges live slots 1 per unit, as
    in Collet, or 2, as in Sil's reference gate.
- **Exact trace.** An agent is tracing Sil's exponent chain from the original energy to the final
  bound: `SIL_LEDGER_TRACE.md`.

## 9. Status

- Pricing done. The two principled candidates are worth −1.75e-5 (mixed step, cautious reading)
  and −2.7e-5 (Sil-LOW). The optimistic readings are larger but not yet scoreable.
- Each needs a new analytic theorem:
  - Sil's transfer at the step's first layer, with Collet's LOW/HIGH split at the second;
  - or Sil's native deletion restricted to LOW rows at rate `q`, with the HIGH rows counted.
  - Either is of the order of Sil's 421-file development; not started.
- Proved in Lean: the payment algebra, the thresholds `6q/(1+q)` vs `6q`, Sil's floor `26/7` and
  when it beats `6κ`.

## 10. Discrete start, exact gates, and the return lever s_P (2026-10-25, late)

**The start is a fan** (`discrete_chain.py`, `fan.py`, `mixed_certs.py`).
- The continuum run starts on Sil's face at `s = 0.016` and jumps from slope 3.72 to 2.52. A finite
  chain with coarse steps stalls on the line `L/B = 6q/(1+q)` at `q = 0.7499` (den3 → 0), and with
  `q` optimized it trails the continuum by ~0.0015 in E.
- But the jump is realizable as a **fan**: faces through the one point `(s0, E0)` on Sil's line,
  each a legal mixed step from the previous one. With `q = 7499/10000` and `s0 = 16/1000`, **21 fan
  steps pass the exact draft SourceValid3** (`mixed_certs.py`: the 16 scalar gates with
  `den3, F′, a + d`, the new gates `b − 2e − d ≥ 0` and `d ≥ 0`, the weak cap at `F′`, the three
  sectors, and HIGH Bernstein trees). Slope 3.72 → 2.5219723 at `B = 0.9808216`
  (`L/B = 2.5712855 < 18/(7 − 4·2⁻¹⁵)`), so the fine family can start with `q ≤ 3/4`.
- `d(cap)` in the fan steps is about 0.006, not infinitesimal. The draft gates charge it like the
  pool, and they hold.

**The faces no longer bind** (`floor_lemmaD.py`, `diag_return.py`). At `s_P = 0.052`,
`s_C = 0.054`, θ* = 0.8744022 does not move when `B_P` or `B_C` rise by 0.005 or `L_P` drops by
0.1. The binding is the `new_top` cover at `δ ≈ 0.4385`, `p → 1/2`. There the capacity is
`C_N(d₊) = min(s_P·h, (2y − (2 − B_P)h)/L_P)`, and with the mixed faces its first branch binds.
(With PR 76's faces the second branch binds instead: `(B_P − 0.843)/3 ≈ 0.043 < s_P`.)

**The `dMinus` cliff is not real.** The receipt `ds ≥ 3/4` is the field `dMinus_lower : 3/4 < dMinus`
of `ReturnD/Schedule.lean`. All 9 of its uses in our fork need only `dMinus > 1/2`:
`GenericFeedback` (d ≥ 0), `PhysicalDirect/Geometry` (d > 0), `Active` (1/2 < d), `SelectedBin`
(0 < d, 1/2 ≤ d), `SourceSelection` (1/200 ≤ dm, 1/2 ≤ d). With the field relaxed to 1/2
(`sp_beyond.py`):

| s_P | face caps | θ* |
|---|---|---|
| 0.052 | 0.0549989 | 0.8744022 |
| 0.053 | 0.0549989 | 0.8743795 |
| 0.054 | 0.0549989 | 0.8743568 |
| 0.0549 | 0.0549989 | 0.8743364 |
| 0.056 | 0.065 | 0.8743115 |

The next limit is the second branch, `s_P ≤ (B_P − (2 − 2y/h))/L_P ≈ 0.0565–0.0575` along the mixed
flow. That is where the faces matter again, through `(B − 0.843)/L`. The continuum gates allow face
caps up to 0.08.

## 11. What binds the mixed flow, and the atlas at the new design point (2026-10-26)

**Binding gates.**
- **HIGH branch 5** (`dI = 1 − p`, `bI = pF`, `eP = L_H − 2p`, `hP = 2p·B_H·F`) at `p = 1/2`,
  `ν = q`, width `b = s` (the crossing). Margin about 1e-4 along the whole flow.
- **The weak cap** at `b = cap = 0.075`, margin about 2e-5. So 0.075 is about the largest uniform cap.
- **The K-copy count is not binding.** `K = 8, 16, 64` give identical slopes.
- **The HIGH parent: self beats fixed.** A fixed stronger HIGH parent (Sil's face, the natural face)
  instead of the previous face is worse.

**Return atlas at the new point** (`../strip-mine/atlas2.py`, ε = 3e-3, units 1e-7).
- **Count branches.** The old count branch's `(1 − δ)` in `N_old = (1 − δ)J + δCV/2`: +4128. The affine
  branch's `(1 − δ)`: +1356.
- **Return polynomial constants:** `1/2` +3367, `3/4·d·N` +2445, `δ/2` +1526, `y/2` +1403,
  `13h/75` ±840.
- **Faces:** `B_P` −277, `h` −167, `L_P` +35; `B_C`, `L_C`, `s_C`, `s_P` 0.

**h fine scan.** `h = 0.8044` gives θ\* = 0.8742701; 0.803 → 0.8742757; 0.806 → 0.8742972.
