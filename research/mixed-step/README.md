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
  0.8745804. The cover breaks at `δ ≈ 0.44122`, `p → 1/2`: the count's own terms (atoms 1 and 4,
  `../barriers/README.md`), with no face involved.
- **What the source side can give.** At most −2.7e-5, of which P is worth about two thirds.
- **The readings against the cap.**
  - Sil-LOW reaches the cap, which is why its θ* is flat in C.
  - The mixed step's cautious reading already takes −1.75e-5 of it.
- **Sil-LOW is probably not real.** Its selected block is large (`d ≈ 0.35·b`), and the HIGH gate
  charges a first-layer amplifier (`a(5 − 6ρ)` for the pool). The pricing above ignores that
  charge. The parentless pool step fails for the same reason; that is why the face chain exists.
  The mixed step has no such charge: in the faceless family the excess, and so `d`, is
  infinitesimal at each pivot. Only the regress condition `c·qβ < e + q` matters there.

## 4. What decides it (open)

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

## 5. Status

- Pricing done. The two principled candidates are worth −1.75e-5 (mixed step, cautious reading)
  and −2.7e-5 (Sil-LOW). The optimistic readings are larger but not yet scoreable.
- Each needs a new analytic theorem:
  - Sil's transfer at the step's first layer, with Collet's LOW/HIGH split at the second;
  - or Sil's native deletion restricted to LOW rows at rate `q`, with the HIGH rows counted.
  - Either is of the order of Sil's 421-file development; not started.
- Proved in Lean: the payment algebra, the thresholds `6q/(1+q)` vs `6q`, Sil's floor `26/7` and
  when it beats `6κ`.
