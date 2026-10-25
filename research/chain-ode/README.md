# The source chain as an ODE (2026-10-24)

The 59- and 107-node source chains (`../repeated-marks/cchain_k8b.json`,
`../cap-induction/chain_h45.json`) are, to within about 1e-4 in face height, the Euler discretization
of one ordinary differential equation for their envelope. This note derives the equation from the
binding gates, checks it against the chains, and uses it to price the chain's levers.

## Derivation

Write `E(s)` for the envelope (the largest proven plain length `m₁ + m₂` at slot width `s`). A node
pivoting at `s` has line `B − Λz` through `(s, E(s))`, so `B = E + Λs`.

- **HIGH gate at the pivot.** After Lemma F the cap side is slack. The binding gate is the regular
  HIGH gate at the crossing `b ≈ s`, at density `ν = q`:
  `1 − ρ(q) − q(t + s) + G = 0`, with `t = E(s)` and `ρ(ν) = 1 − 10ν/(15 − 6ν)`.
  Write the marked gain as a fraction of its structural cap (Lemma C): `G = g·qs`. Then
  `10/(15 − 6q) = X` with `X = E + (1 − g)s`, that is

  `q = (15 − 10/X)/6`.
- **LOW limit.** The node must serve as the next LOW parent, so `Λ ≥ 6qB` (the LOW denominator
  `1 − 6qB/Λ` stays positive). With `B = E − sE'` and `Λ = −E'`:

  `E'(s) = −6qE/(1 − 6qs)`.
- **Start.** Use the natural face `(1, K = 4.4973108)` while its slope is smaller. The ODE slope
  equals `K` at `s ≈ 0.0135`, the committed chain's first pivot.

## Calibration

`g(s)` is read off the consolidated chain as the gain each node actually needs at its crossing:

| `s` | 0.014 | 0.018 | 0.022 | 0.026 | 0.030 | 0.034 | 0.038 | 0.042 | 0.046 | 0.050 |
|---|---|---|---|---|---|---|---|---|---|---|
| `g` | 0.43 | 0.57 | 0.69 | 0.78 | 0.85 | 0.89 | 0.93 | 0.95 | 0.97 | 0.98 |

| | `E(0.0412)` | `E(0.045)` |
|---|---|---|
| ODE with this `g(s)` | 0.837123 | 0.826235 |
| consolidated chain (107 nodes, Lemma F) | 0.836998 | 0.826106 |
| committed chain (59 nodes) | 0.836795 | 0.825745 |

The ODE sits 1.2e-4 above the consolidated chain. That is the total left in discretization and
small gate reserves, worth under 1e-6 in θ.

## What the model says

- **Early in the chain the gain is far from its cap.** For `s < 0.03` the HIGH gain is 40–85% of
  `νS`. The binding facet is the inverse cap `r + 2z ≤ F` paired with the plain slot facet
  (`2pS`, which coincides with the parent face). The K-copy inverse facet is about twice as large
  and is not binding. So the early gain is limited by slot cost 2 in the marked inverse moment (atom
  1), and not by faces or slot supply. Using the best of all earlier faces as the HIGH plain
  witness, even separately for each amplitude class, gives exactly the same gain.
- **Late in the chain the gain is at 95–98% of its cap.** There the gate is effectively the
  unmarked condition `ρ(q) + q·t ≤ 1`: the faces at `s ≈ 0.041–0.045` sit on the unmarked
  zero-density boundary `t = 10/(15 − 6q)`, with `q ≈ Λ/(6B)`.
- **Prices (envelope change at `s = 0.0412` / `0.045`):**

  | change | `ΔE` |
  |---|---|
  | perfect marked gain (`g = 1`) everywhere | +1.6e-3 / +1.6e-3 |
  | perfect gain only for `s < 0.03` | +1.1e-3 / +1.0e-3 |
  | gain fraction +0.05 everywhere | +4.5e-4 / +5.2e-4 |
  | exchange rate `6 → 5.94` | +9.3e-4 / +9.8e-4 |
  | unmarked count `ρ` lowered by 0.001 / 0.0025 | +5.2e-4 / +6.0e-4; +1.31e-3 / +1.52e-3 |

  With `dθ/dB_P ≈ −6.7e-3` and `dθ/dB_C ≈ −4e-3`, envelope gains of about 1e-3 at both widths are
  worth about 1e-5. The rebuilt discrete chains of `../atom-targets/README.md` respond about 20%
  more strongly than the ODE: `ε_H = 1e-3` gives +6.3e-4 there against +5.2e-4 here, and
  `ε_H = 2e-3` gives +1.26e-3 against about +1.05e-3. Those chains bind at the cap, where `ε_H`
  also relaxes the amplifier term. So the ODE's prices are good to about 20%.
- **The chain forgets its seed.** If `E` is too high, `X` and hence `q` rise and the slope steepens,
  so perturbations decay (by about 25% per 0.02 of width). This is why re-feeding the natural cost
  is worth 1e-8.

## Consequence

The chain has no slack of its own. Its envelope is fixed by three inputs: the unmarked
zero-density exponent `ρ(ν)` near `ν ≈ 0.5–0.75`, the exchange rate 6, and the slot cost 2 that caps
the early gain. All three are the atoms listed in `../barriers/README.md`.

Run: `python3 chain_ode.py` (seconds).

## Two LOW classes with an older parent (priced, negative)

The idea: rows with density in `[q₁, q₂)` are erased with an older parent `j` (larger `Λ_j/B_j`,
so `q₂ < Λ_j/(6B_j)` is allowed). The HIGH gate then starts at `q₂ > q₁`. The amplifier is shared
by all rows (they are classified after both transforms), so at the pivot it becomes
`a₂ = q₂·gap_j/(Λ_j − 6q₂B_j)`, where `gap_j` is the envelope's excess over node `j`'s line. The
HIGH gate pays `a₂(5 − 6ρ)`.

| node | `d(H+G)/dν` at `ν = q` | net HIGH reserve change, `j` = 1, 2, 3, 5, 8 steps back (best margin) |
|---|---|---|
| 60 | 0.182 | −2.2e-4, −2.9e-4, −3.5e-4, −4.6e-4, −6.2e-4 |
| 70 | 0.175 | −2.2e-4, −2.9e-4, −3.5e-4, −4.6e-4, −6.3e-4 |
| 76 | 0.171 | −2.1e-4, −2.8e-4, −3.5e-4, −4.7e-4, −6.4e-4 |

The gate rises only about 0.17 per unit of density, because the gain fraction falls with `ν`.
The amplifier the older parent needs always costs more. This is consistent with the earlier
"multi-ancestor LOW parents: nothing measurable".

## A first integral (2026-10-25)

With the gain at its cap (`g = 1`, which holds to within 2–5% for `s ≳ 0.035`), `X = E` and
`6q = 15 − 10/E`. The flow becomes

  `E′ = −E(15E − 10)/(E − 15sE + 10s)`.

Write it as `M ds + N dE = 0` with `M = 15E² − 10E` and `N = E − 15sE + 10s`. Then
`(M_E − N_s)/M = 2/E + 3/(3E − 2)` depends on `E` only, so `μ = 1/(E²(3E − 2))` is an integrating
factor. The potential is

  **`F(s, E) = 10s/E + log(3 − 2/E)`, constant along the flow.**

- Lean: `../lean-lab/ChainFirstIntegral.lean` (Lie derivative zero; constancy along solutions).
- Numerically, RK4 from `(0.0135, 0.9)` keeps `F` constant to 1e-13.
- The continuum chain's faces at `s = 0.0412` and `0.045` give `F = −6.2e-4` and `−1.08e-3`. They
  differ because `g ≈ 0.95–0.98` there, not 1. The difference is worth about 1.2e-4 in `E`.

Consequences:
- The late chain is a level curve of an explicit function, so its envelope (and the ceiling it
  feeds) involves a logarithm. It is transcendental rather than algebraic. Nice closed forms of the
  method's inputs (θ = 11/12 − ℓ/4, the corner `R = N/J`, `ρ(ν)`) do not make the optimum algebraic.
- A closed-form or monotone-flow proof of the chain (invariant plus the comparison principle of
  `../lean-lab/MaximalEnvelope.lean`) could replace the finite graph and reach the ceiling. Next
  step: the early regime `g < 1`, where `X = E + (1 − g)s` and `g` comes from the binding facets.

## The p-family: the whole continuum chain in closed form (2026-10-25)

**Gate reduction.** Fix the binding amplitude class `p` of the HIGH count, with its two binding
facets: the marked-inverse budget, inverse branch `(1/(1−p), pF/(1−p))`, and the slot supply, plain
branch `(1, 2pS)` (`../repeated-marks/gain_fast.py`).
- The ρ-terms of the HIGH gate cancel identically, since `αF/(ν + 3k/2) = 10/(15 − 6ν) = 1 − ρ(ν)`.
  The gate becomes the cutoff root `ξ = E + 2ps`.
- Solving for the threshold:

  `6q_p(s, E) = 5((3 − p)E + 4ps − 2) / ((1 + p)E + 4p²s − 2p)`,

  which gives `15 − 10/E` at `p = 0` and `5(5E + 4s − 4)/(3E + 2s − 2)` at `p = 1/2`.

**Each class flow is Darboux-integrable.** The flow `E′ = −6q_pE/(1 − 6q_p s)` (`darboux.py`,
`family_p.py`, `first_integrals.py`):
- has the invariant lines `E = 0` and
  `L_p = (3 − 2p)(5 + p)E + 4p(5 − 2p²)s − 2(5 − 2p²) = 0`;
- has the integrating factor `1/(E² L_p)`;
- has the first integral

  `I_p(s, E) = log(L_p/E) + 2(5 − 2p²)(5s − p) / (5(1 − p)² E)`.

The special cases are `p = 0`: `log(3 − 2/E) + 10s/E` (up to constants), and `p = 1/2`:
`log((11E + 9s − 9)/E) + (36s − 3.6)/E`. Lean: `../lean-lab/ChainFamilyIntegrable.lean`
(gate reduction, threshold formula, Lie derivative zero for every `p`).

**The chain is the switching flow.** The HIGH count's gain is a minimum over classes, so the
binding class maximizes the threshold (`envelope_flow.py`):

  `E′ = −6q*E/(1 − 6q*s)`, `6q* = max_{p ∈ [0, 1/2]} 6q_p(s, E)`, `E(0) = 1`, slope capped at `K = 4.4973108`.

| `s` | E (closed-form flow) | E (continuum ceiling, full 16-gate solver) | `p*` |
|---|---|---|---|
| 0.0135 | 0.9393161 | | 0.500 |
| 0.0200 | 0.9115839 | | 0.491 |
| 0.0300 | 0.8734638 | | 0.347 |
| 0.0412 | 0.8371464 | 0.8371458 | 0.221 |
| 0.0450 | 0.8262533 | 0.8262527 | 0.186 |

The agreement is 6e-7. So the whole face map (gates, fees, Lemma F self cells, caps) contributes
nothing beyond this one-line ODE at the accuracy that matters for θ. The 59-node Lean graph,
Collet's 64 faces and upstream #72's 21,527 count transitions all approximate the same explicit
switching flow. Its only inputs are:
- the unmarked count `ρ(ν) = 1 − 10ν/(15 − 6ν)`;
- slot cost 2, in the inverse facet;
- the slot supply facet;
- the LOW limit `Λ = 6qB` (exchange rate 6);
- the natural seed slope `K = 6κ`.

So the ceiling is an explicit functional of the four atoms.

**The binding class is explicit** (`pstar.py`). `∂_p(6q_p) = 0` is quadratic in `p`:
`s(4s − E)p² − 2s(3E − 2)p + (E − 1)² − Es = 0`, up to a factor −4. Its interior root is

  `p*(s, E) = [s(3E − 2) − √(Es)·(1 − E − 2s)] / (s(E − 4s))`, clipped to `[0, 1/2]`,

and at the maximum `6q* = 5(E − 4s)/(2 − E − 8p*s)`. It matches the numerical argmax to 5 decimals:
`p* = 0.34689, 0.22129, 0.18554` at `s = 0.03, 0.0412, 0.045`. So the chain's vector field is
explicit:
- for `s ≲ 0.02` it is the rational field of `p = 1/2`;
- after that, the algebraic field above (involving `√(Es)`), up to the seed cap `K`.

