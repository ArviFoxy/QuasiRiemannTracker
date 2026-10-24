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
