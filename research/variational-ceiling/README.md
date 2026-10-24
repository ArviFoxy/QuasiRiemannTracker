# The face map's continuum limit and the ceiling of the source graph (2026-10-24)

**Question.** The source graph (the chain of faces `G(B, Λ, h)` that feeds the final return) is a
finite DAG. Treat it as a discretization of a variational problem, and find the best envelope
that *any* graph built from the same source-step gates can reach. That is the ceiling of the
face-map approach with the current analytic inputs.

## 1. The face map as a control problem

A face is a line `B − Λz` (plain capacity against slot width `z`) with a cap `h`. The source step
proves a face from a LOW parent and a HIGH parent on the width cells `[b_×, h]`, with a LOW/HIGH
threshold `q < Λ₀/(6B₀)` (the LOW denominator `den = 1 − 6qB₀/Λ₀ > 0`). The gates are the 16 scalar
gates, the weak guard, the special sectors, and the HIGH gate with the repeated-mark gain
(`../repeated-marks/ss_fb.py`). With Lemma F, a node can switch to itself as LOW parent beyond a
join `b₁`, so the cap side costs only the fees.

State: the envelope `E(s) = max_faces (B − Λs)`. Control: the next face's slope and thresholds.
Objective: θ* of the exact return, which depends on the envelope near `s = 0.0412` (physical face)
and `s = 0.045` (count face). The exact evaluation reproduces the consolidated chain:
`E(0.0412) = 0.8369975`, `E(0.045) = 0.8261064`, `θ* = 0.8747257` (`evalfaces.py`).

## 2. The continuum limit and its comparison principle

As the pivot spacing `δ → 0`, a node's LOW and HIGH parents tend to the node itself. The LOW excess
`b + (t − B₀)/Λ₀` tends to the allowance `e` at every width, so the amplifier is
`a = (qe + r)/den` with `den = 1 − 6qB/Λ` (the node's own ratio). The envelope then obeys

  `E'(s) = −Λ_min(s, E(s))`,

where `Λ_min(s, e)` is the flattest slope for which some threshold `q` passes every gate at the pivot
`b = s` and at the cap, for the face `(e + Λs, Λ, cap)` as its own parent (`continuum.py`).
A higher envelope makes the HIGH gate harder, so `Λ_min` is nondecreasing in `e`.
`../lean-lab/MaximalEnvelope.lean` proves the resulting comparison principle: any envelope with
`E' ≤ −Λ_min(s, E)` stays below this solution. Within the continuum class it is the ceiling.

The fees enter here. The amplifier `r/den` costs about `1.5r/den` in the HIGH gate, while `den`
costs `q` (`Δq ≈ (Λ/6B)den`, at about 0.17 per unit `q`). So the optimal `den ≈ √(18r)`: with
Collet's `r = 10⁻⁸` the solver settles at `den ≈ 3.7·10⁻⁴`, about 0.1% in slope.

## 3. The continuum limit is not the ceiling: the lag effect

At the consolidated chain's own points, the continuum needs a steeper slope than the discrete
chain achieved:

| `s` | chain slope | continuum minimal slope at the chain's `(s, E)` |
|---|---|---|
| 0.02 | 4.0831 | 4.0918 |
| 0.03 | 3.5280 | 3.5376 |
| 0.04 | 3.0106 | 3.0166 |

A finite step has a first-order advantage. A hybrid node at pivot `s` with LOW parent at `s − δ` uses
the parent's ratio `R(s − δ) ≈ R(s) + |R'|δ` on its old-parent cells `[b_×, b₁]` around the pivot
(`R = Λ/6B`, `R' ≈ −7.7`). Its self cells start at `b₁ > s`, where the node's line lies below the
envelope (node 0: `q₁ = 0.7434` against `q₂ = 0.7372`, `b₁ = 0.01391 > 0.0135`). To first order:
- the old-parent side gains about `0.17|R'|δ ≈ 1.3δ` in the HIGH gate (0.17 per unit `q`) and pays
  `[q(Λ − 1) + ∂G/∂S]δ/2 ≈ 1.0δ` for sitting at `b_× ≈ s − δ/2`;
- the self side gains about `2Δb` at `b₁ = s + Δb`;
- the price is the old-parent excess `(Λ₀ − Λ)(b − b_×)/Λ₀`, amplified by `1/den₁`, which grows like
  `δ(δ/2 + Δb)/den₁` and limits both.

So the ceiling is a discrete optimum with a finite step. Measured on uniform-step hybrid chains
(density floor 0.45, Lemma F, same gates and fees as the consolidated chain):

| pivot spacing | `E(0.0412)` | `E(0.045)` | θ* |
|---|---|---|---|
| 0.002 | 0.8366036 | 0.8256990 | 0.8747301 |
| 0.001 | (running) | | |
| 0.0005 | (running) | | |
| 0.0005 to `s = 0.0335`, then 0.00025 (consolidated) | 0.8369975 | 0.8261064 | 0.8747257 |
| 0 (continuum) | (running) | | |
