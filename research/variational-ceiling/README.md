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

(results below)
