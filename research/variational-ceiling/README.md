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
`b = s` and at the cap, for the face `(e + Λs, Λ, cap)` as its own parent (`continuum.py`;
`continuum2.py` is the same solver with warm starts). Checking the two endpoints is exact. With a
self parent the amplifier `a` does not depend on `b`. The scalar gates and the special sectors are
then affine in `b`, through `T(b) = t(b) + b`. The HIGH gate is affine plus a minimum of affine gain
forms, hence concave in `b`. So every gate attains its minimum over `[s, cap]` at an endpoint.
A higher envelope makes the HIGH gate harder, so `Λ_min` is nondecreasing in `e`. Measured:
`Λ_min(0.025, E ± 0.002) = 3.7683 / 3.8128 / 3.8580` and `Λ_min(0.04, E ± 0.002) = 2.9720 /
3.0166 / 3.0620` around the chain's heights, i.e. `∂Λ_min/∂E ≈ 22.5`. So a height perturbation
decays like `e^{−22.5Δs}`. The envelope at the evaluation widths is set by the gates over the last
few hundredths of width, and the seed is forgotten.
`../lean-lab/MaximalEnvelope.lean` proves the resulting comparison principle: any envelope with
`E' ≤ −Λ_min(s, E)` stays below this solution. Within the continuum class it is the ceiling.

The fees enter here. The amplifier `r/den` costs about `1.5r/den` in the HIGH gate, while `den`
costs `q` (`Δq ≈ (Λ/6B)den`, at about 0.17 per unit `q`). So the optimal `den ≈ √(18r)`: with
Collet's `r = 10⁻⁸` the solver settles at `den ≈ 3.7·10⁻⁴`, about 0.1% in slope.

## 3. The discrete chain is a first-order (Euler) scheme for the continuum

The chain builder (`../cap-induction/hybchain2.py`) places each new node so that it crosses its
parent's line at its own pivot. So the envelope at the pivots obeys `E_{k+1} = E_k − Λ_k δ`: an
explicit Euler step with the node's slope. Two first-order effects compete:

- **At the pivot the node is flatter than the continuum.** Its old-parent cells use the
  predecessor's larger ratio `R(s − δ)`, and its self cells start at `b₁ > s`, where the node's line
  lies below the envelope. At the chain's own `(s, E)` the continuum needs 4.0918 / 3.5376 / 3.0166
  where the chain used 4.0831 / 3.5280 / 3.0106 (`s = 0.02 / 0.03 / 0.04`).
- **The slope is frozen over the step while the true slope falls** at `|Λ'| ≈ 55`. Over
  `[0.0195, 0.02]` the continuum averages 4.1068 against the chain's 4.1110.

The second effect wins, about `(|Λ'|/2 − 19.4)δ ≈ 8.3δ` of slope per unit width. With the
contraction `∂Λ_min/∂E ≈ 22.5`, the height gap relaxes toward about `8.3δ/22.5`. So **finer is
better, and the continuum limit is the ceiling**, consistent with the comparison principle. The
gate is hardest at the smallest width of a node's cell, so a node's slope is always pinned at the
start of the interval where its line is used. Shifting the crossing does not make the scheme
second order; only a smaller `δ` closes the gap.

Measured (density floor 0.45, Lemma F, same gates and fees as the consolidated chain):

| pivot spacing | `E(0.0412)` | `E(0.045)` | θ* |
|---|---|---|---|
| 0.002 | 0.8366036 | 0.8256990 | 0.8747301 |
| 0.001 | 0.8368603 | 0.8259606 | 0.8747273 |
| 0.0005 | (running) | | |
| 0.0005 to `s = 0.0335`, then 0.00025 (consolidated) | 0.8369975 | 0.8261064 | 0.8747257 |
| 0 (continuum) | (running) | | |

Height gap continuum − consolidated chain: +3.0e-5 at `s = 0.0135`, then +3.4e-5, +3.8e-5, +4.2e-5,
+4.7e-5, +5.1e-5, +5.5e-5 at `s = 0.0155, …, 0.0205` (still growing).

## 4. Fees

The fee schedule `(e, r, f)` (allowance, low fee, high fee) is part of the face map. The amplifier
of a self cell is `a = (qe + r)/den`, so the LOW denominator trades `r/den` in the gates against
`den` in the threshold. At the optimum `den ≈ √(14.8r)`, and the cost is about `8.85√r` in
log-slope: 0.09% at Collet's `r = 10⁻⁸` (the solver settles at `den ≈ 3.7·10⁻⁴`), and 100 times less at
`r = 10⁻¹²`, where the solver settles at `den ≈ 3.7·10⁻⁶`. PR #71's recost of Collet's graph used
exactly this freedom: the fine tuple `(10⁻¹⁷, 10⁻¹², 10⁻¹⁰)` that the accepted source theorem permits.
The same recost applies to our graph (`hyb_fees.py`, `continuum.py … 1e-17,1e-12,1e-10`).

| run | `E(0.0412)` | `E(0.045)` | θ* |
|---|---|---|---|
| consolidated chain, fees `(10⁻¹², 10⁻⁸, 10⁻⁷)` | 0.8369975 | 0.8261064 | 0.8747257 |
| same pivots, fees `(10⁻¹⁷, 10⁻¹², 10⁻¹⁰)` | (running) | | |
| continuum, fine fees | (running) | | |

## 5. Conclusion

(pending the runs)
