# Quantitative targets for the binding atoms

How far each binding estimate must move to lower θ by 1e-5. Computed with `targets.py`, a float model
of the final return (FR13) with a generic LP count (inverse, plain and long witness lines, plus the
natural count). Faces are the consolidated Lemma-F chain's (`../cap-induction/chain_h45.json`) with
h = 401/500.
- The model's base value is θ* = 0.8747496. The exact certificate gives 0.8747266; the model omits
  the admission windows and the affine/capped candidates.
- It finds the same binding point as the exact return: d = h, δ ≈ 0.452, p = 1/2, top conductor edge.

| atom | where it comes from | current | change needed for −1e-5 |
|---|---|---|---|
| inverse-moment budget, r + 2z ≤ m_I | MI column branch: reflected length T_d ≤ F_c (`../lean-lab/MIBranches.lean`) | m_I = 1 | m_I = 1 + 5.9e-4 |
| inverse-moment slot cost, r + s_I z ≤ 1 | slot primes in the conductor of the second reflection | s_I = 2 | s_I = 1.995 |
| long Möbius moment, exponent (a_L + b_L r)/6 at r ≈ 1.155 | sixth-power amplification u ↦ ua⁶ | (1+5r)/6 | lower by 2.7e-4 (or b_L = 4.9987) |
| physical face P, height B_P | source chain (LOW/HIGH, amplifier 6) | 0.9610 | +1.5e-3 |
| physical Gram coefficient c_g in θ = k + x/2 + c_g(y − x) | sixth-power frequencies k = e·r⁶ in the Gram lemma 14.1 (sextic theta residue), the P_a^{1/6} term | 1/12 | 1/12 − 1.27e-4, i.e. P_a^{1/6} → P_a^{1/6 − 2.5e-4} |

In this model the count face C showed no first-order effect at the binding point. The exact
evaluation in the previous session gave dθ/dB_C ≈ −4e-3, so 2.5e-3 of face height.

Reading guide:
- The long branch and the physical Gram term need the smallest relative changes. Each is a single
  power saving of about 2.5e-4 in one exponent.
- Both are sixth-power phenomena. One is the amplification exchange rate 6. The other is the
  redundancy count (P_a)^{1/6} of sixth-power frequencies, which is real: it is the residue (bias)
  term of sums of sextic Gauss sums.
- A saving in either must come from cancellation that is invisible to absolute values over the
  sixth-power-invariant directions.

Run: `python3 targets.py` (about 20 minutes).

## The probe geometry carries the same slot cost (added 2026-10-24)

The physical probe's only binding geometry constraint is the marked energy (Collet foundations (198),
Theorem 7.1):

$$M+2z\le N_*\quad\text{with}\quad M=x+y,\ z=\ell,\ N_*=1+\ell,\qquad\text{i.e.}\quad x+y+\ell\le1.$$

The `2z` is the same active-slot term `T_d = 2H + 2z_a − N_*` of the reflected energy (paper
Lemma 14.3) that gives the inverse moment its slot cost 2.

With the true signal shift `k = 5/6 − x/3 − ℓ/6`, `θ_phys = 5/6 − ℓ/6 + (x+y)/12`. Allowing
`x + y + ℓ ≤ 1 + ε` (so `y → y + ε` at fixed `x, ℓ, h`) and re-solving the return in the float model
(`me.py` variant of `targets.py`):

$$\frac{d\theta^*}{d\varepsilon}=-0.0628 .$$

This is linear for `ε ≤ 1e-3`. So:

| atom | change needed for −1e-5 |
|---|---|
| marked-energy relaxation `ε` | `1.6e-4` |
| marked-energy slot cost `c` in `M + cz ≤ N_*` (`ε = (2−c)ℓ`, `ℓ ≈ 0.1676`) | `2 → 1.99905` |
| same slot cost in the count's inverse moment (table above) | `2 → 1.995` |

The probe geometry is therefore about five times more sensitive to the reflected-energy slot cost
than the count is.

A soft version does not help. Past the constraint, the column branch (dual length `v ≤ H + η`)
costs the full excess, `Σ|T|² ≪ Z^{M+η}`, which is `η/2` in the low bound. Re-solving gives
`Δθ ≈ (−0.0627 + 0.389(1−ω))η` if the column branch kept only a fraction `1−ω` of the excess. A gain
needs `ω > 0.84`: an almost diagonal quadratic large sieve at dual length `K^{1+η}` for the reflected
Gauss-sum coefficients. That is the same metaplectic Lindelöf-type input as before (see
`../LOG.md`, "Amplifying the rows of the MI column branch").
