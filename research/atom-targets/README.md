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

## The plain fourth moment is the decisive lever (added 2026-10-24, `plain2.py`)

Both source faces are faces of the plain fourth moment with slots: `C` for the count's plain
witness, `P` for the physical numerator. Float model, `θ*` change:

| change | `Δθ*` |
|---|---|
| count face `C` → `(B, Λ) = (1, 2)` (slot cost 2, as in the inverse moment) | −5.8e-5 |
| physical face `P` → `(1, 2)` | −7.6e-4 |
| both | −1.35e-3 |
| modest: `Λ_C 2.90 → 2.85`, `Λ_P 3.01 → 2.95` (2%) | −2.5e-5 |

The numerator's capacity `C_N = (B_P h − 4ℓ)/Λ_P` enters `E` as `−qC/2`, which is why `P` dominates.
The slope is `Λ ≈ 6qB`. The 6 is the descent's defect/allowance ratio from sixth-power row
amplification (`../LOG.md`, "Exact origin of the plain slot cost"). The `q ≥ 1/2` is the LOW energy,
pinned by the HIGH gate.

## Compounded lever map: the chain's feedback is small (added 2026-10-24, `compound/`)

The tables above hold the source faces fixed. In reality the same atoms also enter the source chain
(the HIGH count and the LOW amplifier), so the faces move too. `compound/compound.py` rebuilds the
59-node K = 8 chain with a modified atom, re-selects the faces and re-solves the float return.
`compound/direct.py` applies the same atom with the base chain's faces held fixed. About 10 CPU-minutes
per run.

| change | direct `Δθ*` (faces fixed) | compounded `Δθ*` (chain rebuilt) | feedback |
|---|---|---|---|
| MI slot cost `2 → 1.99` | −2.01e-5 | −2.03e-5 | 1% |
| long exponent lowered by `1e-3` | −3.70e-5 | −3.91e-5 | 6% |
| LOW amplifier exchange rate `6 → 5.94` (1%) | 0 | −5.3e-6 | all |

Base: θ* = 0.87475087 (float model, K = 8 chain faces `C = (0.95609, 2.89662)`,
`P = (0.96076, 3.00926)`).

Consequences:
- The sensitivities are linear and additive to about 5%. The chain does not amplify an improvement in
  the count. The fixed point "better count → lower `q` → flatter faces → better count" contracts
  quickly.
- On its own, the sextic exchange rate needs `6 → 5.89` (1.9%) for −1e-5. A 1% cut moves the count
  face only by `Λ_C 2.8966 → 2.8811` (−0.5%, with `B_C` +2e-4), so the exchange rate reaches the
  faces at about half strength. The physical face's selected pivot changes (0.04 → 0.0395), so its
  two rows are not directly comparable.

## Value of each source-step gate (added 2026-10-24, `compound/gatevoi.py`, `compound/highrelax.py`)

Each source-step gate was disabled or relaxed in turn, then the K = 8 chain was rebuilt. The P face
here is selected without PR #69's `Λ_P > 3` restriction. That restriction only served FR21, which
Lemma D removes, and dropping it moves θ* by −2e-7.

| change | envelope `B − Λs` at `s = 0.0412` | θ* (float) | Δθ* |
|---|---|---|---|
| none | 0.836795 | 0.87475067 | 0 |
| centered gate (G5) disabled | 0.836797 | 0.87475066 | −1e-8 |
| HIGH gate disabled | first node jumps to `(B,Λ) = (0.9785, 2.902)` at pivot 0.0135, then `q < 1/2` stops the chain | — | (≈ +0.022 in envelope) |
| HIGH gate relaxed by `ε_H = 5e-4` | 0.837110 | 0.87474851 | −2.2e-6 |
| `ε_H = 1e-3` | 0.837423 | 0.87474634 | −4.3e-6 |
| `ε_H = 2e-3` | 0.838052 | 0.87474191 | −8.8e-6 |
| `ε_H = 4e-3` | 0.839325 | 0.87472516 | −2.6e-5 (chain reaches `Λ = 3B` at pivot 0.041 and stops at `q = 1/2`) |
| amplifier free in every gate except the LOW construction (all `a`-terms dropped from HIGH, centered, `1 − T − 5a`, `1 − r₀ − T − 4a`, `1 − r₀ − T − 4.5a`, `1/75 − a`, `L − 7a`) | 0.837046 | 0.87474896 | −1.7e-6 |

Reading:
- The HIGH gate alone sets the chain's descent speed. With it switched off, the chain reaches the LOW
  limit `Λ = 6qB` with `q = 1/2` at once, and the face height at the evaluation widths rises by
  about 0.02.
- The marginal value is `dθ*/dε_H ≈ −4.4e-3`, so 1e-5 needs `ε_H ≈ 0.0025`.
- The HIGH gate is `1 − ρ(ν) − νT − a(5−6ρ) + G(ν) > 0` at `ν = q`. Its count part `ρ − G` is the
  same three-line count as the return's (at `ν = 0.505`: 0.556 against R(0.505) ≈ 0.555). So the
  chain route needs a count improvement of 0.0025 at densities 0.5–0.75, about 30 times what the
  return needs directly (`dθ/dR = 0.133`, so 7.5e-5).
- The chain is therefore not a cheap amplifier of count improvements. Once `ε_H ≳ 0.004`, the floor
  `q ≥ 1/2` (LD1) binds next.
- The amplifier's own costs are not the limit either. Making it free in every gate (it still
  shrinks the child scale `F = 1 − 6a` in the LOW construction) gains only 1.7e-6
  (`compound/voi_freeamp.log`). What limits the descent is the non-amplifier part of the HIGH gate,
  `1 − ρ(ν) − νT + G(ν)` at `ν = q`, i.e. the HIGH count itself.

## Natural seed cap and the HIGH gate's binding facet (added 2026-10-24, `compound/seedcap.py`)

Collet allows any fixed seed cap `h0` that the natural capacity inequality permits (sources.tex,
"the first input is the already proved natural theorem G(1,K,h0)"). The chain uses `h0 = 0.055` and
caps `min(0.0549989, s + 0.016)`. Rebuilding the K = 8 chain with a larger seed cap and larger caps:

| `h0` | cap offset | envelope at `s = 0.0412` | θ* (float) |
|---|---|---|---|
| 0.055 | 0.016 | 0.836795 | 0.87475067 |
| 0.065 | 0.016 | 0.836798 | 0.87475065 |
| 0.08 | 0.016 | 0.836798 | 0.87475065 |
| 0.08 | 0.025 | 0.836562 | 0.87475225 |
| 0.08 | 0.035 | 0.836243 | 0.87475442 |

The seed cap is worth 2e-8. Wider caps lose, because the centered gate binds at `b = cap`.

The reason shows in the HIGH gain at the end of the chain (`ν = q`, `b = cap`). Its binding facet on
every late node is the pair (inverse cap `r + 2z ≤ F`, parent face `B₀ − Λ₀z`) at `p ≈ 0.45–0.5`.
The plain cap line `2p·h₀·F` is 4% above it, and the K-copy inverse line is three times above it. A
larger parent cap therefore cannot raise `G`. The binding inverse facet is the same slot cost 2 that
binds the return's count.
