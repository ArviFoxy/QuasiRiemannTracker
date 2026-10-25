# The proof in harmonic-analysis terms (briefing document, 2026-10-25)

This is a reading guide to the OpenAI 7/8 proof and Collet's refinement. It is written in the
language of Fourier and Mellin analysis, frames and filter banks. It is meant as the starting
brief for new research rounds. Details and numbers are in `LOG.md`, `barriers/README.md` and the
topic directories.

**One sentence.** Build one object, the *probe*, from the sextic character family, and evaluate it
twice: as a correlation in a Fourier basis (low side) and as a Mellin contour integral (high side).
A zero of the target L-function at `Re s = β > θ` makes the two evaluations contradict each other.

## Translation table

| number theory | harmonic-analysis reading |
|---|---|
| Hecke character `ψ_u` (one row) | one atom: a Fourier basis vector of a multiplicative group |
| family `{ψ_u : u ≤ U}` | a dictionary of `U` atoms |
| large sieve inequality | upper frame (Bessel) bound for that dictionary |
| "diagonal" bound | tight-frame regime: each atom gets its fair share |
| "N-term" | coherence of an undercomplete dictionary |
| Gauss sum | change of basis between additive and multiplicative Fourier bases |
| Dirichlet series / Mellin transform | Fourier transform in log scale |
| dyadic blocks `n ~ U^r` | octave filter bank (uniform bands in `log n`) |
| Möbius / plain / prime blocks | inverse filter `1/L` / the filter `L` / a band of `−L′/L` |
| detector identity `L·M = 1 + tail` | perfect-reconstruction identity |
| Poisson summation, theta reflection | duality transforms trading a long sum for a short one |
| sixth-power copies | exactly repeated atoms, used to complete a frame |
| marks (slots) | modulation by a character, which widens the bandwidth (conductor) |
| probe | matched filter for the target's `1/L` |

## 1. Characters as Fourier bases

Rows `u` are elements of `Z[ω]` of norm `≍ U`. Columns `n` are ideals. The kernel is
`ψ_u(n) = (u/n)₆`.
- **Fixed `u`:** `n ↦ ψ_u(n)` is a Hecke character.
- **Fixed `n`:** `u ↦ ψ_u(n)` is a character mod `n`.
- **Reciprocity:** sextic reciprocity makes the kernel essentially symmetric, so one can Fourier
  transform in either variable.

Gauss sums are the entries of the change-of-basis matrix between additive and multiplicative
characters. Since `|G|² = N(n)`, the two bases are mutually unbiased. Two exact structures carry
the proof:
- **Sixth-power invariance.** `G(u, hp⁶) = G(u, h)`: rows `u` and `ua⁶` carry the same atom.
- **Theta reflection.** Cubic Gauss sums are the Fourier coefficients of Kubota's `θ₃`.
  Modularity turns a sum of length `N` into a dual sum of length `conductor/N`.
  Hasse–Davenport turns Möbius-weighted sextic Gauss sums into `θ₃` coefficients. Order 6 is the
  one explicit case (`LOG.md`, "Why order 6").

## 2. Mellin transforms and the detector filter bank

Perron's formula writes a smoothed sum as a contour integral. Moving the contour trades the sum for
residues; for `1/L` the residues sit at the zeros of `L`. The three filters, all at the zero `ρ`:
- **`M_r`:** Möbius block of length `U^r`, the truncated `1/L`.
- **`S_m`:** plain block, the truncated `L`.
- **`Q_z`:** prime slot, a band of `−L′/L`. By the explicit formula a zero makes every prime band
  coherent (self-saturation).

**Detection (foundations Lemma 14.2) is perfect reconstruction.** `L·M = 1 + tail`. At a zero the
unit term survives, so some subband pair lights up: `|M_r S_m|² ≥ U^{δ(r+m)}`, with
`Re ρ = (1+δ)/2`. The zero-free region caps each subband's gain, so both factors are saturated. The
corner of this bank is triple-tight (`lean-lab/DetectorCorner.lean`).

## 3. The large sieve as a frame bound

`Σ_u |⟨a, ψ_u⟩|² ≤ Δ‖a‖²`.
- **`N ≤ U`:** `Δ ≈ U`, the diagonal.
- **`N > U`:** `Δ = N`, attained by vectors in the span. This is the N-term.
- **Generic sextic bound:** it carries extra Gauss-bias terms. These are sharp (de Faveri; Xu–Sang,
  arXiv:2610.17675).

So the proof bounds only structured vectors whose dual expansions are short:
- **Inverse moment (Möbius vectors):** Poisson in `u` plus theta reflection. Diagonal for
  `N ≤ U^{1−c}`.
- **Plain fourth moment:** reflect both plains. Diagonal up to total length 1.
- **Amplification:** embed rows via `ua⁶` into a family of size `N`. This gives
  `Σ_u|M_u|² ≤ U^{1/6}N^{5/6}`, the long line `(1+5t)/6`, exchange rate 6 (`barriers/` atom 2).
- **Marks:** after Poisson a slot modulates the dual by a cubic character and raises its
  conductor by `N(P)²`. Between `K` and `K·N(P)` lies a dead zone with no reflection, where the full
  N-term is paid. That is slot cost 2 (atom 1; `atom1/README.md`, `lean-lab/MIBranches.lean`).

## 4. The count

Chebyshev against the frame bounds gives three lines for `log_U #(bad rows)` (Collet NR1):
- `I(r) = 1 − δ(p + (1−p)r)`: marked inverse moment.
- `P(m) = 1 − 2δm − 2δp·z(m)`: plain fourth moment with slots, slot cost `Λ` from the source faces.
- `L(t) = 1/6 + (5/6 − δ)t`: amplified long moment.

At the binding bin `δ ≈ 0.455` they cross at `R ≈ 0.604`, with `r* + m* = t*`. In zero-density terms
the count is about `U^{2.22(1−σ)}` at `σ ≈ 0.727`.

## 5. The probe: a matched filter

**Low side** (7/8 §6, §12–15).
- The probe is a correlation `Σ_m A_m B_m`. `A` is a Gauss-sum polynomial; `B` is a completed
  cubic-theta row carrying the probe's prime marks (total length `ℓ`).
- Poisson in `m` puts the target's own `1/L` on the sixth-power frequencies `k = a⁶e₀`. That is the
  signal channel.
- Cauchy–Schwarz with the marked energy (Theorem 7.1, `x + y + ℓ ≤ 1`) gives
  `β ≤ θ_low = 11/12 − ℓ/4`.
- The 1/12 bias is exactly the signal (`lean-lab/SignalChannel.lean`).

**High side** (7/8 §19–20; Collet (192)–(223)).
- Per row, the Euler product gives `numerator × slots × 1/L(s, ηψ̄_u)`.
- Shifting the contour picks up the target's residue and the bad rows' leakage.
- The leakage is bounded by `(#bad)^{3/4}·(energy)^{1/4}`. This produces the balance
  `3ℓ/4 + δ/2 + δp(ℓ − C/2) + (3h/4)R = 5/12 + 5h/12` (`lean-lab/BalanceAlgebra.lean`), and
  `θ = 11/12 − ℓ/4` at the largest admissible `ℓ`.
- For `η = 1` one zero saturates the denominator, the slots and the numerator together.

## 6. The source chain

A face `G(B, Λ, h)` is a certified plain fourth moment with slot cost `Λ`, valid on the half-plane
`m₁ + m₂ + Λz ≤ B`. Each step thresholds the slot outputs: LOW rows are deleted pointwise, HIGH
rows are counted by the detector bank. Better counts give cheaper slots in the next face. Our
improvement repeats slot filters `K` times in the HIGH count's inverse witness (foundations
Lemma 8.1; `repeated-marks/`). That gives the Lean value 0.8747289.

**The faces are tangent lines of one explicit curve** (`chain-ode/README.md`). The unproven region
of (plain length, slot width) is convex; the faces are its supporting lines; in the limit they are
the tangents `(B, Λ) = (E − sE′, −E′)` of the envelope `E(s)` (a Legendre transform). The gate is
the ODE `E′ = −6q*E/(1 − 6q*s)` with the closed form
`6q* = 5(√E − 2√s)²/(2 − E − 4√(Es))` for the binding class (`lean-lab/ChainSwitching.lean`).
Each class flow is solved by Lambert W. Ceiling about 0.874724. Only the regular HIGH gate at
`ν = q` binds, and half its value lies in the last 0.01 of slot width (`ν ≈ 0.51`, `p ≈ 0.2`).

**Why this curve** (`chain-structure/README.md`). The closed form is an exact AM–GM balance over
amplitude classes between the slot term `4s` and the plain term `E`, written as a sum of squares
(`lean-lab/ChainAMGM.lean`), so it is the maximum over all classes. Each class flow has the
zero-length line `E = 0` as a double invariant line, whose exponential factor `exp((5s − p)/E)` gives
the Lambert W solutions (`lean-lab/ChainLambertOrigin.lean`). The switching flow has no invariant
curve of degree ≤ 2 besides `E = 0`. Within the method the curve is optimal up to 0.9e-6, so only
the atoms move it.

**The proof now uses this curve** (`faceless-chain/README.md`). The Lean source chain is one
family of faces, the secant lines of a five-piece cubic envelope following the flow, each piece
certified for all its 2¹⁶ faces at once. The proof reaches 34989/40000 = 0.874725
(`Candidate.bound_sharp`); the declared statement stays 8747289/10^7.

## 7. Why it is stuck

- **Fourier steps preserve an invariant.** Poisson and theta reflections generate an affine
  reflection group (C̃₂, D̃₄) with an invariant linear form (`lean-lab/FEGroup.lean`). Only exact
  symmetries (Hecke operations) move it, at the fixed rates 6 and 3.
- **Marks open the dead zone.** Closing it needs slot-twisted cubic Gauss-sum vectors to be nearly
  orthogonal to the span of the quadratic characters (Lindelöf on average for twisted theta series).
  The GL(2) analogue, uniform in the level, is open.
- **The corner is triple-tight.** Escaping it needs smoothness of the Möbius profile across scales,
  hence control of zero clusters.
- **The unmarked count is a lattice game** (`round9/README.md`, `lean-lab/ZeroDensityGame.lean`).
  The extremal adversary is the two-term model `L ≈ 1 + bU^{−s₀(s−a)}`, `s₀ = 5/(15 − 6ν)`, whose
  saturated lengths form the lattice `s₀ℕ`. It defeats every count that depends only on length.
  Only the long moment at `3s₀` moves `ρ(ν)`, with sensitivity `4ν/(5 − 2ν)`.
- **High side:** the triangle inequality over bad rows is intrinsic, since phases align by tiny
  height shifts.
- **Low side:** the bias is the signal.
- **Why order 6.** Absorbing μ into one Gauss sum needs a quadratic subcharacter (Hasse–Davenport).
  The leftover cubic Gauss sums must be explicit theta coefficients, which on `GL(2)` exist only
  for orders 2 and 3 (Kazhdan–Patterson). The leftover twist `χ⁻³` must be quadratic for the sharp
  quadratic sieve. Only `6 = 2·3` does all three. Order `n` would give the baseline `1 − 1/(2n)`.
- **The common root of the atoms (P1).** The column branch (and the inverse moment past its
  diagonal) is:
  - a reciprocity-signed dual form, where positivity re-creates the `N` term;
  - built from sextic Gauss sums after the second Poisson step, i.e. Kazhdan–Patterson again;
  - Lindelöf on average for quadratic twists of `θ₃` in a family thinner than its critical length.
  Each of these is open even in the `GL(2)` analogue.
