# Round 9, fresh-framing agent: report (2026-10-25)

Brief: question the framing of the remaining 6.1e-6 and name the assumption that, if false, would
make it easy. This note condenses the agent's report. The claims are the agent's own unless marked
as checked here.

## Bottom line

No change was found that gets 6.1e-6 without a new mean-value input. In one row, all of the
following co-occur:
- the count corner;
- slot saturation at `p = 1/2`;
- the Hölder-critical numerator;
- the saturated long Möbius sum on the high side.

So no argument made one row at a time can move θ. Only family-level inputs (the atoms) remain.

## What binds

The binding is one equation at `(δ, p, d) = (0.4546, 1/2, h)`, as in `../../return-slack/README.md`.
Each term is either an exact normalization or the capacity of one family mean value.
- `a = (1+δ)/2`: the `s`-contour sits just right of the row's bin.
- `−y/2`, `−ℓ/2`: normalizations.
- `h/4`, `3hR/4`: Hölder against the slotted plain fourth moment.
- `−h/6`: after Poisson the dual frequency is `H = u·a⁶`, and the weight sees only `N(H)`. So the
  top rows (`q_u ≍ Z^h`) get `a = 1` only, while the principal row has `Z^{h/6}` sixth-power copies.
- `R`: the I/P/L corner.
- `C`: the chain.

All relevant heights are `O(1)`, so the triangle inequality, Chebyshev, the sup over external
tuples and the dyadic splits cost only logs. The only power losses are the restored dual
diagonals inside the mean values:
- the I-line column branch;
- the energy wall;
- the amplification ball;
- the plain descent's ratio 6.

The contour `Re w = 1 − a − 6e` is optimal (Phragmén–Lindelöf alternatives are worse because
`Y > U^{1/2}`). Hölder at exponent 4 equals the layer-cake optimum.

## The interpolation lemma, repaired (round 7's dismissal upheld)

**The gap.** Round 7's resonance model has degree `d ≤ 43`. Its `−L′/L` lives only on the
discrete scales `U^{n·m*/d}`, so at generic slot lengths the model sits in amplitude class `p ≈ 0`,
not in the binding class `p = 1/2`.

**Fine lattice** (`fine_resonance.py`). With `d` up to 3200 and a Beatty set whose period is
coprime to `d`:
- every coefficient of `P` and `1/P` stays at most 1;
- the gap `(r*, t*)` stays exact;
- the slot sums at every scale stay a constant fraction of a single zero (median `|p_n| = 0.44`,
  minimum about `1/d`).

So the dip and `p = 1/2` co-occur. The vanishing `p_n` in the first runs was a `gcd(d, k₂) > 1`
artifact.

**Numerator length** (`perturbed_resonance.py`). The return's numerator has length
`n₀ = 0.418 > m* = 0.414`. The adversary uses `L = P(Y)(1 + εY^{j₀})` with `ε = U^{−0.00075}`:
- the Möbius gap is refilled only at level `ε^k`;
- the refill decays at 0.187 per unit `r` against the tent's 0.114;
- the dip margin is exactly −3e-4, so the corner survives.

With one face for both uses, the refill decays at `δ(1 − 2p/Λ)/2` against the tent's
`δ(1 − p)/2`. These are compatible iff `Λ > 2`, which holds (`Λ ≈ 2.9`).

## Assumptions that would make it easy

- **(A) Arbitrary slot coefficients.** Lemmas 17.1, 18.1 and 14.3 are proved for arbitrary bounded
  slot coefficients, but the application uses smooth prime weights times fixed characters.
  Dropping the generality is P1 in its use (a) form (`η ≥ 0.0085` at `N/K = U^{0.129}`).
  - Averaging over the slot height `τ` gives only the Frobenius norm, which equals the `N`-term.
- **(B) The dual weight sees only `N(H)`.** If the dual frequencies with sixth-power part
  `N(a) < Z^{ε′/6}` could be removed, the top rows would vanish while the principal row loses only
  a negligible part of its copies.
  - The top would move to `h − ε′`. `E` has slope 0.40 in `d` there (0.58 counting the
    `K₀^{1−6z₀}` factor), so `Δθ ≈ −(0.09–0.13)ε′` before the low side is paid.
  - Restricting `H` by its sixth-power content corresponds, on the original side, to non-integral
    shifts of `χ_A(m)`, and the restricted pieces have no low-side bound.
  - The agent priced the naive combination of `K₀` pieces as about break-even even under
    optimistic assumptions, and expects the route to fail, but did not prove it impossible.
- **(C) For `η = 1`, one zero drives the denominator, the numerator and the slots.** This is
  forced: the numerator must be the row character to keep the principal pole, and the slot main
  part `Σχ_p(u)` carries no `η` (16.10).

## Candidates, by size

1. The dual sixth-power restriction (B): about `−0.1ε′` before the low side. It needs a
   Gram × energy bound for the probe with its dual restricted to `N(a) ≥ Z^{ε′/6}`, at a cost
   below `0.11ε′–0.16ε′` in `θ_low`. Expected to fail (a guess).
2. P1 use (a) for the probe's actual smooth prime vector:
   `Σ_{k≤K}|Σ_{n~N} c(n)(n/k)₂W|² ≤ (K + N^{0.9915}K^{0.0085})‖c‖²` at `N = K·U^{0.129}`, with
   `c(n) = g̃(n)Π_i A_i(n)`.
3. The long line: `λ ≥ 0.1676` at `t = 1.155`.
4. Within the method, the face family is 0.9e-6 above the continuum ceiling, so any of the above
   stacked with the ceiling needs about 5.2e-6.

Caveat: the resonance models are analytic models of single L-functions. They show that arguments
made one row at a time cannot work; they do not show the adversary exists in the family.

Files: `fine_resonance.py`/`.log`, `perturbed_resonance.py`/`.log`.
