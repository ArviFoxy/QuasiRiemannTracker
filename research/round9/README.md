# Round 9: why the zero-density exponent is what it is (2026-10-25)

Context: the Lean proof reaches 34989/40000 = 0.874725 (`Candidate.bound_sharp`). The milestone
0.8747189 needs 6.1e-6 more. The chain and the return are at their ceiling, so the missing amount
has to come from an analytic input (`../LOG.md`, "Revision … after rounds 7–8").

## 1. The unmarked count is a lattice game, and only the long line can move it

The late chain's binding gate contains the unmarked zero-density exponent
`ρ(ν) = 1 − 10ν/(15 − 6ν)` at `ν = q ≈ 0.45–0.5`. Lowering it by 0.001 there is worth about 5e-6
in θ (`../chain-ode/README.md`, prices). Xu–Sang (2610.17675) found the same exponent as
`(31 − 32σ)/(21 − 12σ)`. It is assembled from three inputs:

- **I:** the inverse moment. A saturated Möbius block of length `y ≤ 1` counts `1 − νy`.
- **P:** the plain fourth moment. A saturated plain block of length `m ≤ 1/2` counts `1 − 2νm`.
- **L:** the sixth-power amplified long moment. A Möbius block of length `y ≥ 1` counts
  `(1 + 5y)/6 − νy`.

Prop. 8.3 of the 7/8 paper gives every bad row, for every `t ∈ [1, 3/2]`, a saturated pair
`(M_r, S_m)` with `r ≤ t ≤ r + m` and `m ≤ 1/2`.

**Statement** (`../lean-lab/ZeroDensityGame.lean`, proved):
- The defender's best detector length is `t* = 3s₀`, where `s₀ = 5/(15 − 6ν)`, and the count there
  is `ρ(ν)` (`count_ge_rho`, `count_at_tstar`).
- The adversary whose saturated lengths form the lattice `s₀ℕ` supplies a pair for every `t`
  (`lattice_pairs`). Every product witness `M^i S^j` it offers has length `ks₀` and counts at least
  `ρ` (`lattice_counts_ge`, `lattice_plain`). So `ρ` is exactly the value of the game.
- The explicit adversary is the two-term model `L(s) ≈ 1 + b U^{−s₀(s − a)}` with `|b| = 1`. It
  gives `1/L ≈ Σ(−b)^k U^{−ks₀(s−a)}`, so the Möbius blocks are saturated at `ks₀` and vanish in
  between, and the plain block is saturated at `s₀`.
  - The model meets every constraint the count uses: the zero-free bounds right of `a + 6e` and
    the reflected bound, which needs `s₀ ≤ 1/2`.
  - It is the `d = 1` case of round 7's resonance model.
  - Its zeros sit on `Re = a` with density `s₀/(2π)·log U`. The Littlewood plus fourth-moment
    count of round 7 gives `1 − 2νs₀ = ρ` for it.
- **Why `15 − 6ν`.** Two lattice steps must fit below the diagonal threshold 1 and three must
  reach above it (`2s₀ ≤ 1 ≤ 3s₀`). The adversary balances the diagonal count at `2s₀` (I, and
  equally P at `s₀`) against the long line at `3s₀`:
  `1 − 2νs = 1/6 + (5/6 − ν)·3s` gives `s = 5/(15 − 6ν)`.

**Consequences.**
- Every count that depends only on a witness's length is defeated at the same value: mixed
  moments `M·S`, products, prime blocks, Hölder or fractional moments, detectors with larger `t`,
  and several `t` at once. The lattice adversary's saturated objects all have lengths in `s₀ℕ`.
- Only the long moment at `y = 3s₀ ∈ [1, 3/2]` matters. Lowering its exponent by `ε` lowers `ρ` by
  `ε·4ν/(5 − 2ν)`, which is 0.44ε at ν = 0.45 and 0.5ε at ν = 0.5 (`rho_sens`, proved; numerics
  in `lattice_game.py`).
- **Any long witness will do, but only one kind has a moment.** The adversary's witnesses of
  length `3s₀` are `M_{3s₀}`, `M_{2s₀}S_{s₀}` and `S_{s₀}³`. A bound below `(1 + 5y)/6` at
  `y = 3s₀` for any of them would lower `ρ`. Only the Möbius block has a proven long moment
  (amplification of the inverse moment).
  - A plain sixth moment `Σ_u|S_{s₀}|⁶` is out of reach. It is not available even at total length
    `≤ 1`, because a third plain factor costs `6κ` (`../lean-lab/DeletionRate.lean`).
  - The mixed products have no moment at all past the diagonal.
- **The long moment cannot be bootstrapped from zero counts.** A row whose zeros all lie left of
  `(1 + δ′)/2` has `|M_u(U^t)|² ≤ U^{tδ′}`. Summing `U^{ρ(δ′) + tδ′}` over bins gives 1.1667 at
  `t = 1.155` and 1.2273 at `t = 1.25`, worse than the amplified 1.1292 and 1.2083.
- **The long line is self-referential beyond the diagonal.** For `D > U`, a bad row contributes
  `D^δ` to `Σ_u |M_u(D)|²`, more than its diagonal share. So a diagonal bound there already
  implies the count of rows saturated at length `D`, and is at least as hard as the count it would
  feed. Amplification escapes this only by moving into a family where `D < H`.
- **What the bar needs, in this language.** Lower the amplified exponent `(1 + 5t)/6` by about
  1.6e-4 at `t ≈ 1.155` (the HIGH count's corner). Equivalently, one of:
  - a sixth-power-free family bound `Σ_u |M_u(D)|² ≪ U + D^{1−η}U^η` with `η ≥ 1/6 + 1.03e-3`
    (amplification is the case `η = 1/6`);
  - the full-family diagonal (17.87) up to `D = H^{1 + 1.7e-4}`.

  In the inverse-moment proof the obstruction past `r = 1` is the column branch. With Möbius
  coefficients this should be P1 with `μ` in place of the slot sum (`../P1_PROBLEM.md`); this has
  not been checked line by line.

**What is new here.** The three-line balance (`../lean-lab/ReturnAlgebra.lean`), the triple-tight
corner (`DetectorCorner.lean`) and the λ test for the long line (`JointNumerator.lean`) were
already proved. The new parts are:
- the extremal adversary, together with the proof that no count depending only on length beats
  it;
- the closed-form sensitivity;
- the failed bootstrap.

Files: `lattice_game.py`, `lattice_game.log`, `../lean-lab/ZeroDensityGame.lean`.

## 2. Fresh-framing agent (`fresh_framing/README.md`)

- **No per-row lever.** In one row of the binding class, all of these co-occur:
  - the count corner;
  - slot saturation at `p = 1/2`;
  - the Hölder-critical numerator (length `n₀ = 0.418`);
  - the saturated long Möbius sum.

  Round 7's resonance model had to be repaired first: with a fixed small degree its slot sums
  vanish at generic lengths. A fine lattice with a Beatty set coprime to its period keeps the dip
  and `p = 1/2` together. A perturbation `L = P(Y)(1 + εY^{j₀})` covers the numerator with a dip
  margin of −3e-4. With one face for both uses, the refill decays at `δ(1 − 2p/Λ)/2` against the
  tent's `δ(1 − p)/2`, so the two are compatible iff `Λ > 2`.
- **One new candidate (B): restrict the dual sixth-power content.**
  - After Poisson the dual frequency is `H = u·a⁶`, and the probe's weight sees only `N(H)`.
  - Dropping the frequencies with `N(a) < Z^{ε′/6}` removes the top rows (`q_u > Z^{h−ε′}`) and
    leaves the principal row almost all of its `Z^{h/6}` copies.
  - The high side's top moves to `h − ε′`, worth `Δθ ≈ −(0.09–0.13)ε′` before the low side.
  - On the original side the restriction is a non-integral shift of `χ_A(m)`, and the restricted
    pieces have no low-side bound. The agent priced the naive version at break-even.
  - Not proved impossible. Logged as an open candidate.
- Otherwise the agent confirms the atoms: P1 use (a) for the actual smooth prime vector
  (`η ≥ 0.0085`), and the long line (`λ ≥ 0.1676` at `t = 1.155`).

## 3. Candidate (B) priced: the dual sixth-power restriction is a dilation of `X` (closed)

The probe is `Σ_m F(m)W₀(q_m/Q)` with `F` periodic modulo `M = b*·s·c` and `Q = q_{b*}XY`
(7/8 paper (6.1)). Poisson gives the dual frequencies `H`, with weights `F̂(H)Ŵ₀(HQ/M)` and range
`H ≲ Z^h`, `h = 1 + ℓ − x`.

**The restriction is an `X`-dilation.**
- For `b` prime to `M`, the arithmetic factor is a product of sextic Gauss sums, so
  `F̂(b⁶H) = F̂(H)`.
- Hence `Σ_H F̂(b⁶H)Ŵ₀(b⁶HQ/M) = N(b)^{−6}·Σ_m F(m)W₀(q_m/(QN(b)⁶))`.
- With the probe's `X^{−1/2}` normalization, keeping only the frequencies with `b⁶ | H` is the probe
  at `X·N(b)⁶` with weight `N(b)^{−3}`.
- Write `1_{a(H) ≥ A₀} = Σ_{b⁶ | H} f(b⁶)`, where `a(H)⁶` is the sixth-power part of `H`. The
  Möbius transform `f` is supported on `N(b) ≥ A₀`, with `|f| ≤ d(b)`. So the restricted probe is
  `Σ_{N(b) ≥ A₀} f(b⁶) N(b)^{−3} I_η(X·N(b)⁶, Y, Z)`, plus corrections for `b` not prime to the
  moduli.

**Signal.** Each term carries `N(b)^{−3}·(N(b)⁶)^{1/3} = N(b)^{−1}` times the signal, through the
outside power `X^{1/3}Z^{s−5/6}Z^{ℓ/6}`. Then `Σ_b f(b⁶)/N(b) = 1`, which is the residue of the tail
of `ζ(6z)`, so the signal is preserved, as the agent said.

**Low side.**
- Every dilated term has the same `Y` and slot length `ℓ` but `x′ ≥ x + ε′`. So it violates the
  marked-energy wall `x + y + ℓ ≤ 1`, which is tight at the optimum, and its energy pays the
  dead-zone (`N`-term) excess.
- Even before the wall, the terms weigh `N(b)^{−3 + 6g}`, where `X^g` is the growth of the raw
  low bound at fixed `Y`.
  - With `g = 7/12` (outside power `X^{1/3}` times the `x`-slope `1/4` of
    `θ_low = 2/3 + (x + y)/4`) the sum is dominated by the largest `b`.
  - With `g = 5/12` (Gram diagonal `X^{1/2}` times the bias `X^{−1/12}`) it converges, and
    `θ_low` rises by about `ε′/12`. That is about the high-side gain `0.09ε′`: the agent's
    "break-even".
  - Either way the wall cost comes on top.
- Taking the base probe at `x − ε′` instead extends the dual range to `h + ε′`, and the restriction
  then removes exactly that extension. The top is back at `h`.

**Verdict.** Within this probe the top of the high side moves only with `x`, and `x` is already at
its optimum. Restricting the dual sixth-power content is a reweighted `X`-dilation whose low side
is worse. The high-side gain would need a probe whose low estimate does not grow with `X`. The
marked-energy wall says that is P1 (use (b)). Closed.

## 4. Numerics: the long Möbius moment is at its diagonal (`numerics/README.md`)

For the actual sextic family over `Z[ω]` (778 rows at `U = 3000`, 2076 rows at `U = 8000`), the
mean of `|M_u(U^t)|²` stays within 0.89–1.08 of its diagonal for `t` from 0.6 up to 1.4. Over
that range amplification allows a factor up to 20 (`t = 1.4`). So atom 2 is an artifact of the
method, like P1 in round 7's toy models.

A proof would need square-root cancellation in a Möbius bilinear form whose kernel is incomplete
sextic character sums of conductor up to `D² ≫ U`. That is a twisted Chowla-type correlation on
the wrong side of the parity barrier. Even the full family of characters to one modulus needs
Möbius correlations for this; only averages over moduli (Barban–Davenport–Halberstam) avoid them.
