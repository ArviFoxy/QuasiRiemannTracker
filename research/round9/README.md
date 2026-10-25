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
