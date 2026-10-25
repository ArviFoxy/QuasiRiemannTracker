# Upstream PR 74 (Sil, "fourth-power source moments"): analysis (2026-10-25)

PR 74 is the new bar: 1749387/2000000 = **0.8746935**, 3.54e-5 below our PR 73 (0.8747289). The
target for us is now 1e-5 below it, **≤ 0.8746835**. Our single-stage follow-up (0.8747252) is
behind it.

Source: `upstream` = GTimG/QuasiRiemannTracker, `refs/pull/74/head` = `bf20f0d3`, author Sil
(TheSil). The submission `submissions/sil-fourth-power-20261025/` has 478 Lean files (about 106k
lines) in `src/Candidate/FourthPower/`, no README. Upstream main's latest verified entry is still
PR 71.

## 1. What it does

- **Builds on** the OpenAI baseline, Collet's PR 69 (generic source, counting and transport) and
  PR 67 (two-level affine bootstrap, used as the incumbent 0.8747759). It does **not** use PR 73
  (repeated marks) or our face family.
- **The new idea: a fourth-power transfer of Gauss sums.**
  - `GaussUnits.fourth_power`: for a sextic character `χ` and a unit `u`,
    `G(k·u⁴) = χ(u)²·G(k)`. A fourth-power multiplier on the frequency changes a sextic Gauss
    sum only by a cubic phase.
  - `GaussTransfer.fifth_free_nonunit_zero`: the Gauss sum vanishes at `D⁴k` when the (fifth-free)
    modulus shares a prime with `D`.
  - The existing proof amplifies by sixth powers, which leave Gauss sums exactly invariant (the
    "exchange rate 6"). Fourth powers cost a phase that disappears in mean squares.
- **Result: one strong source face.** `RepairedRestrictedSource.targetFace` is
  `globalFace (99999/100000) (93/25) (3/50)`: a plain fourth moment with slots, valid on
  `m₁ + m₂ + (93/25)z ≤ 0.99999` for `z ≤ 3/50` ("the paper's 93/25 root capacity",
  `OuterFreshMixedCapacity.lean`).
  - Collet's natural face is `G(1, 9/2, 11/200)`: slot cost `6κ` with `κ = 3/4` from `β ≤ 7/8`.
  - The slot cost drops from 4.5 to 3.72, i.e. an effective exchange rate of about
    `3.72/0.75 ≈ 4.96` instead of 6. (Our lever map priced "exchange rate 6 → 5.93" at 6e-6.)
- **No source chain.** The return's faces are all implied by the one source face (`Face.Included`
  in `Parameters.lean`: smaller slope and cap under the same half-plane):

  | face | intercept | slope | cap |
  |---|---|---|---|
  | count | 0.99999 | 3.72 | 0.05499 |
  | physical | 0.96886 | 3.14175 | 0.043 |
  | x | 0.96226 | 3.1481 | 0.0549989 |
  | y | 0.96739 | 3.2731 | 0.0549989 |

- **Return parameters.** `θ = 0.8746935`, `h = 39823/50000`, `ℓ = 11/3 − 4θ`, `x = 1 + ℓ − h`,
  `y = h − 2ℓ`, incumbent 0.8747759 (PR 67), physical slope `12567/4000`. The proof is by
  contradiction: in the branch `θ < β` the source face holds, and the return contradicts it.
- **Use of the contrary hypothesis.** The source construction uses `θ < β` only to get
  `β ≥ 51/100` (`RepairedActualSideProvider.actual_small_contribution`:
  `hβ := (contrary_inputs hcontra).1`). A small fork of the top-level statements, taking
  `51/100 ≤ β` instead, would make the source face available for any target `θ ≥ 0.51`.

## 2. Combining it with our proof (float model)

- **The idea.** Run our face family (repeated-mark HIGH count, Lemma F, ODE/Lambert flow) from
  Sil's source face instead of Collet's natural face, then our final return (Lemma D,
  `h = 401/500`).
- **The Lean interface matches exactly.**
  - Collet's `Graph.P s` is `GlobalSource s.B s.L s.cap`.
  - Sil's `RepairedRestrictedSource.actual_global_source` proves
    `GlobalSource (99999/100000) (93/25) (3/50)`.
  - So his theorem can be the first parent of our chain, in place of `natural92`, which comes
    from Collet's `natural_global_source`.
  - The steps still use the cap `6(2β − 1) ≤ 9/2`, which holds from the baseline's 7/8.
- **Where the family must start: at the tangency.** The family begins where the flow's slope
  equals the start face's slope. Before that point the start face beats anything the flow
  produces.
  - Collet's natural face (slope 9/2): tangency at `s₀ ≈ 0.0124`, which is why the single stage
    starts at 0.01228.
  - Sil's face (slope 93/25, intercept 0.99999): flow slope along the face is −4.89 at `s = 0.005`,
    −4.16 at 0.025, and −3.72 at **`s₀* ≈ 0.0329`** (`closed_flow.slope`).
- **Float model** (`scratchpad/silstart2.py`). The first face is `E(s₀) = 0.99999 − 3.72·s₀`, the
  flow is unchanged, and the return's incumbent is 7/8. It reproduces the single stage's exact
  0.8747252 when started on the natural face at its tangency.

  | start | breakpoints | end faces C / P | θ* |
  |---|---|---|---|
  | natural (1, 9/2) at 0.01228 | single-stage | (0.95652, 2.8990) / (0.96070, 3.0000) | 0.8747252 |
  | Sil at 0.01228 (before tangency) | single-stage | (0.96617, 3.0111) / same | 0.8746741 |
  | Sil at 0.0135 | 6 pts to 0.046 | (0.95939, 2.8450) / (0.96628, 3.0000) | 0.8746658 |
  | Sil at tangency 0.0329 | 0.0329, 0.0365, 0.0400, 0.0424 | (0.97922, 3.1673) / same | 0.8746130 |
  | Sil at tangency | …, 0.0450 | (0.97306, 3.0264) / same | 0.8746092 |
  | Sil at tangency | …, 0.0460 | (0.97066, 2.9736) / (0.97187, 3.0000) | 0.8746084 |
  | Sil at tangency | …, 0.0470 | (0.96824, 2.9215) / (0.97187, 3.0000) | **0.8746076** |

- **About 8.6e-5 below PR 74, and 7.6e-5 below the target 0.8746835.** The chain's physical face
  (0.97187, 3.0) beats Sil's (0.96886, 3.142) at every width, as a chain built on his face should.
- **Earlier pricing does not apply.** The finding `dθ*/dK ≈ 6e-5` was for tiny changes of the
  natural cost. A much better start face moves the tangency itself, from 0.0124 to 0.0329.

## 3. What a submission would need

1. **Sil's package as a dependency.** Fork the few top-level source statements so they assume
   `51/100 ≤ β` instead of `theta < β`.
2. **Our face family regenerated from the new start.** The breakpoints must be re-tuned, and the
   step certificates regenerated with the packed pipeline.
3. **Our final return regenerated** at the new θ, with the incumbent from the baseline (7/8), or
   from PR 74's theorem itself (`β ≤ 0.8746935`).
4. **Checks:**
   - the end faces satisfy the return's receipts (e.g. physical slope `≥ 3`: here 3.011);
   - the step machinery accepts a `globalFace` start other than Collet's natural face;
   - the build time with a 106k-line dependency.

## 4. Update: exact result of the combination (see `../combined/README.md`)

- **Exact θ\* = 349843/400000 = 0.8746075** (float estimate above: 0.8746076).
- **Breakpoints** `0.0329365, 0.0376, 0.0423, 0.0472`.
  - The start must be at the tangency to within about 1e-7.
  - The end is set by the q floor (`L/B ≥ 3`), not by the HIGH-parent floor.
- **Return:** `h = 401/500`, 42 rows, 17 windows. The binding box is the `new_top` edge at
  `p → 1/2`, covered by the count face C.
- **Return transport bound.** At this θ, `ℓ = 11/3 − 4θ = 0.16824` exceeds the bound `ℓ < 0.1678`
  that the transport layer was forked with. `fork_transport.py` now takes the bounds from
  `QRH_RELAXED`. With `ℓ < 0.1690` the regenerated layer differs in three lines, and only weak facts
  use that bound (`4ℓ < h`, `ℓ ≤ 1`).
