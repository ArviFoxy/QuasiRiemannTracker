# Exact arithmetic evidence

Run `python3 rational-check.py` from any directory. It uses only the Python standard library and writes `rational-receipt.json` beside itself.

It checks:

1. **Endpoint constants.** θ, c, h, ℓ, x, y, κ*, d₋, d₊ and B are exactly the values in `Bundles/B000.lean`.
2. **Cycle61 scalar design checks** at the new endpoint. Each margin is recomputed and must be positive: `plain_upper_gap`, `slot_upper_gap`, `slot_lower_gap`, `actual_supply`, `detector_supply`, `lower_supply`, `four_ell_y`, `bmax_below_4_25`, `shift_exact`, `junction`, `extension`, `floor`, `lower_row`, `small_row`, `principal_w`, `principal_z`, and the `J` positivity checks. `probe_boundary` must be identically zero.
3. **New window facts.**
   * `m_lo > 41/100` and `m_hi < 44/100`.
   * `(B − 2m_lo)/Λ = 1/25`.
   * `(1 − 6·(3/4)·17/500)/2 = m_hi`.
4. **Ten Bernstein certificates.**
   * The three Cycle61 row certificates, regenerated in `Bundles/B021.lean`. The new-h row now covers only the complement of the region.
   * The new-count row on the region, in three boxes.
   * The six region validity conditions, in `Affine/Certificates.lean`.

   Every coefficient must be positive (231 coefficients in total). The row boxes must tile `[0, 3/4] × [0, 1/2]` with disjoint interiors.
5. **Lean cross-check.** If the submission source is present, the script parses the same Lean files. It checks that every `…Power` polynomial, every `…Coefficients` matrix and every box in an `…Identity` statement equals the computed one exactly.

The scripts in `../scripts` are the generators:

| script | role |
|---|---|
| `poly.py`, `model.py` | polynomial model |
| `genlean.py` | Lean certificate blocks |
| `patch_consts.py` | endpoint constant replacement |
| `fastopt.py`, `pickh.py` | float search for θ and h |

These checks do not establish the analytic hypotheses. Lean does that.
