# Conditional θ: what the return gives if an atom holds (round 9, 2026-10-25)

`conditional_theta.py` re-solves the float model of the final return (`../../atom-targets/targets.py`)
with one atom moved. The faces are held fixed, so these are return-only effects. The full chain
would gain more through `ρ` and the faces. The model's base is 0.8747496; the exact certificate is
lower, so only differences are meaningful.

| change | θ* (float model) | Δθ* |
|---|---|---|
| none | 0.8747496 | 0 |
| long Möbius moment diagonal, `L(r) = 1 − δr` for `r > 1` (`a_L = 6`, `b_L = 0`) | 0.8668468 | −7.90e-3 |
| long line slope 1% lower (`b_L = 4.95`) | 0.8743558 | −3.94e-4 |
| inverse-moment slot cost halved, `r + z ≤ 1` (`s_I = 1`) | 0.8705715 | −4.18e-3 |
| long line diagonal and `s_I = 1` | 0.8668468 | −7.90e-3 |

Reading:
- **The long moment is the big lever.** If it is diagonal, as round 9's numerics suggest
  (`../numerics/`), the return alone would drop by about 8e-3, which is 1300 times the 6.1e-6 still
  needed. With the long line diagonal, the slot cost no longer binds.
- **The needed change is tiny.** Linearly, 6.1e-6 needs `b_L ≈ 4.9992`, about `1.5e-4` off the
  long-line exponent at `r ≈ 1.155`. That is a power saving of `U^{1.5e-4}` over sixth-power
  amplification in `Σ_u |M_u(U^{1.155})|²`.
- **No proof is in sight.** For a complete character group the analogous statement is the variance
  of `μ` in residue classes to a single modulus `q` at length `q^{1.155}`. That variance needs
  Möbius autocorrelations along `qZ`. We know of no power saving for a single modulus in this
  range.
- `s_I = 1` is a hypothetical, far stronger than P1 (P1 is worth about 6–7e-6). It is listed only to
  show that the slot cost and the long line are the two capacities that set `R`.

Run: `python3 conditional_theta.py` (about 25 minutes).
