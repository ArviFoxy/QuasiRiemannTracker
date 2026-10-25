# Strip mining the exact pipeline (2026-10-25)

The goal: rank every constant of the exact proof pipeline by how much θ* moves when it moves. That
tells mechanism searches (new conductors, moments, transfers) where to dig.

## Tools

- `knobs.py`: rewrites `../repeated-marks/cert_return.py` through Python's AST so that every numeric
  literal in the return's formula functions becomes a named knob `function:line:col:value`. The
  functions are `branch_affine`, `branch_old`, `admission_polys`, `geometry`, `edges`,
  `return_poly` and `receipt`, plus the module constants V, M±, S₋, M_H and R₀.
- `atlas.py EPS NPROC`: bumps each knob, and the design parameters (faces, `h`, `sC`, `sP`, `tf`),
  by a relative EPS. It recomputes θ* exactly by binary search on the exact return, starting from
  our certified faces (`FinalReturn/ReturnConstants.lean`); the base θ* is 0.8746075.
- `source_atlas.py`: the same for the source flow (literals of the HIGH-threshold closed form,
  the LOW exchange rate, Sil's start face, the q floor, den, φ), scored through the exact return.
- `floor_scan.py`: the return's floor with perfect source faces, against the return's design
  parameters.

## Return atlas (EPS = 3e-3; `atlas_eps0.003.json`)

151 knobs: 31 move θ*, 111 do not, and 9 make the certificate invalid when bumped.
Δθ* is in units of 1e-7 for a +0.3% bump.

| knob | Δθ* | where it comes from |
|---|---|---|
| `1` in `N = (1−δ)J + VδU` | +1082 | count R = N/J (NR2; the three witness lines I, P, L of NR1) |
| `13` and `75` in `13h/75` | ±925 | FR13 numerator term `(z₀ − 1/6)h`, `z₀ = 17/50` |
| `1` in the `N-tail` admission | +822 | FR8: the natural tail join. **Binding at the current θ*.** |
| `2` in `A = 2 − 4p/Λ` | +649 | NR2 (inverse/plain crossing) |
| `/2` in `y/2` of E | +557 | probe geometry `y = h − 2ℓ` |
| `2` in the `mL` window `(B − L·s₊)/2` | +542 | FR8 plain window |
| `9/100` in `−9d/100` | −480 | FR13 `(1/4 − z₀)d` |
| J and D literals | +466 … −54 | NR2 |
| `2` in `(2 − B_P)d` of `C_N` | +403 | new physical capacity (NR3) |
| `2` in `2y` of `C_N` | −173 | same |
| face heights `B_P`, `B_C` | −173, −88 | source faces: dθ/dB_P ≈ −5.9e-3, dθ/dB_C ≈ −3.0e-3 |
| `5/6` in `V = 5/6 − δ` | +153 | L line `1/6 + Vr` (sixth-power long moment, atom 2): −1e-5 needs `5/6 → 0.8317` |
| `h`, `L_P`, `L_C` | +39, +26, +17 | |
| `sC`, `sP`, `tf` | 0 | the windows are slack at the current faces |

**Tried and rejected: the tail join from Sil's face** (`mh_test.py`). The `N-tail` admission uses
`M_H = (1 − K·17/500)/2`. Taking the join from Sil's face (`M_H = 0.4368` instead of 0.4235) gives
θ* = 0.8747157, which is worse. The larger `M_H` breaks the receipt `B − 2M_H − L(s₋+η) > 0` for
face C. Two-sided; no free gain.

## The return floor (perfect source faces)

| design | floor θ* |
|---|---|
| `sC = 13/250` (current) | 0.8745804 |
| `sC = 27/500` or `549/10000` | 0.8745760 |
| face caps 0.06, `sC = 0.059` | 0.8745760 |

- **What can cap the floor.** The face-branch admission (FR8) and the physical width
  `s_P·h ≤ C_N`.
- **Example.** With the mixed-step faces the binding at the floor is the `new_top` cover at
  `δ ≈ 0.503`. There the capacity is `s_P·h = 0.0361`, not the face's 0.047 (`../mixed-step/`).
