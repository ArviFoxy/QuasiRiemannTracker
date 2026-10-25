# The faceless source chain: one family of faces instead of a source graph (2026-10-25)

The user asked to remove the finite source graph from the proof and replace it with the exact
continuum flow, and to prove that step in Lean. This is done. The submission
`arvi-repeated-marks-20261024` now proves the bound **34989/40000 = 0.874725** (before: 0.8747289,
−3.9e-6). The 59 certified nodes `Finite/Node00–58` are gone. The structure behind the flow is in
`../chain-structure/README.md`.

## The flow the family follows

The continuum limit of the Lean gates (`continuum_lean.py`: the face is its own LOW and HIGH parent,
`q = (1 − den)L/(6B)`) is the closed-form switching flow of `../chain-ode/README.md`:

  `E′ = −6q*E/(1 − 6q*s)`, `6q* = 5(√E − 2√s)²/(2 − E − 4√(Es))`.

- It is the `p = 1/2` (Lambert) class up to `s ≈ 0.01942`, then the interior class `p*`.
- It agrees with the full-gate continuum solver to 3.5e-5 in slope and 1.7e-6 in height
  (`closed_flow.py`, `eval_cont.py`).
- The continuum flow stops at `s ≈ 0.0427`, where the HIGH parent reaches Collet's guard
  `B ≥ 22/23` (`cont_lean.log`).

## The family (`family2.py`)

- Five pieces with breakpoints `σ = 0.0123480, 0.01942, 0.0252, 0.0310, 0.0367, 0.0424270`
  (rationalized). On piece `j`, `s = σ_j + H_j y` with `y ∈ [0, 1]`.
- `E_j(y)` is a cubic Hermite interpolant of the flow, integrated by RK4 with the LOW denominator
  `den = 2⁻¹⁵` and a slope reserve `φ = 1e-4`, coefficients rounded to 1e-14. Piece 0 starts
  exactly on the natural face, `E(σ₀) = 1 − Kσ₀`.
- Faces are secant lines on the grid `Dy = 2⁻¹⁶`:
  - `L(y) = (E(y) − E(y + Dy))/(H·Dy)`;
  - `B = E + sL`;
  - `q(y) = (1 − den)L(y − Dy)/(6B(y − Dy))`, so the crossing with the parent is exactly `s(y)` and
    the LOW denominator is exactly `den`;
  - cap `0.0549989`, fees `(1e-17, 1e-12, 1e-10)`.
- End faces (piece 4):
  - count face `C` at `y = 1 − Dy`: `B = 0.9565249539`, `L = 2.8986524856`;
  - physical face `P` at `y = 41741/2¹⁶` (last grid face with `L > 3`): `B = 0.9607191456`,
    `L = 3.0000025199`.
- The start: `σ₀` is where the flow's slope reaches `K(1 − 4e-6)`. Earlier starts fail `B ≤ 1`
  or the first step's `1/75 − a` gate at the cap.
- The end: `σ₅` is the last point where the parent keeps `B₀ ≥ 22/23`. The return is flat there:
  moving `C` back by 2000 grid steps changes θ* by 1e-7, so an extra final step below the guard
  (as the old graph's node 58 did) gains nothing.

## The Lean proof (`lean/`, submission `Faceless/`, `Graph/`)

| file | content |
|---|---|
| `Poly.lean` | rational polynomials as coefficient lists; evaluation lemmas; the Taylor test `tm1` and `posOn` (positivity on `[0, 1]` by dyadic intervals) |
| `IPoly.lean` | integer polynomials; the Kronecker test `tm1K` (split into positive and negative parts, evaluate at a large base, read the digits): fast in the kernel, which has GMP `Nat` but slow `Rat`; `posOn` and soundness |
| `Family.lean` | `Piece` (σ, H, Dy, cubic `E`), its face `node y`, and the exact identities `crossing = s(y)`, `sourceDen = den`, closed forms of the source atoms `t`, `A`, `D` |
| `HighCert.lean` | the HIGH gate of a whole piece: `6³B₀³·Dn·highGate` with `ν = q + u(3/4 − q)` is a bicubic in `(u, p)` with coefficients polynomial in `y`; integer Bernstein leaves `ib33` on a dyadic `(u, p)` tree, each coefficient certified on `y ∈ [0, 1]`; `high_pos_of_certI` |
| `ScalarCert.lean` | the 16 scalar gates, the weak guard, the special sectors and the cell condition as polynomials in `y` (multiplied by positive atoms) |
| `Validity.lean` | `Piece.Certs` (all certificates of a piece) and `Certs.valid`: every step `node (y − Dy) → node y`, `y ∈ [0, 1]`, is `SourceValid2` |
| `Gen/Data.lean` | the five pieces |
| `Gen/Scalar*.lean`, `Gen/High*.lean`, `Gen/Piece*.lean` | 5 × 69 one-variable certificates, 60 HIGH trees (5 pieces × 2 width endpoints × 6 branches), assembled into `piece{j}_certs` |
| `Gen/Steps.lean` | the four concrete steps: natural → piece 0 and the junctions piece `j−1` → piece `j`, by `decide +kernel` |
| `Chain.lean` | `piece_sources` (induction on the grid index `i < 2¹⁶`), `chain_sources : P faceC ∧ P faceP` |
| `Endpoint.lean` | the face literals by `decide +kernel`, then Collet's endpoint with the new count and physical faces |

Refactor of the fork: `SourceValid2 := SourceValidC ∧ HighPos ∧ q < 3/4 ∧ CellRatio`, where
`HighPos` is real positivity of the HIGH gate on the cell. Concrete nodes still prove it from
Bernstein trees (`highPos_of_valid`); the family proves it from `certI`.

Kernel cost: 78 certificate modules in 9m23s on 4 cores. The hardest HIGH tree takes 96 s, scalar
files about 55 s, the steps 34 s. The full candidate build is 15707 jobs. `Candidate.bound` depends
on `propext`, `Classical.choice`, `Quot.sound` only. The canonical challenge wrapper at
`34989/40000` compiles, and the upstream `npm run check` passes (316 tests).

The final return was regenerated for the new faces:
`../repeated-marks/gen_return_lean.py faces.json 8747250/10000000 401/500 0 1 OUT 13/250 9/200 global`
(34 row rectangles, 11 admission windows; before 36 and 13).

## Reproduce

```sh
SIG=0.0123480,0.01942,0.0252,0.0310,0.0367,0.0424270
python3 gen_all.py OUTDIR        # Data, Scalar*, High*, Piece* (exact; minutes)
python3 gen_steps.py OUTDIR      # Steps.lean
python3 exact_check.py $SIG      # SourceValid2 at sample faces, exact rationals
python3 exact_junctions.py $SIG  # the junction steps
python3 theta_family2.py $SIG    # θ* = 8747250
```

## Dead ends and fixes on the way

- First families (`family.py`, global grid) had `B > 1` at the start. The start must be where the
  flow's slope is just below `K`.
- A Rat-based kernel check of the HIGH trees was too slow. Integer leaves and then the Kronecker
  test made it fast.
- `continuum_lean.py` first reported "infeasible" because the `B ≤ 1` guard broke the bracket; the
  slope is now bracketed by `L ≤ (1 − E)/s`.
- The HIGH minimum was first missed by the grid; a fine `p` grid at `ν = q` fixed it.

## Value

−3.9e-6 against the previous Lean value, below the 1e-5 bar on its own. The continuum ceiling of
the method is 0.8747241, so the formal family is within 0.9e-6 of it. The gain over the graph is
the simplification: the source chain is one explicit curve with a uniform certificate.
