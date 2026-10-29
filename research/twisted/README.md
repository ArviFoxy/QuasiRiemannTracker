# Twisted transfers (D1, task 149): result

**Verdict: closed as negative with today's Lean.** No twisted type pays more than 1e-5 under any
conductor charge the library supports. The lead checked the key citations against the Lean.

## Lean facts (checked)

- `all_scale_buffered_slot` (Collet, `Cycle61/Moment/LowBranch/Slot.lean`):
  - It chooses C before Z, d and the base character ν, assumes twisted-family conductors ≤ Z^d,
    and loses only Z^{2εd}.
  - So the LOW side is already uniform in the conductor.
  - This refutes the R2 note's claim that no Lean statement charges a conductor cost.
- `PricedPackedSource` (Sil, `CubeFree/Leaf/Contract.lean`) fixes a finite anchor family before Z.
  `UnitFaceSource` likewise fixes the characters before Z. So parents and HIGH counts are per
  character, and a twist whose conductor grows with Z is not covered.
- `sieveNorm_sharp` (baseline `CubicSieve/Sharp.lean`) gives the cubic large sieve
  C(MN)^ε(M + N + (MN)^{2/3}). It beats the trivial bound, but after the Cauchy–Schwarz over D it
  exceeds W × (per-D source) by about N/W. So the room it gives is e = 1 − α′/d ≪ 0.

## Derived and numerical (not proven)

- The best twisted type, D¹ j = 0, does not add to the payment π. Instead it lifts the density
  cut q toward 3/4 wherever L/B > 2 + κ, with break-even κ* = L/B − 2.
- At today's floor-½ chain the simple block's wall is Λ = 2B, which is exactly the κ = 0 twisted
  wall. A twisted type can raise faces upstream but cannot extend the chain.
- Pricing (`scan_split.py`, continuum chain + exact six-branch return; the baseline reproduces
  0.873870999):

| conductor charge | Δθ |
|---|---|
| κ = 0 | −6.17e-5 |
| κ = 0.25 | −3.46e-5 |
| κ = 0.5 | −4.0e-6 |
| joint count κ′ = 1/7 (needs parent theorems over many base characters, which do not exist) | −8.0e-6 |
| current Lean count κ′ = 2/7 | 0 |

- No zero-density estimate for twisted families with conductor exponent below about 1/6 is known
  to the agent [inference].

## Useful by-products

- Lifting q to 3/4 upstream is worth 3.5–6.2e-5, whatever does the lifting. A doubled block (D2)
  would lift it all the way down to Λ ≈ 1.64B if a source existed. Re-price it with `scan_split.py`.
- Two pieces of Lean work are mechanical and reusable:
  - generalise `ds_low_aux` to arbitrary (e, c, r);
  - prove the block-side identity on the pattern of `transfer_value_general` (`arvi_newpowers/Rigidity.lean`).

## Files

- `twisted_ode.py`: chain model.
- `scan_split.py`: role-split pricing.
- `make_table.py`: builds the table above.
- `q3_identities.py`: numerical checks of the other constructions. Twist-cancelling pairs: none in
  69 pairs. Conjugate and rational blocks: no gain. Bi-dilation: nothing new.
- `scan_k*.json`: results.

`scan_split.py` expects a copy of `research/newpowers/ta` beside it, in `ta/`.
