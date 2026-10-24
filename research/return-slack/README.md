# Slack of the exact return at θ* = 0.8747257 (2026-10-24)

`receipts.py` evaluates the exact return certifier (`../repeated-marks/cert_return.py`, global mode,
`h = 401/500`, `s_+ = 13/250`, numerator cap `9/200`, no `Λ_P > 3` receipt) on the consolidated
Lemma F chain (`../cap-induction/chain_h45.json`). It prints every scalar receipt and every
conductor edge's minimum return coefficient. Output: `receipts_8747257.log`.

Result:
- **No scalar receipt binds.** The smallest slacks are `principal_z = h/600 − 1/1000 − 1/4000`
  (8.7e-5, depends on `h` only), the count face's cap margin (3.0e-3), the `floor` receipt
  (3.5e-3), and the conductor kink ordering (7.5e-3).
- **Only one edge binds.** `new_top` (`d = h`, capacity `C = 0.033116`) has minimum return
  coefficient 1.7e-7. The next edge, `new_kink` (`d = 0.7945`), has 1.2e-3. The other edges are
  far from binding.
- At `new_top` the rectangles use the face-C branch near the binding point
  `(δ, p) ≈ (0.4546, 1/2)` and the old (natural face, `Λ = 6κ`) branch elsewhere.

So θ* is fixed by a single equation. At `d = h`, with `θ = 11/12 − ℓ/4`:

  `5/12 + 5h/12 = 3ℓ/4 + δ/2 + δp(ℓ − C/2) + (3/4)h·R(δ, p)`,  `C = (B_P h − 4ℓ)/Λ_P`,

taken at the adversarial `δ` (where `dR/dδ ≈ −0.957`). Solving for `ℓ` gives
`dθ/dR = (3h/16)/(3/4 + δp + 2δp/Λ_P) = 0.133`. The `h`-derivatives of the two sides are 0.41667
and 0.41677, so `h` sits at a flat optimum. No receipt, guard or admission window is a lever. Only
`R` (the count's atoms) and the physical face `(B_P, Λ_P)` (the chain's atoms) can move θ*.
