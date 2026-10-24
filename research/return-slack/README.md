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

## Origin of every term in the binding balance (2026-10-24)

Collet's return exponent (return.tex NR6) is
`E = 1/2 + 13h/75 − y/2 − ℓ/2 − 9d/100 + δ/2 + δp(ℓ − C/2) + (3d/4)R`, required `≤ θ`. Term by term,
with sources:

| term | origin |
|---|---|
| `1/2 + δ/2 = a` | the `s`-contour `Re s = a + 16e` just right of the row's zero (real part `a = (1+δ)/2`); OpenAI 7/8 high-bin lemma, `E(d) = a − 7/8 + …` |
| `−y/2` | the `Y^{−1/2}` normalization of the weighted numerator (foundations (223)) |
| `−ℓ/2 (+ℓz₀)` | slot normalization: each main slot is `−P_i^{z−1/2}Q_i`, taken on `Re z = z₀ = 17/50` |
| `+δpℓ = qℓ` | slot amplitudes `|Q_i| ≤ P_i^{g_i}` with `Σℓ_ig_i = qℓ`, `q = δp ≤ δ/2` (zero-free bin) |
| `−δpC/2` | the slots inside the numerator's fourth moment, capacity `C = (B_Ph − 4ℓ)/Λ_P` at `d = h`, give `U^{−qz_A/2}` |
| `(3d/4)R` and `d/4` | Levy's Hölder step `#class^{3/4}(Σ_all|N|⁴)^{1/4}` gives `U^{3R/4 + 1/4}` |
| `13h/75`, `−9d/100` | `(z₀ − 1/6)h` and `(1/4 − z₀)d`; `z₀` cancels at `d = h` (`../lean-lab/ReturnAlgebra.lean`) |

The low side gives `θ = 2/3 + (x + y)/4`: the Gram's diagonal `Z^{x/2}` times its sextic bias
`P_a^{1/12} = Z^{(y−x)/12}`, and the signal normalization `k = (4 + y − x)/6`. Two constraints
fix `y`:
- the marked energy is tight, `x + y + ℓ = 1` (`M + 2z ≤ N_*` with `N_* = 1 + ℓ`);
- the conductor edge is `h = 1 + ℓ − x` (the Poisson rows run up to the dual of `X`).

So `y = h − 2ℓ` and `θ = 11/12 − ℓ/4`. Substituting into `E ≤ θ` at `d = h` gives the balance
`3ℓ/4 + δ/2 + δp(ℓ − C/2) + (3h/4)R = 5/12 + 5h/12`.

A unit of slot length `ℓ` buys `1/4` in θ. On the high side it costs:
- `+1` through `y` (half from the marked energy's slot cost, half from the conductor edge);
- `−1/2` from the slot normalization;
- `+δp` from the binding rows' amplitudes;
- `+2δp/Λ_P` through the numerator capacity.

The net coefficient is `3/4 + δp + 2δp/Λ_P = 1.131` at the binding point. That reproduces
`dθ/dR = (3h/16)/1.131 = 0.133`. Every term is either an atom (the count `R`, slot cost 2 in the
marked energy, the bias `P_a^{1/6}`) or a fixed normalization. The probe's own bookkeeping has no
slack left.
