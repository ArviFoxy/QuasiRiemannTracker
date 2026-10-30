# The theta span V of the sextic large sieve (Arvi's "replace M by an operator with the RIP we need")

The reduction is in Lean (`../../lean/arvi_kwall/FlatDilution.lean`). If M = (flat low-rank part on V) +
(I − P_V)M, then RIP of M on every thin row set follows from a **full-family** bound for (I − P_V)M, and the V
part is diluted by |W|/R. This directory measures what V is.

| script | measures |
|---|---|
| `theta_span.py B L` | dual energy ratio r = ‖Eᵀc‖²/(S‖c‖²) of theta row vectors conj G(z,1)·profile against random phases; profile Gram (rank one?); detectors' projections; top singular values with V removed |
| `theta_profile.py B L` | is the excess rank one in the radial profile? Compares profiles with I(U) = ∫U t^{−5/6} ≠ 0 and = 0 |
| `theta_blocks.py B L` | small-modulus row vectors χ_z(m), and twisted theta vectors conj G·χ_z(m)·χ_z(u) |
| `theta_top.py B L` | structure of the top singular vectors (radial, small primes, characters, units) |
| `theta_topspan.py B L` | overlap of the top singular vectors with the twisted-theta and block spans; compressed spectra |

**Findings** (logs `theta_*B*.log`):
- **Theta excess.** +16%, +18%, +24% at B = L = 3000, 10⁴, 3·10⁴ (6, 11, 23 sd), against the random-phase
  baseline.
  - It is rank one in the profile: +18–20% when I(U) ≠ 0, and −5%…+3% when I(U) = 0. This matches Xu–Sang's
    Gauss-Gram main term, arXiv 2610.17675.
  - It is not the top of the spectrum: removing V changes the top singular value by < 0.1%.
- **Block structure.** The top of the spectrum exceeds the Marchenko–Pastur edge by +2.5% (B = 10⁴) and +9%
  (B = 3·10⁴). It sits partly in the span of small-modulus row characters χ_z(m), N(m) ≤ 100: 26–35% of the top
  vector's mass, and the compressed top is +38% / +72% over a random span. The top block combination is a short
  prime-pool row vector Σ_m χ_z(m). Mechanism open.
- **Both parts are flat** (unimodular on coprime rows), so both dilute on thin row sets.
- **What the K-wall now needs.** The full-family large sieve off V = theta ⊕ blocks, at the balanced point.
