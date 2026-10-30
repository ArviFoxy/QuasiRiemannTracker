# The theta span V of the sextic large sieve (Arvi's "replace M by an operator with the RIP we need")

The reduction is in Lean (`../../lean/arvi_kwall/FlatDilution.lean`). If M = (flat low-rank part on V) +
(I − P_V)M, then RIP of M on every thin row set follows from a **full-family** bound for (I − P_V)M, and the V
part is diluted by k·|W|/R. That needs k = dim V small. This directory measures what V is, and finds that k cannot
be small.

| script | measures |
|---|---|
| `theta_span.py B L` | dual energy ratio r = ‖Eᵀc‖²/(S‖c‖²) of theta row vectors conj G(z,1)·profile against random phases; profile Gram (rank one?); detectors' projections; top singular values with V removed |
| `theta_profile.py B L` | is the excess rank one in the radial profile? Compares profiles with I(U) = ∫U t^{−5/6} ≠ 0 and = 0 |
| `theta_blocks.py B L` | small-modulus row vectors χ_z(m), and twisted theta vectors conj G·χ_z(m)·χ_z(u) |
| `theta_top.py B L` | structure of the top singular vectors (radial, small primes, characters, units) |
| `theta_topspan.py B L` | overlap of the top singular vectors with the twisted-theta and block spans; compressed spectra |
| `theta_twists.py B L [per_bin] [bins]` | excess of twisted thetas conj G·χ_z(u)·χ_z(m) as a function of N(m), against conjugate and plain twists and random phases |
| `theta_powers.py B L` | which row vectors carry the excess: plain, conj G, G, and Gauss-sum powers |

All scripts build E and the row Gauss sums through `theta_core.py`.

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
- **Only conj G carries the excess.** Plain rows show a deficit (r = 0.85–0.93 against 0.946). G and the Gauss-sum
  powers conj G², G², conj G³ are neutral (0.90–0.98) (`theta_powers_B30000.log`).
- **One spike per twist.** Every twisted theta conj G·χ_z(m) carries the same excess, +0.084 ± 0.005 for
  34 ≤ N(m) ≤ 2200 at B = 3·10⁴. It ends near N(m) ≈ B²/L. m = 1 carries +0.221 ≈ 2.6 copies
  (`theta_twists_B30000.log`). Mechanism: in the Poisson dual, the frequencies h = m·j⁶ all repeat atom m.
- **What the K-wall needs (corrected).** V is not low-dimensional. Asymptotically every twist with
  N(m) ≤ B^{1−6γ} keeps an excess ≥ B^γ. Two statements remain:
  - (LS off V) for that B^{1−6γ}-dimensional V, at the balanced point;
  - a detector condition ‖P_V M a‖² ≲ L·B^γ‖a‖², which is an unbalanced twist sieve.
  See the journal, "Where the theta excess lives".
