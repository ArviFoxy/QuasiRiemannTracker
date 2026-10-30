# (L2) probe: quadratic twists kill the Patterson bias of cubic Gauss sums over primes (D1)

`l2_probe.py X Kmax nk` sums the normalized cubic Gauss sums g̃(π) = g(π)/√p over primary split primes with
N(π) ≤ X, with and without twists. It reuses `../moments_probe/fastgauss.py` (C prime Gauss sums, snapped to the
exact cube root of π/|π|). Log for X = 10⁶ (78,462 primes, 12 values of k up to N(k) ≈ 4600): `l2_X1e6.log`.

| sum | \|T\|/√(#primes) at X = 10⁶ | reading |
|---|---|---|
| T0 = Σ g̃(π) | 19.9 (local slope 0.754) | Heath-Brown–Patterson main term ∝ X^{5/6}/log X |
| Tcub2 = Σ g̃(π)·conj (k/π)₃ = Σ g̃(k, π) | 14.8 (N(k) = 7) → 5.2 (N(k) ≈ 4600) | main term at parameter k, ≈ T0·N(k)^{−1/6} (0.75 vs 7^{−1/6} = 0.72; 0.37 vs 427^{−1/6} = 0.365) |
| Tcub = Σ g̃(π)·(k/π)₃ = Σ g̃(k², π) | 0.24–2.65 | no main term: the theta coefficient at a square vanishes |
| Tquad = Σ g̃(π)·(k/π)₂ | 0.10–2.30 | **no main term**: the quadratic twist kills the bias |
| Tsex = Σ g̃(π)·(k/π)₂·conj (k/π)₃ (D1's dual combination) | 0.25–1.54 | no main term, square-root size |

**Reading for D1 (L2).**
- In D1's dual, the prime variables carry the sextic symbol (r/P)₆ = (r/P)₂·conj (r/P)₃, so their sums are
  Tsex-type. Numerically these have no Patterson main term for any k tested, and they are of random-walk size
  X^{1/2}, with no visible growth in N(k).
- The provable input is Heath-Brown–Patterson's X^{5/6} (with a loss N(k)^c), which gives Λ = 5/3.
- Square-root cancellation in both prime variables would give Λ → 1, the ideal face. The truth is far from the
  wall; the obstruction is proof.
