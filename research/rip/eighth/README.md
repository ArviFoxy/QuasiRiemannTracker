# Plain eighth moment of the thin sextic family (input of D1's dispersion route)

`eighth_probe.py`: κ₈ = mean_u |X₁X₂|⁴ / (mean_u |X₁X₂|²)², with balanced smooth plain sums of total length
B^μ (`../moments_probe/probeC.py` weights), against the multiplicative surrogate. Log: `eighth_1.log`.

| B | μ = 0.6 | 0.8 | 0.93 | 1.0 | (N₁N₂)²/R at μ = 1 |
|---|---|---|---|---|---|
| 3·10⁴ | 4.95 (model 4.77) | 5.59 (5.87) | 6.06 (7.50) | 6.02 (7.59) | 1.1·10⁵ |
| 10⁵ | 5.18 (5.37) | 6.70 (6.99) | 6.76 (7.88) | 6.16 (8.63) | 3.5·10⁵ |
| 3·10⁵ | 5.78 (5.89) | 6.75 (7.50) | 7.44 (9.01) | 7.12 (10.30) | 1.1·10⁶ |

**Reading.**
- There is no N-term: an N-term would push κ₈ toward (N₁N₂)²/R, up to 10⁶ here.
- κ₈ grows slowly with B, like the random multiplicative model, and sits below it past μ ≈ 0.8 (the functional
  equation, as in probe C).
- So the plain eighth moment is Lindelöf on average past the row count. That is exactly the input that
  `lean/arvi_primeface/Dispersion.lean` needs to make the prime-pool face diagonal (with Huxley's large sieve).
