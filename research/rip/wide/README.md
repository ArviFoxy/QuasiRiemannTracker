# Wide random features on the sextic atoms (RIP program (4))

This directory is about a randomized dictionary of *different* atoms, as opposed to subsets or re-phasings of the
characters. A degree-ℓ feature is a product of ℓ Rademacher projections. These are the polynomial pieces of wide
dot-product kernels such as ReLU's arc-cosine kernel. The Lean side is `../../lean/arvi_rip/WideFeatures.lean`:
`exists_wide_rip` gives a positive counting measure of operators with RIP of order ≈ μ^{−ℓ} for any data of
coherence μ.

`wide_probe.py B L [P0] [m]` uses the exact sextic family (rows of norm in [B, 2B], sources of norm ≤ L), with
log `wide_B3000_L3000.log` (R = 848 rows, S = 778 sources). It measures:
- coherence, over all pairs and within slot-selected sets;
- the λ range on W of the raw Gram and of the degree-ℓ and ReLU kernels;
- the same for m sampled features;
- the large-value count certificates of each degree for a plain-sum detector.

| row set W (212 rows) | coherence ·√S | raw Gram | degree 2 | degree 3 | ReLU high-pass |
|---|---|---|---|---|---|
| random | 3.4 | [0.24, 2.32] | [0.94, 1.06] | [0.996, 1.004] | [0.98, 1.12] |
| slot-selected | 3.5 | [0.23, 2.32] | [0.94, 1.07] | [0.996, 1.004] | [0.97, 1.13] |

**Reading.**
- The wide dictionary has RIP far beyond √ (the raw coherence certifies about 8 rows).
- The zero gives a degree-1 large value |⟨a, x_z⟩| ≥ v. Higher degrees pay v^{−2(ℓ−1)}: at the measured large
  values, degrees 2 and 3 certify 10²–10⁵ times more than degree 1.
- Degree ≥ 2 is already diagonal from the full-family sieve at length ≥ B², since Θ₆(2x) = 2x for x ≥ 1.
- So the K-wall sits in the degree-1 part, and the next construction must put its randomness there (journal,
  RIP (4)). `FRESH_LOOK.md` (agent report) collects designs for that. Its scripts are `wide_tests.py` (typicality of
  slot-selected W against random multiplicative and i.i.d. Schur models, centered fourth moments, 4-cycles) and
  `wide_tables.py` (its tables), with results in `wide_B*_s*.json`. The certificate it recommends, the centered
  fourth moment, is `../../lean/arvi_rip/FourthMoment.lean`.
