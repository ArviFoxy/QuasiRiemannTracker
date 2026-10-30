# arvi_rip: restricted isometries and the square-root barrier (research, not a submission)

Lean prefix `Submissions.arvi_rip`, namespace `QRH.ArviRIP`. Mathlib only. Every theorem below depends only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorry`, `admit`, `axiom` or `native_decide`).

## Why this package exists

The faces' K-wall is a restricted-isometry problem. Take the sextic characters χ_z (rows z ~ B) on sources of
norm ≤ L. The selected norm asks that the rows of a large-value set W act almost orthogonally at L = B.
Selection at slope δ gives |W| = B^{1−δ}, so δ < 1/2 means beyond √(dimension). The Lean barrier
`arvi_kwall` shows that amplify-and-reflect cannot cross δ = 1/2. This package builds the general RIP
language in which a beyond-√ argument has to be written, starting with the classical barrier itself.

## Files

| file | content |
|---|---|
| `Coherence.lean` | `gershgorin_rip`: unit columns of coherence μ satisfy the RIP on every support S with constant μ(\|S\| − 1). `frame_potential_ge` and `welch`: the Welch bound N² ≤ n(N + N(N − 1)μ²), via the frame-potential identity `gram_frame_frobenius`. `coherence_order_barrier`: once N ≥ 2n, a coherence certificate (k − 1)μ ≤ δ forces k ≤ 1 + δ√(2n). This is the square-root barrier: coherence alone never certifies order beyond ≈ √n. |

| `FlatRIP.lean` | BDFKK's Lemma 3 in fixed-support form. `flat_rip_on`: if every bilinear sum of disjoint flat combinations on W satisfies \|⟨Σ_{J₁}u, Σ_{J₂}u⟩\| ≤ δ√(\|J₁\|\|J₂\|) (`FlatOn u W δ`), then \|‖Σ a_z u_z‖² − ‖a‖²\| ≤ 32 δ (T + 2^{−T}√\|W\|)² ‖a‖² for every T. With 2^T ≥ √\|W\| the constant is 32 δ (T + 1)², so polylog. The steps are: `cube_vertex` (an affine map on [0,1]^s attains its maximal norm at a vertex), then `flat_cube`; `flat_dyadic` (telescoping dyadic pieces with a Chebyshev count per level); `flat_nonneg`; `flat_complex` (four nonnegative parts); and `avg_identity` with `count_split` (each off-diagonal pair is split by exactly a quarter of the subsets of W). |

Every known explicit beyond-√ RIP construction goes through `flat_rip_on`. What remains, and is open, is the
flat bilinear estimate itself for our dictionary (the sextic characters on a large-value set W at the
self-dual length), with δ ≪ 1/log² once |W| exceeds √(dimension).

Build: `lake env lean Submissions/arvi_rip/Coherence.lean` (≈ 11 s) and `.../FlatRIP.lean` (≈ 13 s), on a warm cache.
