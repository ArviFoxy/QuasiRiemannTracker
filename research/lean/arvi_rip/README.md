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

Planned next: `FlatRIP.lean`, BDFKK's Lemma 3 (flat RIP of order k ⇒ RIP of order 2sk with constant
44 s δ log k). Every known beyond-√ construction goes through it.

Build: `lake env lean Submissions/arvi_rip/Coherence.lean` (about 11 s on a warm cache).
