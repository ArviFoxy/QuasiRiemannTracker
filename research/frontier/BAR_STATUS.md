# What clears the 5e-5 bar on the current design (2026-10-31)

One table of every lever priced in the float model of the newTop row (`fresh-look/second/base_models/worth.py`,
h = 0.8097), at the banked native-line design: end face (B, Λ) = (0.99999, 2.0001), K = 1/2 + 10⁻⁶. The model
reproduces the bank, 0.87338228. Bar: θ ≤ 0.8733319666 (5e-5 below PR 99). The binding point is newTop, δ = 0.426,
p = 1/2. Prices are first order [numerical]; each "needs" column is the single-lever requirement.

## The levers

| lever | sensitivity | bar needs | what it requires | status |
|---|---|---|---|---|
| end face Λ (native line) | ≈ 1.5e-5 per 0.01 in Λ | Λ ≤ 1.9673 | one of the three rows below | — |
| ↳ cut K < 1/2 (K-wall) | Λ_end ≈ 6KB/(1+K) | K ≤ 0.4877 | PR 93-type selected norm below slope 1/2 **at its fixed point** (excess γ → 0; the corner fails for every γ > 0 as the slot width → 0). At the binding corner the leaf vector is plain × plain at self-dual length, so this is Lindelöf on average for a fourth moment of the sextic family | open; beyond input A (journal 2026-10-31, "balanced corner", "tolerates no excess") |
| ↳ envelope coefficient c < 6 | ≈ 5e-5 per 0.1 in c | c ≤ 5.9 | a selected-block type with cost (e, c, r) better than Sil's simple D⁴ block (1, 6, 1): barrier cqB/(e + qr) | rigidity: every twist-free block has c = 6; twisted types lose the room (R2 ledger) |
| ↳ doubled-block share φ | barrier 3B/(1.5 + φ) at q = 1/2 | φ ≈ 2.5% | squared-prime slots visible to zeros | no mechanism (`DIRECTIONS.md` D2) |
| long slope (B2) | ≈ 4.3e-6 per 0.001 of saving | saving 0.178 (deletion: 1/6) | Möbius sieve past the family size, saving (D/H)^λ with λ ≥ 0.178: twisted Chowla | open (journal 2026-10-30, "B2 pinned") |
| numerator capacity C at the binding | ≈ 2.3e-5 per 0.001 | +0.0022 (the cap then binds at 0.0607) | more capacity from the physical face | no mechanism: the physical face is one linear face (B fixed along the native line), so the Cauchy–Schwarz midpoint rule (T8′) gains nothing here |
| D2 (P1, weakest form) | — | η₀ ≈ 7e-4 | power saving in the cross moment (X) for fixed P ≠ P′ (affine multiple Dirichlet series past w = 1) | open over number fields (known over function fields); numerically η₀ ≈ 1/2 |
| D4 (sixth moment, thin family) | — | ε₆ ≈ 0.115 | sixth moment of plain sums in the thin sextic family | proven ε₆ ≤ 0.213; numerically ≈ 0 |
| D1 (face outside Sil's packing) | — | Λ ≤ 1.97 | the K-wall at every slope (constant excess ≲ 0.034 at slope 1/2 absorbable) plus the Mellin rescue | open |

Not levers: the end face's cap (θ* does not depend on it at the binding), numCap alone, the face parameter B
(θ* rises by ≈ 1.6e-4 per 0.01 decrease in B), the prime-dilated reference alone (moves the native end by ≈ 10⁻⁴).

## What the 2026 literature says

- de Faveri–Dunn–Hoffstein (arXiv 2607.07911) prove that the cubic and quartic large sieves are not orthogonal and
  conjecture the order-n operator norm A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n} (X^{7/6} at the balanced point
  for n = 6). So the excess is real for general vectors, and every lever above that touches the sieve must use the
  structure of its vectors.
- Diaconu–Ion–Paşol–Popa (arXiv 2607.27131): second moments of r-th order Hecke L-functions via multiple Dirichlet
  series. No fourth moment of a cubic or sextic family is known.

## Side results of this round (no θ yet)

- Prime-dilated short reference: the reference wall needs no metaplectic input; Lean core done
  (`lean/arvi_prime_dilation/`, `correlation_bound`).
- Three Poisson steps evaluate the twist mean square of one smooth Gauss-sum factor without the functional equation
  (the polar term comes from ζ_K(6s) at s = 1/6). Checked against DFDH (journal, "The owed check", 2026-10-31):
  - Their route is on the twist side (Kubota series, Rankin–Selberg, Lindelöf on average). Ours is dual and
    elementary.
  - Every step is now written, including non-squarefree h and squarefree sources.
  - The polar shape |W̃(s₀)|²H^{1−1/n}X^{1+2/n} matches the existing logs for n = 3 (H- and X-scaling) and n = 6.
  - Its one gap against DFDH is the restriction to squarefree twists, which our K-wall does not need.
- Bilinear balanced-point bound for a ⋆ b (balanced, arbitrary coefficients): B^ε(B + X + B^{5/6}X^{5/18}), excess
  1/9 instead of 1/6.

## Literature, re-checked late October 2026

No fourth moment, Lindelöf-on-average or structured large sieve for cubic or sextic families has appeared since
July; the nearest new items are Dunn's bilinear sieve for metaplectic cusp-form coefficients (arXiv 2403.13151 v5)
and the PGL₂ cubic moments of Hu–Petrow–Young (arXiv 2506.14741 v2).

## Reading

Every lever that would clear the bar on its own is one of three named problems: a sharp fourth moment of the sextic
family on balanced smooth convolutions, a Möbius sieve past the family size (twisted Chowla), or a power saving in
an affine multiple Dirichlet series. The native line itself is rigid: its barrier is Λ = c·κ·B/(e + κ·r), and the
known block types give c = 6 with κ ≥ 1/2.
