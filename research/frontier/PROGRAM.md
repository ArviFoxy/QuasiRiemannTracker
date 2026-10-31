# The faces program: dependency tree, sizes and risks (2026-10-31)

One page that collects what the journal entries of 2026-10-31 established about the only new-math route whose open
inputs are of known type. Evidence tags as in `../journal/JOURNAL.md`.

## Goal and payoff

A face past Λ = 2 in the count and physical faces. **Λ ≈ 1.967 clears the bar** θ ≤ 0.8733319666 (5e-5 below
PR 99) at the banked design.
- This is the float model of the newTop row, `fresh-look/second/base_models/worth.py`, with h = 0.8097. At
  Λ = 2.0001 it reproduces the bank, 0.87338228. Λ = 1.97 gives +4.2e-6 against the bar and 1.96 gives −1.15e-5.
- At PR 97's design (h = 0.8001361) the same bar needs Λ ≈ 1.951. The roadmap payoff with both walls moved is −1e-4 to −5e-4 (`README.md`, "Roadmap for the faces").

Both walls must move:
- the **K-wall** (K < 1/2), at slope ≈ 0.48 with excess γ ≈ 0.015;
- the **reference wall** (target 2), the short reference past √A for smooth × prime vectors.

Either alone buys nothing (journal, "Faces past Λ = 2"; target 2 alone moves the native end from 2.005 to about
2.003).

## Dependency tree

| id | input | type | status | size |
|---|---|---|---|---|
| A | **6-fold Kubota theory, index aspect**: continuation and functional equation of ψ⁽⁶⁾(m, w) (index conductor N(m)), polynomial growth on Re w = 1/2 + ε, uniformly in m | classical (Kubota 1969 for general n); not formalized anywhere | missing | paper-level in Lean (the baseline's cubic development is 53k lines) |
| A′ | Lindelöf on average in the index aspect, Σ_{N(m)≤M}\|ψ⁽⁶⁾(m, 1/2 + ε + it)\|² ≪ M^{1+ε}(1 + \|t\|)^R | from A plus the sextic large sieve (approximate functional equation of length ≤ N(m)^{1/2} keeps Sil's Θ₆ diagonal) | missing; the cubic analogue is David–de Faveri–Dunn–Stucky Lemma 6.6 | moderate once A exists |
| A″ | Mellin rescue: Mellin-zero plain vectors (and convolutions with the zero in the long factor) have spike correlations at square-root size on average over twists | A + A′ + contour shift | numerically at the null (twist, dilation, convolution, mollified shapes; `../rip/theta/`) | small once A, A′ exist |
| B | **Target-2 decomposition**: ‖E_{A,B}λ‖² ≤ C(AB)^ε{A‖λ‖² + (A/B)Σ_{N(h)≤B²/A} w_h\|⟨λ, f_h⟩\|²} for B ≤ A^{2/3} | fork of Sil's `SievePoissonBound` (kernel split, Gauss-sum factorization of the dual terms) and `SieveDescent` | restricted descent in Lean (`../lean/arvi_kwall/RestrictedDescent.lean`) | moderate (≈ 1–2k lines) |
| C | **Corrected recursion** for the K-wall: de Faveri's recursion run off the spikes to the fixed point 1 + γ, in weighted form G ≼ B^{1+γ}I + Σ w_f ff* over the generated family | elementary, new; a fork of Sil's formal sieve | iteration arithmetic (`silStep`, `tendsto_silIter`) and transposition (`TransposeCorrection.lean`) in Lean; step 3's corrected Cauchy–Schwarz and level closure are the open core | paper-level, then a large fork |
| D | Λ_row: row thetas on slot-selected rows, closed by amplification | `SpikeRule.lean` (formal for slopes > 7/36) | conditional on C | small |
| E | Face forks: native or density machinery carrying the new gates | Lean engineering on the 119 ReturnD modules and the face chain | not started | large |

Order: A → A′ → A″ feeds B (reference wall) and C (K-wall); C → D; B, C, D → E.

## What is settled (2026-10-31)

- **The 6-fold cover is unavoidable for a power saving.**
  - Plain sums meet the sextic spikes. By Möbius absorption those are Möbius-signed cubic sums, which the cubic
    theory does not reach.
  - A Rankin–Selberg square of θ₃ against the cubic Kubota Eisenstein series does give the sextic series. But it
    carries ζ_K(3w − 1) from the theta's cube support (τ₃(cd³) = N(d)^{1/2}τ₃(c), a Lean theorem). A power saving
    that way needs RH for ζ_{ℚ(ω)}.
  - Inside the bootstrap it gives only X^{0.6245}. The K-wall's tolerance would need θ₀ ≤ 0.52.
- **The cubic analogues are theorems on paper** (DdFDS24 Lemmas 6.6–6.7), and in Lean only for pole-free sums.
  - The baseline's reflection is for ∂̄θ₃.
  - A cubic polar Voronoi twin is about 3k lines. It is a template only: the faces need n = 6.
- **The design rule for vectors.** The pole sits in the long factor; a Mellin zero or a Möbius sign there removes
  the spike. Either factor of a convolution can carry it.
- **Exact orthogonality is impossible** (dilations fill the space). The corrected sieve must be weighted, with
  explicit corrections, and it transposes with image corrections (Lean).

## Risks, in order

1. **C's level closure.** The corrected Cauchy–Schwarz must pull the dual's spikes back to explicit corrections,
   with a family that closes up. This is numerically supported (`theta_level2`, `theta_local_spikes`) but
   unproved. It is the only mathematical risk that is not of classical type.
2. **A's size.** It is classical, but no proof assistant has the n-fold Kubota Eisenstein series for n ≥ 4. The
   baseline's n = 3 development is the template. How much of it is generic in n is unmapped.
3. **D1's low slopes** matter only if D1 replaces the faces route. The faces route needs the K-wall near slope
   0.48 only.

## Alternatives (each blocked by a named open problem)

| route | blocked by | comparison class |
|---|---|---|
| P1 (inverse slot cost 1.9709 at the current bar) | power saving in a self-dual affine multiple Dirichlet series | fourth moment of quadratic L-functions over number fields: log savings only (Li 2024) |
| D2 (P1 at fixed indices, η₀ ≈ 0.002) | the same affine series, continued past w = 1 | known over function fields, open over number fields |
| B2 (long slope, saving 0.1782 against deletion's 1/6) | twisted Chowla for Möbius past the family size | classical open |
| D1 (prime-pool face) | the K-wall at all slopes, or the plain eighth moment of the thin family | Lindelöf on average for an eighth moment |
| D4 (sixth moment) | thin-family sixth moment past the row count | open |

## The other architecture: PR 96 (blocked by size and verification, not by an open problem)

- PR 96 (liqsweep, 224 pages, no Lean) replaces OpenAI's probe by a sextic × cubic two-slot probe with a Hecke target
  of nonzero infinity type. It claims 0.8392.
- Its own constraint model, re-derived in `../pr96/CONSTRAINTS.md`: 0.8791 with de Faveri's sieve and its chart, and
  0.8656 with the Voronoi chart dpx. Below 0.87 it needs the K-chart infrastructure and dpx or the graded inverse
  theorem GS1.
- Its polar objects are cubic. It imports Kazhdan–Patterson for n ∈ {3, 6}, but downstream uses only D̃₃, with
  twists of every infinity type. So it needs no 6-fold cover, but it does need non-spherical cubic Eisenstein series.
- **Cost.** A new probe layer (the OpenAI analogue is ≈ 264k lines), Hecke characters with infinity type (10–20k), the
  uniform cubic Voronoi split (5–15k), angular Poisson (2–4k) (`../pr96/LEAN_INVENTORY.md`).
- The 3k-line cubic polar formula is the l = 0 slice of its Chapter 2. That is a direct ingredient, where the faces
  route uses it only as a template.

## Recommendation

- No θ gain is in reach of library-only or engineering work. The architecture limit (0.87338197) is PR 99's value.
- Every gain needs either a classical-but-unformalized theory (A) plus new elementary sieve work (C), or one of
  the named open problems.
- On paper, C is the piece to settle first: it is elementary, carries the only non-classical risk, and Sil's formal
  sieve is its base.
- In Lean, B is the cheapest standalone theorem: a corrected unbalanced sextic large sieve.
