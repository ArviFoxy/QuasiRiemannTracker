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
- the **K-wall** (K < 1/2), at slope ≈ 0.48 with excess γ → 0: the selected norm at its fixed point up to Z^ε
  (journal, "The K-wall tolerates no excess", 2026-10-31; the earlier γ ≈ 0.015 came from a coarse grid);
- the **reference wall** (target 2), the short reference past √A for smooth × prime vectors.

**What each wall must reach (journal, "Downstream to the bank", 2026-10-31).**

| end face Λ | θ* − bar | cut K | short-reference threshold γ |
|---|---|---|---|
| 1.9673 (the bar) | 0 | 0.4877 | 0.509 |
| 1.965 | −3.6e-6 | 0.4870 | 0.5095 |
| 1.93 | −6.0e-5 | 0.474 | 0.519 |
| 1.85 | −1.8e-4 | 0.446 | 0.543 |

- The reference wall is a constant in Sil's root interval, not a slope. So it needs only B ≤ A^{0.51} at the bar,
  where target 2's corrections run over twists N(h) ≤ A^{0.02}.
- **It needs no metaplectic input** (journal, "The reference wall needs no metaplectic input"). The reference's
  vectors are convolutions with the slot primes. Gauss-sum multiplicativity makes every spike correlation a bilinear
  sextic form in (s, q²), and Sil's formal `OptimalBound` bounds it pointwise in the twist. The short reference is
  then diagonal up to b ≤ min((1 + S)/2, 3/4 − S, (6 + S)/11), which covers every face down to Λ ≈ 1.80. Input A is
  needed for the K-wall only.
- The K-wall binds. At the bank's interface it is the single statement `NaturalSelectedCellNormFrom δ₀`
  (`../lean/arvi_polar_sketch/RootEnergyFrom.lean`: it gives R1 at every K ≥ δ₀ + 10⁻⁶).
- The scalar gates of the line close down to Λ = 1.965 at K₀ = 0.4869, γ₀ = 0.51 (`Walls.lean`).

Either alone buys nothing (journal, "Faces past Λ = 2"; target 2 alone moves the native end from 2.005 to about
2.003).

## Dependency tree

| id | input | type | status | size |
|---|---|---|---|---|
| A | **6-fold Kubota theory, index aspect**: continuation and functional equation of ψ⁽⁶⁾(m, w) (index conductor N(m)), polynomial growth on Re w = 1/2 + ε, uniformly in m | classical (Kubota 1969 for general n); not formalized anywhere | missing | 15–30 person-months (agent scoping, 2026-10-31): the baseline's ≈ 14k-line analytic spine is generic, but it has no functional equation or growth bound even for n = 3. N1a (series, germ at 7/6) 4–7, N1b +2–6, N3 (functional equation) 8–18, N2 (growth) +1–2 |
| A′ | Lindelöf on average in the index aspect, Σ_{N(m)≤M}\|ψ⁽⁶⁾(m, 1/2 + ε + it)\|² ≪ M^{1+ε}(1 + \|t\|)^R | from A plus the sextic large sieve (approximate functional equation of length ≤ N(m)^{1/2} keeps Sil's Θ₆ diagonal) | missing; the cubic analogue is David–de Faveri–Dunn–Stucky Lemma 6.6 | moderate once A exists |
| A″ | Mellin rescue: Mellin-zero plain vectors (and convolutions with the zero in the long factor) have spike correlations at square-root size on average over twists | one dominant smooth factor: three Poisson steps prove it only for twist ranges H ≥ B^{0.51–0.63}; below, the squarefree support of the Gauss-sum vectors puts cubic symbols (h/d)₃ into the Möbius blocks of the dual, which defeat the last Poisson step, so A (or a squarefree sieve in the dual) is needed again (journal, "The owed check", second correction, 2026-10-31); balanced convolutions: see A‴ | numerically at the null (twist, dilation, convolution, mollified shapes; `../rip/theta/`) | small for one dominant factor (Sil's `pair_poisson` and the baseline's reflection are steps 1–2) |
| A‴ | **Balanced convolutions** (the K-wall's binding corner x₁ ≈ x₂ ≈ 0.40–0.5): twist mean square ≤ B^{5/6+γ}H^{1/6}‖v‖² for B^{0.23} < H < B^{0.76} (γ → 0), i.e. Lindelöf on average for a fourth moment of the sextic family | a power-saving asymptotic for a smoothed fourth moment of short sextic character sums; A and A′ do not reach it | **open, type unknown** (natural tool: a metaplectic Kuznetsov formula on the 6-fold cover) | unknown |
| B | **Target-2 decomposition**: ‖E_{A,B}λ‖² ≤ C(AB)^ε{A‖λ‖² + (A/B)Σ_{N(h)≤B²/A} w_h\|⟨λ, f_h⟩\|²} for B ≤ A^{2/3} | fork of Sil's `SievePoissonBound` (kernel split, Gauss-sum factorization of the dual terms) and `SieveDescent` | restricted descent in Lean (`../lean/arvi_kwall/RestrictedDescent.lean`) | moderate (≈ 1–2k lines); the bar needs it only up to B ≤ A^{0.51}, and for the reference's slot-convolution vectors the dual terms are bounded by Sil's `OptimalBound` alone (no A) |
| C | **Corrected recursion** for the K-wall: de Faveri's recursion run off the spikes to the fixed point 1 + γ, in weighted form G ≼ B^{1+γ}I + Σ w_f ff* over the generated family | elementary, new; a fork of Sil's formal sieve | iteration arithmetic (`silStep`, `tendsto_silIter`) and transposition (`TransposeCorrection.lean`) in Lean; step 3's corrected Cauchy–Schwarz and level closure are the open core | paper-level, then a large fork |
| D | Λ_row: row thetas on slot-selected rows, closed by amplification | `SpikeRule.lean` (formal for slopes > 7/36) | conditional on C | small |
| E | Face forks: native or density machinery carrying the new gates | Lean engineering on the 119 ReturnD modules and the face chain | not started | large |

Order: A → A′ → A″ feeds B (reference wall) and C (K-wall); C → D; B, C, D → E. A‴ feeds C at the balanced corner.

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
2. **A‴, the balanced corner (2026-10-31).** The K-wall's binding geometry has two plain factors of comparable
   length. Their twist mean square in B^{0.25} < N(m) < B^{0.67} is a fourth-moment-type statement, beyond A. This is
   now the largest risk.
3. **A's size.** It is classical, but no proof assistant has the n-fold Kubota Eisenstein series for n ≥ 4.
   - Mapped 2026-10-31: the baseline's analytic spine (≈ 14k lines) is generic in n. The sextic needs Γ(12), the
     quadratic Kubota character and 21 cusps.
   - The baseline has neither the functional equation nor any growth bound, even for n = 3. So A costs
     15–30 person-months.
4. **D1's low slopes** matter only if D1 replaces the faces route. The faces route needs the K-wall near slope
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

## The reference fork in Lean (plan, 2026-10-31)

- Sil's `SievePoissonBound.coherent_weighted_bound` already writes the dual sum as a bilinear form. It splits it
  by Cauchy–Schwarz into two completed sieves λ(L₁, N₁)·λ(L₂, N₂) over rows V·K (gcd part times dual frequency).
- In the reference regime, the √-barrier excess there is the sixth-power multiplicity of the dual frequencies:
  K = K₀·D⁶ gives the same row character on sixth-power-free sources.
- The fork:
  1. extract the sixth powers from the dual frequencies (Sil's `SieveDescent` already does this);
  2. for the repeated rows, bound each correlation pointwise by the bilinear bound for slot convolutions, instead
     of by the sieve;
  3. keep the rest of Sil's proof.
- The bilinear core (phase multiplicativity under CRT; Cauchy–Schwarz into `OptimalBound` with rows q²) is being
  formalized in `Submissions/arvi_prime_dilation/`.

## Recommendation

- No θ gain is in reach of library-only or engineering work. The architecture limit (0.87338197) is PR 99's value.
- Every gain needs either a classical-but-unformalized theory (A) plus new elementary sieve work (C), or one of
  the named open problems.
- On paper, C is the piece to settle first: it is elementary, carries the only non-classical risk, and Sil's formal
  sieve is its base.
- In Lean, B is the cheapest standalone theorem: a corrected unbalanced sextic large sieve. For the reference's
  slot convolutions it needs no metaplectic input (above).
- So the bar is gated by the K-wall alone: the balanced-point corrected sieve (C) plus input A, or Λ_src. Prime
  dilation provably does not help at the balanced point: the dual problem there is balanced again, with about B
  frequencies, and pointwise bounds cannot sum them.
- **Update (2026-10-31, journal "Three Poisson steps …").** Input A is neither necessary nor sufficient for the
  K-wall:
  - not necessary away from the balanced corner for twist ranges H ≥ B^{0.51–0.63}, where three Poisson steps give
    A″ for one dominant smooth factor (withdrawn below that range the same day: the squarefree support of the
    Gauss-sum vectors blocks the last Poisson step; see the journal's second correction);
  - not sufficient at the binding corner, where the leaf vector is a balanced convolution of two plain factors and
    the band B^{0.25} < N(m) < B^{0.67} needs A‴, a fourth-moment-type input that A and A′ do not reach.
  - So the faces route to the bar has an open input of unknown type, and the 15–30 person-month estimate no longer
    bounds its cost.
