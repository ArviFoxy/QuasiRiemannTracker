# Frontier after the selected-leaf PR (#97, θ = 0.87341198)

Next bar: θ ≤ 0.87336198. Evidence tags as in `../journal/JOURNAL.md` (entries of 2026-10-30).

**Position (2026-10-30, end of day).**
- **Banked in Lean:** θ = 0.87338228 (`../lean/arvi_bank/`). That is −2.97e-5 against #97 and 2.03e-5 short of the
  bar. No library-only lever remains.
- Every route to the bar needs one of three open problems:
  - **P1**, the θ-biased quadratic sieve: inverse slot cost 1.9882 alone suffices. This is the cheapest single
    route.
  - **B2**, twisted Chowla (rate-6 deletion): long slope 0.8328.
  - **The faces' two walls:** the √A reference (target 0/1) and K ≥ 1/2.
- All three are the Kummer-twist rates (2 for slots, 6 for deletion and packing) meeting the Gauss-sum bias
  (journal: "Map of walls by Kummer rate").

## Where the bound binds

The return binds on the newTop edge, uncapped count branch, at δ ≈ 0.452 (zeros at real part 0.726) and p = 1/2.
There θ moves by ≈ 0.12 × (change of the count). The count is ≈ 0.607 and the bar needs ≈ 0.6066 without the banked
levers.

## What each new input would be worth

Computed with `worth.py` and `density_past2.py`, the float model of the newTop row. It reproduces 0.87341197.

| input | Δθ |
|---|---|
| banked engineering: line to Λ = 2.0001 (no fork) | −7.4e-6 |
| banked engineering: h = 0.8097 with `floor_margin` ≤ 1/1000 (fork the 119 ReturnD modules for `BoundsN`), with the line | −2.97e-5 in total: **0.87338228, built in Lean** (`../lean/arvi_bank/`, 150 modules, 17.5 min summed) |
| long slope 5/6 → 0.8226 (the B2 long Möbius moment) | −5.4e-5 |
| face at Λ = 1.97 / 1.9 (B = 0.99999) | −5.1e-5 / −1.6e-4 |
| trading B for Λ past 2 at slope s0 | pays iff s0 < 0.089 |

## Why each is hard

- **Count words.** Three bounds compete:
  - the inverse word, amplified by the slot to length 1;
  - the plain word, through the face;
  - the long word, from the sixth-power thickening.

  The count already beats the ζ analogue of the best large-value theorem. With Guth–Maynard inputs the same
  minimax gives 0.620 (`../subroot/zd_calibration.py`, which reproduces Ingham, Huxley and Guth–Maynard exactly).
  Better large values buy nothing here.
- **Long slope 5/6.** The sixth-power thickening is tight for its method. Any improvement needs cancellation in a
  twisted Chowla-type Möbius correlation (`../P1_PROBLEM.md`), a classical open problem.
- **Faces below Λ = 2.** The ideal face is Λ = 1, so 2 is a limit of the method. Inside Sil's framework there are two
  walls.
  1. **Square-root cut.** Native steps stop at 6KB/(1 + K) = 2B because K ≥ 1/2. Density steps have slope
     σ = 0.110 > 0.089 at the end face, because their HIGH count gives κ(1/2) = 7/8; κ > 0.902 would be needed.
  2. **Root reference.** Every face lies in P + 2S + 9u/2 < 1. The 2 = 3/2 + 1/2:
     - 3/2 comes from the exceptional block's saving rate 2/3. That rate is sharp for one lemma only: rate 3/4 is
       reachable in Sil's FP version, but the cube-free fork that proves our line caps α < 2/3.
     - 1/2 comes from the short reference, at the diagonal threshold √A of the optimal general sextic large
       sieve (de Faveri, Thm 1.1).

## Single atoms that reach the bar from the engineering limit (second fresh look, LP game)

| atom | now | needed | problem |
|---|---|---|---|
| **slot cost in all three places** (inverse word, count face, physical face; `slotcost.py`) | 2 | **1.9936** | the √-barrier for prime vectors in the sextic large sieve |
| long slope | 5/6 | 0.83280 | B2 (twisted Chowla) |
| slot cost in the inverse word | 2 | 1.9882 | P1 (theta dilates against quadratic rows) |
| Λ in the count and physical faces | 2.005 | ≈ 1.987 | Sil's reference plus the square-root cut |
| p_max | 1/2 | 0.4934 | sharp |
| fibre margin | 0 | 0.00147 | no correlation between cutoffs is forced |

## Open new-math targets, in order of plausibility

0. **Break the √-barrier for prime slots with Dunn–Radziwiłł's dispersion** (journal 2026-10-30, "Dunn–Radziwiłł's
   corrected cubic large sieve"). Their Props 8.1 and 9.2, read with sharper bookkeeping, make the **cubic**
   large sieve diagonal for smooth prime vectors up to B ≈ A^{3/5}. That means a cost ≈ 1.67 per unit of slot
   width; the bar needs only 1.9936. Their GRH can be replaced by the bootstrap's zero-free half-plane
   Re s > β ≤ 7/8, and η = 1/3 comes from Heath-Brown–Patterson. Open steps:
   - a sextic (or quadratic × cubic) version;
   - (smooth × prime) vectors, since the face's plain factors are not w-rough;
   - Lean (the metaplectic stack).

   Reach: it acts on the faces' prime slots (Sil's √A reference), not on P1. P1 is a joint
   quadratic-row × cubic-slot norm, and for a single row the D–R sieve is in its B > A regime, where it does not
   help. The faces also need the native step's K ≥ 1/2 wall moved, so target 0 alone does not reach the bar.
1. **A structured sextic large sieve at the short reference.** It should be diagonal up to B ≤ A^{2/3} for
   smooth × prime vectors. Route: #96's graded inverse theorem, whose excess sits on correlations with (m₀/n)₆ for
   small m₀, plus a lemma that smooth factors kill those correlations (Pólya–Vinogradov). Paper theorem; not in
   Lean. It pays only together with item 2.
2. **The square-root cut in the leaf.** Either a selected bound for slot rows at slope just below 1/2, or a HIGH
   count with κ(1/2) > 0.902. The count-side version is beyond Guth–Maynard, but the leaf needs a different
   inequality, and it has not been priced.
3. **A face-proving method outside Sil's packing.** Selected rows already reach the ideal face (PR 93's selected
   norm); the loss sits on unselected rows. Unpriced.

## P1 route (2026-10-30)

P1 follows from a fourth-moment asymptotic for the matrix of twisted theta central values S(k, P): with random
sizes, Tr((SS*)²) ≈ KLN²(K + L), which gives ‖S‖²_op < N². The tool would be a multiple Dirichlet series for
quadratic twists of θ₃ ⊗ ψ_P. Nearest results:
- Dunn, arXiv 2403.13151: fixed cubic cusp form, coefficients over primes;
- arXiv 2607.27131: second moments of cubic L-functions over Q(√−3).

Neither covers twists of θ₃.

