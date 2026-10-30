# Frontier after the selected-leaf PR (#97, θ = 0.87341198)

Next bar: θ ≤ 0.87336198 (5e-5 below #97). Open upstream PRs: #98 (Bebel, θ = 0.8733821435) and **#99** (Bebel,
θ = 0.8733819666133, "positive-reserve-selected-gap": a selected-energy adapter for every fixed positive gap above
1/2, i.e. the engineering limit K → 1/2⁺ that fresh look 2 priced at 0.87338197). Against the best open PR the bar
is θ ≤ **0.8733319666**. Our bank (0.87338228) is 3.1e-7 above #99. Evidence tags as in `../journal/JOURNAL.md` (entries of 2026-10-30).

**Position (2026-10-30, end of day).**
- **Banked in Lean:** θ = 0.87338228 (`../lean/arvi_bank/`). That is −2.97e-5 against #97 and 2.03e-5 short of the
  bar. No library-only lever remains.
- **Upstream PR #98** (Joseph Bebel, open) proves θ = 0.8733821435 with the same three engineering moves (line to
  Λ = 2.00001, widened return geometry, five windows). It beats the bank by 1.4e-7. Once it merges, the
  engineering limit is taken and the full 5e-5 must come from new math (right-hand column below).
- Every route to the bar needs one of three open problems:
  - **P1**, the θ-biased quadratic sieve: inverse slot cost 1.9882 alone suffices. This is the cheapest single
    route.
  - **B2**, twisted Chowla (rate-6 deletion): long slope 0.8283 (pivot at t = 1, saving λ = 0.1717).
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

| atom | now | needed (#97 bar) | needed (#98 bar) | problem |
|---|---|---|---|---|
| **slot cost in all three places** (inverse word, count face, physical face; `slotcost.py`) | 2 | **1.9936** | **1.9844** | the √-barrier for prime vectors in the sextic large sieve |
| long slope (pivot at t = 1) | 5/6 | 0.82830 | 0.82180 | B2 (twisted Chowla); pinned: a Möbius sieve past the family size with saving (D/U)^λ, λ ≥ 0.1717 (#98 bar: 0.1782; deletion gives 1/6) |
| slot cost in the inverse word | 2 | 1.9882 | 1.9709 | P1 (theta dilates against quadratic rows); pinned: cross-moment (X), saving Z^{0.001} at the #97 bar |
| Λ in the count and physical faces | 2.005 | ≈ 1.987 | Sil's reference plus the square-root cut |
| p_max | 1/2 | 0.4934 | sharp |
| fibre margin | 0 | 0.00147 | no correlation between cutoffs is forced |

## The master conjecture (2026-10-30, night): one statement behind every new-math route

**(MC) Structured sextic sieve.** In the thin sextic family over Z[ω] (rows z, N(z) ~ Z), vectors built from
theta-uncorrelated factors (plain sums, prime pools with non-Patterson phases, and their products) are
*generic*: their large-sieve energies sit at the diagonal (Lindelöf on average, no N-term). The Gauss-bias excess
of the general sextic sieve lives only on the theta-type span.

| route | what it needs from (MC) | reduction | numerics |
|---|---|---|---|
| K-wall (faces' K ≥ 1/2) | dilution of the selected norm on slot-selected rows of slope ≤ 1/2 | `lean/arvi_kwall/Dilution.lean` | Gram is Marchenko–Pastur; slot-selected rows look random (RIP (2)) |
| D1, prime-pool face, row splitting | the same dilution; PR 93 covers slope > 1/2 at Λ = 1 | `lean/arvi_primeface/RowSplit.lean` | F/D = 1.00 ± 0.02 past both face lines; worst case Λ ≤ 1.07 (`rip/prime_pool/`) |
| D1, dispersion | the plain **eighth** moment Σ\|X₁X₂\|⁴ ≪ Z^{1+ε}‖c‖⁴ at total length ≤ Z; Huxley's large sieve over the twists (classical) | `lean/arvi_primeface/Dispersion.lean` | κ₈ = 5–7.4 against N-term sizes up to 10⁶ (`rip/eighth/`) |
| D4, sixth moment | plain sixth moment past the row count | – | M₆ = O(1) up to N³/R = 10⁷ (`rip/moments_probe/`) |
| D2, P1's weakest form | fixed-index cross-correlations of twisted theta columns | – | decay K^{−1/2} (`rip/moments_probe/`) |

- **Known cases:**
  - quadratic family, all vectors (Heath-Brown);
  - cubic family, prime vectors up to A^{3/5} (Dunn–Radziwiłł);
  - thin cubic and quartic families, character-sum moments, under GRH only (Gao–Zhao, arXiv 2508.14534).
- **Not available to us:** the bootstrap's half-plane does not replace GRH (it loses N^{0.75k}).
- **Structural leads:**
  - Davenport–Hasse makes sextic Gauss sums at squarefree arguments conjugate cubic ones times Hecke factors
    (`lean/arvi_primeface/Duplication.lean`).
  - In physical space χ₆ = χ₂·χ̄₃, so the sextic dictionary is the Hadamard product of the quadratic dictionary
    (Heath-Brown: diagonal for all vectors) and the conjugate cubic one. The product family over pairs (z, z′) is
    diagonal, and the sextic family is its diagonal: a thin-subset (RIP) question again.
- **The truth is far from every wall; the obstruction is proof.** The cleanest single target is the plain eighth
  moment: with Huxley it gives the prime-pool face with no face condition at all.

## Fresh look 2 (2026-10-30, late): the leading new-math line

- **D1, a face proved outside Sil's packing** (`../fresh-look/second/directions.md`). The target: the twisted
  fourth moment Σ_z|X₁X₂Q|² with a zero-forced prime pool Q is diagonal at prime cost Λ. Prices: Λ = 1.82 gives
  −3e-4, 5/3 gives −4.9e-4, 1.97 gives −5e-5. It bypasses the K-wall and the root reference: both belong to the
  native induction, not to the moment.
  - First brick in Lean: the quadratic Davenport–Hasse relation, which makes sextic Gauss sums at primes conjugate
    cubic ones times a Hecke factor (`../lean/arvi_primeface/`).
  - The ledger reduces to (L2), Heath-Brown–Patterson twisted by quadratic characters uniformly in the twist,
    and (L3), survival of the prime phase under Type-I plain coefficients (journal, "D1").
  - Numerology: Heath-Brown–Patterson in both prime variables of the dual pair sum gives Λ = 5/3.
- **Numerics agree that the truth is far from every wall** (journal, "D2 and D4 numerics"):
  - fixed-index cross-correlations (X_fix) decay like K^{−1/2};
  - the thin family's plain sixth moment has no congruence N-term;
  - the sextic Gram matrix is Marchenko–Pastur on slot-selected rows.

  All are instances of one structured large sieve: theta-uncorrelated vectors are generic for the sextic
  dictionary. D1 needs the smallest piece of it (prime pools).
- **Pricing rules from the same run:**
  - a count theorem valid only below slot slope 1/2 is capped at −7.6e-5, unless paired with PR 93's joint count
    J = 1 − ν above 1/2;
  - the amplitude-class corner reduces to round 10's wall.

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
   - **Barrier [Lean, built; `../lean/arvi_kwall/`].** Below slope 1/2, PR 93's amplify-and-reflect rules allow
     B^{7/6} at the balanced point L = B, even from the optimal sextic sieve Θ₆. A slope just below 1/2 therefore
     needs a direct operator-norm bound on the large-value rows at L = B, i.e. Guth–Maynard for the sextic family
     at the reflection's self-dual point.
3. **A face-proving method outside Sil's packing.** Selected rows already reach the ideal face (PR 93's selected
   norm); the loss sits on unselected rows. At the binding the slot slope is 2pδ ≈ 0.43 < 1/2, so every binding
   row is unselected. This target is therefore the face problem itself (the Λ row of the atom table), not a
   separate lever.

Write-up of target 0's mechanism: `DR_PRIME_SIEVE.md`.

**Decision (Arvi, 2026-10-30): no port of #96.** #96 is not formally verified, so we will not replace the ~205k-line
probe stack because of it. Its ideas (the K-chart, GS1, the Voronoi split) may be borrowed inside our stack.

## P1 route (2026-10-30)

P1 follows from a fourth-moment asymptotic for the matrix of twisted theta central values S(k, P): with random
sizes, Tr((SS*)²) ≈ KLN²(K + L), which gives ‖S‖²_op < N². The tool would be a multiple Dirichlet series for
quadratic twists of θ₃ ⊗ ψ_P. Nearest results:
- Dunn, arXiv 2403.13151: fixed cubic cusp form, coefficients over primes;
- arXiv 2607.27131: second moments of cubic L-functions over Q(√−3).

Neither covers twists of θ₃.

**P1 pinned down (deep-dive, 2026-10-30).** For the application's smooth slot weights, a Schur argument reduces
P1 to one estimate:

  (X)  |Σ_{k squarefree, N(k)≤K} S(k, P)·S(k, P′)‾| ≤ K·N·L^{−η}  for P ≠ P′,  η ≈ 0.0076.

That is a saving of only Z^{0.001} over the trivial bound. Notes:
- The n = m diagonal is ≈ KL, because (n/PP′)₃ cancels.
- Quadratic Poisson maps the k-sum (length K) to an h-sum of length N²/K and back, so the form is self-dual and
  every positivity step loses.
- There is no polar term to subtract: the twisted Kubota series is entire for χ_k ≠ 1.
- Square rows must be excluded, since they carry the pole.

Nearest tool found later: **#96's K-chart** (journal, "#96's K-chart is the nearest tool to P1"). The functional
equation of the cubic Kubota series at a fixed index shortens a quadratically twisted cubic Kubota sum to its dual
length, and then the quadratic large sieve applies. That is the move P1 needs, to shorten N = KL before the sieve.
It comes from an unrefereed preprint and is under evaluation.


## Classification of the three walls (2026-10-30, late)

Each wall is a power saving needed exactly at the self-dual point of a Poisson map. There, every positivity step
returns the trivial bound (journal: "One shape for all three walls").

| wall | needed | classified as | status |
|---|---|---|---|
| P1 / (X) | cross-moment saving L^{−η}, η ≈ 0.008 (#97 bar) or ≈ 0.017 (#98 bar) | second moment of quadratic twists of the index-P Kubota series: an **affine** multiple Dirichlet series (Cartan matrix [[2,0,−1],[0,2,−1],[−2,−2,2]], det 0). The twist conductor N(k)² is the double bond. | Same class as the number-field fourth moment of quadratic L-functions, where only log savings are known (Li 2024; Shen–Stucky 2024). Parabolic continuation plus Bochner does not reach the centre. The K-chart (#96) gives only single-index bounds. |
| B2 (long word) | N-term saving η ≥ 0.1717 (#97 bar) or 0.1782 (#98 bar) in the complete-family Möbius moment past H = D | the same core estimate as P1 (theta columns against quadratic rows after reflecting `RawMoment`), but needing η > 1/6 to beat deletion ("never combine") | twisted Chowla strength |
| faces' K-wall | selected norm at slope ≈ 0.48 within B^{0.015} of its fixed point at source length ≈ B^{0.96} (the t = 0 corner) | Guth–Maynard for a thin family at the kernel's self-dual point (conductors multiply). Equivalently, at the binding corner (two plain sums just below √(conductor), slot sliver s ≈ 0.03), a classical-strength structured face suffices: a twisted fourth moment of the sextic family whose prime twist goes past the √ limit, i.e. the faces' slot-cost atom again | barrier proved in Lean (`lean/arvi_kwall/`); the Θ₆ closure is about 11× too weak; the parent face only relieves the tiny-slot corner; pointwise bootstrap bounds on the plain sums do not help (journal, "K-wall corner") |
| faces' reference | short reference past √A for smooth × prime vectors | GS1-type structured sextic sieve (#96, unverified) | pays only together with the K-wall |
