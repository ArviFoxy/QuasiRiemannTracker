# Frontier after the selected-leaf PR (#97, θ = 0.87341198)

**Update (2026-10-31).** Upstream merged #98 and #99. Bebel's open #100 and #101 refine #99 at the 1e-16 level
(0.87338196661320752), so the bar stays θ ≤ **0.8733319666**. New today, none of it a θ gain: the price of rank
(`../orders/README.md`: no other power-residue family beats the sextic base), the residue mechanism of the sextic
outlier and the masked-null two-sided tests (journal, 2026-10-31).

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

## Open question: a power saving off both thetas

**A proof route with the right exponent (2026-10-31; derived + Lean arithmetic, journal "de Faveri's recursion, run
off the spikes").** de Faveri proves the optimal sieve (arXiv 2610.04045) by a Poisson/monotonicity recursion whose
fixed point 1 + 1/n is the theta exponent. Run off the twisted source thetas of kernel norm ≤ M, the Poisson step
keeps only kernels above M, and monotonicity conserves A·M. The theta term is then A·B^γ along the orbit, and the
iteration becomes α ↦ 2 + γ − (1+γ)/α, with attracting fixed point **1 + γ**: exactly (LS off V) with twist range
B^{1−6γ} (`../lean/arvi_kwall/OffSpikeIteration.lean`). Open, in order:
1. the dual problem's own thetas at the fixed point (the correction becomes multi-level; level-2 directions
   conj g̃² carry an angular Hecke twist and show no excess numerically);
2. restriction to sub-lattices (gcd sorting, the b^♮ b^* split, coprimality), handled by the corrected form
   rather than orthogonality;
3. combining the row side into one two-sided statement.
The cubic family (explicit Gauss sums, one theta) is the place to try these first. The older sketches below
stayed at the self-dual point.

Can the Heath-Brown / de Faveri recursion (Poisson, duality, recursion on the large sieve constant) prove a power
saving for the sextic large sieve at L = B once both thetas are removed (`../lean/arvi_kwall/SourceSpike.lean`)?
Three fresh-look attempts (2026-10-31) each ran out of output budget before writing anything, so there is no
analysis yet. A future attempt should be split into separately briefed pieces: (1) the Poisson step for G and H at
L = B with the primary/odd normalization; (2) whether the corrected remainder is self-similar under duality; (3) the
cubic check, where the two thetas coincide.

**First sketch (2026-10-31, heuristic).**
- The mechanism agent's exact Poisson formula (`../rip/theta/theta_dualcore.py`, Task A) writes the off-diagonal Gram
  as D_g̃·(Σ_h w_h conj χ(h) χ(h)*)·D_g̃*, with dual length about B at L = B.
- The spikes are the h with a large sixth-power part. Remove them, and the remainder is the Gram of the dual family
  on sixth-power-free h: again a balanced sextic large sieve, so the structure is self-similar.
- At the next level, the sixth-power-free restriction is a Möbius sum over d⁶. It multiplies that level's theta
  multiplicity by Σ_{N d ≤ Y} μ(d)/N(d), which tends to 0 only like the prime number theorem error exp(−c√log Y).
- So the naive corrected recursion gains a sub-power factor, not a power. A power saving would need the dual family's
  own spikes (twists, sources) handled with a genuine saving at each level. The open question is whether the
  two-sided projection supplies that.

**The source spikes are residues, and that changes what Λ_src is (2026-10-31; numerical + heuristic, journal "The
block outlier is a residue").**
- The source theta's row image is one vector built coherently over every source scale. This fits the residue of
  the sextic Kubota series in the source variable: `E f(z) ≈ L^{1/3} conj τ₆(z)`, with `τ₆` the sextic theta
  coefficients.
- A twisted source spike `f(x)(x/m)₆` has row image `z ↦ Φ(zm)`, and `Φ` is the same residue, so it is about
  `L^{1/3} τ₆(zm)`.
- **Cubic case.** Patterson's `τ₃` is a Gauss sum, hence twisted-multiplicative. Then `τ₃(zm)` factors into `τ₃(z)`,
  `τ₃(m)` and residue symbols, and `Λ_src` is again a twist sieve, which the amplification step handles.
- **Sextic case.** `τ₆` has no such factorization (no unique Whittaker model for n = 6 > r + 1). So `Λ_src` is a
  bilinear form in sextic theta coefficients at products, `Σ_m |Σ_{z∈W} b_z τ₆(zm)|²`. That is a new object, not a
  twist sieve.
- Its natural tool is the automorphy of `θ₆` itself: detect `n ≡ 0 (mod z)` additively and use the theta
  transformation at the cusps `a/z`. Whether the leftover twist after that step is quadratic (as for the cubic
  theta, where it makes the quadratic large sieve sharp) is the next thing to check.
- Numerically the twisted images are flat on slot-selected rows at 3·10⁴ (journal, "Twisted source spikes are flat
  on slot-selected rows"), so `Λ_src(W) ≈ ρ Λ_src` there.

**What the K-wall needs, split by the residue picture (2026-10-31; heuristic map, nothing proved).**
- On a slot-selected set W, `selected_of_gradedTwoSided` bounds the selected norm by `C B^{1+ε} + Λ_row + Λ_src`.
  The first term is the two-sided spike-free conjecture: open, and as hard as a large sieve past the √-barrier.
- The residue parts have explicit shapes, so their dilution on W is a separate question:
  - **untwisted residue** (`τ₆` on the rows). W is a large-value set of a slot sum `T(z) = Σ_π χ_z(π)`. Moments
    `Σ_z |τ₆(z)|² |T(z)|^{2k}` expand into `Σ_z |τ₆(z)|² ψ(z)` for characters ψ whose conductor is a product of slot
    primes. These are Rankin–Selberg sums of `θ₆` with itself, twisted by ψ. Metaplectic Rankin–Selberg theory
    (meromorphic continuation, a pole only for ψ trivial) should give power savings for small conductors. That
    would prove the residue's energy on W is its density share. Plausibly within reach; not attempted.
  - **twisted residues** (`τ₆(zm)`). Their Gram on W has entries `Σ_{z∈W} τ₆(zm) conj τ₆(zm′)`: multiplicative
    shifted convolutions of theta coefficients. Without twisted multiplicativity for `τ₆` there is no known tool.
- So, beyond the conjecture itself, the sextic K-wall's new arithmetic input is a shifted-convolution bound for
  sextic theta coefficients at products. The cubic analogue would follow from Patterson's formula.
- **Revised (2026-10-31, journal "Λ_src is a Rankin–Selberg problem").** The twisted part is a dilation, Φ_m(z) = Φ(zm),
  so the amplified Gram on W is Σ_z ψ(z) τ₆(zm) conj τ₆(zm′): a Rankin–Selberg integral of the dilated thetas θ₆(m·),
  θ₆(m′·), twisted by the amplifier's characters, not an additive shifted convolution. The ψ = 1 part is the
  Petersson Gram of the dilated thetas; numerically that family is as well-conditioned as the masked null's images.
  The ψ ≠ 1 parts are entire. de Faveri–Dunn–Hoffstein's regularized metaplectic Rankin–Selberg is the tool. So
  the K-wall chain's three inputs are (i) the off-spike recursion, (ii) amplification, and (iii) this Rankin–Selberg
  computation. None is a classical open problem, but each is a long technical program.
- **Duality does not close `Λ_src` (checked, 2026-10-31).** By `rowInner_rowImage`,
  `Σ_i w_i |⟨b, E s_i⟩|² = Σ_i w_i |⟨E^H b, s_i⟩|² ≤ β_src ‖E^H b‖²`, with `β_src` the Bessel constant of the weighted
  source spikes in source space. That gives `Δ_W ≤ C B^{1+ε} + Λ_row + β_src Δ_W`, which closes only if `β_src < 1`.
  But `CorrectedLargeSieve` must cover the outlier itself, which forces `w_i ≳ 1/‖s_i‖²` and so `β_src ≥ 1`. So
  `Λ_src` needs a direct bound: flatness of the residue images on W.
- **For the Dunn–Radziwiłł route** (journal 2026-10-30, obstacle 3: "the sextic theta function has no explicit
  coefficients"). The term a corrected sextic large sieve has to subtract is the residue of the sextic Kubota series,
  which is what the numerics now show the outlier to be. That term exists analytically whether or not `τ₆` is
  explicit, and an upper bound needs its size and its interaction with the remainder, not its values. Its size is
  Rankin–Selberg, `Σ_{N z ≤ X} |τ₆(z)|² ≍ X^{5/6}`. So obstacle 3 is less "no explicit formula" than "no Type II
  (bilinear) estimate for `g̃₆(ab)` with the residue removed", the sextic analogue of their Prop 10.1. [heuristic]

## Queued directions

### Q1. A product (tensor) RKHS for the dual frame, with a multiresolution that resolves W at its own coarse scale (queued 2026-10-31, Arvi)

Origin: the RKHS/basis-pursuit discussion of 2026-10-30. Status [heuristic]; nothing built yet.

**The lever.** `../lean/arvi_kwall/DualFrame.lean` proves the dual-frame bound
Σ_{z∈W} |D(z)|² ≤ c_W(Q)·λ_max(M*QM)·‖a‖² for every positive definite row metric Q. Here
c_W(Q) = sup{⟨v, Q⁻¹v⟩ : v a unit vector supported on W}. The bound is exact as Q → P_W, so the design of Q is the
whole content.
- Q = I is the trivial restriction bound.
- A generic smooth Q, i.e. a generic RKHS on the frequency side, cannot help at L = B. The balanced point is
  critical (Nyquist) sampling, so there is no room for smoothing that ignores the arithmetic.

**The proposal: build Q from the structure that defines W.**
- **Products of short pieces.** Slot-selected rows are cut out by products of short prime sums
  T_i(z) = Σ_{p∈P_i} c_p χ_z(p) over disjoint prime ranges P_i. The characters factor over the same pieces:
  χ_z(n₁n₂) = χ_z(n₁)χ_z(n₂). So take a product kernel Q = ⊗_ℓ Q_ℓ, one factor per prime-size scale ℓ. With such a
  kernel, ⟨Ma, QMa⟩ should factor over the pieces of the sources.
- **A multiresolution that resolves W at its own coarse scale.** The cells at level ℓ are the joint values of
  (χ_z(p))_{p ≤ P_ℓ}. W is measurable at the level ℓ_W of the slot primes.
  - Make Q exact (cell-resolving) at levels ≤ ℓ_W. Then c_W(Q) = O(1) when W is a union of cells.
  - Make Q smooth (averaging) above ℓ_W. That is where λ_max(M*QM) should gain over the plain large sieve.
- **Include the theta's coarse structure.** The theta spikes are Gauss sums times class functions of z mod 36
  (journal, 2026-10-31: supplementary twists by λ, ω and 2). The same coarse levels can carry them, which links this
  to the spike-free conjecture (`SexticSpikeFree.lean`; corrected to the two-sided form in `SourceSpike.lean`).

**First steps.**
1. Wait for the wide-kernel Q test at B = 10⁴ (large-B numerics agent, `../rip/theta/theta_dualframe.py`).
2. Build a two-level product Q at B = 10⁴: exact on the slot-prime cells, averaging on the rest. Compute c_W(Q) and
   λ_max(M*QM), and compare with Q = I and Q = P_W.
3. Lean: a Kronecker-product lemma, i.e. the dual-frame bound for Q = Q₁ ⊗ Q₂ with factorized c_W.

**What would kill it.** λ_max(M*QM) does not drop below the plain large sieve once c_W(Q) is kept O(1). That would
mean the coarse cells carry no averaging gain at the balanced point.

**First results (2026-10-31; `../rip/theta/theta_ampframe.py`, log `theta_ampframe_B10000.log`).** Setting: B = L = 10⁴,
W the top 10% of rows by |T|, T the slot sum over the 10 split primes with norm in [40, 80], |W| = 281.

| metric Q | bound | note |
|---|---|---|
| truth \|E_W\|²/S | 1.768 | |
| oracle P_W + 0.1 I | 1.857 | |
| Q = I | 4.261 | trivial |
| single amplifier \|T\|²/A | 4.015 | −6% |
| ½ amplifier + ½ I | 3.480 | −18% |
| squared amplifier | 9.83 | worse |
| mean of slot sums at three scales | 11.4 | worse |
| geometric mean of the three scales | blows up | |

- **Amplification is the diagonal case of the dual-frame bound.** With Q = |T|²/A we have Q ≥ 1 on W and
  ⟨Ea, QEa⟩ = Σ|TD|²/A.
- **Naive multi-scale families fail.** Slot sums at other scales are uncorrelated with W (correlation about −0.01 to
  −0.06), and normalizing them on W wrecks c_W. The coarse level must be W's own defining scale.
- **The best diagonal Q is the oracle**, the indicator of {|T|² ≥ A}. So Q1 becomes: approximate that indicator by
  structured weights whose λ_max(EᴴQE) is provable. (An earlier version of this note said higher polynomial degree
  gets closer to the oracle. The second scan below shows the opposite for positive polynomials in |T|².)
- **Open question:** can a non-diagonal Q (a true RKHS on the rows) beat every diagonal one at the same proof cost?

**Second scan and controls (2026-10-31; `theta_ampframe.py` with model `rand`, `theta_ampfree.py`; logs
`theta_ampframe2_B10000.log`, `theta_ampframe_rand_B10000.log`, `theta_ampfree_B10000.log`).** Same setting. Below,
x = |T|²/A, so x ≥ 1 exactly on W, and every metric is normalized so that c_W = 1. The columns are:
- sextic E: the bound for the sextic matrix;
- random E: independent sixth roots of unity on the same zero pattern, with W and x built the same way from the
  random slot columns;
- free edge: the edge of the free Poisson law of the weights,
  λ₊(q) = min_w [1/w + (1/S)Σ_z a_z/(1 − a_z w)] with a_z = s²q_z and s² = 0.951 the fraction of nonzero symbols.
  For q = 1_W this is the Marchenko–Pastur edge (1 + √(s²|W|/S))².

| metric q | dynamic range on W | sextic E | random E | free edge | sextic / free |
|---|---|---|---|---|---|
| truth, 1_W | 1 | 1.768 | 1.678 | 1.677 | 1.054 |
| oracle 1_W + 0.1 | 1 | 1.857 | 1.770 | 1.767 | 1.051 |
| Q = I | 1 | 4.261 | 3.944 | 3.951 | 1.078 |
| x, the single amplifier | 2.90 | 4.015 | 3.687 | 3.750 | 1.071 |
| x² | 8.44 | 9.831 | 9.111 | 9.265 | 1.061 |
| ½x + ½ | 1.95 | 3.480 | 3.294 | 3.338 | 1.043 |
| x^{1/2} | 1.70 | 3.121 | 2.961 | 2.994 | 1.042 |
| min(x, 1) + 0.03 | 1 | 2.462 | 2.335 | 2.363 | 1.042 |
| min(x, 1)⁴ + 0.1 | 1 | 2.109 | 1.982 | 2.014 | 1.047 |

(`theta_ampfree_B10000.log` has all 16 metrics. The ratio sextic/free stays in 1.04–1.08 on every line.)

- **The table is free probability.** The free edge reproduces the random matrix within 2% on every line, and within
  0.5% for the truth, the oracle and Q = I. The sextic matrix is the free edge times a nearly uniform 4–8%, which is
  its theta excess at B = 10⁴. The ranking of diagonal metrics carries no
  arithmetic.
- **The amplifier's loss is its dynamic range.**
  - A single-row test vector a = conj(e_z)/‖e_z‖ concentrates D on one row, so the bound is at least about
    max_z q_z / min_W q.
  - For x this test alone gives 3.43 of the 4.02.
  - Capping x at 1 on W removes 70% of the amplifier's excess over the truth: 4.015 → 2.462, against a truth of 1.768.
  - Positive polynomials in x, the provable ones, are increasing on W. So raising the degree widens the dynamic
    range: x² is worse than x.
- **These are constants, not exponents.** A slot sum has sub-Gaussian tails, so over R rows the dynamic range of x is
  about log R / log(1/ρ). That is a B^{o(1)} loss. Metric design among diagonal Q moves constants only.
- **The exponent content is in proving λ_max(EᴴQE).**
  - For Q a polynomial in slot sums, EᴴQE is the Gram of the longer, amplified family. Its bound is that family's
    large sieve at an unbalanced point, theta excess included.
  - Non-diagonal Q built from character features χ_z(m) (the product kernels of the proposal) turn EᴴQE into Grams of
    dual sums Σ_z χ_z(n)·conj χ_z(m) over the moduli. Those are large sieves on the dual side, with their own theta.
- **The coarse structure that matters is the spike family.**
  - Take the non-diagonal metric Q = P_V^⊥ + ε·P_V, with V the spike family of `SexticSpikeFree.lean`, extended by the
    source-theta images of `SourceSpike.lean` (twisted thetas
    and supplementary class functions: low twists, coarse congruence data).
  - Then c_W(Q) ≤ 1 + ‖P_V P_W‖²/ε, and λ_max(EᴴQE) ≤ λ_max off V + ε·(spike strength).
  - The dual-frame bound becomes "large sieve off V, plus the spikes' overlap with W". That is the recursion
    inequality S_W ≤ Δ + Λ_W of the K-wall (task 197).
  - So the "include the theta's coarse structure" part of the proposal is the spike-free conjecture itself. The rest
    of Q1 moves constants.

**Status [numerics at 10⁴ + derivation].**
- As a separate lever, Q1 is closed: the optimal diagonal metric is known in closed form (the free edge is minimized
  by the oracle), and its exponent content reduces to the spike-free conjecture.
- What would reopen it: a metric whose EᴴQE has a provably smaller theta excess than the plain large sieve. The
  sextic/free column is the quantity to watch. If it shrank with B for some structured Q while staying flat for Q = I,
  that Q would be a lever. A B-scan of that column is the one remaining test.
