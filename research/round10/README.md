# Round 10: the long witness from the real-L-function side (2026-10-25)

Context: the bar needs 6.1e-6 beyond the face family's 0.874725, and every lever reduces to P1 or
the long Möbius moment (atom 2). Round 9 showed that `ρ(ν)` is the value of a lattice game.
This round asks whether the structure of real L-functions (Euler product, functional equation,
the bin's zero-free window, a global zero-free strip) gives the defender anything the game
leaves out. Conditional values are in `../round9/conditional/`: a diagonal long moment would be
worth −7.9e-3 on the return alone, and the bar needs only a `U^{1.5e-4}` saving at `r ≈ 1.155`.

## 1. Pieces of the long witness under `μ·log = −Λ∗μ` (`pieces.py`, `pieces.log`)

On squarefree `n`, `μ(n) log n = −Σ_{p|n} log p · μ(n/p)`. So
`M(D) log D ≈ −Σ_P Q(P)·M(D/P)` over dyadic prime blocks `Q(P) = Σ_{p~P} χ(p) log p`.

The tools on bin rows:
- The amplitude cap (7/8 Lemma 19.1, from the bin's zero-free buffer) bounds the prime block
  pointwise: `|Q(P)|² ≤ P^{1+δ}`.
- The Möbius factor gets a mean value: the inverse moment if `D/P ≤ U`, amplification if longer.

With `P = U^p` and `D = U^t`, the piece's count exponent is:
- `1 − tδ + pδ` for `p ≥ t − 1`;
- `L(t) − (5/6 − δ)p` for `p < t − 1`.

A piece beats the amplified long line `L(t) = (1 + 5t)/6 − δt` exactly when
`p < (L(t) − 1 + tδ)/δ`. At the lattice adversary's own length `t = 3s₀`, that bound is exactly
`p < s₀`.
- A prime factor shorter than `s₀` beats `ρ`.
- The adversary's pieces sit at `p = s₀` (count exactly `ρ`), `2s₀` and `3s₀` (worse).
- So the identity reproduces the game exactly. Round 3 recorded the fixed point; this shows
  where it binds.

Numbers: at `t = 1.155`, `δ = 0.4546`, the pieces beat `L(t) = 0.6041` for `p ∈ (0, 0.284)`, with
the best `0.545 = 1 − δ` at `p = t − 1`. Pieces with a long prime factor are worse, reaching 1 at
`p = t` (the primes themselves).

## 2. Amplification is the 11/12 strip

The amplified exponent is `(1 + 5t)/6 = 1 + (t − 1)(2·(11/12) − 1)`: the excess length `t − 1`
costs exactly what a pointwise bound from a zero-free strip at `11/12` would. Two consequences:
- Amplification gives the inverse second moment `Σ_u |1/L(σ + it, χ_u)|² ≪ U^{1+ε}` exactly for
  `σ > 11/12`. Summing the amplified blocks `D^{1/2−σ}(U^{1/6}D^{5/6})^{1/2}` converges iff
  `σ > 11/12`.
- **Global-strip bootstrap.** The proof is by contradiction, so we may assume the refuted zero
  has maximal real part `β*` (≈ 0.875). Then every row is zero-free right of `β*`, and every
  Möbius or prime block has `|·|² ≤ B^{1 + δ*}` with `δ* = 2β* − 1 ≈ 0.749 < 5/6`.
  - A clean factorization `(short factor of length D/U, pointwise) × (Möbius of length U, inverse
    moment)` would then give the long line slope `δ* ≈ 0.749` instead of `5/6`. That is a
    10% lower slope, worth far more than the bar (1% is worth −3.9e-4 on the return alone).
  - No identity gives that factorization. Every one includes pieces whose short factor is
    longer than `D/U`:
    - Vaughan's Type II middle range (both factors near `√D`);
    - Heath-Brown's all-Möbius products, which have no mean value;
    - the long-prime pieces of `μ log = −Λ∗μ` (count up to 1.34 with `δ*`, column 2 of
      `pieces.log`).
  - Contour-shifting the whole block to `Re s = β*` loses the full `D^{δ*}`, not `(D/U)^{δ*}`.
  - This is a sharper form of round 3's "splitting rows by zero supremum is circular". The
    supremum gives a strong pointwise bound, but the method has no factorization that uses it
    only on the excess length.

## 3. The adversary as a real L-function

The two-term model `1 + bU^{−s₀(s−a)}` has its zeros on `Re s = a`, in a vertical progression of
density `s₀·log U/(2π)`. That is a fraction `s₀ ≈ 0.41` of all zeros in a unit window. On the
critical line it has `|L| ≈ U^{s₀δ/2}`.
- **Littlewood.** A fraction `c` of the local zeros at `Re ≥ a` forces the window average of
  `log|L(1/2 + it)|` to be at least `cδ/2·log U`.
  - The diagonal fourth moment then counts such rows by `U^{1 − 2cδ}`; at `c = s₀` this is `ρ`
    (round 7).
  - A `2k`-th moment with excess `ε_k` gives `1 + ε_k − k s₀ δ`. So a sixth moment with excess
    below `s₀δ ≈ 0.18` would beat `ρ`. The known route, a pointwise bound times the fourth moment,
    has excess `2κ`, with `κ` the subconvexity exponent (`3/16` Burgess-type, so 0.375).
- **Window convexity.** A bin row is zero-free right of `a` in its window. Borel–Carathéodory and
  Hadamard's three circles give Lindelöf there (`|L(σ + it)| ≤ U^{o(1)}` for `σ ≥ a + η`).
  Phragmén–Lindelöf with the functional equation then gives `|L(1/2 + it)| ≤ U^{δ/4}`, i.e.
  `c ≤ 1/2`.
  - The adversary fits because `s₀ < 1/2`. This is the same constraint as round 9's "reflected
    bound, which needs `s₀ ≤ 1/2`".
  - Killing the adversary pointwise needs a window subconvexity better by `U^{(1/2 − s₀)δ/2}`
    (≈ `U^{0.02}`): at most a fraction `s₀` of the local zeros at `Re ≥ a`, not `1/2`.
- **The functional equation adds nothing.** The two-term model alone violates it: it has
  `|L(1 − a)| ≈ U^{s₀δ}`, where the equation requires `U^{δ/2}`. But a real L-function with the
  same Dirichlet-coefficient profile satisfies it through the dual sum of the approximate
  functional equation, which supplies the `U^{δ/2}` without touching any witness. The
  coefficient-level adversary is consistent.

## 4. Status

The barrier is now stated in four equivalent ways, all at the same value `ρ`:
- the lattice game (round 9);
- the `μ log = −Λ∗μ` pieces, binding exactly at `p = s₀`;
- Littlewood with the fourth moment, binding at a zero fraction `s₀`;
- window convexity versus a needed window subconvexity of `U^{0.02}`.

Each "free" structure of real L-functions (Euler product, functional equation, the bin's window,
the global supremum strip) is already used or is consistent with the adversary. Moving `ρ`, and
hence the bar, needs one of:
- a long-moment saving past `D = U`;
- a sixth moment with excess below `s₀δ`;
- a window subconvexity;
- a factorization identity whose pointwise factor is confined to the excess length.

## 5. Two structural reasons the long moment resists (added the same day)

- **Every decomposition carries the long prime sum.** `μ log = −Λ∗μ`, Vaughan, Heath-Brown and
  largest-prime splittings all contain the piece with `n` prime, i.e. `Q(D) = Σ_{p~D} χ(p)`.
  - This family has no mean value for prime sums beyond `U^{1/2}`. The general sextic sieve
    (7/8 Lemma 9.1) carries `(KD)^{2/3}`, and the reflected witnesses need Möbius coefficients.
  - The only bound on `Q(D)` for `D > U` comes through the Möbius polynomial itself:
    amplification of the inverse moment bounds it implicitly.
  - So no identity can confine the pointwise factor to the excess length `D/U` (§2).
- **Poisson duality is exactly self-dual.**
  - Poisson in the rows writes the off-diagonal as `(U/D²)·[Σ_{h ≲ D²/U}|T_h|² − (dual diagonal)]`,
    with `T_h = Σ_n μ(n)ε(n)χ_n(h)` and `ε(n)` the normalized sextic Gauss sum.
  - The dual is in the diagonal regime (`D²/U > D`). A power-saving asymptotic for it, with
    relative error `(D²/U)^{−η}`, `η > (t − 1)/(6(2t − 1)) ≈ 0.02`, would beat amplification at
    `t = 1.155`.
  - But Poisson in `h` returns the original off-diagonal, up to fixed reciprocity twists from Θ:
    the root numbers combine to `|ε(n)|² = 1`.
  - So an asymptotic for the dual is equivalent to one for the original. Breaking the symmetry
    needs arithmetic input from outside Poisson duality: Möbius correlations, metaplectic spectral
    theory, or the bin structure.

## 6. Literature check (round 10)

- **Liu**, arXiv:2610.26835 (19 Oct 2026). Hecke L-functions over number fields via
  `K(ζ₁₂)` and class-field descent.
  - Boundary `B♭ = 0.874886647…`, the root of a quartic, reached by a limiting argument as the
    infimum of a refined comparison system.
  - It is behind upstream (0.874773) and us (0.8747289). Its ingredients (parameter variation,
    Xu–Sang's averaged numerator, limiting argument) add nothing new for the atoms.
  - The limiting idea (prove every `B > B♭`, conclude the open half-plane) is what the face family
    already does. The continuum ceiling 0.8747241 is 0.9e-6 from the face family and needs no new
    analytic input.
- **Darbar–Kerr–Munsch–Shparlinski**, arXiv:2604.02960. Zero density over sets of characters
  mod `q` with a small product set. Not applicable: the sextic family's product set
  `{χ_{uu′}}` has size about `U²`.
- **Sang** 2610.15291 (0.8748867) and the 2610.12234 parameter variations: as recorded before.
- Nothing found on sixth moments, short-sum large values or past-diagonal Möbius moments for
  cubic or sextic families.
