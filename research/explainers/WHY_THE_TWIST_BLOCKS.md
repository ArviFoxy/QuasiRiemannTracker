# Why the slot twist blocks the proof (harmonic-analysis view), and the tensor picture

Question from Arvi (2026-10-25): why is the twist blocking us, in Fourier terms? Could tensor
networks or representation theory help with these multilinear forms?

## The objects

- **Rows.** Quadratic characters `χ_k`, `N(k) ≤ K`. These are `K` Fourier modes on the
  multiplicative group of `Z[ω]`.
- **Columns.** A vector `c(n)`, `N(n) ~ N` with `N > K`:
  `c(n) = g̃(n)·A(n)` and `A(n) = Σ_{P~L} a_P (n/P)₃`.
  - `g̃(n)` are the normalized cubic Gauss sums, i.e. the Fourier coefficients of Kubota's cubic
    theta function `θ₃`.
  - `A(n)` is a combination of `L` cubic characters, the slots.
- **What P1 needs.** `Σ_k |⟨c, χ_k⟩|² ≲ K·‖c‖²`: every mode sees only its fair share of `c`'s
  energy. This is needed for `N` slightly above `K` (use (b): `N = K^{1+1.1e-4}`).

## 1. The frame bound is an uncertainty principle

`K` modes in `C^N` with `N > K` span a `K`-dimensional subspace `V`.
- A vector inside `V` puts all its energy into the modes, which costs `N` per unit of energy (the
  large sieve's `N` term).
- A vector spread out relative to `V` costs `K` (the diagonal).

So "diagonal" means that `c` is incoherent with the modes. That is an uncertainty statement: `c`
cannot be concentrated on the span of the quadratic characters.

## 2. How the method normally wins: Fourier self-duality

- **Poisson summation is the Fourier transform.** A smooth sum of length `N` against a character
  of conductor `q` equals a dual sum of length `q/N`.
- **Theta reflection is stronger.** The coefficients of `θ₃` are, up to normalization, their own
  Fourier transform (automorphy), like a Gaussian. A sum of `g̃(n)` of length `N` reflects to a sum
  of `g̃` of length `C/N`, where `C` is the conductor. The self-dual point `√C` is the critical
  length.
- **Either way the sum is short.** Below `√C` the sum is short. Above it, reflect and it becomes
  short. A short sum has a diagonal frame bound, so no `N` term is ever paid.

## 3. What a twist does

- **A twist is a modulation.** Multiplying `θ₃`'s coefficients by a character of conductor `q`
  spreads the spectrum. The twisted series is self-dual only at conductor `q²·C`, so its critical
  length moves out by a factor `q`.
- **The row twist is built in.** The rows twist by `χ_k`, with conductor about `k`. Without slots
  the critical length is about `K`, matching the `K` rows.
- **The slot twist breaks the match.** The slot twist `(n/P)₃` multiplies the conductor by `N(P)²`,
  so the critical length becomes about `K·L`.

## 4. The dead zone

For `K < N < K·L` a sum of length `N` has no short side:
- it is too long for the frame bound to be diagonal, because `N > K`;
- it is too short for the duality to help, because reflection gives length `(KL)²/N > KL > N`,
  which is longer.

In time–frequency terms the vector is short neither in `n` nor in the dual variable, and the
uncertainty principle forbids making both short. The binding configurations of the proof sit just
inside this window: use (a) at `N = K·L`, use (b) at `N = K^{1.0001}`.

## 5. Why positivity cannot cross it

- **The only route left.** Inside the window, expand `|·|²` and apply Poisson in the rows `k`.
- **The `N` term comes back with signs.** The off-diagonal becomes a dual quadratic form whose
  terms carry signs from quadratic reciprocity, and its diagonal reproduces exactly the `N` term.
- **So beating `N` needs cancellation in a signed sum.** That is an asymptotic formula with a
  power-saving error, not an inequality.
- **Positivity forgets the signs.** Any positivity step (Cauchy–Schwarz, triangle inequality,
  dropping terms) loses the signs and gives `N` back.

So the twist blocks the proof by moving the self-dual point (`KL`) away from the number of modes
(`K`). That opens a window where the method has no short side, and crossing it needs cancellation
that positivity cannot see.

## 6. The tensor picture

Let `S(k, P) = Σ_n g̃(n) χ_k(n) (n/P)₃` be the `K × L` matrix of twisted central values. Then

  `S = Σ_{n≤N} g̃(n) · u_n ⊗ v_n`, with `u_n = (χ_k(n))_k ∈ C^K` and `v_n = ((n/P)₃)_P ∈ C^L`.

This is a sum of `N` rank-one tensors weighted by the unimodular theta phases `g̃(n)`. P1 asks
for the operator norm `‖S‖² ≲ K·N` (use (a)), against the trivial `≈ N²`.

- **Random phases solve it.**
  - If the `g̃(n)` were independent random phases, non-commutative (matrix) Khintchine would give
    `‖S‖² ≲ max(L·‖Σ u_n u_n*‖, K·‖Σ v_n v_n*‖) ≈ K·N`, which is exactly P1. Both frame operators
    are about `N·I`, by the large sieve.
  - Numerically the true matrix is within 2% of the random-phase one
    (`round7/signal-processing/`). So P1 is a derandomized matrix Khintchine for the theta phases.
- **The deterministic tool is the trace method:** `‖S‖^{2p} ≤ tr((SS*)^p)`.
  - **The trace is a ring tensor network.** It has `2p` Gauss sums around a cycle, joined by
    propagators: `⟨u_n, u_{n'}⟩` (short quadratic character sums) and `⟨v_n, v_{n'}⟩` (cubic).
  - **What is known and what is not.** Paired cycles give the random-phase value. Every other
    cycle needs cancellation in `2p`-point correlations of cubic Gauss sums along multiplicative
    patterns.
  - **`p = 2` is already open.** It is the mixed-moment lemma of `../P1_PROBLEM.md`. It needs the
    single-mark sum `F_P` below `N²/√L`, a twisted second moment of `θ₃` at its own self-dual
    point.
- **Representation theory.**
  - `g̃(n)` are Fourier coefficients of `θ₃`, a vector in an automorphic representation of the
    3-fold metaplectic cover of `GL(2)` over `Q(ω)`. Twisting is tensoring with idele-class
    characters.
  - Correlations of `θ₃`'s coefficients are governed by its spectral theory: Rankin–Selberg,
    shifted convolution sums, a metaplectic Kuznetsov formula. A derandomization would come from
    there: write `tr((SS*)²)` spectrally and show that the non-paired part is small.
  - The `GL(2)` analogue (quadratic twists of a fixed form, uniform in a thin family) is open as
    well.
- **A concrete handle.** Twisted multiplicativity, `g̃(a)g̃(b) = g̃(ab)·(cross symbols)` for coprime
  `a, b`, can contract the ring network algebraically.
  - Products of Gauss sums around a 4-cycle collapse to Gauss sums at products.
  - That may reduce `tr((SS*)²)` to second moments of twisted `θ₃`, where Rankin–Selberg results
    exist (Lindelöf on average in the cubic-twist aspect, de Faveri–Dunn–Hoffstein).
  - This is the next thing to check, numerically first.
