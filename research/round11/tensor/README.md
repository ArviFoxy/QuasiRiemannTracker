# Round 11: the tensor route to P1 (trace method, sectors, freeness)

Question from Arvi (2026-10-25): could tensor-network or representation-theory ideas handle the
multilinear forms behind P1?

**Answer.** The tensor view reduces P1 at use (a) to one clean statement:
- the fourth-moment network splits exactly into sectors;
- every sector but one is controlled rigorously, given the single-mark bound of
  `../bilinear_notes.md` §6 (a sketch);
- the remaining sector is an alternating fourth moment. It is small exactly when two explicit
  arithmetic operators are nearly *free* in Voiculescu's sense.

In the `Z[ω]` model the theta phases behave like random phases in this sector. No available tool
proves the needed cancellation, so the route does not reach the bar. One by-product looks worth
pursuing, averaging over the slot height. A formal-code study ruled it out (§7).

Scripts: `four_cycle.py`, `four_point.py` (data cached in `data/`, logs `*.log`). They reuse
`../../round7/signal-processing/{zw,build}.py`.

## 1. The objects

- **The matrix.** `S = Φ D X`, a `K × L` matrix:
  - `Φ(k,n) = (n/k)₂`;
  - `D = diag(g̃(n))`, the normalized cubic Gauss sums;
  - `X(n,P) = conj((n/P)₃)`, with `N(n) ~ N`.
- **Use (a)** sits at `N = K·L`, with `K = Z^{0.742}` and `L = Z^{0.129}`. The large sieve gives
  `‖S‖² ≤ N²`. The target is `‖S‖² ≤ N²·Z^{−0.001}` (`η = 0.0076`).
- **The trace method.** `‖S‖⁴ ≤ tr((SS*)²)`, so it suffices to show `tr((SS*)²) ≤ N⁴·Z^{−0.002}`.
- **Random phases** give `tr((SS*)²) ≈ N²KL(K + L) ≈ N⁴/L`, which is far below that.
  So use (a) needs the fourth moment only within `Z^{0.127}` of its random value. (Use (b) would
  need the `p`-th moment with `p ≈ 10⁴`, so this route is for use (a) only.)
- **As a ring network.** `tr((SS*)²) = tr((B̃A)²)`, with two propagators between the four theta
  vertices:
  - `A = ΦᵀΦ`, the quadratic propagator, `A(n,m) = Σ_k χ_k(nm)`;
  - `B̃ = D B D*` with `B = XX*`, the cubic propagator dressed by the theta phases,
    `B̃(n,m) = g̃(n)B(n,m)conj g̃(m)`.

## 2. Exact sector decomposition

Split each propagator into its diagonal (`d`, `n = m`) and off-diagonal (`o`) parts. The 16 traces
`tr(B̃_x A_y B̃_z A_w)` add up to `tr((SS*)²)`. In each, the theta phase is
`g̃(n₁)conj g̃(n₂)g̃(n₃)conj g̃(n₄)`, and a diagonal propagator identifies two vertices.

| class | sectors | phase | bound at use (a) |
|---|---|---|---|
| phase-free | `odod`, `dodo`, `dddd`, … (opposite diagonals, or ≥ 3 `d`) | 1 | rigorous, see below |
| 2-point | exactly one `d`, or two adjacent `d` | `g̃(n)conj g̃(m)` | `≈ w·(‖S‖_F² − diag)` |
| 4-point | `oooo = tr((B̃_o A_o)²)` | all four | open |

**Phase-free sectors** (rigorous):
- `odod = Σ_{n≠m} K_nK_m|B(n,m)|² ≤ K²‖X*X‖_F² ≈ K²LN² = N⁴/L`, by cubic orthogonality, since the
  conductors `L²` are much smaller than `N`.
- `dodo ≤ L²‖ΦΦᵀ‖_F² ≤ L²·K(K + N)N ≈ N⁴/K`, by the quadratic large sieve.

**2-point sectors.** Each equals a weight `w ∈ {KN, LN, KL}` times the off-diagonal part of the
second moment, `‖S‖_F² − Σ_{k,P}Σ_n|·|²`, up to lower-order terms. Checked numerically below.
- The single-mark bound `F_P ≪ N·K^{7/6}` gives `‖S‖_F² ≤ N²K^{1/6}`.
- So these sectors are `≤ KN·N²K^{1/6} = N⁴·Z^{−0.0053}`, which is enough.
- The bare large sieve (`‖S‖_F² ≤ LN²`) gives only `N⁴`, which is not.

**The 4-point sector is the whole problem.** By Cauchy–Schwarz,
`|oooo| ≤ ‖B̃_oA_o‖_F² = tr(B_o²C²) ≈ N²‖S‖_F²`, with `C = D*A_oD`.
- At Lindelöf-on-average (`‖S‖_F² ≈ N²`, unproved) that is `N⁴`, exactly the threshold. A power
  saving `N^{−0.0023}` below Cauchy–Schwarz would then pass.
- With the single-mark Frobenius bound it needs `N^{−0.144}`. That is essentially the full random
  cancellation, which numerically is about `N^{−0.148}` for theta.

## 3. Three equivalent forms of the missing 4-point lemma

- **Commutator / freeness.**
  - `tr(B_oCB_oC) = tr(B_o²C²) − ½‖[B_o, C]‖_F²`. So the 4-point sector is small exactly when the
    off-diagonal cubic slot Gram `B_o` and the theta-conjugated quadratic Gram `C = D*A_oD` are
    "maximally non-commuting".
  - In free-probability terms: the alternating moment `τ(b c b c)` of two centred elements
    vanishes when they are free.
  - Conjugation by random diagonal unitaries makes such matrices asymptotically free
    (Anderson–Farrell, *asymptotically liberating sequences*).
  - P1(a) via the fourth moment is therefore **derandomized asymptotic freeness** under the
    diagonal unitary `diag(g̃)`. The literature has nothing for deterministic arithmetic phases. The
    closest derandomizations use Legendre symbols, for RIP, via Weil (Bandeira–Fickus–Mixon–Moreira).
- **Cauchy–Binet.**
  - `tr((SS*)²) = ‖S‖_F⁴ − 2Σ_{k<k′, P<P′}|S(k,P)S(k′,P′) − S(k,P′)S(k′,P)|²`.
  - So the fourth-moment route needs a *lower* bound for the 2×2 minors: `S` must be far from low
    rank in mean square.
- **Schur–Weyl.**
  - With `Π = S⊗S`, `tr((SS*)²) = ‖Π_sym‖² − ‖Π_anti‖²`.
  - Random matrices have the symmetric and antisymmetric parts nearly equal in norm.

## 4. Contracting the ring by twisted multiplicativity

`g̃(n₁)g̃(n₃) = g̃(n₁n₃)(n₁/n₃)₃` turns `S(k,P)S(k′,P′)` into one theta sum of length `N²`. Its
coefficients are twisted divisor sums `Σ_{n₁n₃=a}(n₁/n₃)₃ f(n₁)h(n₃)`, the Dirichlet convolution of
two twisted theta series.
- That product has conductor about `(K²L)²` and length `N² = K²L²`. So it is past its critical
  length `K²L` by `L`, with dual length `K²`.
- But nothing links the two factors of `tr((SS*)²)` except the shared labels `k, k′, P, P′`. The
  contraction rewrites the fourth moment rather than shortening it.
- The metaplectic reason: products of theta coefficients are coefficients of `θ₃ ⊗ θ₃`. For `θ₃`,
  prime dilations are not Hecke operators, only cube dilations are.

## 5. Numerics (`Z[ω]` model, true `g̃` against random unimodular phases)

| model | `K′, N′, L′` | `tr4` theta / random | phase-free share | 2-point share | `oooo` share | `oooo/CS` theta | `oooo/CS` random |
|---|---|---|---|---|---|---|---|
| `K=200, N=2·10⁴, L=100` | 50, 2574, 20 | 4.32e11 / 3.8–4.8e11 | 0.97 | −0.004 | +0.033 | +9e-4 | −1e-3 … +2e-4 |
| `K=400, N=4·10⁴, L=200` | 98, 5170, 32 | 1.04e13 / 0.97–1.02e13 | 0.954 | +0.018 | +0.026 | +7e-4 | −5e-4 … −2e-4 |

- **The 2-point sectors match** `w·(‖S‖_F² − diag)`. For example, in the larger model, random draw 0:
  `odoo = 0.0121` against the predicted `K′N′(‖S‖_F² − diag)/tr4 = 0.0130`.
- **The 4-point sector** sits about 1000× below its Cauchy–Schwarz bound, for theta as for random
  phases. Theta's value is slightly positive in both models (random ones change sign). This is a
  small bias, possibly from the Gauss-sum bias at squares, and it shrinks from 0.033 to 0.026
  with size.
- **The normalization holds:** `CS/(N′²‖S‖_F²) = 0.94–0.95`.

## 6. Where the representation theory would have to enter

The freeness statement is about `θ₃`'s coefficients as a vector, against two operator algebras
generated by quadratic and cubic characters. A spectral proof would expand the alternating moment
over the automorphic spectrum of the 3-fold cover:
- Rankin–Selberg / shifted convolutions of `θ₃` give the 2-point information that the 2-point
  sectors already use;
- the alternating 4-point term needs a 4-point (triple-product-type) spectral input that is not
  available, even for `GL(2)` quadratic-twist families.

## 7. By-product checked and dropped: slot averaging plus the single-mark lemma

- **The idea.** Averaging the column branch over the slots' Mellin height (`T ≫ L`) or over random
  slot signs would remove the cross terms `P ≠ P′`. The single-mark lemma (`η ≈ 0.041` on the
  slot-diagonal part) would then be enough for use (a).
- **Why it fails.** A scoping study of the formal code (`../tau_average_scope.md`, with file:line
  evidence) shows the count cannot do this, for two independent reasons:
  1. **Pointwise use.** The count applies the marked inverse moment pointwise in the slot height:
     the batch's fixed point `z`, or each row's own height. Its gain `2qz` is the size of the slot
     sums at that point, made coherent by the zero through the explicit formula.
  2. **Averaging erases the gain.** Any average that removes `P ≠ P′` (Montgomery–Vaughan with
     `T ≫ L`, or random signs) also forces every row's averaged slot energy down to `O(‖a‖²)`. That
     erases the HIGH amplitude classes. Paying the window in Chebyshev instead gives the I-line
     `1 − δr − 2qz + z`, which is worse than no marks: 0.6627 against 0.6040 at the binding.
- **The averaged moment is trivial anyway.** It is diagonal from the unmarked inverse moment
  alone. So round 9's dismissal stands, for this reason rather than "Frobenius = N-term".
- **The range is not available either.** Slot heights are at most `Z^{2τ} ≤ L^{1.6·10⁻⁵}`.
- **What the formal library has** (same study):
  - a general Voronoi/reflection identity for `θ₃` twisted by sextic characters of a finite prime
    family;
  - the cubic and quadratic sieves and the hybrid norm, for general vectors;
  - no sextic large sieve;
  - the long line, for Möbius polynomials only.

## 8. Verdict

- The tensor/trace route turns P1(a) into one lemma: a 4-point cancellation, equivalently
  derandomized freeness of `B_o` and `diag(g̃)* A_o diag(g̃)`. The numerics support it.
- No known tool proves it. Even its Cauchy–Schwarz form needs the Frobenius norm at
  Lindelöf-on-average.
- Use (b) is out of reach of the trace method.
- The slot-averaging by-product in §7 is ruled out: the count needs the slot sums pointwise at
  each zero's height.
