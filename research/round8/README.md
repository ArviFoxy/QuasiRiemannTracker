# Round 8: the large-sieve input revisited, and the chain's optimality in Lean (2026-10-25)

Context: the Lean proof now uses the face family (`../faceless-chain/`) and reaches 34989/40000
internally (`Candidate.bound_sharp`). The milestone 0.8747189 needs 6.1e-6 more. The chain and the
return are at their ceiling (`../chain-structure/README.md`, `../LOG.md` "Last checks"), so the
missing amount must come from an analytic input. The cheapest is the column branch P1
(`../atom1/README.md`): about `K^{1.2e-4}` in the probe (use (b)), or `η ≥ 0.0076` in
`(K + N^{1−η}K^η)` for the inverse-moment budget (use (a)).

## 1. Proved: the switching flow is the maximal admissible envelope

`../lean-lab/ChainOptimal.lean` (compiles, standard Mathlib):
- `Q_mono`: every class threshold `6q_p = 5A_p/D_p` increases with the plain length `E`, because
  `D_p = pA_p + (1 − p)²E` and `A_pE′ − A′_pE = (4ps − 2)(E′ − E)`.
- `rate_mono`: the class descent rate `QE/(1 − Qs)` increases in `Q` and in `E`.
- `maximal_envelope`: every envelope that passes all class gates stays below the flow driven by a
  binding class (local comparison principle).
- `closed_form_binding`: in the interior regime the binding class is
  `p* = (a² + ab − 1)/(b(a − 2b))` and its rate is the closed form (via the sum of squares of
  `ChainAMGM.lean`).

The hypotheses (`A_p, D_p > 0`, `1 − Q_ps > 0`, `4ps < 2` for all `p ∈ [0, 1/2]`) hold along the
whole chain with margins `A ≥ 0.169`, `D ≥ 0.293`, `1 − Qs ≥ 0.871`. `p*` is interior from
`s ≈ 0.0194` on (0.63 at `s = 0.0123`, 0.49 at `0.0199`, 0.21 at `0.0424`). The early regime is covered too
(`half_binding`): `A_{1/2}D_p − A_pD_{1/2} = (1/2 − p)·h(p)` with `h` linear in `p`,
`h(0) = 2s(2 − E) − 4(1 − E)²` and `h(1/2) = s(8 − 7E − 4s) − 4(1 − E)²` (the sign of `∂_pQ` at
`p = 1/2`). So the boundary class binds exactly while `s(8 − 7E − 4s) ≥ 4(1 − E)²`, and that curve is
where the switching flow changes regime (`early_regime.py`; on the chain `h(1/2)` changes sign
between `s = 0.0194` and `0.0199`). This is the formal answer to "is the curve fully optimal": yes,
within the method's gates, in both regimes.

## 2. P1, re-derived

**Two formulations, made exact.**
- *Subspaces.* In `C^N` (functions of `n ~ N`), let `V = span{(·/k)₂ : k ≤ K}` (dimension `K`) and
  `βW = span{g̃(n)·conj((n/P)₃) : P ~ L}` = the prime dilates `g̃(nP)/g̃(P)` of the theta
  coefficients (dimension `L`). P1 for arbitrary slot coefficients is
  `‖Proj_V Proj_{βW}‖² ≤ N^{−η}`. Random subspaces give `≈ 1/L`.
- *Central values.* `⟨g̃·a, v⟩ = Σ_{k,P} a_P b̄_k S(k, P)` with
  `S(k,P) = Σ_n g̃(n)(n/k)₂conj((n/P)₃)W(n/N)`. Each `S(k,P)` sits exactly at the critical point of
  `θ₃ ⊗ (·/k)₂ ⊗ conj(·/P)₃` (conductor `≈ (kP)²`, length `N = KL`). So P1 is a bilinear-form bound
  for the matrix of central values over the two-parameter family. Pointwise Lindelöf for every entry
  gives only `N²` (a flat `K × L` matrix can have rank one).

**What is and is not rigorous.**
- The hybrid norm (MF2.29) proves `‖S‖²_op ≤ N^{2+ε}`. That equals the *conjectured* Frobenius norm
  `KLN = N²` (Lindelöf on average).
- The best rigorous Frobenius bound is `Σ_P Σ_k |S(k,P)|² ≤ L(K + N)N ≈ LN²` (quadratic sieve per
  mark). The cubic sieve per row gives `K(N + L + (NL)^{2/3})N ≈ KN²`, which is worse. So even the
  Frobenius norm is off by `L`.
- P1 asks for the operator norm a power below the true Frobenius norm, i.e. a stable rank of the
  central-value matrix at least `N^η`. That is two levels beyond what is proved.

**Correction to round 7, Lemma Q3.** Round 7 states "trivially `‖E‖_op ≤ N^{1+ε}` (product of two
large sieves)". With `M ≍ 27K` cubic moduli and `N = K^{1.174}`, Heath-Brown's cubic sieve term
`(MN)^{2/3} = 9K^{1.449}` exceeds `N`. It is sharp (de Faveri–Dunn–Hoffstein 2607.07911; the
extremal vector is the Gauss-sum vector). So the product of the two sieves gives only
`‖E‖_op ≤ 3K^{0.138}N = N^{1.118}`. Lemma Q3 as an operator-norm statement over all `β` is
therefore much stronger than use (a) needs. Use (a) only needs the smooth slot weight `φ`. For it,
`Σ_n |Σ_μ φ(μ)(μ/n)₃|² ≈ N‖φ‖²` (Poisson in `μ`, no bias), so the correct target is the vector
inequality `Σ_{k≤K}|Σ_n c_I(n)(n/k)₂W|² ≤ N^{−η}(K + N)‖c_I‖²` for `c_I(n) = Σ_μ φ(μ)(μ/n)₃`.
That is a quadratic large sieve for one explicit cubic-character polynomial. Poisson in `μ` turns
it back into `g̃(n)` times a cubic sum of length `L/27`, the original problem.

**Slot design cannot help.** Restricting slot primes to residue classes mod a fixed modulus costs
nothing in exponents. But `(n/P)₃ = (P/n)₃` depends on `P` mod `n`, not on `P` mod `q₀`, so the
`n`-structure of the column vector is unchanged.

**An inverse-moment "source chain" fails at once.** Splitting rows by slot amplitude before
Poisson, the LOW part costs `max_LOW|Q_u|²·Σ_u|M_u|² ≈ Z^{m+qz}` against the averaged marked bound
`Z^m`. Marks cost through the allowed inverse length `r`, not through the moment.

## 3. The remaining guards

- `Λ_P ≥ 3` (return receipt `source_lambda_low`): worth at most 1e-7 on the face family.
- `B_H ≥ 22/23` (HIGH parents): it enters Collet's root completion (`root_dependent_power`,
  `gain_row_loss`). There the gain's sensitivity to `F` must stay below `ρ(ν) − 1/4` so that the
  sixth-root series converges with weight `N(B)^{−3/2}`. θ* is flat in the count-face position at
  the end of the chain (1e-7 per 2000 grid steps), so relaxing this guard is worth well under 1e-6.

**Extending the family past its end.** The count face is used at slot width about 0.045, past
its tangent point 0.0424, where a later tangent would sit about 1.9e-4 higher (convexity,
`|Λ′| ≈ 55`). Pricing θ* with the count face taken from the continued flow: s = 0.0435, 0.045,
0.0465, 0.048, 0.050 give 8747246, **8747243**, 8747245, 8747252, 8747270. So the best possible gain
is 7e-7. It would need two guards relaxed: `B_H ≥ 22/23`, and the density floor `q ≥ 1/2`
(`q = 0.4973` already at `s = 0.0435`). The floor is an analytic requirement (atom 3), so this is
closed.

**Return parameters re-checked on the new faces.** θ* = 8747250 for count-window caps
`sC ∈ {13/250, 53/1000, 27/500, 549/10000}` and physical caps `sP ∈ {43/1000, 11/250, 9/200, 23/500}`;
neither binds. The conductor top stays optimal at `h = 401/500` (0.800: 8747258, 0.801: 8747252,
0.803: 8747252, 0.804: 8747258).

## 4. Literature (checked again)

No new input. Dunn 2403.13151 (cusp-form kernel), Baier 2605.01635 / 2609.21195 (square moduli),
and the QRH follow-ups 2610.12234, 2610.15291, 2610.17675 are all as recorded in
`../literature/README.md`.

## 5. Status

The bar needs a new analytic input. The method's curve is now proved optimal in Lean given the
gates. The single remaining lever of the right size, P1, is a statement about the stable rank of a
matrix of twisted metaplectic central values, which no known technique reaches.
