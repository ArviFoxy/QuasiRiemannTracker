# Atom 1: slot cost 2 in the reflected energy (consolidated note, 2026-10-24)

Slot cost 2 binds in three places: the count's marked inverse moment, the probe's marked
energy, and the source chain's HIGH inverse cap. This note collects what is known about it, the
smallest change that would pass the bar, and why every route tried so far fails. Short entries are
in `../LOG.md`. The four-atom summary is `../barriers/README.md`.

## 1. Where it comes from

Collet, foundations Theorem 7.3 (marked inverse moment):

$$r+2z\le m\ \Longrightarrow\ \sum_{q_u\ll Z^m}|M_u(Z^r)Q_u|^2\ll Z^{m+\epsilon}.$$

The proof applies Poisson summation to the row sum. In the binding child (`../lean-lab/MIBranches.lean`)
the columns have length `F_c = r + z`, the rows `H = M_c = 2(r+z) − m`, and the marks `z`. The child's
reflected energy (MF2.36–MF2.38) has two branches:

- **Row branch.** Exponent `H + z − u_h − (T_d − v)/2`. It has slack.
- **Column branch.** Dual length `v` up to `T_d = 3r + 5z − 2m`, exponent `T_d`. It must not exceed
  `F_c`.

`T_d ≤ F_c ⟺ r + 2z ≤ m`.

The column branch is bounded by the hybrid norm (MF2.29):

$$\sum_k\Big|\sum_P\frac{a(P)}{\sqrt{q_P}}\sum_{n,b}\beta(n,b)\chi_k(nb)^3\chi_P(n)^{-2}\Big|^2
\ll (K+NB)\,B\,\{N+L+(NL)^{2/3}\}.$$

Here `K = Z^H` are the rows, `N = Z^v` the dual indices, `L = Z^z` the slot tuples, and `β` the
reflected cubic-theta (cubic Gauss sum) coefficients. The bound is a quadratic large sieve over `k`
(the row twist `χ_k³` is quadratic) times a cubic large sieve between `n` and the slot tuples (the
twist `χ_P^{-2}` is cubic). In the column branch (`v > H`) the factor `K + N` is paid at `N`.

## 2. Exact form of the constraint

- The dual sum is twisted by `χ_k³χ_P^{-2}`, so its critical length is `Z^{H+z}`.
- In the inverse moment, `T_d ≤ H + z ⟺ r + 2z ≤ m`. The budget is exactly the statement that the
  dual sums stay inside this joint critical length.
- In the probe's marked energy (Theorem 7.1), `M + 2z ≤ N_*` is `T_d ≤ H`, the row count, which
  lies inside the joint critical length.
- Between the row count and the joint critical length, the quadratic sieve's `N` term charges the
  full excess.

## 3. The target

Binding configuration of the count: `δ ≈ 0.4546`, `p = 1/2`, detected inverse length `r = 0.742`,
marks `z = (1 − r)/2 = 0.129`, so `K = Z^{0.742}`, `L = Z^{0.129}` and `N = KL = Z^{0.871}`.

| goal | needed |
|---|---|
| 6.8e-6 (with Lemma F, reaches the milestone 0.8747189) | budget `r + 2z ≤ 1 + 5.5e-4`, i.e. the column branch `≤ Z^{0.871 − 0.0011}`. Float model: budget `1.0004` gives `Δθ* = −4.96e-6`. |
| 1e-5 alone | budget `1 + 5.9e-4` |
| 1e-5 via the probe instead | `x + y + ℓ ≤ 1 + 1.6e-4`, with at most 16% of the excess kept |

## 4. Reformulations

- **Operator norm.** With `S(k,P) = Σ_n β(n)χ_k(n)³χ_P(n)^{-2}` (central values of the twisted theta
  series at the binding), the column branch is `‖S a'‖²` with `‖a'‖ ≍ 1`. The hybrid norm's bound
  `K²L²` equals the Frobenius norm `‖S‖_F²` under Lindelöf on average. For a random-like matrix,
  `‖S‖²_op ≈ N(√K + √L)² ≈ K²L`. Slot cost 2 is the gap between the Frobenius and operator norms.
- **Specific coefficients.** The theorem is stated for arbitrary slot coefficients. In every
  application they are smooth prime weights times fixed characters. Then the column coefficient
  `c(n) = β(n)A(n)` (with `A(n) = Σ_P a(P)q_P^{-1/2}χ_P(n)^{-2}`) has a large projection onto
  `span{χ_k³}` only if it correlates with quadratic characters. Generically the projection is a
  `K/N` fraction and the sieve sum is the diagonal `K‖c‖²`.
- **What a proof needs.** Cancellation in the Poisson-in-`k` dual terms, i.e. Type II-type sums
  `Σ_n β(n)A(n)(j/n)` for `j ≤ N²/K` together with their signed sum over `j`. This is a Type II
  estimate for cubic Gauss sums twisted by quadratic characters. The nearest known result,
  Dunn–Radziwiłł Prop. 9.1/10.1, treats cubic twists with an inexplicit saving `X^{ρ}` (`ρ < 1e-4`)
  and partly assumes GRH.

## 5. Routes tried and why they fail

| route | why it fails |
|---|---|
| improve the row branch (coupled hybrid norm, `../lean-lab/CoupledHybrid.lean`) | the row branch already has slack (`F_c − 3z/2`) |
| zero-free pointwise bounds on the slot sums | they save `z(1 − κ)`; the hybrid norm already saves all of `z` |
| probe redesigns (cube marks, deleting marks) | lose the sextic slot factor, or pay more than they save |
| re-reflect the dual sums (closure of 2026-10-24, then rechecked) | the critical length is `Z^{H+z}`, because the slot twist enters the conductor. At the binding `T_d = H + z`, so there is nothing to re-reflect. Slightly beyond it, de Faveri's optimal sextic sieve costs `A^{7/6}`, which is worse than the excess. |
| "the excess is a genuine dual diagonal" (heuristic of 2026-10-24) | retracted: the off-diagonal is a signed bilinear form (reciprocity sign), not a square. For generic coefficients the true size is the diagonal. |
| DDHL-type second moments for the quadratic twists (`u^{3/2}`) | need an exponent below `1.1728` at `K = Z^{0.742}`; `3/2` is far too weak |
| treat `(k, P)` as one sextic family, Cauchy over `P` | the sextic sieve's `A^{7/6}` at `A ≈ N` is worse |
| trilinear Hölder (fourth moments of `B`, `A`) | `K^{5/2}L^{3/2} > K²L²` |
| a quadratic sieve over `k` with bounds for each `k` separately (cubic sieve inside) | `K·N^{2/3}`-type, worse than `N` |
| amplify the rows so the marks fit | marks cost `5/3` per unit after amplification, gain `δ ≈ 0.45` |

## 6. Assessment

Slot cost 2 is a worst-case artifact (operator norm over arbitrary slot coefficients) for a column
branch whose true size, for the coefficients actually used, is plausibly the diagonal. A saving of
`Z^{0.0011}` out of a plausible `Z^{0.129}` would be enough. But every available large sieve is
optimal for some coefficient vector, so a proof must use the arithmetic of cubic Gauss sums against
quadratic characters. That is the open Type II problem above.
