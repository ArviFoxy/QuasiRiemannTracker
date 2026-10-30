# arvi_rip: restricted isometries and the square-root barrier (research, not a submission)

Lean prefix `Submissions.arvi_rip`, namespace `QRH.ArviRIP`. Mathlib only. Every theorem below depends only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorry`, `admit`, `axiom` or `native_decide`).

## Why this package exists

The faces' K-wall is a restricted-isometry problem. Take the sextic characters χ_z (rows z ~ B) on sources of
norm ≤ L. The selected norm asks that the rows of a large-value set W act almost orthogonally at L = B.
Selection at slope δ gives |W| = B^{1−δ}, so δ < 1/2 means beyond √(dimension). The Lean barrier
`arvi_kwall` shows that amplify-and-reflect cannot cross δ = 1/2. This package builds the general RIP
language in which a beyond-√ argument has to be written, starting with the classical barrier itself.

## Files

| file | content |
|---|---|
| `Coherence.lean` | `gershgorin_rip`: unit columns of coherence μ satisfy the RIP on every support S with constant μ(\|S\| − 1). `frame_potential_ge` and `welch`: the Welch bound N² ≤ n(N + N(N − 1)μ²), via the frame-potential identity `gram_frame_frobenius`. `coherence_order_barrier`: once N ≥ 2n, a coherence certificate (k − 1)μ ≤ δ forces k ≤ 1 + δ√(2n). This is the square-root barrier: coherence alone never certifies order beyond ≈ √n. |
| `FlatRIP.lean` | BDFKK's Lemma 3 in fixed-support form. `flat_rip_on`: if every bilinear sum of disjoint flat combinations on W satisfies \|⟨Σ_{J₁}u, Σ_{J₂}u⟩\| ≤ δ√(\|J₁\|\|J₂\|) (`FlatOn u W δ`), then \|‖Σ a_z u_z‖² − ‖a‖²\| ≤ 32 δ (T + 2^{−T}√\|W\|)² ‖a‖² for every T. With 2^T ≥ √\|W\| the constant is 32 δ (T + 1)², so polylog. The steps are: `cube_vertex` (an affine map on [0,1]^s attains its maximal norm at a vertex), then `flat_cube`; `flat_dyadic` (telescoping dyadic pieces with a Chebyshev count per level); `flat_nonneg`; `flat_complex` (four nonnegative parts); and `avg_identity` with `count_split` (each off-diagonal pair is split by exactly a quarter of the subsets of W). |
| `Hoeffding.lean` | Hoeffding's inequality in finite counting form, with no measure theory. `sum_exp_signs` and `prod_cosh_le` give the exponential moment Σ_ε exp(λΣa_k sgn ε_k) = Π 2cosh(λa_k) ≤ 2^{\|κ\|} exp(λ²Σa²/2). `card_ge_le` and `card_abs_ge_le` count the patterns with \|Σ a_k sgn ε_k\| ≥ t: at most 2·2^{\|κ\|}·exp(−t²/(2σ²)) when Σa² ≤ σ². `card_cond_le` is the conditional form: the coefficients may depend on the entries outside a set p, and Hoeffding runs over the entries in p with the rest frozen. It is the counting version of conditioning. |
| `Thinning.lean` | Random row thinning is energy-neutral. Bernoulli weights over subsets (`bern`, `bern_total`, `bern_mem`). `thin_avg`: the average energy over thinnings is exactly ρ·energy(W). `avg_bound_ge`: any bound dominating the energy on each thinning averages to at least ρ·energy(W). `thinning_pays_back`: a ρ-diluted bound ρX + Y on every thinning gives only X + Y/ρ on W. `closure_payback`: in the K-wall closure, max(1, 7/6 − δ₀) + δ₀ ≥ 7/6. Scope: this only shows that thinning or re-phasing the sextic atoms themselves cannot help. It says nothing about dictionaries made of different atoms (see below). |
| `WideFeatures.lean` | **A dictionary of different atoms with RIP by counting measure.** A degree-ℓ feature is a product of ℓ Rademacher projections, feat_w(x) = ∏⟨w_i, x⟩. These are the polynomial pieces of wide dot-product kernels; ReLU's arc-cosine kernel is a positive mixture of them. `sum_feat_mul_conj`: the averaged features reproduce ⟨x, y⟩^ℓ exactly, so coherence μ becomes μ^ℓ. `sum_norm_sq_sum_pi` and `card_filter_le_sum_div`: variance over independent draws and Chebyshev, in counting form. **`exists_wide_rip`**: for any unit data (N points, coherence ≤ μ, ℓ¹ norms ≤ C) with 4N²C^{4ℓ} < mε², a positive measure of m-feature operators has RIP constant ε + (μ^ℓ + ε)(\|S\| − 1) on every support. That is order ≈ μ^{−ℓ}, against ≈ μ^{−1} for the raw data. `count_le_of_rip`: RIP ⇒ large-value count. `mixture_ge_min`: a mixture of degrees never beats its best degree. |
| `RandomRIP.lean` | **Random sign dictionaries break the square-root barrier.** The columns are u_j = (sgn ε(r, j)/√n)_r. `card_bad_le`: for a disjoint pair (J₁, J₂), at most 2·2^{nN}·exp(−δ²n/4) sign matrices have a large flat sum while ‖Σ_{J₂}u‖² ≤ 2\|J₂\|. This is `card_cond_le` with the J₂ column sum as the frozen variance. `flat_of_not_bad`: a matrix that avoids all these events has flat RIP δ on every pair of size ≤ k. The proof is strong induction on \|J₁\| + \|J₂\|: flat RIP on the smaller pairs inside J₂ bounds ‖Σ_{J₂}u‖² through `flat_rip_on`. `exists_rip_sign` and `exists_rip_sign_explicit` then follow by a union bound, using `card_pairs_le` (\|pairs\| ≤ (N + 1)^{2k}). If 2(N + 1)^{2k}·exp(−δ²n/4) < 1, some n × N sign matrix has unit columns with RIP of order k on every support. So k ≈ δ²n/(8 log(N + 1)), linear in n, against k ≲ √n for coherence (`coherence_order_barrier`). |

Every known explicit beyond-√ RIP construction goes through `flat_rip_on`, and so does the random one in
`RandomRIP.lean`. What remains open is the flat bilinear estimate itself for our dictionary: the sextic
characters on a large-value set W at the self-dual length, with δ ≪ 1/log² once |W| exceeds √(dimension).

Build: `lake env lean Submissions/arvi_rip/Coherence.lean` (≈ 11 s), `.../FlatRIP.lean` (≈ 13 s),
`.../Hoeffding.lean` (≈ 9 s), `.../RandomRIP.lean` (≈ 9 s) and `.../WideFeatures.lean` (≈ 13 s), on a warm cache.

**Status of the randomized-dictionary direction** (journal, "RIP program (3)" with its correction, and
"RIP program (4)"). `Thinning.lean` only rules out re-randomizing the *same* atoms. The open proposal is a
dictionary of *different* atoms: wide, not localized in frequency (random-feature type), with RIP proved by a
positive measure of good operators, and tied to the sextic rows by coherence bounds. `WideFeatures.lean` is the
first construction of that kind.
- On the actual slot-selected rows (`../../rip/wide/`) its kernels of degree ≥ 2 have RIP far beyond √.
- The zero's detector is linear (degree 1), and the K-wall lives there: the full-family sieve already controls
  degree ≥ 2.
- The next construction has to bring randomness into the degree-1 part (journal, RIP (4)).
