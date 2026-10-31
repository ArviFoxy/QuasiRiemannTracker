# arvi_kwall: the faces' K ≥ 1/2 wall is a property of the method (research, not a submission)

Lean prefix `Submissions.arvi_kwall`, namespace `QRH.ArviKWall`. One file, `Closure.lean`, Mathlib only; it checks
in about 8 s on a warm cache. Both top theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What it proves

PR 93's selected norm is built from three rules. In log scale (x = log_B of the source length, n(x) = log_B of the
selected norm, rows of norm ≈ B selected at slope δ) they read:

| rule | statement |
|---|---|
| initial bound | n(x) ≤ Θ₆(x) = max(1, x, 5/6 + x/3, 1/3 + 5x/6), the optimal general sextic sieve. PR 93 itself starts from the weaker L + B². |
| amplification by a selected slot block | n(x) ≤ n(y) − δ(y − x) for x ≤ y |
| reflection (Poisson at conductor B²) | n(x) ≤ max(x, x − 1 + n(2 − x)) for 1 ≤ x ≤ 2 |

- `nstar_rules`: for 1/3 ≤ δ < 1/2, the function n*(x) = max(x, 7/6 + δ(x − 1) + (1 − 2δ)·max(x − 1, 0)) obeys all
  three rules, and n*(1) = 7/6.
- `no_balanced_bound_below`: so no argument built from these rules certifies a selected norm below B^{7/6} at the
  balanced point L = B.
- `fixed_point_not_derivable`: in particular the slope-δ fixed point max(x, 1 − δ + δx), which PR 93 reaches for
  δ > 1/2 and which equals B at L = B, does not follow from the rules.

## Why it matters

- The faces' native steps end at Λ = 6KB/(1 + K), which is 2B at K = 1/2. A face below Λ = 2 needs the selected
  leaf at K < 1/2.
- Below slope 1/2 the selection buys nothing at the balanced point, even with the optimal sextic sieve as the
  starting bound. The loss is exactly Θ₆'s excess 1/6 there.
- The reason: one amplify–reflect cycle x = 1 → y → 2 − y → 1 changes the bound at the balanced point by
  (1 − 2δ)(y − 1). That is a gain only if δ > 1/2.
- So moving the wall needs a new direct estimate for the selected rows at L = B: a Guth–Maynard-type operator-norm
  bound on a large-value set of the sextic family. Neither a better start nor more rounds can do it.

## Dilution.lean (RIP program)

- `fixed_point_of_dilution`: the diluted initial bound n(x) ≤ max(1, x, Θ₆(x) − δ) plus amplification gives
  n(x) ≤ 1 − δ + δx on [0, 1] for every δ ≥ 1/6.
- `kwall_is_dilution`: for δ ∈ [1/3, 1/2) both statements hold at once:
  - the undiluted rules admit n(1) = 7/6;
  - the diluted bound forces n(1) ≤ 1.

  So the whole K-wall is the gap between Θ₆ and its dilution on thin row sets.
- Numerics in `../../rip/`: the sextic Gram matrix follows Marchenko–Pastur, and slot large-value sets behave like
  random subsets. So the dilution holds empirically.

## FlatDilution.lean (Arvi's "replace M by an operator with the RIP we need")

- `norm_restrict_le`: write the row vector y = Ma as y = Σ_j c_j θ_j + r, with k flat row vectors
  (|θ_j(z)|² ≤ c/R). Then on **every** row subset W:
  ‖y|_W‖ ≤ √(k c |W|/R)·‖c‖ + ‖r‖, where the last norm is over all rows.
- Take θ_j to be the theta row vectors conj G(z,1)·profile. The Gauss sums of squarefree moduli are unimodular, so
  these vectors are flat. Take r = (I − P_V)Ma. Then
  Σ_{z∈W} |⟨a, χ_z⟩|² ≤ (√(k c |W|/R)·‖P_V M‖ + ‖(I − P_V)M‖)²·‖a‖².
- The theta excess is diluted by |W|/R on every thin set. What remains is the large sieve for the operator
  (I − P_V)M on the **full** family. No thin-set argument and no condition on the detector are needed.
- So the K-wall reduces to the full-family statement ‖(I − P_V)M‖² ≲ (R + S)·B^ε for a low-dimensional theta span
  V (journal, "large sieve off V").
- **Correction (journal, "Where the theta excess lives").** The theorem is right, but its hypothesis cannot be met
  with small k.
  - Every twisted theta conj G·χ_z(m) with N(m) ≤ B^{1−6γ} carries its own excess (Poisson multiplicity), so V needs
    k ≈ B^{1−6γ}. Then √(k c |W|/R) ≫ 1.
  - What survives: (LS off V) for that V, plus a detector condition ‖P_V M a‖ small for the leaf's vectors. With
    those, no dilution is needed.

## Fortified claims (elementary linear algebra behind the journal's RIP and K-wall entries)

Mathlib only, namespace `QRH.ArviKWall`. Every theorem named below depends only on `propext`, `Classical.choice`
and `Quot.sound`. These files record the elementary facts the journal relies on; none of them closes the K-wall.

| file | content |
|---|---|
| `DualFrame.lean` | **The dual-frame (Q-metric) bound** (journal, "RIP (4) fresh look"; ≈ 8 s). `qform_cauchy_schwarz`: for Q ⪰ 0, \|⟨u, Qw⟩\|² ≤ ⟨u, Qu⟩⟨w, Qw⟩. `dual_cauchy_schwarz`: if Q P = 1, then \|⟨v, y⟩\|² ≤ ⟨v, Pv⟩⟨y, Qy⟩. `dual_frame_bound`: for Q positive definite Hermitian, every row subset W and every row vector y, Σ_{z∈W} \|y_z\|² ≤ c_W(Q)·⟨y, Qy⟩, where c_W(Q) = sup{⟨v, Q⁻¹v⟩ : v supported on W, ‖v‖ = 1} (`cW`). `dual_frame_large_sieve`: for y = Ma, if ⟨Ma, QMa⟩ ≤ λ‖a‖² for all a, then Σ_{z∈W} \|(Ma)_z\|² ≤ c_W(Q)·λ·‖a‖². `cW_one_eq`, `dual_frame_bound_one` and `dual_frame_large_sieve_one`: Q = 1 gives c_W = 1, which is the trivial restriction bound. The bound is the factorization M_W = (P_W Q^{−1/2})(Q^{1/2} M) in elementary form: a reformulation, exact as Q → P_W, so the choice of Q is the whole content. |
| `AntiSelfDual.lean` | **Anti-self-dual Gram matrices are capped at twice the diagonal** (journal, "No anti-self-dual row class"; ≈ 10 s). `AntiSelfDual A U` is A = −U Aᶜ Uᴴ, with Aᶜ the entrywise conjugate. `exists_flip`: for U unitary, every x has a y = conj(Uᴴx) with ‖y‖ = ‖x‖ and Re⟨x, Ax⟩ = −Re⟨y, Ay⟩. `two_d_bound`: if G = D + A is positive semidefinite, D real diagonal with 0 ≤ D_ii ≤ d, then Re⟨x, Gx⟩ ≤ 2d‖x‖² for all x. `eigenvalue_le_two_d` and `eigenvalues_le_two_d`: so λ_max(G) ≤ 2d. `two_d_bound_sharp`: the constant 2 is attained, by σ_y with U = 1 and D = 1. `plus_sign_no_cap`: the opposite sign `SelfDualPlus A U` (A = U Aᶜ Uᴴ) gives no cap. The all-ones matrix J on m ≥ 2 indices is real, so J = 1·Jᶜ·1ᴴ, and G = 1 + J is positive semidefinite with 0 ≤ D_ii ≤ 1 and eigenvalue m + 1 > 2. This documents an idea the numerics refuted (the effective Poisson sign is +1 class by class). |
| `SpikeFree.lean` | **The large sieve with the spikes removed** (journal, "Where the theta excess lives"; ≈ 10 s). `CorrectedLargeSieve M Δ f w` says Σ_z \|(Ma)_z\|² ≤ Δ‖a‖² + Σ_k w_k \|⟨f_k, a⟩\|² for every a. `selected_of_corrected`: the same bound holds with Σ_{z∈W} on every row subset W. `off_spikes`: if ⟨f_k, a⟩ = 0 for all k, then Σ_z \|(Ma)_z\|² ≤ Δ‖a‖². `detector_condition`: if Σ_k w_k \|⟨f_k, a⟩\|² ≤ η‖a‖², then Σ_{z∈W} \|(Ma)_z\|² ≤ (Δ + η)‖a‖² for every W, with no thin-set argument. `exists_unit_orth_large` and `exists_unit_orth_form`: if a form is ≥ Δ'‖x‖² on a subspace E of dimension k + 1, every subspace V of dimension ≤ k has a unit vector x ∈ E with x ⊥ V and form value ≥ Δ' (E ∩ Vᗮ ≠ 0). `detectorSpan_finrank_ge` and `card_detectors_ge`: so if ‖Ma‖² ≥ Δ'‖a‖² on such an E with Δ' > Δ, the span of the f_k has dimension ≥ k + 1 and there are at least k + 1 detector vectors. With each twisted theta carrying its own excess, V cannot be low-dimensional. |
| `TransferLemmas.lean` | **Transfer lemmas for randomized dictionaries** (fresh look §1.1–1.3; ≈ 10 s). `douglas_easy`: if X = AY and ‖Ax‖ ≤ c‖x‖ for all x, then ‖Xv‖² ≤ c²‖Yv‖² for all v. `douglas_gram`: so XᴴX ≼ c²YᴴY, i.e. c²YᴴY − XᴴX is positive semidefinite. `gram_mixture_offdiag`: for rows z ≠ z′ and u : Z → Ω → (σ → ℂ), summing over all ω : Z → Ω (counting measure on the product space), Σ_ω ⟨u_z(ω_z), u_z′(ω_z′)⟩ = \|Ω\|^{\|Z\|−2}·⟨Σ_t u_z(t), Σ_t u_z′(t)⟩, by `sum_pi_two`. `gram_mixture_offdiag_avg`: so the average off-diagonal Gram of independent random rows is the Gram of the mean rows. `stdBasis_ripOn_zero`: the standard basis of ℂ^S has RIP constant 0 on every support. `stdBasis_cross_coherence` and `exists_coherence_ge`: a flat vector (\|x_n\|² = 1/S) has \|⟨e_n, x⟩\|² = 1/S with every e_n, and 1/S is the minimum for a unit vector (Parseval). `equal_rows_not_rip` and `cross_coherence_no_information`: all of this also holds for the family whose rows are all one flat vector, whose RIP constant on W is at least \|W\| − 1. So "the dictionary has RIP and is incoherent with the rows" gives no bound on ‖X_W‖. |

## SexticSpikeFree.lean: the balanced-point large sieve with the theta term removed (conjecture, OAI definitions)

Namespace `QRH.ArviKWall.BalancedSieve`. The file imports the OpenAI baseline's
`Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Physical`, so the baseline's oleans must be built.
On a warm cache it checks in about 6 s. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
The conjecture is a `def … : Prop`, and nothing in the file assumes it.

- **Objects (OAI's own).**
  - Rows `sexticRows B`: squarefree ideals of ℤ[ω] coprime to 6 with B ≤ N z ≤ 2B.
  - Sources `sexticSources L`: ideals coprime to 6 with squarefree norm ≤ L, taken at their primary generators.
  - Kernel `orderKernel k z n = χ_z(n)^k` with χ_z = `idealRowHom` (k = 1 sextic, k = 2 cubic).
  - The row Gram form `dualForm` is b* E E* b = Σ_n |Σ_z b_z conj χ_z(n)^k|².
- **Spike family.** Every twist m = x + yω with N m ≤ M (all associates) gives three shapes:
  - the twisted theta g̃(z)·conj χ_z(m)^k, where g̃ is the phase of the row's Gauss sum (`powerGauss_one`: at k = 1
    the sum is OAI's `sexticGauss`);
  - the plain character χ_z(m)^k;
  - its conjugate conj χ_z(m)^k.

  Each shape is multiplied by a radial profile (B/N z)^{j/2}, j < J.
- **Conjecture `SpikeFreeLargeSieve k q`** (`SexticSpikeFree` = (1, 6), `CubicSpikeFree` = (2, 3)). For every ε > 0
  there is C such that for B ≥ 1, if b is orthogonal to every spike with N m ≤ C B^{1−qε} and j ≤ C B^ε, then
  b* E E* b ≤ C B^{1+ε} ‖b‖². The refinement `GradedCorrectedLargeSieve` asks for
  E E* ≼ C B^{1+ε} I + Σ w_i f_i f_i* with the multiplicity weights w = C B^ε (B/N m)^{1/q}.
- **Proved.**
  - `spikeFree_of_graded`.
  - `selected_of_corrected`: a corrected large sieve plus a Bessel constant Λ_W for the weighted spikes on W ⊆ rows
    gives Σ_{z∈W} |Σ_n a_n K(z,n)|² ≤ (Δ + Λ_W)‖a‖². The proof is by duality with the test vector D·1_W. This one
    inequality is both the restriction step and the detector condition.
  - `selected_of_graded` and `selected_of_graded_flat`: the latter uses the union bound Λ_W ≤ |W| Σ w for the flat
    spikes (`norm_spikeVector_le`). With the graded weights it helps only for very small W.
  - `corrected_trivial`: Δ = |R||S| always works.
  - `exists_orthogonal_of_card_lt`: with fewer spikes than rows, some nonzero b is orthogonal to all of them.
- **Convention.** This is the b* E E* b form. Most earlier theta scripts measure |Eᵀc|², whose spikes are the complex
  conjugates (conj g̃·χ(m)). See `research/rip/theta/theta_offspan.py` and the journal entry of 2026-10-30.
- **Relation to `SpikeFree.lean`.** That file corrects on the source side, where the selected bound is plain
  restriction. Here the spikes live on the rows, as the Poisson theta vectors do, so the selected bound needs
  duality and a Bessel bound for the spikes on W.
