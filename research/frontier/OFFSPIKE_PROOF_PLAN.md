# Proof plan: the corrected n-th order large sieve by de Faveri's recursion run off the spikes

Status: plan, 2026-10-31. Nothing here is proved except the iteration arithmetic
(`../lean/arvi_kwall/OffSpikeIteration.lean`). Evidence tags as in `../journal/JOURNAL.md`. Do the cubic case (n = 3)
first: its Gauss sums and theta are explicit (Patterson), it has one theta and two Poisson levels, and every numerical
check below was also run for it.

## Target

For n ∈ {3, 6}, moduli a ∼ A (n-th-power-free, coprime to the fixed set S), arguments b ∼ B, and every λ:

  Σ_a |Σ_b λ_b χ_a(b)|² ≤ (AB)^ε (A + B + A·c₁ + B·c₂) ‖λ‖² + Corr_src(λ) + Corr_row(λ),

with c₁ = (B²/(A M))^{1/n}, c₂ = (A²/(B M_V))^{1/n}, and explicit corrections:
- Corr_src(λ) = Σ_{levels ℓ} Σ_{N m ≤ M} Σ_{|t| ≤ (AB)^ε} w_{ℓ,m}·|⟨λ, f_{ℓ,m,t}⟩|², with f_{ℓ,m,t} the level-ℓ twisted
  source theta N(b)^{it} (levels: `../journal`, "The Poisson levels"; three for n = 6, two for n = 3);
- Corr_row(λ), the same for the row thetas (as a form in λ through E^H), with twist range M_V.

At A = B and M = M_V = B^{1−nγ} the bound is B^{1+γ+ε}: the two-sided spike-free conjecture in its graded form
(`../lean/arvi_kwall/SourceSpike.lean`, `GradedTwoSided`).

## Steps, following de Faveri (arXiv 2610.04045) §§3–7

Each step lists de Faveri's statement, the corrected version, and the evidence.

1. **Completion (Lemma 4.3).** L₁ ≤ L₂: extend the a-sum to all ideals by positivity.
   - Corrected: the source-side corrections are forms in λ, so they pass through unchanged. The row-side
     correction has to be stated for the completed sum (rows: all a ∼ A). [routine; check that the row thetas'
     definition extends to non-squarefree a with the same weights]
2. **GCD sorting (Lemma 4.4).** L₂ ≤ B^ε L₃(A/Δ₁, B/Δ₂): sort by d = (b₁, b₂), remove coprimality by Möbius.
   - Corrected: the sub-problem vectors λ_{d·} twisted by χ(r) need their own corrections, which are restricted
     twisted thetas. [numerical, `theta_restricted_spikes`: restricted twisted thetas carry no excess (0.98–1.02 of
     the null), because the cross term makes them d^{−2} twists. So they can be bounded inside the sub-problem's
     diagonal, with no new correction.]
   - To prove: the d^{−2}-twist identity for the restricted Kubota sum, and that it lands off the residue (as for the
     −1 twists, Kazhdan–Patterson for n = 6, Patterson for n = 3).
3. **Poisson (Lemma 5.1, with Lemma 3.3 coupling of root numbers).** L₃ ≤ A + (A/B)·[dual sums over a′ ≲ B²/A],
   bounded through L₂(K, ·) by Cauchy–Schwarz.
   - Corrected: split the dual a′ by kernel. Kernels ≤ M give exactly the level-1 corrections (twisted source
     thetas β·χ(m) with multiplicity (K/N m)^{1/n}). The Mellin variable t gives the N^{it} twists. Kernels > M go to
     step 4.
   - Cauchy–Schwarz with corrections: |S₁||S₂| ≤ ½(|S₁|² + |S₂|²) keeps the corrected form (AM–GM), so the dual's
     corrections pull back to λ-corrections (through β·N^{it}). [derived]
   - The pull-back of the dual's own spikes is the next Poisson level. [numerical, `theta_level2`: levels exist,
     grow with B, and close up: u³ is an angle for n = 6, and for n = 3]
4. **n-th powers (Lemma 6.1).** L₂(K, B) ≤ max_{R ≤ (K/M)^{1/n}} R·L₁(K/R^n, B) on kernels > M.
   - Corrected: the multiplicity is at most c₁ = (B²/(AM))^{1/n}, which is the A·c₁ term. [derived]
5. **Monotonicity (Lemma 4.2).** L₁(A₁, B) ≲ L₁(A₂, B) for A₂ ≥ C A₁ log, via rows a·p and λ·conj χ_p.
   - Corrected: the source twist range shrinks, M → M A₁/A₂ (A·M conserved), and the row range grows,
     M_V → M_V (A₂/A₁)² (A²/M_V conserved). So c₁ and c₂ are constant along the orbit. [derived; the source part is
     exact]
   - The (x/p)^{−1} twists produce local spikes on the rows divisible by p with no net excess. [numerical,
     `theta_local_spikes`: 2.4–4.5 on those rows, deficit elsewhere, total at the null]
   - To prove: the redistribution identity E(f conj χ_p)(ap) = E_{p-free} f(a) and the deficit elsewhere, enough for
     the full-row norm.
6. **Symmetry (Lemma 4.1).** L₁(A, B) ≍ L₁(B, A) by reciprocity in classes.
   - Corrected: swaps (M, M_V) and the two correction families. Needs the corrected statement to be symmetric, which
     fixes the row-side levels. [numerical, `theta_level2_rows`: the row side has only weak extra levels]
7. **Iteration (Prop 7.1).** From (E_α): L ≲ A^α + B + A c₁ + B c₂, one pass of 1–5 gives
   L ≲ A + A^{1−α}B^{2α−1} + A c₁; monotonicity to the balance point gives α′ = 2 + γ − (1+γ)/α.
   - The fixed point is 1 + γ. [Lean: `OffSpikeIteration.lean`, `balance`, `tendsto_iter`]
   - The base case (E₂) is trivial (Lemma 7.2, unchanged).

## Where the real work is

- **Step 3's corrected Cauchy–Schwarz and level closure.** This is the substantive new part. The corrections must be
  tracked through the Mellin integral and the coupling factors of Lemma 3.3. The level family must be shown closed
  under "pull back the dual's spikes" with explicit angular characters. For n = 3 everything is explicit, since
  Patterson's τ₃ is a Gauss sum.
- **Step 2's restriction lemma.** This is the d^{−2}-twist identity plus the vanishing that keeps restricted spikes
  off the residue.
- Everything else is de Faveri's bookkeeping with one extra parameter (M, M_V) carried along.

## What it buys

- **K-wall.** With Λ_row (amplification, `SpikeRule.lean`) and Λ_src (metaplectic Rankin–Selberg for dilated thetas;
  journal "Λ_src is a Rankin–Selberg problem"), the corrected sieve at γ ≈ 0.015 gives the selected norm the K-wall
  needs.
- **Reference wall.** In the unbalanced regime only steps 2–3 are needed (one Poisson step), plus a detector condition
  for the reference vectors (journal, "The reference wall's detector condition").
- **Payoff.** It comes only with both walls and the Lean forks of the native or density machinery: −1e-4 to −5e-4
  (frontier, "Roadmap for the faces").

## Lean route (2026-10-31)

Sil's formal optimal sextic sieve (`FourthPower/Sieve*.lean`, about 6,100 lines; `optimal_bound`) is de Faveri's
recursion. Its `step α = (12α − 7)/(6α − 1)` is the n = 6 case of 2 − (n−1)/(nα − 1). The corrected version is a fork:
1. `SieveGrowthAlgebra.secondaryCoefficient`: carry the twist range M_tw, giving (2N/(M·M_tw))^{1/6}.
2. Monotonicity: shift the twist range (A·M conserved).
3. `SieveImprovement.step`: replace by 2 + γ − (1+γ)/α (arithmetic already in `OffSpikeIteration.lean`).
4. `SievePoissonBound`: split the dual sum by kernel. The small-kernel part becomes the correction form, and the
   large-kernel part is bounded as before.

Step 4 is the analytic addition. Steps 1–3 are bookkeeping on proved code.
