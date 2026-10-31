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
   - **Alternative without Cauchy–Schwarz (2026-10-31, derived; the identity is numerical to 1e-9).** With a
     Gaussian weight the row Gram is exactly self-dual (`../rip/theta/theta_poisson.py`):
     G_L(z, z′) = √(L/M)·ε·g̃(z)conj g̃(z′)·conj G_M(z, z′) on coprime pairs, where M = 27N(z)N(z′)/(4L) and ε is
     constant on class pairs mod 4 and mod 9 (`theta_poisson_B10000.log`, item 3).
     - So a corrected bound for the dual family transfers exactly. A correction f becomes g̃·conj f times class
       characters mod 36. The pair-dependent length M becomes N^{it} twists by a Mellin separation in N(z)N(z′).
       The class-phase matrix costs a bounded factor (its singular values, through AM–GM).
     - The rotation f ↦ g̃·conj f is an involution up to class characters, since |g̃| = 1. Non-coprime pairs
       still need the gcd sorting of step 2.
     - Caveat: this replaces only the Poisson step. The n-th-power descent and the alternation of the two sides
       are unchanged.
4. **n-th powers (Lemma 6.1).** L₂(K, B) ≤ max_{R ≤ (K/M)^{1/n}} R·L₁(K/R^n, B) on kernels > M.
   - Corrected: the multiplicity is at most c₁ = (B²/(AM))^{1/n}, which is the A·c₁ term. [derived]
5. **Monotonicity (Lemma 4.2).** L₁(A₁, B) ≲ L₁(A₂, B) for A₂ ≥ C A₁ log, via rows a·p and λ·conj χ_p.
   - **Simpler in Sil's form (2026-10-31):** with rows = all moduli of norm ≤ T, monotonicity is inclusion
     (`theta_mono`). The vector is not twisted, the twist range μ stays fixed, and no local spikes arise. The step map
     is `silStep` (fixed point 1 + γ; Lean: `OffSpikeIteration.lean`, `tendsto_silIter`). The de Faveri-form items
     below are kept for reference.
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

## In Sil's form: the excess is the sixth-power multiplicity (2026-10-31)

[derived from Sil's `SieveDescent.lambda_sixth_extraction` and `SievePoissonBound.coherent_weighted_bound`]

- **Where the excess sits.**
  - After Poisson, Sil's recursion bounds the dual sum by completed sieves λ(L, N) over rows V·K (gcd part times dual
    frequency), then extracts sixth powers: λ(L, N) ≤ Σ_D θ(L/N(D)⁶, N).
  - On sixth-power-free sources, a row R₀D⁶ has the same character as R₀. So the D ≠ 1 copies are repeated rows:
    row R₀ counted w_{R₀} = #{D : N(R₀D⁶) ≤ L} ≈ (L/N R₀)^{1/6} times. That is the theta term, i.e. the spikes.
- **Corrected step (an identity, no loss).** Keep the D = 1 copy, θ(L, N), for the recursion. Move the D ≠ 1
  copies into the correction Σ_{R₀}(w_{R₀} − 1)|⟨λ′, χ_{R₀}⟩|². Pulled back through the Poisson identity, it is
  Σ (w − 1)|⟨λ, f_{R₀}⟩|², with f = phase·conj χ (Sil's `pair_coupling` normal form).
- **Level family.**
  - The dual vector is λ·conj(phase)·N^{it}, up to class characters. Its own corrections pull back to
    conj(phase)²·χ, and level j gives conj(phase)^j·χ_k.
  - Since phase³ is an angle (a Hecke character ξ of infinity type), the family is
    {conj(phase)^j·ξ^m·χ_k : j ∈ {0, 1, 2}, m ≥ 0}: three spiky types with accumulating angular twists. That
    matches the "about 400 levels, mostly angular twists" count below.
- **Step 1, precisely (2026-10-31) [derived; the named lemmas are Lean].**
  - Sil's recursion (`SievePoissonRecurrence.lambda_recurrence`) assumes λ(L, B) ≤ A(LB)^ε(L^α + L^{1/6}B). It
    concludes λ(M, N) ≲ M + M^{1−α}N^{2α−1} + M^{5/6}N^{1/3}. The last term is the dual's multiplicity L^{1/6}B at
    L = N²/M, i.e. the theta term.
  - **The split is an identity.** Write the completed rows of norm ≤ L as aboveRows μ L (sixth-power-free kernel
    > μ) and belowRows μ L. The energy over all rows is the sum of the two (positivity, nothing lost).
    - Above: `RestrictedDescent.aboveRows_extraction` and `root_bound_of_above` (Lean) bound it by
      Σ_{D: μN(D)⁶ < L} θ(L/N(D)⁶, B). The multiplicity is (L/μ)^{1/6} instead of L^{1/6}, so the theta term
      becomes M^{5/6}N^{1/3}μ^{−1/6} = B^{1+γ} at M = N = B, μ = B^{1−6γ}.
    - Below: the rows are R = R₀D⁶ with N(R₀) ≤ μ. Since rowValue(R₀D⁶)(I) = rowValue(R₀)(I)·(gen D/I)₆⁶, a
      repeated row is row R₀ **restricted to the columns coprime to D**, and it vanishes elsewhere. So the below
      energy is Σ_{R₀ ≤ μ} Σ_D |⟨μ_{(D)}, row_{R₀}⟩|², with μ_{(D)} the vector restricted to columns coprime to D.
      Pulled back through the Poisson identity, these are **restricted twisted thetas** (step 2's objects).
  - **Design rule: every metaplectic fact goes to the application.**
    - Keep the restricted thetas as corrections, instead of proving they carry no excess. That removes step 2's
      d^{−2}-twist and Kazhdan–Patterson vanishing from C, so C becomes purely elementary bookkeeping on Sil's
      proved code.
    - The application then bounds ⟨v·1_{(·,D)=1}, f⟩ for its own vectors. By Möbius over d | D that is a dilation
      of v, which is the dilation aspect of input A that the K-wall needs anyway.
  - **Corrected Cauchy–Schwarz.**
    - `coherent_weighted_bound` pairs a-side rows V·K with b-side rows U·K for the same dual frequency K. So the
      split must be by the sixth-power part of K, which repeats both sides together.
    - For K with kernel ≤ μ, keep the coupled form. By AM–GM, |Σ conj(a)·b·kernel| ≤ (|A_K|² + |B_K|²)/2, which
      leaves correction forms on each half.
    - Sil's argument stays unchanged on the rest.
- **Fork points in Lean.**
  - `lambda_sixth_extraction`: split D = 1 from D ≠ 1.
  - `coherent_weighted_bound`: keep the D ≠ 1 rows as correlations instead of sieving them.
  - The reference (one step, every dual frequency a correction, slot convolutions) is the special case where the
    correlations are bounded pointwise by the bilinear form (journal, "The reference wall needs no metaplectic
    input").

## Target 2 needs only one step (2026-10-31)

In the reference regime B ≤ A^{2/3} one Poisson step suffices. The source spikes are the dual's small-kernel rows,
so removing them is a row restriction, and the rest of the dual is bounded by Sil's proved optimal sieve. This gives
‖E_{A,B}λ‖² ≤ C(AB)^ε {A‖λ‖² + (A/B)Σ_{N(h) ≤ B²/A} w_h|⟨λ, f_h⟩|²} (journal, "Target 2 needs one corrected Poisson
step"). This is a moderate fork of `SievePoissonBound` and `SieveDescent`. The recursion below is needed only for the
K-wall.

## Form of the statement (2026-10-31)

The recursion cannot prove a bound for vectors exactly orthogonal to a fixed spike span. Each Poisson step restricts
to coprimality with r ≤ B^γ, i.e. dilations, and after the ≈ log(1/ε)/γ steps the accumulated dilated family spans
the source space (journal, "Exact orthogonality cannot be the corrected sieve's form"). The target is the weighted
form G ≼ B^{1+γ}·I + Σ_f w_f f f*, with the weights carried through the recursion. Applications then need
Σ_f w_f |⟨λ, f⟩|² small: Patterson-type mean values in the twist aspect (numerically confirmed) and the dilation
aspect (untested).

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
2. Monotonicity: unchanged. It is inclusion in Sil's form, and the twist range stays fixed.
3. `SieveImprovement.step`: replace by `silStep 6 γ` (arithmetic proved in `OffSpikeIteration.lean`; `silStep_sil`
   checks that γ = 1/6 gives Sil's map).
4. `SievePoissonBound`: split the dual sum by kernel. The small-kernel part becomes the correction form, and the
   large-kernel part is bounded as before.
5. `completed_of_exponent`: the dual's own (row-side) theta N^{5/6}L^{1/3} is no longer absorbed by L^{1/6}N once the
   twist range is nontrivial (ratio (Lμ/N)^{1/6}). The corrected hypothesis must be two-sided and transposable
   (E compressed on both sides), because this lemma uses the swap θ(L, N) = θ(N, L).

Steps 4 and 5 are the analytic additions. Steps 1–3 are bookkeeping on proved code. The precondition family grows
by one level per step (journal, "Sil's inclusion monotonicity"): about 400 levels for γ = 0.015, mostly angular
twists of the three spiky ones.
