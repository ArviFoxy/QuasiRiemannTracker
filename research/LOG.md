# Research log

Goal: lower θ in "every Dirichlet L-function is nonvanishing on Re s > θ" by at least 1e-5 against
the best upstream PR (smaller gains count only if they simplify or clarify the proof).

| reference | θ | note |
|---|---|---|
| upstream PR #70 (Mark Lewko) | 0.874772906 | |
| upstream PR #71 (recost of PR #69 graph), best upstream PR | 0.87477290596 | 4e-11 below #70; checked 2026-10-24 |
| this branch, Lean (`submissions/repeated-marks-20261024`) | 0.8747289 | 4.4e-5 below PR #70 |
| next milestone (1e-5 below this branch) | ≤ 0.8747189 | |

Conventions: `θ*` values are exact-return evaluations (rational certificates) unless marked "float".
Each entry records the idea, the measured effect, and where the artifacts are. Negative results are
kept on purpose.

---

## 2026-10-23

**1. Proof analysis (PR #69, Collet).** Read the paper and Lean. All estimates are ℓ² bounds for
character evaluation maps over K = Q(√-3), closed by Poisson/Gauss sums, cubic-theta reflection,
recursion, sixth-power amplification and the zero detector. The final count is the weighted mean of
three witness lines (inverse I, plain P, long L; weights 0.505/0.193/0.303).

**2. Doubled marks in the source HIGH count.** The HIGH inverse witness may use each marked slot
twice (foundations Lemma 8.1 already allows repeated lists). New 59-face graph, exact certificate:
θ = 0.8747514. → `doubled-marks/`. Superseded by 3.

## 2026-10-24

**3. Repeated marks (K copies), per-class cutoff, Lemma C, Lemma D.** θ = 0.8747289, formalized in
Lean (`Candidate.bound`, standard axioms only). → `repeated-marks/`,
`submissions/repeated-marks-20261024/`.
- Lemma A_K: slots repeated K times in the inverse witness.
- Lemma B_K: one detector cutoff per amplitude class.
- Lemma C: payment for any monotone min-of-facets gain with `G ≤ νS` (replaces HF12).
- Lemma D: the physical face applied through its global source theorem at every shift.

**4. Lemma E (amplitude split of LOW/HIGH): REFUTED.** Erasing low-amplitude HIGH rows as LOW rows
needs zero-free slot bounds uniformly in real power and height (`ActualLow`); amplitude at the
detected zero says nothing at other heights. All gains from it were void.

**5. Lemma F (cap induction): valid, below the bar.** A node can be its own LOW parent at a smaller
cap. Consolidated with finer pivots and a HIGH density floor 0.45: θ* = 0.8747257 (−3.2e-6).
→ `cap-induction/`, `lean-lab/LemmaF.lean`.

**6. Lever map.** Sensitivities at the binding point (d = h, δ ≈ 0.4546, p = 1/2):
- dθ/dB_C ≈ −4.0e-3 and dθ/dB_P ≈ −6.7e-3 (face heights);
- per 1e-3 of line exponent: I 6.7e-5, L 4.0e-5, P 2.6e-5;
- dθ/dR ≈ 0.133.

The four binding exponents:
- MI slot cost 2;
- sextic amplifier exchange 6;
- long slope (1+5r)/6;
- plain slot cost 6κ.

A catalogue cross-check (21.9k records) found nothing that moves them. → `cap-induction/README.md` §4.

**7. Re-derivation of the binding structure (this session).**
- *Coupled hybrid norm (new lemma, proved abstractly).*
  - Mechanism: the active slot product's Gauss-sum coefficient is twisted-multiplicative. A balanced
    split of the slots gives a bilinear form with a cubic-symbol kernel. Heath-Brown's cubic sieve
    then removes the `L` term of MF2.29, giving `u'_h = min(z, (v+z)/3) ≥ u_h`.
  - Result: no θ gain. In the MI's binding child the row branch has slack (exponent `F_c/2` at
    `v = 0`, `F_c − 3z/2` at `v = H`). Only the column branch binds, and it is exactly
    `T_d ≤ F_c ⟺ r + 2z ≤ m`.
  - Conclusion: the slot cost 2 is the slot primes entering the second reflection's conductor
    squared. → `lean-lab/MIBranches.lean`, `lean-lab/CoupledHybrid.lean`.
- *Numerator glue (14.7), Hölder vs pointwise.*
  - Replacing the fourth-moment Hölder bound by the pointwise bound `|S'| ≪ U^{δλ/2}` for class rows
    (zeros ≤ a + 2e) gives E-contribution `dR + δℓ = 0.56093` against Hölder's
    `d/4 + 3dR/4 − δpC/2 = 0.56026` at the binding point.
  - Interpolating (`|N|^k ≤ max^{k−4}|N|⁴`) is affine in 4/k, so the optimum is an endpoint.
  - Result: Hölder is optimal by 6.7e-4 in E. No gain.
- *Plain sixth moment / higher Hölder.* Unavailable: the reflected length λ = 2ℓ/h = 0.4186 has
  3λ > 1.
- *Halász–Montgomery / Huxley large values.* Useless here: the witness threshold U^{δr} is below the
  Pólya–Vinogradov off-diagonal U, and the mean-square off-diagonal gives U^{1+r/2−δr} > U.
- *Heath-Brown/Vaughan decomposition of the long Möbius witness.* Pure Möbius pieces are short and
  weak. Mixed pieces (μ*1) are not canonical (the canonical energy forbids extra n-coefficients),
  and Möbius×slot pieces raise the amplification cost (marks cost 5/3 > 2δp in the long branch).
  No gain.

- *Count-face selection.* Choosing face C by the binding plain width `(B − 2m*)/Λ` instead of the
  height at z = 0.045 selects the same node (θ* = 0.8747266). No gain.
- *Bootstrap re-feed.* Rebuilding the consolidated Lemma-F chain with the natural cost re-fed from
  θ = 0.8747289 (`K = 4.4967468` instead of 4.4973108) changes face heights by about +3e-6 per node,
  worth about 1e-8 in θ. The chain's end faces are set by the LOW/HIGH dynamics (q → 1/2), not by the
  seed. No gain.
- *Probe geometry decoupled from the pool (x + y < 1 − ℓ).*
  - The generic return fixes x + y = 1 − ℓ. The marked energy (198) only needs x + y + ℓ ≤ 1, and
    (199) only needs 1 + 3ℓ < 2(x + y).
  - At fixed (x, y) the return exponent rises with ℓ (∂E/∂ℓ ≈ +0.47, mostly via the conductor top
    h = 1 + ℓ − x), which looked like a large gain.
  - It is not. Collet's own definition of the signal normalization is k = 5/6 − x/3 − ℓ/6
    (`Cycle61/Assembly/Geometry.signalShift`), which equals (4 + y − x)/6 only on x + y = 1 − ℓ. With
    the true k, θ_phys = 5/6 + (x + y)/12 − ℓ/6.
  - E and θ_phys then have opposite gradients along the constraint: a Pareto optimum. No gain.
- *Self-HIGH-parent induction* (the node at a smaller cap as its own HIGH parent). The chain's HIGH
  parent is already the immediate predecessor, and at the binding pivot both faces coincide. No gain.
- *Residue structure of the inverse witness* (idea, not a result). At a zero,
  `Σ_n μ(n)ψ(n)n^{-ρ}W(n/D) = Ŵ(0)/L'(ρ) + (left-shifted integral)`, so all dyadic inverse witnesses
  share the residue 1/L'(ρ). If the residue dominated, the inverse witness could always be taken at
  length r ≈ 1, giving the density-hypothesis value I = 1 − δ. Blocked: the error term needs control
  of 1/L to the LEFT of the zero, and nothing is known there.

- *Where the plain slot cost 6κ comes from* (foundations §7.2.5–7.2.8, MF3.70–MF3.72).
  - Each plain-descent step amplifies the Gauss-row norm by `h ↦ hp⁶` (density saving ℓ, ball
    enlargement 6ℓ). The child's capacity defect is at most 6(w + ℓ) against an allowance Δ ≥ w + ℓ.
  - The defect is paid by deleting slots pointwise (MF3.47). A slot of length d releases 6κd
    capacity and costs κd energy.
  - So plain slot cost = 6 × (pointwise slot energy). Slots cannot be reflected through the
    functional equation, unlike plains, so they have no other exit.
  - The source chain's LOW/HIGH split lowers the energy κ → q ≈ 1/2 (Λ ≈ 6qB ≈ 2.9). The factor 6 is
    the same sixth-power exchange rate as the long branch and the LOW amplifier.
  - Any improvement here needs either a non-pointwise slot treatment inside the descent (the Patterson
    bias of plain duals is what forces the amplified descent) or a better exchange rate. Both are atoms.
- *Long Möbius moment = zero density in disguise.*
  - For D > U, Σ_u|M_u(D)|² beyond the diagonal is a Barban–Davenport–Halberstam-type statement in
    the regime "polynomial longer than the family". Even for classical characters this needs
    zero-density input.
  - Sixth-power amplification gives U^{1/6}D^{5/6} for free. Re-amplification stalls, and splitting
    rows by zero supremum is circular.
  - Type I pieces of Vaughan's identity vanish for D > U^{1+ε} (long plain sums are ≈ 0 by Poisson),
    so the long sum is pure Type II. But Type II with Möbius × rough coefficients has no admissible
    moment beyond the diagonal.
- *Conductor top h.* The exact certificate's h = 401/500 is optimal (h = 0.801, 0.803: θ* = 0.8747268).

- *Structured slot coefficients in the MI column branch.* The physical slots carry fixed finite-order
  characters (Θ), not arbitrary weights, so their prime sums obey the zero-free bootstrap
  `|Σ_p χ(p)W(p/P)| ≪ P^{β*}` (the input that gives the plain moment its slot cost 6κ).
  - In the reflected energy (paper Lemma 14.3) the column branch is the large sieve's dual diagonal:
    the dual length is `v = T_d = 2H + 2z_a − N_*`, because the slot primes sit in the reflection
    modulus `c` and the cubic-theta reflection has conductor `q_c²`.
  - In that branch the hybrid norm (Lemma 14.2) already saves the full slot length (`u = z_a`), while
    the zero-free pointwise bound saves only `z_a(1 − κ)`.
  - Result: no gain. Slot cost 2 is the square of the reflection modulus, not a weakness of the slot
    sum.
- *Zero-detector variants (paper Prop. 8.3).* A zero gives an inverse block `M_r` and a plain block
  `S_m` with `r ≤ t`, `r + m ≥ t`, `m ≤ 1/2`. The long line comes from the edge block (`r ≈ t`,
  `m ≈ 0`), where the detector polynomial on `(D*, 2D*]` is exactly `−μ(n)`.
  - Smoother mollifier cutoffs (Selberg-type weights `P(log(D*/l)/log D*)`) change only log factors.
  - Second-order detector `C = 2M − M²L` (tail `(1 − ML)²`, supported beyond `D*²`): it gives two
    independent witness pairs with `r_i + m_i ≥ τ`. The adversary puts both at the same point, and the
    plain product `S_{m1}S_{m2}` is weaker than `|S_m|⁴`. Worse than first order.
  - Several cutoffs `t` at once (covering formulation): a row escapes every detector iff the
    `t`-range is covered by intervals `[r, r+m]` of saturated bad blocks. Below the single-detector
    optimum, short crossing blocks cover up to `r_X + m_X` and pure long blocks cover beyond `ℓ_X`,
    and these overlap. No gain.
  - Truncating the plain factor instead of the inverse puts `1/L` in the contour integral, with a
    pole at the zero. Impossible.

- *Repeated slots in the HIGH count's plain branch.* Collet's plain source moments allow overlapping
  marked pools, so the plain witness could also take K copies (cap `KS` instead of `S`). But along
  the whole consolidated chain the binding facet of the HIGH gain is (inverse cap, parent affine cap),
  never "available slots" on the plain side (checked at nodes 20, 40, 55, 58, `ν ∈ [q, 0.6]`). No gain.
- *Plain × slots through the generic sextic large sieve.* `Σ_u|S_m Q_z|² ≪ U` holds for
  `m + z ≤ 1/2` with no special structure (the `U^{5/6}D^{1/3}` term is harmless there), but the
  resulting count `1 − δ/2` is far worse than the fourth-moment line. A fourth moment with MI-type
  slot cost 2 instead of `Λ ≈ 3` would give `P(m*) ≈ 0.585` (vs 0.604). It is blocked by the
  Patterson bias of plain duals, which is exactly why the source theorem needs the amplified descent.

- *Physical Gram exceptional frequencies, re-derived with the exact correlation (paper Lemma 13.3,
  Prop. 15.2).* The Gram sum `Σ_m|A_m|²` has probe coefficients `c(s) = 1_σ(s)χ_s(b*)ξ̄(s)/τ`.
  After Poisson the residual columns carry `c(dm₁)χ_{m₁}(k)` and `c̄(dm₂)χ̄_{m₂}(−k)`.
  - At a prime `p ∈ S`, `p ∤ 6`, with `ξ_p = (·/π_p)^j`, the two column exponents are `1 − j + v`
    and `−1 + j − v` (`v = v_p(k)`). They vanish together exactly when `v ≡ j − 1 (mod 6)`.
  - So for `k = a⁶e₀`, with `e₀` the S-supported element fixed by `ξ`, both complete means survive
    and there are `≍ K_R^{1/6}` genuine main terms.
  - A mixture of several `ξ_i` gives only diagonal (`i = k`) main terms with weights `|λ_i|²`, so
    they cannot cancel.
  - Result: `c_g = 1/12` (the `P_a^{1/6}` term) is genuine, as found earlier.

- *Amplifying the rows of the MI column branch (near miss).* In the reflected energy (paper
  Lemma 14.3, 14.16) the row character is `χ_k(nb)³`, which is quadratic. So its exact invariance
  group is the squares (`k ↦ ka²`), with exchange rate 2 instead of 6.
  - Naively, amplifying the residual rows lets the column branch pay `H + (L−H)/2` instead of the
    dual length `L = v + ℓ_b`. That would turn `r + 2z ≤ m` into roughly `r + (21/11)z ≤ m`, far
    more than the 1.995 needed.
  - It fails. Amplification needs a large sieve over the full redundant family `{k' ≤ KP²}`, and
    for generic dual coefficients that family's constant contains a redundancy term `≥ N·P`. The
    single-character test vector `c_n = χ_{k₀}(n)³` attains it, in exactly the regime `L > K` where
    the column branch lives.
  - The MI's own sixth-power amplification (Lemma 17.6) escapes this only because it applies the
    Möbius moment in its diagonal regime (`D < H`). There the redundancy is harmless.
  - Any gain would need a structured (non-generic) bound for the dual coefficients `β(n,b)`, and
    that alone would already remove the dual-diagonal term.

- *Why the reflected-energy slot cost is 2, and why the probe cannot avoid it.*
  - Divisibility marks `p | A` on the theta index are detected by additive characters mod `p`, or
    equivalently by a twist mod `p` after factoring out `p` (twisted multiplicativity
    `γ₂(DA') = γ₂(D)γ₂(A')χ_{A'}(D)⁴`). Either way `p` enters the cusp denominator `c`.
  - The cubic theta reflection at cusp `a/c` rescales by `c²`. That is the `2z_a` in `T_d`.
  - Probe redesign does not escape it. The high-side sextic slot factor `χ_p(u)` comes only from
    local exponent `j ≡ ±1 (mod 6)`, i.e. `p ∥ c` (an active mark). Cube marks (`p | n`, inactive,
    free in the reflection) would give the quadratic factor `χ_p(u)³`, which is tied to the zeros
    of `L(s, ψ_{u³})`, not the row's own zero. The numerator would then pay up to
    `κ/2 · ℓ ≈ 0.06` with no count gain.
  - Removing some active marks pointwise costs `ℓ₂/2` in the low bound for a relaxation of `2ℓ₂`
    (net `Δθ ≈ +0.13ℓ₂`, a loss). Using zero-free prime-sum bounds on the reflected slot sums is
    worse than the hybrid's mean-square saving.

- *Large-values methods cannot help this framework (Guth–Maynard type, Halász, Huxley).*
  - Every witness count is Chebyshev applied to a mean value that is already diagonal in its own
    family. The marked inverse moment is diagonal for `r + 2z < 1`. The plain fourth moment with
    slots is diagonal on its face. The long branch is the MI's diagonal bound in the amplified
    family `{v ≤ H}`, where `D < H`.
  - In each case Chebyshev already gives density-hypothesis strength for that witness and its
    capacity. All losses against `1 − δ` come from capacities (slot costs 2 and `Λ ≈ 3`) and from
    the amplification's sparsity (`P⁵`), never from large values.
  - So an improved large-values estimate, even a Guth–Maynard analogue for the sextic family,
    would not move `R`. Only longer or cheaper witnesses can.

- *Exact origin of the plain slot cost `6κ` (Collet MF3.70–MF3.72, paper §18.5–18.8).*
  - The plain moment is proved by induction on the width `M` with invariant
    `A + (6κ−1)z ≤ M` (`A = n₁ + n₂ + z`). Each step must lower the width by at least `σ`, so the
    child's excess grows: `(A'−M') − (A−M) ≤ g − d − (K₀−K) + w − w_o ≤ 6(w + ℓ)` (MF3.70).
  - In the amplified main norm (`w = 0`) the row ball must grow by `6ℓ*` (`= 2σ`) to contain
    `hp⁶`. That growth also supplies the width progress, and the only allowance is the density
    saving `ℓ*`, so the ratio is 6. For the valuation-1 extraction error the ratio is `σ/ℓ_p ≤ 6`
    (pool primes have `ℓ_p ≥ σ/6`); valuations 6 and 7 give ratios `≤ 2` and `≤ 12/7`.
  - The defect is paid by deleting whole slots pointwise: `|∏Q|² ≤ Z^{κz}` (MF3.47). Deleting
    length `d` releases `6κd` of capacity for `κd` of energy (MF3.72).
  - So slot cost = (defect/allowance ratio 6) × (pointwise energy `κ`, or `q` after LOW/HIGH).
  - Without amplification the step has no allowance at all (`Δ_child ≥ w + ℓ = 0`), so the
    sixth-power amplifier is what pays for the induction's progress, not something the slots need.
  - Reducing the ratio needs a cheaper allowance than `G(u, hp⁶) = G(u, h)`. Folding rows modulo
    the Gauss moduli fails because `H(h) = Σ_u B(u)G(u,h)` has no short period. Reflecting long
    child plains is already used for `A > 5M/6`.

- *Why the inverse moment is cheaper than the plain moment (structural, from paper Prop. 5.1 and
  (4.7)).*
  - The completed reflection is the functional equation of
    `T(s,Ψ) = L₀(s,Ψ)·D(s,Ψ)`, `D = Σ_{n sf} γ₂(n)ᾱ(n)Ψ(n)q_n^{-s}`. This is the Mellin transform
    of the (twisted) cubic theta function, which is entire.
  - Its squarefree coefficients are `θ(n) := γ₂(n)ᾱ(n) = μ(n)λ̄(n)γ₂(n)`. Here
    `α(p) = −γ₂(p)³ = −π'_p/|π'_p|`, so `α = μλ` with `λ` an angular Hecke character.
  - After the first Poisson step in the rows, an inverse polynomial's column coefficient is
    `μ(z)γ₋₁(z)`. By `γ₁γ₂ = μαG` this is exactly a theta coefficient (`= ᾱγ₂χ(−1)G`). The
    Möbius sign pairs with the Gauss sum, and the theta reflection applies, at cost `c²`.
  - A plain polynomial gives `γ₋₁(z)` alone, i.e. `μ(z)·conj(θ(z))·G(z)`: a Möbius-twisted theta
    coefficient. It has no functional equation, so plains cannot use the reflection recursion.
    They need the twice-Poisson amplified descent, with its ratio-6 bookkeeping.
  - Consequence: lowering the plain slot cost through reflection would need a reflection-type
    identity for Möbius-twisted cubic theta series, i.e. an "inverse theta" recursion. That is
    open direction 2, stated precisely.

- *Why the MI stops at `D = U` (mechanism).*
  - The initialization (paper (17.71)) bounds the nonprincipal Poisson expression by a positive
    canonical square. To do so it restores the principal (`z₁ = z₂`) terms.
  - For an inverse polynomial of length `D` over rows `u ~ U`, the dual rows run up to
    `H' = D²/U`. The restored dual diagonal then contributes `(U/D)·H'·D = D²` (unnormalized),
    i.e. `D` after normalization.
  - So any argument that passes through the positive canonical square gives `U + D`, and the
    diagonal bound needs `D < U`. Beating `D` for `D > U` needs signed cancellation in the
    off-diagonal (random signs give only `D√U`), not a better bound for the square. This is the
    analytic form of "the long Möbius moment is zero density in disguise".

- *Compounded lever map* (`atom-targets/compound/`). The source chain was rebuilt with each atom
  modified, the faces re-selected and the float return re-solved.

  | change | faces fixed | chain rebuilt |
  |---|---|---|
  | MI slot cost 2 → 1.99 | −2.01e-5 | −2.03e-5 |
  | long exponent −1e-3 | −3.70e-5 | −3.91e-5 |
  | LOW exchange rate 6 → 5.94 | 0 | −5.3e-6 |

  The chain's feedback adds only 1–6%. The "better count → lower q → flatter faces" loop contracts
  quickly, so no atom is secretly amplified by the chain. The exchange rate needs 6 → 5.89 for −1e-5.
- *Fresh-perspective agent on the count (cold read).* Nothing usable; it independently confirms the
  closures.
  - Any convex or Hölder combination of the three lines, and several cutoffs at once, gives at best
    the minimum of the lines. The gap condition `r_I(R) + m_max(R) = r_L(R)` fixes `R` for one
    cutoff and for many.
  - Its main proposal is a scale-transfer lemma for the Möbius witness via the residue `1/L'(ρ)`.
    This is Turán's explicit-formula method.
    - For `1/L`, the residues `1/L'(ρ')` of the other zeros are unconstrained (near-double zeros
      make them huge). The regress "cancelled at a smaller scale → a left zero with a larger
      residue" never closes. This is the same obstruction as the earlier "residue structure" entry.
    - For `L'/L` the residues are positive multiplicities, so the prime witness is saturated at
      almost every scale. Only tight clusters need Turán, at a constant loss. But a prime witness
      has no diagonal mean value at length `U` in this family: the generic sextic sieve carries
      `(UN)^{2/3}`-type terms, and the theta reflection needs Möbius coefficients. Writing it as
      `Λ = μ * log` turns it back into the mollifier detector's blocks.
  - Its challenge to slot cost 2 (slot coefficients are smooth prime sums at one height) is answered
    by the MI-column entry above: the cost is the reflection modulus `c²`, independent of the
    coefficients.

- *Growing the probe's auxiliary modulus `b*` (Gram exceptional frequencies).* In the additive Gram
  bound (paper Prop. "quantitative additive Gram bound") `P_a = Y'²/Q` with row ball
  `Q = q_{b*}X'Y'`. A large single prime in `b*`, which leaves the Euler factor ≈ 1, would shrink
  the exceptional count `P_a^{1/6}` by `q_{b*}^{1/6}`. But the completed-row norm (paper Lemma
  "compensated completed-row norm") is taken over the same ball and is diagonal there (`∝ Q`).
  The low bound `Y'^{-1/2}P_a^{1/12}(row norm)^{1/2}` therefore scales as `q_{b*}^{5/12}`, a loss.
  Fixed `b*` is optimal. The Gram's `P_a^{1/6}` stays a genuine sixth-power-invariance count:
  `A_{ma⁶} = A_m` and `B_{ma⁶} = B_m` on coprime parts.

- *What binds at the end of the source chain* (`atom-targets/compound/bindgates.py`).
  - Along the K = 8 chain the binding gate is the regular HIGH gate `H_ν + G > f` at `ν = q` and
    `b = cap`. Only the first node is bound by the centered gate. Every other gate has reserve
    ≥ 1e-3.
  - The solver puts `q` just below `Λ0/(6B0)`, the largest value with a positive LOW denominator.
    So `q` tracks the parent's slope: 0.74 at the start, 0.505 at the end.
  - The HIGH gate carries the amplifier term `a(5 − 6ρ) ≈ 1.53a`, about 0.0135 at the end, because
    HIGH child rows are counted in the amplified child. The child has scale `F = 1 − 6a` and budget
    `F + a`. Rows are classified only after both transforms: the paper enlarges to all rows before
    any Poisson step. So this term cannot be avoided by classifying first.
  - Pricing: dropping the term entirely (`HIGH_NOAMP=1`, chain rebuilt) gives only
    `Δθ* = −3.2e-7` (`noamp.log`). The centered terminal gate `5/6 + αL_ref − T − 9a > 0` binds at
    once instead.
  - The real currency is the amplifier width `a = (qX + r)/(1 − 6qB0/Λ0)`. Here `X` is the slot
    excess at the cap, about 7e-5 per step. The denominator is about 0.003 at the end, so the
    amplifier mostly pays for its own scale shrink, and every gate containing `a` (HIGH, centered,
    `1 − T − 5a`, …) feels it.
  - The chain's limit is `Λ → 6qB` with `q ≥ 1/2` (LD1), i.e. `Λ_∞ = 3B ≈ 2.87`, 1% below the
    current end (2.897). Reaching it would need a cheap amplifier, i.e. the exchange rate 6 again.

- *Explicit-formula scale transfer for the Möbius witness, made quantitative* (follow-up to the
  fresh agent's suggestion A and the earlier "residue structure" entry).
  - **How saturation is obtained.** Saturation of both witnesses (paper Prop. "Two saturated
    witnesses") comes from the buffered zero-free bin: no zeros right of `a + 2e` in the window
    gives pointwise upper bounds `|M_r|² ≤ U^{δr}` and `|S_m|² ≤ U^{δ min(m,1−m)}`. The detector
    gives the product lower bound. Saturation is therefore a statement at one scale only.
  - **Contributions of the zeros.** By Mellin inversion, a zero `ρ'` of depth `δ'` contributes
    `A(ρ',D) = D^{δ'/2}/|L'(ρ')|` to the normalized witness at its height.
    - The bin's own zero (`δ' = δ`) saturates every scale at once, if and only if
      `|1/L'(ρ)| ≳ 1`. In that case the Möbius block at `r = 1` is saturated, and `I(1) = 1 − δ`
      (the density hypothesis) would apply.
    - A left zero (`δ' = δ − 2η'`) saturates the level-δ witness exactly at the scales
      `D ≤ |1/L'(ρ')|^{1/η'}`.
  - **What the adversary needs.** At the binding crossing `r* = 0.742`, beating the transfer to
    `r = 1` needs a left zero with `|1/L'(ρ')| ∈ [U^{r*η'}, U^{η'})`. For the transfer to give
    nothing beyond the current R (`1 − δ + 2(1 − r*)η' ≥ 0.6047`), the adversary needs
    `η' ≥ 0.115`, i.e. `|L'(ρ')| ≈ U^{−0.085}`.
  - **Why it is not excluded.**
    - Near-double zeros do not supply this: their two residues cancel and act like a double pole,
      `D^{ρ'} log D / L''`.
    - A power-small `|L'(ρ')|` needs `Π|ρ' − ρ_j| ≲ U^{−0.085}` over nearby zeros.
    - Jensen at a point of the zero-free line (`|L| ≥ U^{−ε}`) with the convexity bound still
      allows about `0.36 log U` zeros within distance `0.12`. That is only mildly above the average
      density, and enough for `|L'| ≈ U^{−0.085}`.
    - The truncated left integral (`1/L` on `Re s = a − η`) has the same issue.
  - **Verdict.** The transfer would need a count of rows with locally elevated zero density left
    of their rightmost zero, at better than `U^{R}`. No tool gives that (zero counts carry no power
    saving for multiplicity). Blocked, but the obstruction is now explicit.

- *Re-reflecting the column branch's dual sums (why the recursion cannot continue).*
  - **The idea.**
    - In the reflected energy's first branch, the energy is `max(H, v + ℓ_b)`: rows against dual
      length.
    - The dual sums are a fixed cusp expansion `d_θ(m)` twisted by the quadratic `χ_h(m)³`, whose
      conductor is about `N(h) = Z^H`. So their critical length is `Z^H`.
    - When `T_d = 2H + 2z − N* > H`, the functional equation of `d_θ ⊗ χ_h³` would send length
      `Z^{T_d}` to `Z^{2H−T_d} = Z^{N*−2z} < Z^H`. The root number disappears in `|·|²`, so the
      column branch would be diagonal and slot cost 2 would go away.
  - **Why it fails.** The first reflection turns the row twist into a quadratic one because the
    Fourier and theta factors combine as `χ_p^{−1}χ_p^{−2} = χ_p^{3}` (paper Step 4). A second
    reflection multiplies in another theta factor, `χ_p^{3}χ_p^{−2} = χ_p`, so the re-reflected sums
    are sextic twists again.
  - **Consequence.** The generic sextic sieve's `(Z^H L')^{2/3}` term is `Z^{4H/3}` near the
    boundary `L' ≈ Z^H`, which is worse than paying the column excess. Each reflection alternates
    the twist between quadratic and sextic, and only the quadratic step has a sharp large sieve.
    This is the precise reason the MI recursion stops, and why slot cost 2 is intrinsic.

- *Free amplifier and natural seed cap (two more chain experiments, `atom-targets/compound/`).*
  - Making the LOW amplifier free in every gate except its own construction (all `a`-terms dropped
    from the HIGH, centered and auxiliary gates) gains only 1.7e-6 (`voi_freeamp.log`). The chain's
    descent is limited by the HIGH gate's count part `1 − ρ(ν) − νT + G` at `ν = q`, i.e. by a
    zero-density estimate for the family at `σ = (1 + q)/2 ≈ 0.75`. `ρ` is the Xu–Sang exponent.
  - Raising the natural seed cap `h0` (any fixed `h0` is admissible) from 0.055 to 0.08 gains 2e-8.
    Wider caps lose 1.6e-6 to 3.8e-6 because the centered gate binds at `b = cap`.
  - The HIGH gain's binding facet on every late node is (inverse cap `r + 2z ≤ F`, parent face). The
    plain cap line and the K-copy line are slack. So the chain feels slot cost 2 directly, but only
    through `ε_H`, at `dθ/dε_H ≈ −4.4e-3`.

- *Is the column-branch excess a real size? (heuristic computation, correcting the barrier list).*
  - The column branch bounds a mean square of the form `Σ_{h~Q} |D_h(N)|²`, with
    `D_h(N) = N^{-1/2} Σ_{m~N} g̃(m)(m/h)₂ W(m/N)` (theta coefficients with a quadratic twist), at dual
    length `N = Q^{1+η}` beyond the critical length `Q`. The barrier list said that Lindelöf-quality
    bounds for these twisted theta sums would remove the excess `N`.
  - Summing over `h` first gives the exact decomposition
    `Σ_h |D_h|² = Q·(diagonal) + (Q/N²) Σ_{|j| ≤ N²/Q} |Σ_m g̃(m)ε(m)(j/m)₂ W'(m/N)|²`
    (Poisson in `h` modulo `m₁m₂`; quadratic Gauss sums `(j/m₁m₂)√(m₁m₂)`). The second term is a sum
    of squares. If the dual sums have square-root size on average (no conspiracy between cubic Gauss
    sums and quadratic characters), it equals `(Q/N²)·(N²/Q)·N = N`. So the excess is the dual
    diagonal, the natural size, not a weakness of the large sieve.
  - The reflection picture agrees once the alternation is taken into account. Past the critical
    length, `D_h(N)` reflects to a sextic-twisted theta sum of length `Q²/N`. A mean square of
    `Q^η` per row needs these sums to be biased at size `Q^{η/2}`, which the sextic sieve's
    `(QL')^{2/3}`-type terms allow.
  - Consequence: no bound on the twisted theta sums themselves can remove slot cost 2 inside the
    column branch. Atom 1 can move only by restructuring the inverse moment before the positive
    canonical square, keeping signed off-diagonal terms (the same conclusion as "Why the MI stops at
    `D = U`"). This is a heuristic (it assumes square-root dual sums on average), not a proof.

- *The source chain is an ODE* (`chain-ode/`). The binding gates reduce the chain to
  `E'(s) = −6qE/(1 − 6qs)` with `q = (15 − 10/X)/6` and `X = E + (1 − g(s))s`. Here `E` is the
  envelope, the first equation is the LOW limit `Λ ≥ 6qB`, the second is the HIGH gate at the pivot,
  and `g` is the marked gain as a fraction of its cap `νS`.
  - With `g(s)` read off the consolidated chain, the ODE reproduces the 107-node chain to 1.2e-4 in
    envelope at `s = 0.0412` and `0.045`. So discretization and gate reserves hold less than 1e-6 of
    θ.
  - Correction to the "free amplifier" entry: the HIGH gain is far below its cap early in the chain
    (`g ≈ 0.43` at `s = 0.014`, 0.85 at 0.030) and close to it late (0.95 at 0.042). A perfect gain
    everywhere would raise both faces by 1.6e-3, about 1.7e-5 in θ. But the early gap is the
    inverse cap `r + 2z ≤ F` (slot cost 2). The best of all earlier faces as HIGH plain witness,
    even chosen per amplitude class, gives exactly the same gain.
  - Late in the chain the faces sit on the unmarked zero-density boundary `t = 10/(15 − 6q)`. So the
    chain is fixed by `ρ(ν)` (the long line), the exchange rate 6 and slot cost 2.
  - The ODE is contracting (perturbations lose about 25% per 0.02 of width), which is why the seed
    does not matter.

- *The slot contour `z₀ = 17/50` in the return (foundations §14.7).* FR13's constants decode as
  `13h/75 = (z₀ − 1/6)h` and `−9d/100 = (1/4 − z₀)d`. They come from the numerator bound (223),
  `Y^{-1/2} Z^{ℓ(z₀−1/2)+ℓq} U^{1/4+3R/4−qz_A/2}` with `U = Z^d`. So `z₀` enters `E` only as
  `z₀(h − d)`, which vanishes at the binding conductor edge `d = h`. The lower limit `z₀ > 1/3`
  (Euler convergence, `1 − 6z₀ < −1`) is therefore irrelevant at the binding point. At `d = h` the
  exponent is `E = 1/2 − 5h/12 + ℓ/2 + δ/2 + δp(ℓ − C(h)/2) + (3/4)hR`, and `∂E/∂h ≈ −7e-4`, so
  `h = 401/500` is stationary. No gain.

- *Bin-restricted faces via LOW-only source steps (idea, refuted).*
  - **The idea.** The return's plain witness only needs `Σ_{u ∈ bin} |S_u S_u ΠQ_u|²` over rows
    in one zero bin, and these rows are zero-free right of `a + 2e` in the bin's height window. That
    is the framework's `ActualLow` predicate (Collet Lean `LowBranch/Gate.lean`: zero maximum
    `< a + 2e` up to height `3(i+1)Z^τ`). In a source step restricted to such rows the HIGH class
    would be empty. A LOW-only step at `q ≈ δ ≈ 0.4546` has denominator `1 − 6qB₀/Λ₀ ≈ 0.1`
    instead of 0.003, which suggested class-restricted faces with `Λ ≈ 6δB ≈ 2.6`.
  - **Why it fails.** The feedback source step selects zeros on the transformed joint row
    `w = u₀ε e n_± g₂ v_𝒰 h` (foundations (168): "zero selection uses that whole character"),
    after both row transforms. The original row's bin says nothing about `χ_w`.
  - **Without the transforms there is no gain.** Deleting excess slots pointwise on the original
    bin rows costs `q = δ` per unit, which exactly cancels their threshold value `2pδ = δ` at
    `p = 1/2`. Amplifying the original rows (`u ↦ ua⁶`) costs 5 per unit of `α` and buys only
    `6qB₀/Λ₀ ≈ 0.9` of threshold.

## Open directions (ranked, revised 2026-10-24 after the second pass; see `barriers/README.md`)

1. **Reflected-energy column branch slightly past the diagonal.** One input would move the probe
   geometry (`dθ/dε = −0.0628`, so `ε = 1.6e-4` gives 1e-5), the count's MI and the HIGH gain at
   once. It needs an almost diagonal quadratic large sieve at dual length `K^{1+η}` for the
   reflected cubic-theta coefficients, which is Lindelöf-type input for cubic Gauss sums twisted
   by quadratic characters.
2. **Plain fourth moment by a reflection recursion instead of the amplified descent.**
   - The plain canonical coefficient after Poisson is `γ₁ = γ₂²G = λGγ̄₂`: a twisted conjugate
     cubic-theta coefficient with no Möbius factor. The inverse moment's is `ᾱγ₂ = μλ̄γ₂`.
   - It would need the Patterson main term subtracted inside the canonical recursion.
   - Payoff: slot cost 2 instead of `Λ ≈ 3` gives `R ≈ 0.5996`, about 7e-4 in θ, and the source
     chain would become unnecessary.
3. **Long Möbius moment beyond sixth-power amplification.** This needs zero-density-strength
   input. Bootstrapping with the count is circular at `δ ≈ 0.45–0.5`, and the hybrid `t`-aspect is
   worse than sixth powers.
4. Closed this session: joint witnesses (they reproduce Cauchy–Schwarz), the sparse-image large
   sieve (equivalent to the original problem), large-values methods (no loss to recover), the Gram
   bias (genuine), probe redesigns (forced active marks), and detector variants.
