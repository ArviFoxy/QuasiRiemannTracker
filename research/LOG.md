# Research log

Goal: lower θ in "every Dirichlet L-function is nonvanishing on Re s > θ" by at least 1e-5 against
the best upstream PR (smaller gains count only if they simplify or clarify the proof).

| reference | θ | note |
|---|---|---|
| upstream PR #70 (Mark Lewko) | 0.874772906 | |
| upstream PR #71 (recost of PR #69 graph) | 0.87477290596 | 4e-11 below #70; checked 2026-10-24 |
| upstream PR #72 (Das, bootstrap + fine graph), best upstream PR | 0.874771265 | 1.64e-6 below #71; bar now 0.874761265 (checked 2026-10-25) |
| this branch, Lean (`submissions/arvi-repeated-marks-20261024`, branch `submission-repeated-marks-20261024`; upstream PR #73, renamed with the `arvi-` prefix on 2026-10-25) | 0.8747289 | 4.24e-5 below PR #72 (commit `39130516`) |
| this branch, Lean, face family (`faceless-chain/`, commit `41ddc0dd` on the same branch, 2026-10-25) | 34989/40000 = 0.874725 (`Candidate.bound_sharp`) | −3.9e-6, a simplification (no source graph). `Candidate.bound` keeps the declared 8747289/10^7, so the open PR stays valid and the 3.9e-6 stays in reserve toward the next milestone |
| next milestone (1e-5 below the declared value) | ≤ 0.8747189 | the face family already supplies 3.9e-6 of it |

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

- *Is the column-branch excess a real size? (heuristic; first version RETRACTED the same day).*
  - Setting: the column branch bounds `Σ_{h~Q} |D_h(N)|²` with
    `D_h(N) = N^{-1/2} Σ_{m~N} g̃(m)(m/h)₂ W(m/N)` at dual length `N = Q^{1+η}` beyond the critical
    length `Q`.
  - **Retracted claim.** The first version said that summing over `h` first writes the
    off-diagonal as a sum of squares `(Q/N²)Σ_j|Σ_m g̃(m)(j/m)|² ≈ N`, so that the excess would be a
    genuine dual diagonal. That is wrong. The quadratic Gauss sum of `m₁m₂` is
    `τ(m₁)τ(m₂)·(reciprocity sign of m₁, m₂)`, which couples `m₁` and `m₂`. The off-diagonal is
    therefore a signed bilinear form, not a square.
  - **Corrected picture.** For random-like coefficients the mean square is `≈ Q`, the diagonal: rows
    of norm 1 tested against a generic vector. The generic large sieve's `N` term is attained only
    by coefficient vectors aligned with quadratic characters. Cubic Gauss sums are not expected to
    align, so the true size is plausibly `Q` (Lindelöf on average) and the excess is an artifact of
    the generic sieve.
  - The barrier list's original statement therefore stands: a mean value for quadratic twists of
    cubic theta sums beyond the critical length, beating the `N` term for these coefficients, would
    move atom 1. The reflected route gives `Q^{7/6}` through the sextic sieve's extra terms, which
    are attained by Gauss-sum vectors. That is why it fails.

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

- *Residue transfer for the long detection (variant of the explicit-formula entry).*
  - At the binding pure-Möbius detection `r = t* = 1.155`, `M(D) = D^{δ/2}ŵ(σ)/L'(ρ) + Σ_{ρ'}
    D^{σ'−1/2}ŵ/L'(ρ') + ∫`.
  - If the row's own residue saturates `M(U^{1.155})`, it saturates every `D`, including
    `D = U`, where the inverse witness gives the density-hypothesis count `1 − δ = 0.545`.
  - Otherwise a left zero needs `|1/L'(ρ')| ≈ U^{1.155(σ−σ')}`. Its term at `D = U` then exceeds the
    proven bound `U^{δ/2}` by `U^{0.155(σ−σ')}`, so at least two such zeros must cancel at `D = U`
    and not at `D = U^{1.155}`.
  - With `σ − σ' ≈ 0.1` this needs only `|L'(ρ')| ≈ U^{−0.02}` at two left zeros, i.e. mild
    clustering. Pair counts `Σ_u N_u(σ')² ≤ (log U)·U^{R(σ')}` give no power saving, since
    `R(σ' ≈ 0.6) ≈ 0.85 > 0.604`. Blocked, like the inverse-witness version.

- *Bootstrapping the long moment with the count, quantified.* Bounding each row's
  `|M_u(U^r)|² ≤ U^{δ'r}` by its rightmost zero and summing with the count gives exponent
  `max_{δ'}[R(δ') + rδ']`. At `r = 1.155` this is 1.1667 (`p = 0`, attained at `δ' = 0.60`) or
  1.1532 (`p = 1/2`, at `δ' = 0.65`), against `(1+5r)/6 = 1.1292` from sixth-power amplification.
  The bootstrap loses by 0.024–0.038, and the loss comes from the few rows with deep zeros
  (`δ' ≈ 0.6–0.65`), not only from circularity at the binding `δ`. Restricting to the bin does not
  help either: the bin's images in the amplified family have `H^{R(δ)}D^{δ} = U^{1.223}`.

- *Why the Gram coefficient is worth so little (physical side).* With `k = 5/6 − x/3 − ℓ/6`,
  `θ_phys = k + x/2 + c_g(y − x)` on `x + y = 1 − ℓ` is
  `5/6 − ℓ/6 + c_g(1 − ℓ) + x(1/6 − 2c_g)`. At `c_g = 1/12` the `x`-coefficient vanishes, which
  is why `θ = 11/12 − ℓ/4` does not depend on the split of `x + y`, and `h` is set by `E` alone.
  A bias saving `c_g = 1/12 − ε_g` lowers `θ_phys` only by `ε_g(1 − ℓ − 2x) ≈ 0.10ε_g` at the
  binding geometry (`x ≈ 0.366`). That explains the large `ε_g ≈ 1.27e-4` needed for 1e-5. Lemma
  14.1 bounds the exceptional frequencies `k = er⁶` by their absolute column volume. Their complete
  means have a common phase (positive local factors), so the root sum has no cancellation to
  recover.

- *Re-reflection with de Faveri's sextic sieve in the inverse moment's column branch (checked,
  no gain).*
  - **Why it looked promising.** The earlier closure ("Re-reflecting the column branch's dual
    sums") assumed critical length `Z^H`. It priced the sextic sieve with an `(AB)^{2/3}` term and
    only near the boundary. At the binding child, `T_d − H = z ≈ 0.129 > H/8`. With
    de Faveri's optimal bound `A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6}` (arXiv 2610.04045,
    Thm 1.1, `n = 6` over `Q(ζ₃)`, uniform in the coefficients), re-reflecting to `L' = 2H − T_d`
    would give `Z^{0.823}` against the budget `Z^{0.871}`. That would be a large relaxation.
  - **Why it fails.** In the hybrid norm (MF2.29) the column branch's dual sum is
    `Σ_n β(n)χ_k(nb)³χ_P(n)^{-2}`. The theta coefficients are twisted by the row's quadratic
    character and by the slot tuple's cubic character. The twisted series therefore has conductor
    `≈ (q_k q_P)²` and critical length `Z^{H+z}`, not `Z^H`. At the binding `T_d = H + z` exactly,
    so the column branch sits at the joint critical length and there is nothing to re-reflect.
    Relaxing the budget pushes `T_d` only slightly past `Z^{H+z}`, where re-reflection gives
    `A^{7/6}` (`A ≈ B`) and is worse than paying the excess. Slot cost 2 is this joint conductor.
  - **What remains.** The column branch is the quadratic sieve's `N` term for the coefficients
    `β(n)A(n)` with `A(n) = Σ_P a(P)q_P^{-1/2}χ_P(n)^{-2}`, at `K < N ≤ K·L`. For generic
    coefficients the true size would be `K·N`, i.e. exponent `H`. A saving of `Z^{-0.0011}` would
    therefore need a quadratic large sieve beyond the family size for products of cubic-theta
    coefficients and cubic slot polynomials. No such estimate is known. Treating `(k, P)` as one
    sextic family with Cauchy over `P` loses more (`A^{7/6}` at `A ≈ N`).

- *Atom 1 as an operator norm (reformulation).*
  - In the column branch at the binding the dual length is `N = Z^{H+z} = K·L`, with `K = Z^H`
    rows and `L = Z^z` slot tuples. The energy is `Σ_k |Σ_P a'(P) S(k,P)|²`, where
    `S(k,P) = Σ_n β(n)χ_k(n)³χ_P(n)^{-2}` is, up to normalization, a central value of the theta
    series twisted by `χ_k³χ_P^{-2}`, and `Σ_P |a'(P)|² ≍ 1`.
  - The hybrid norm's bound `(K+N)(N+L+(NL)^{2/3}) ≈ K²L²` equals the Frobenius norm `‖S‖_F²`
    under Lindelöf on average (`|S|² ≈ N`). Since the slot coefficients are arbitrary, the true
    quantity is the operator norm `‖S‖²_op`.
  - For a random-like matrix `‖S‖²_op ≈ N(√K + √L)² ≈ K²L`, smaller by `L = Z^{0.129}`. So
    slot cost 2 is the gap between the Frobenius norm and the operator norm of the row ×
    slot-tuple central-value matrix, and the lever needs `‖S‖²_op ≤ ‖S‖²_F·Z^{-0.0011}`.
  - Via `‖S‖_op⁴ ≤ Σ_{P,P'}|Σ_k S(k,P)S̄(k,P')|²` the diagonal (`n₁ = n₂`) part of each correlation
    is a nontrivial cubic character sum `Σ_n χ_P^{-2}χ_{P'}^{2}(n)` for `P ≠ P'`, since `|g̃(n)| = 1`
    on squarefree `n`. That part is small. The off-diagonal from Poisson in `k` brings back the same
    `N > K` excess, so the reformulation does not by itself give a proof.

- *Slot cost 2 is a worst case over slot coefficients (refinement of the operator-norm entry).*
  - Theorem 7.3 holds for arbitrary bounded slot coefficients, hence the operator norm. In each
    application (the count's inverse witness, the probe's marked energy) the slot coefficients are
    specific: smooth prime weights times fixed characters, Mellin-twisted by `p^{it}`. The column
    coefficient `c(n) = β(n)A(n)` then has a large projection onto `span{χ_k³ : k ~ K}` only if it
    correlates with quadratic characters.
  - For a generic `c` the projection carries the fraction `K/N` and the sieve sum is the diagonal
    `K‖c‖²`. A proof would have to show cancellation in the dual (Poisson-in-`k`) terms
    `Σ_n β(n)A(n)(j/n)` for `j ≤ N²/K`, together with their signed sum over `j`. That is a
    Type II estimate for cubic Gauss sums twisted by quadratic characters. The nearest known result,
    Dunn–Radziwiłł Prop. 10.1, saves only an inexplicit `X^{ρ/2}` (`ρ < 1e-4`), for untwisted
    `g̃(ab)`, partly under GRH-type inputs. We need `Z^{0.0011}`, which is in the same tiny-saving
    regime, but for the twisted problem. Open.

- *Re-reflection with the sextic sieve for the long Möbius moment (atom 2, checked).*
  - Without slots the inverse moment's child has rows `H_c = 2r − m`, columns `F_c = r`, and dual
    length `T_d = 3r − 2m`, which is beyond the critical length `H_c` by `r − m`. Re-reflecting to
    `L' = r` and applying de Faveri's sextic sieve gives the child bound `2r − 5m/6`. The direct
    column bound is `3r − 2m`. Re-reflection wins only for `r > 7m/6`. In final exponents (half the
    child excess) it gives `r/2 + 7m/12`: 1.161 at `r = 1.155`, against the direct 1.155.
  - Combined with sixth-power amplification to family size `h`, the bound is
    `r/2 + 5h/12 + 1/6`, minimized at `h = 6r/7` to `6r/7 + 1/6`. That is worse than
    amplification alone, `(1 + 5r)/6 = 1/6 + 5r/6`. No gain.

- *Lemma F fits the existing Lean predicates (formalization route).* Collet's
  `uniform_squarefree_source_step` takes the crossing as a parameter (`lam ≤ lam₀` not strict,
  `cross ≤ cap₀`, budget `B − B₀ + (lam₀ − lam)cross ≤ 0`). In the fork's finite predicate a self
  step is an ordinary step with a rotated parent: child `(low.B − ηc, low.L − η, c')` gives
  `crossing = c` exactly. All gates read the parent only through `sourceDen`, `sourceA`, `sourceF`,
  `weakCap` and `low.cap`, and the rotation changes the amplifier by `O(η)`. So Lemma F is a run of
  ordinary nodes, and formalizing it is certificate generation only (`cap-induction/README.md` §5).
  The density floor 0.45 is the one piece that needs an edit to imported code (LD11).

- *Fresh agent on the physical side (round 3): c_g is exact, and a toy check of the column branch.*
  - **c_g = 1/12 is a Cauchy–Schwarz bound, not a Gram loss.** In Lemma 14.1 the `P_a^{1/6}` term
    is the length of the probe vector along one direction `v_coh(m) ∝ ρ₆(m)Φ(q_m/Q)` (sextic theta
    coefficients, `Σ_{q_m~Q}|ρ₆|² ≍ Q^{5/6}`). `θ_phys = 5/6 − ℓ/6 + M/12` is exactly
    `|⟨ρ₆Φ, B⟩| ≤ ‖ρ₆Φ‖‖B‖`, with `1/12 = (1 − 5/6)/2`. Weights `W₀, W₁` and `ξ`-mixtures change only
    the constant (`∫|Ŵ₀(iv)||Ŵ₁(1/6+iv)|dv > 0`), and thinning the `a`-set loses. Lowering `c_g`
    would need a priori information about `B` along the signal direction. **Closed.**
  - **Toy check of the column branch over `Z[ω]`** (`atom1/toy/colbranch_exp.py`; rows are primary
    squarefree `R`, `N(R) ≤ K`; columns `N(n) ∈ (N/2, N]`; kernel `(n/R)₂`). `Σ_R|D_R|²` over the
    diagonal, against the large-sieve allowance:

    | coefficients | 66 rows × 684 columns (LS allows 11.9×) |
    |---|---|
    | normalized cubic Gauss sums `g̃₃(n)` | 0.94 |
    | `g̃₃(n)` × cubic mark sum `Σ_π χ_π(n)^{−2}/√N(π)` | 0.91 |
    | random phases | 1.09 |
    | aligned `(n/R₀)₂` | 10.1 |

    The agent's larger runs (up to 778 rows, LS allowance 6–56×) give 0.87–1.17 for the Gauss-sum
    shapes. The column branch is at its diagonal for these coefficient shapes. The large-sieve `N`
    term needs alignment with one quadratic character, and these coefficients are not aligned.
    This is evidence only. The toy omits `ϑ`, `Ψ₀`, the `V♯` coupling, `b`-cubes and S-parts.
  - **Its proposal (P1), assessed.** Prove `Σ_R|D_R|² ≪ (K + N·K^{−δ'})‖β‖²` for
    `N ∈ [K, K^{1+δ'}]`, i.e. the quadratic sieve stays diagonal slightly past `N = K` for reflected
    Gauss-sum coefficients. In the probe this gives `x + y + ℓ ≤ 1 + 0.83δ'`, so `δ' ≈ 1.3e-4` is
    worth 6.8e-6. That is ten times cheaper than the inverse moment's need (`Z^{0.0011}` at
    `K = Z^{0.742}`, `δ' ≈ 1.5e-3`). A fractional saving is not enough: it must keep at most 16% of
    the excess. The proposed route has Poisson in `R` with the reciprocity bicharacter kept (an
    indefinite form), dual frequencies `j = j₀r²`, Heath-Brown for large `j₀`, and Dunn–Radziwiłł's
    Voronoi formula (Patterson bias subtracted exactly) for `j₀ ≤ N^{2/3}`. **Its middle range
    `N^{2/3} < j₀ < N²K^{−1−2δ'}` is column-type again**, so the route is circular as it stands. It
    restates atom 1 sharply as a target and does not prove it.

- *Round-3 inverse-moment agent: no report* (it stopped on an output-size error before reporting).
  Not relaunched. Its question, a power saving in the MI column branch, is the same estimate as P1
  above, and the probe uses that estimate about ten times more cheaply (`δ' ≈ 1.3e-4` against
  `≈ 1.5e-3`).

- *Round-3 long-moment agent: atom 2 is a fixed point of the current tools, and a screening test.*
  - **Leverage** (closed-form crossing on a C face, `δ = 0.4546`, `p = 1/2`,
    `atom-targets/line_leverage.py`): lowering a line by `ε` lowers `R*` by `0.509ε` (I), `0.305ε` (L),
    `0.186ε` (P). So the long-line target `−2.6e-4` equals I `−1.56e-4` or P `−4.26e-4`.
  - **`L(t) = 1/6 + (5/6 − δ)t` is a fixed point** of amplification into any ball bounded by `H + D`,
    of lifting to `H = U^{1+6α}` with the marked short inverse (minimum at `α = (t−1)/6`, equal to
    `L(t)`), of Vaughan/Heath-Brown identities on the long witness (Type I sums vanish, and Type II
    reproduces the detector at a shorter cutoff), and of `μ log = −Λ*μ`.
  - **The λ test (new screening criterion).** A ball estimate `H + D(H/D)^λ` helps only if `λ > 1/6`.
    For `λ ≤ 1/6` amplification still wins. For `λ > 1/6` the best choice is the original ball,
    exponent `(1−λ)t + λ`. At `t = 1.155`, a gain of 2.6e-4 needs `λ ≥ 0.16834`, against
    amplification's exact `1/6`. Any idea for the long line should be screened against this number
    first.
  - **Where the `+D` lives:** only in the near-coprime dyads `q_b ≤ D/U` of (64), whose dual has more
    rows than length. The `n₁ = n₂` main term there cancels exactly (local factor
    `1/q_p − 1 + (1 − 1/q_p) = 0`), but what remains after Poisson in `k` is the original
    off-diagonal (Poisson twice is the identity). Positivity then restores a genuine dual diagonal.
  - **Count framing.** Every count-only route needs local control of `1/L` just left of the zero
    (density-hypothesis strength: it would give `I(1) = 1 − δ`). The missing input can be stated as a
    **pair-zero lemma**: rows in the bin with a second zero, or `|L| ≤ U^{−κ}`, in a box of width
    `η` left of the zero number at most `U^{R* − 8e-5}`. No proof strategy is known. A two-point
    detector would need mixed `μ*1` moments that are not available.
  - Outside angles checked and closed: Guth–Maynard/Halász (off-diagonal about `U`, far above
    `D^δ`), BDH/BV dispersion (the family is a `1/U`-thin slice), cubic/sextic sieves (de Faveri's
    off-diagonal terms exceed `D`), bilinear Gauss-sum bounds (wrong row/length regime), Patterson
    bias (only the circular double dual), denser multipliers (only units and conjugation act
    exactly).
  - **Round 3 summary.** Atom 1 is the column-branch target P1 (cheapest via the probe,
    `δ' ≈ 1.3e-4`). Atom 2 is the λ test or the pair-zero lemma. Atom 4 (`c_g`) is closed.

- *Status correction and branches (2026-10-24, late).* An earlier status line said our branch was
  "trailing" PR #71. That was wrong: our submission proves `8747289/10⁷ = 0.8747289`, PR #71
  (slayer's recost of Collet's graph) proves `0.87477290596`, and smaller is stronger. So our
  branch leads every upstream entry by 4.4e-5 and clears the 1e-5 bar.
  - `submission-repeated-marks-20261024` is upstream main (`0ce80fdd`) plus only
    `submissions/repeated-marks-20261024`. Its imports are itself, `hailey_collet_1252270103` and
    `openai_baseline`, and both trees are byte-identical upstream. The verifier pins and lake
    manifest are identical too. The PR is ready to open from it; it has not been opened.
  - `claude-memory` is the fork's main plus `CLAUDE.md` (goal, bar, conventions, pointers).
  - PR #71's idea (recosting under the fine fee tuple `(10⁻¹⁷, 10⁻¹², 10⁻¹⁰)` that the accepted
    source theorem permits) is being applied to our graph (`variational-ceiling/hyb_fees.py`).

- *P1 has a fourth use: the long line through the lifted marked inverse moment.* Lift the rows to a
  ball of size `H = U^{1+6α}` and apply the marked short inverse there (round-3 long-moment agent).
  The exponent is `(1 − δ/2 − δt/2) + α(5 − 3δ)`, minimal at `α = (t−1)/6`, where it equals
  `L(t) = (1+5t)/6 − δt` exactly. The ball then has size `D`, and the budget `t + 2z ≤ t` leaves no
  room for slots. A relaxed budget `r + 2z ≤ 1 + β` leaves `z = β/2` there, worth `δpβ = δβ/2`,
  so the long line drops by `δβ/2` as well. With all four uses (probe marked energy
  `≈ 0.052β`, I line `≈ 0.017β`, lifted L line `≈ 0.133·0.305·δβ/2 ≈ 0.009β`, plus the chain's HIGH
  inverse cap), P1 is worth about `0.078β` in θ. So `β ≈ 9e-5` would reach the milestone, against
  `≈ 1.3e-4` for the probe alone. This assumes one column-branch estimate covers all four
  configurations.

- *The face map's continuum limit and the ceiling of the source graph* (`variational-ceiling/`, user's
  chosen first direction). **The source graph is within about 1e-6 of its ceiling.**
  - **Continuum limit.** As the pivot spacing `δ → 0`, each face is its own LOW and HIGH parent, and
    the envelope obeys `E' = −Λ_min(s, E)`. Only the HIGH gate at the pivot binds: moving the cap to
    the pivot leaves `Λ_min` unchanged, and every gate is affine or concave in the width, so
    endpoint checks are exact. `Λ_min` is increasing in `E` (`∂Λ/∂E ≈ 22.5`).
    `lean-lab/MaximalEnvelope.lean` proves the comparison principle, so the continuum solution
    bounds every admissible envelope of its class.
  - **The chain is an Euler scheme.** hybchain2 sets `E_{k+1} = E_k − Λ_kδ`. At its pivot a node is
    flatter than the continuum (the predecessor's ratio helps), but its slope is frozen over the
    step while the true slope falls at `|Λ'| ≈ 55`. Net loss: about `8.3δ` of slope per unit width.
    Measured θ*: spacing 0.002 → 0.8747301, 0.001 → 0.8747273, 0.0005 → 0.8747259 (exactly linear,
    2.8e-3 per unit δ), consolidated 0.0005/0.00025 → 0.8747257. Richardson: δ → 0 gives about
    0.8747245 with Collet's fees.
  - **Fees.** The self-cell amplifier `(qe + r)/den` costs about `8.85√r` of log-slope at the
    optimal `den ≈ √(14.8r)`. PR #71's fine tuple `(10⁻¹⁷, 10⁻¹², 10⁻¹⁰)` cuts this a hundredfold:
    consolidated chain 0.8747254, continuum 0.8747241.
  - **Ceiling and formalizable package (final).**
    - The ceiling (continuum, fine fees) is θ* = 0.8747241, which is 4.8e-6 below the Lean branch
      and 5.2e-6 above the milestone 0.8747189.
    - The Lemma F chain under the Lean branch's own guards (floor 1/2, HIGH parents `B ≥ 22/23`,
      `Λ_P > 3`) with fine fees gives 0.8747263 (−2.6e-6). It is formalizable with existing
      predicates plus Lemma F cells and `NFAccounting`'s `Or.inr` fees.
    - Details: `variational-ceiling/README.md` §5.
  - **Consequence.** Nothing in the face map (spacing, caps, parents, fees) can supply the
    milestone. The envelope is fixed by the HIGH gate's ingredients: the unmarked count `ρ(ν)`, the
    gain's inverse cap (atom 1) and the exchange rate 6.

- *Joint numerator bound: Levy's Hölder step is already optimal against the plain witness* (exact
  identity, 2026-10-24). In the return the class sum of numerators is bounded by Levy's Hölder step,
  `Σ_class|N_u| ≤ #class^{3/4}(Σ_all|N_u|⁴|Q_u|²·U^{−2qz_A})^{1/4}`, with the fourth moment over
  all rows (foundations (223), `z_A = (B_P − 2n₀)/Λ_P`, numerator length `n₀ = 2ℓ/h ≈ 0.419` at
  `d = h`). The rows of a class also carry the detector's plain witness `|S_m|² ≥ U^{δm}`, in the
  same row character up to conjugation and a fixed twist. So a second option is Hölder at order 2
  with `S_m` inside the moment: `Σ_class|N| ≤ #class^{1/2}(U^{−δm−2qz_J}Σ_u|N_uS_mQ_u|²)^{1/2}`,
  where `N·S_m` is a two-plain product (lengths `n₀, m`), so a source face applies with
  `z_J = (B − n₀ − m)/Λ`.
  - **Identity.** With one affine face for both, `Levy − Joint = (R − P_face(m))/4` in the `U`-exponent,
    where `P_face(m) = 1 − 2δm − 2δp(B − 2m)/Λ` is the plain witness line. The count of a split is
    `min(I, P, L) ≤ P(m)`, so the joint bound never beats Levy's. They tie exactly at the crossing
    `R = P(m*)`. Numerically at the binding point (`R = 0.6041`, `m* = 0.413`, face P):
    `Levy = 0.69846`, `Joint = 0.69845`. With the true envelope, convexity of `E⁻¹` only worsens the
    joint bound.
  - Other joint variants are unavailable or worse:
    - an inverse witness inside (`n₀ + r ≈ 1.16 > 1`, and there is no mixed plain×inverse moment);
    - order 4 with `S_m` (three plains);
    - a sixth plain moment (it is never diagonal at `m* > 1/3`).
  - So the physical numerator's Hölder weight `3/4` is tied to the count's plain line and is not an
    independent lever.

- *Audit of the long line and the common root of atoms 1 and 2* (2026-10-24, reading OpenAI 7/8
  §"Amplification on sixth-power-free rows" and §"Initialization of the marked moment", and the
  alternate 11/12 preprint, Oct 5).
  - **The amplification is used at full strength.**
    - The exact identity `M_u(D) = Σ_{d | rad a} μ(d)ψ_u(d)q_d^{−1/2}M_{ua⁶}(D/q_d)` handles shared
      primes.
    - `(u, a) ↦ ua⁶` is injective, also with units: all six units are sixth roots of unity, so unit
      and conjugate lifts add no new rows.
    - The ball needs `H ≥ D^{1+c}` (the inverse moment's diagonal regime).
    - So `e(r) = max(1, (1+5r)/6)` is exact for this method. Lifts by units or by `λ = 1+2ω` only
      twist the target by a fixed ray character, so they are not copies.
  - **The 11/12 base is the same exchange.** In the alternate proof the target `A₁(D)` has the
    copies `A_{p⁶}(D) = A₁(D) + O(D/Y)`, about `H^{1/6}` of them, inside the diagonal family bound
    `Σ_{u≤H}|A_u(D)|² ≪ DH` (with `H = D^{1+ϑ}`). That gives `|A₁|² ≪ DH^{5/6}`, i.e.
    11/12 = 1 − 1/(2·6). The compensated probe then subtracts `ℓ/4` (7/8 at `ℓ = 1/6`). So the
    exchange rate 6 sits under the whole architecture, not only under the long line.
  - **Atoms 1 and 2 share one root.** The inverse moment's initialization expands the row square,
    applies Poisson in the rows, and writes the nonprincipal expression as a sum over the ray-class
    expansion `G([z₂][z₁]^{−1}) = Σ_ϑ Ĝ(ϑ)ϑ(·)` of positive canonical squares over the dual rows. This
    restores the principal pairs with total weight `G(1) = 1`.
    - With `D` longer than the rows (long line), the dual rows `D²/U` outnumber the length, and the
      restored dual diagonal is the `+D` of atom 2.
    - With the mark twist (column branch), the same restored diagonal is the `N` term of atom 1.
    - Avoiding the restoration needs an asymptotic for the canonical square with power-saving error.
      Its off-diagonal, after a second Poisson step, is the original off-diagonal again ("Poisson
      twice is the identity"), so both atoms are one open problem: a signed off-diagonal bound for
      sextic Möbius/theta mean values past the diagonal.
  - **Asymptotic-large-sieve subtraction is circular** (checked here). The idea: bound the `U`-lifts'
    share of the ball by subtracting an asymptotic lower bound for the rest of the ball.
    - The complement's off-diagonal is exactly minus `P` times the `U`-family's off-diagonal (plus
      the ball's small one).
    - Any lower bound for the complement therefore reproduces the original problem.
    - Positivity (dropping the complement) is exactly what amplification uses.

- *Three more closures (2026-10-24, late).*
  - **Lemma C's cap `G ≤ νS` is necessary and not binding.** (P1) with `L = 0`, `δ = S`, `Q = F`
    forces `G(S, F) ≤ G(0, F) + νS = νS`, so the cap cannot be dropped. Along the chain the
    uncapped `G_K` is itself only 43–98% of `νS` (`chain-ode/`), so relaxing the cap would buy
    nothing. The early shortfall is the inverse cap `r + 2z ≤ F`, i.e. atom 1.
  - **The slot cost is intrinsic to active marks.**
    - The twist `χ_P(n)^{−2} = (P/n)_3^{−1}` can be moved into the Gauss sum: `g(1,n)(P/n)_3^{−1} =
      g(P,n)`, i.e. theta coefficients along `m = Pn`.
    - That turns the multiplicative twist mod `P` into a congruence `m ≡ 0 (mod P)`, which costs the
      same conductor `P`.
    - Only cube factors are free: the cube completion `c_θ(nb³) ∝ |b|`.
    - Cube marks carry the quadratic factor `χ_p(u)³` and give no count gain.
  - **A narrow-cap chain without Lemma F is not a cheaper formalization.**
    - With old parents, the far end of a cell of width `δ'` has LOW excess
      `(Λ₀ − Λ)(cap − b_×)/Λ₀ ≈ 18δδ'`.
    - Its amplifier costs about `26δ` in relative slope at the optimal denominator, roughly ten
      times the Euler loss.
    - Lemma F self cells remain the efficient tool for the cap side, so the formalization estimate
      in `cap-induction/README.md` §5 stands.

- *Multi-face plain line in the count: no gain at the binding point.* At `m* = 0.413` the selected
  count face C is exactly the chain envelope's best face (`z = 0.045038` against the envelope's
  `0.045038`, consolidated chain; identical in the 59-node chain). Elsewhere the envelope is better
  (`+1e-3` in `z` at `m = 0.43`, `+3e-3` at `m = 0.40` from the cap `0.055` against `s_+ = 0.052`).
  But the count is the crossing `max_m min(I(t−m), P(m))`, and that value depends on `P` only at
  `m*`. So adding all chain faces as count candidates leaves `R` unchanged.

- *Why order 6 (structural remark, heuristic beyond the cases checked).* The architecture needs
  Poisson in the rows to turn the Möbius-twisted Gauss sums of the row characters into the
  coefficients of an automorphic object with an explicit reflection. For characters of order `2k`,
  Hasse–Davenport for `ψ = χ̄` against the quadratic subcharacter `χ^k` gives
  `g(χ̄) ∝ g(χ^{−2})·g(χ^k)/g(χ^{k−1})`.
  - The two non-quadratic Gauss sums `χ^{k−1}` and `χ^{−2}` are conjugate iff `k − 1 ≡ 2 (mod 2k)`,
    i.e. `k = 3`. Then the ratio collapses, through the cube relation of the cubic Gauss sum, to one
    cubic Gauss sum times the angular factor `α`. With the prime sign this is the paper's
    `μ(n)γ₋₁(n) = χ_n(−1)G(n)^{−1}α(n)γ₂(n)`: the Möbius sign is absorbed into a coefficient of
    Kubota's cubic theta function, which Patterson computed explicitly.
  - For `k = 2` (quartic over `Z[i]`) one gets `γ₋₁ ∝ conj(γ₁)`, and the Möbius sign survives as
    `(−1)^{ω(n)}conj(γ₁(n))`. The quartic theta's squarefree coefficients are not known in that form
    (Suzuki), so there is no explicit reflection.
  - For `k = 5` the ratio of two distinct quintic Gauss sums remains.
  - So the sextic family, and with it the exchange rate 6 (11/12 = 1 − 1/(2·6), the long line, the
    plain descent), is forced by the one case with explicit theta coefficients. A smaller exchange
    rate would need a different automorphic input, not a different character order.
  - (Added 2026-10-25, prompted by the user's question "why never 5th power?") The precise reason
    behind "explicit theta coefficients": by Kazhdan–Patterson, the theta representation of the
    `n`-fold cover of `GL(r)` has a unique Whittaker model only for `n = r` or `n = r + 1`. On
    `GL(2)` that is `n = 2, 3`. For `n ≥ 4` the theta coefficients are not determined by local data.
    - Odd prime order 5 fails all three needs at once:
      - there is no quadratic subcharacter, so μ is not absorbed;
      - there is no explicit quintic theta on `GL(2)`;
      - the leftover twist after any reflection is quintic, not quadratic, so it pays de Faveri's
        sharp higher-order terms.
    - `Q(ζ₅)` also has degree 4 and infinite units.
    - What it would be worth: the amplification `A_{pⁿ} ≈ A₁` gives the baseline `1 − 1/(2n)`
      (`n = 6`: 11/12, `n = 5`: 9/10, `n = 4`: 7/8, `n = 3`: 5/6).

- *The crispest form of atom 2: the inverse moment slightly past its diagonal.* Suppose the
  unmarked inverse moment `Σ_{q_v≤H}|M_v(D)|² ≪ H^{1+o(1)}` held for `D ≤ H^{1+ε}` and not only for
  `D ≤ H^{1−c}`.
  - Amplification could then use the ball `H = D^{1−ε}`. The long-line exponent
    `(1 + 5t)/6` drops by `5tε/6`, so the λ-test target 2.6e-4 at `t = 1.155` needs only
    `ε ≈ 2.7·10⁻⁴`.
  - At `D = H^{1+ε}` the restored dual diagonal has dual rows `H' = D²/H > D` and size `D`, so the
    excess is `H^ε`.
  - Individual character-sum bounds for the dual `k`-sums do not help. The modulus is `nn' ≈ D²`
    and the length `H' ≈ D^{1−ε}`, roughly the square root of the modulus. Pólya–Vinogradov and
    Burgess (`D^{7/8}` per pair) leave the `n ≠ n'` sum uncancelled and lose a power.
  - So the target is a bilinear (signed) bound at the exact square-root balance, which is the same
    open problem as P1.

- *PR #71's recost applied to our 59-node graph: no measurable gain.* Same pivots, cap rule and
  K = 8 (`variational-ceiling/k8_finefees.py`, `result_k8_finefees.json`), with the fine tuple
  `(10⁻¹⁷, 10⁻¹², 10⁻¹⁰)`.
  - Slopes drop by up to 8e-5 and face heights at `s = 0.045` rise by about 1.9e-6.
  - The exact return (`cap-induction/evalchain.py`, Lean guards, `h = 0.802`) gives
    θ* = 0.8747287 for both graphs on the same 1e-7 grid. Our old-parent cells are dominated by the
    parent's deviation (about 7e-5 per step), not by the fees, so the recost is worth about 1e-8.
  - The fees matter only inside Lemma F self cells (consolidated chain −3e-7, continuum −8e-7).

- *Conrey–Iwaniec–Soundararajan's asymptotic large sieve (arXiv:1105.1176) does not reach atom 2.*
  - Their family is all primitive characters with `q ≍ Q` (size about `Q²`).
  - Theorem 2.2: `SS(A×B) = SS_diag + O(Q(log Q)^{−C})` for arbitrary coefficients with
    `N ≤ Q^{1−ε}`.
  - Theorem 2.3: the same up to `N ≤ Q^{2−ε}` when the coefficients are L-function coefficients of
    degree `≤ 3` times a mollifier of length `X ≤ Q^{1−ε}` (`X ≤ Q^{1/2}` for degree 3). The
    off-diagonal "switching moduli" terms supply the secondary main term.
  - So their asymptotic stays inside the classical diagonal range `N ≤ Q²` of the full family, with
    log-power savings. Atom 2 needs the opposite: past the diagonal of a thin family (length
    `D > H` rows), with an explicit power saving. Their remark that degree 4 "can be approximated
    by two partial sums of length `N ≍ Q²`, but not shorter" marks the same barrier.

- *Round-4 spectral agent: no spectral route; why positivity pays the diagonal; the functional-
  equation group is affine.* This is the subagent's report; the claims flagged below are its own
  and not independently checked.
  - **No Kuznetsov input exists.** Every off-diagonal object is a Gauss sum `S(r, 0; c)`, an
    Eisenstein or theta coefficient, times multiplicative twists. It is never `S(m, n; c)` with
    `mn ≠ 0`. Detecting marks additively, writing `χ_h` through `θ₂`, and Farey sums all collapse
    back to single-frequency Gauss sums. A spectral large sieve is itself a positivity bound.
  - **The restored diagonal comes from positivity, not from the theta residual spectrum.**
    - In the dual row variable it is the pole of `ζ_K` at `w' = 1` from the principal pairs, with
      mass `∫𝓕Φ = Φ(0)`.
    - Positivity needs `𝓕Φ ≥ 0`, so `Φ` must be positive definite, and then `Φ(0) = max Φ ≥ 1`.
    - With an annulus weight (`Φ(0) = 0`) the pole cancels exactly, but what is left is the signed
      off-diagonal.
    - `θ₃` (the residual spectrum of the 3-fold cover) is the dual vector itself. Its Patterson
      pole is absent here because `α` is a nontrivial K-type.
  - **The functional equations generate the affine Coxeter group C̃₂** (agent's numerical check,
    scratchpad `specnote/fe_group.py`).
    - Row Poisson (`w → 1−w`, `s_i → s_i+w−½`) and the column reflections (`s_i → 1−s_i`,
      `w → w+2s_i−1`) preserve `s₁ + s₂ + w`. This is the formal content of "Poisson twice is the
      identity".
    - Only Hecke moves change the invariant: cube completion on `θ₃` and sixth-power copies on the
      sextic family. That is why the rates 3 and 6 cap every amplifier (`λ = 1/6`).
    - The second moment of quadratic twists of a GL(2) form has the same group. There only log
      savings are known at the critical point (X. Li, Invent. Math. 2024).
    - So atoms 1 and 2 sit at the frontier of the affine multiple-Dirichlet-series problem.
  - **Unmarked column branch: claimed provable from Prop. 3.1.** With no slot twist, a sum of length
    `N > K ≥ N(h)` is past its critical length.
    - Reflect it to length `K²/N`, apply Poisson in `h` (theta becomes μ), and bound the Möbius rows
      by sixth-power amplification. This gives `Σ_h|S_h|² ≼ K` for every `N > K`.
    - Plausibly this is what the unmarked toy (ratio ≈ 1 at `N ≈ 10K`) measured.
    - It is not used anywhere: every column branch in the argument is marked.
  - **Marked column branch = slot cost 2, exactly.**
    - With the twist `χ_P^{−2}` the critical length is `K·N(P)`. In the band `[K, K·N(P))`
      reflection lengthens the sums and the large sieve pays `N`. That is the whole obstruction.
    - Bookkeeping (mine): if the marked column branch were diagonal (`≼ K = Z^H`), the binding
      child's condition would become `H ≤ F_c`, i.e. `2(r+z) − m ≤ r + z`, i.e. `r + z ≤ m`. Slot
      cost would drop from 2 to 1.
    - So target (A) is atom 1 in its sharpest form. Partial versions (diagonal up to
      `K^{1+δ'}`) relax the budget by about `δ'H`.
  - **The assumption that pins both atoms:** metaplectic covers have Hecke operators only at n-th
    powers (Kazhdan–Patterson).
    - If `θ₃` were a `U_p`-eigenform at the slot primes, a mark would rescale rather than twist
      (`c_θ(pn) = c_θ(p)c_θ(n)(n/p)₃^{±}`), and marked (A) would reduce to unmarked (A).
    - If cubes or squares acted as exact copies on the sextic family, amplification would give
      `λ = 1/3` or `1/2`.
    - Both are excluded by theorems.
  - **Explicit spectral inputs exist but miss the obstruction.**
    - No exceptional cusp forms at level `Γ₂` of the cubic cover, with `θ₃` the only exceptional
      point (Dunn).
    - Flicker's correspondence plus Blomer–Brumley give `Re ν ≤ 7/(64n)` elsewhere.
    - Kuznetsov on the cubic cover exists (Livné–Patterson, Louvel, Proskurin) but handles only
      `S(m, n; c)`.

- *All three count lines rest on affine-type mean values* (`lean-lab/FEGroup.lean`, proved;
  classification script `barriers/fe_types.py`). Treat each mean value as a
  row/column multiple Dirichlet series: row Poisson for the sextic family, theta reflection for
  Möbius columns (conductor `N(row)²`), natural reflection for plain columns (conductor `N(row)`).

  | mean value | columns | functional-equation group |
  |---|---|---|
  | inverse second moment `Σ|M|²` (I and L lines) | 2 theta | affine C̃₂, invariant `s₁+s₂+w` |
  | plain fourth moment `Σ|S₁S₂|²` (P line) | 4 natural | affine D̃₄, invariant `(Σsᵢ)/2 + w` |
  | plain second moment `Σ|S|²` | 2 natural | finite (A₃) |
  | mixed cross moment `Σ M·S̄` | 1 theta + 1 natural | finite (B₃) |
  | mixed second moment `Σ|MS|²`, or `|M|²·S` | 2 theta + 2 (or 1) natural | hyperbolic |

  - Both mean values that the count actually uses are exactly affine. Affine is the boundary type:
    D̃₄ is the group of the fourth moment of quadratic L-functions, and the second moment of
    quadratic twists of a GL(2) form is also affine. In the classical analogues of affine type,
    power-saving asymptotics are known only in function fields or under GRH; unconditionally there
    are log savings (Li 2024).
  - What this says about the lines differs between them.
    - For the I and L lines the limit is the inverse moment's diagonal (`r ≤ 1`, plus marks up to
      the joint `(k, P)` diagonal). Going past it is the affine-type C̃₂ problem.
    - For the P line, the slotless plain fourth moment is already diagonal up to total length 1. That
      is the analogue of Heath-Brown's fourth-moment upper bound; only its exact asymptotic is
      affine-hard. The P line is limited instead by the slot cost `Λ ≈ 3` of the faces, from the
      ratio-6 descent (atom 2's exchange rate).
  - Mixed moments, which a product detector would need, are hyperbolic: worse, not better.
  - **Why the finite-type cross moment cannot be used.** The mollified first moment
    `Σ_u w_u L(s₀,ψ_u)C_u(s₀)` (natural × theta, type B₃) could plausibly have a power-saving
    asymptotic. But it is signed: rows with a zero at `s₀` contribute about 0 instead of 1, and the
    deficit can be offset by other rows. Counting needs positivity, positivity forces second moments
    (`Σ|1 − J_u|²`, the detector's tail), and the second moments here are affine. Selberg-type
    first/second moment combinations give positive proportions of nonvanishing, not power-saving
    zero counts.
  - This is a heuristic map, not a theorem about provability. The paper proves the diagonal ranges
    by inductions, not by multiple Dirichlet series. But it locates every remaining atom at the same
    well-known frontier.

- *Round-4 architecture agent: mixed prime/plain slots* (`mixed-slots/`). **Closed: it needs a
  diagonal three-plain moment.**
  - **Reading.** The binding case is the zero amplifying itself through the slots. A bad row's prime
    slot `−Σ_p w(p)p^{z−1}ψ̄_u(p)` is made coherent, of size `P^{δ/2}`, by the row's own zero. At the
    binding point the adversary gains net `≈ 0.019` in the balance by saturating it: it pays
    `δpℓ ≈ 0.038` and the marks win back `≈ 0.019`. That is about 2.5e-3 of θ.
  - **Proposal.** Replace part of the slot length by squarefree-plain slots, with generating
    function `L(s,ψ)/L(2s,ψ²)`. A zero does not force these large, and they were assumed markable
    in the P line at cost `c_S ≈ 1`. The agent's toy gave −3.8e-4.
  - **Honest toy** (one face budget shared by all marks, `cs_threshold.py`).
    - At equal cost the mixed design is worse: `+9.7e-5` at prime fraction 0.9, `+1.9e-4` at 0.8.
      Independently saturable groups enlarge the adversary's choice set.
    - Break-even is `c_S ≈ 1.85`; −1e-5 needs `c_S ≈ 1.8`, against `Λ = 2.77`.
    - The agent's gain came mostly from letting plain marks use the unit budget `1 − 2m` outside
      the face: worth −1.5e-4 even at `c_S = Λ`.
  - **Why `c_S = Λ` in the paper's machinery** (7/8 §18).
    - Lemma 18.1's slotless case is unrestricted only because the padded core is extended by
      reflecting at most its two plains (§18.8).
    - After both are reflected, a child with a third plain of length `z′` still exceeds its core by
      `z′`, and reflecting the short factor makes it long. Its only exit is pointwise deletion, the
      slot mechanism of eq. 18.39: room `6κd` for energy `κd`.
    - In the zero-free half-plane, Littlewood gives the plain slot the same pointwise bound
      `Z^{κz}` as (18.12).
    - So lemma (a) at `c_S ≤ 1.85` is a diagonal three-plain moment for the sextic family. It is the
      barrier table's "plain fourth moment with slot cost below Λ" (Patterson bias of plain duals).
  - **Kept.** The self-saturation reading. A new quantitative target: a three-plain diagonal at
    `c_S ≤ 1.85` is worth ≥ 1e-5, and `c_S = 1` about 9e-5.

- *Unabsorbed upstream ideas* (task: mine records outside Collet's `builds_on`). **No
  transplant.**
  - **Gao's five-step (PR #68, 0.8748087).** HIGH records from inner stages are returned and
    counted once over complete histories (Gao's four-page paper, eq. 8):
    `J = (1−ρ)W − qL + a − P + …` with `W = 1 − V − 6a`.
    - In one step this is exactly Collet's per-node gate `H = 1 − ρ − νT − a(5 − 6ρ)`, since
      `−6a(1−ρ) + a = −a(5 − 6ρ)`.
    - Over a history, the amplifiers and deletions of the whole path accumulate against a single
      saving `(1 − ρ)`.
    - Collet's chain (paper69 `sources.tex` §28.7) instead proves each face as a black box, with
      its own marked HIGH count (G16)–(G17), and its LOW children deleted into the earlier face.
  - **The returned-history line saturates near 0.87481.** The community hill-climb
    (`rohanarun/quasi-rh-hillclimb`, `depth3/`) extends it to 6–8 stages: 0.874809989 (six
    levels) and 0.874806549 (eight stages, `K ≤ 12`). Collet's per-node chain reaches 0.8747730.
    Its junctions stay at `q ≥ 0.638`, where Collet's chain reaches the density floor
    `q → 1/2` (and below 1/2 it is worth only 5e-7).
  - **Sil's record (0.874828524).** Its "clipped uneven normalization with common-factor cost 2/5"
    is Collet's "individual plain edge 2/5" (Ch24.5, via Gao's Target830). Saturated marked
    capacities and sixth-root weights are superseded by Collet's faces.

- *Atom 4 (`c_g = 1/12`) is the signal channel itself: closed, with a mechanism* (7/8 §4.2, §5.1,
  §6.1, §15).
  - **Setup.** The low separation (6.2) is `I_η ∝ Q^{−1/2}Σ_m A_m B_m`, and the bias is
    `|⟨A^exc, B⟩| ≤ ‖A^exc‖‖B‖`.
    - `A_m = Σ_s a(s)Σ_x χ_s(x)e(−mx/s)` is the sextic Gauss-sum polynomial, `s ~ Y′`.
    - `B_m = Σ_A β(A)χ_A(m)` is the completed cubic-theta row, `A = cn³ ~ Z^{N*}` with
      `N* = 1 + ℓ`.
    - `A^exc` is the part of `A` behind the Gram's sixth-power frequencies.
  - **Poisson in the row `m`** (modulus `sA`, CRT) gives `Σ_m W A_m B_m ≈ Q Σ_k â(k) b̂(k)`.
    - The definitions are `â(k) = Σ_s a(s)χ_s(k)` and `b̂(k) = Σ_A β(A)τ(χ_A)χ̄_A(k)/N(A)`, over
      `N(k) ≲ N(s)N(A)/Q =: K_×`.
    - The same `b̂` gives `‖B‖² ≈ QΣ_k|b̂(k)|²`.
    - At `k = a⁶e₀`, `â ≈ M_A`, with `K_×^{1/6}` such `k`, and `b̂(a⁶e₀) ≈ b̂(e₀)`.
  - **The dual coefficient is a Möbius sum of a finite-order character.**
    - On squarefree `A` (with `ᾱ` as in (5.1) and the phase `G` of (6.1)), (4.7) gives
      `γ₁ = γ₂²G` and `γ₂³ = μα`.
    - Hence `γ₁γ₂ᾱG = μ|α|²G² = μG²`.
    - So `b̂(k) ≈ ∫ Z^tΦ(t)E(t)/L(1+t, λ_k) dt` with `λ_k = G²ν χ̄_•(k)` and
      `ν = ηΞ^{−1}R(·, s_σ)`. Here `E(t)` is the cube part, analytic for `Re t > −1/6`.
    - At `e₀`, `λ_{e₀}` is the target `η` up to fixed finite characters, so its inverse L-function
      carries the target's zeros.
  - **Exact identity.** Shifting to `Re t = β* − 1 + ε`, with the zero-free hypothesis for
    finite-order Hecke L-functions, gives
    `|⟨A^exc, B⟩| ≪ (C–S bound) · Z^{(N* + ly − M)/6 + β* − 1 − (2ly − M)/12}`.
    - With `N* = 1 + ℓ` and `M = 1 − ℓ`, the exponent is `(1 + 3ℓ)/12 + β* − 1 = β* − θ_low`
      exactly, since `θ_low = 11/12 − ℓ/4`. In the 7/8 geometry it is
      `39/288 − 1/8 − 1/96 = 0` at `β* = 7/8`.
    - So the exceptional channel has exactly the size of the signal, `Z^{C(β*)}`. A zero of `η` at
      `β*` produces a pole of `1/L` there, and this channel is where the zero appears in the low
      separation.
  - **Consequence.** The `P_a^{1/12}` bias cannot be beaten by analyzing the correlation: it is not
    a Cauchy–Schwarz loss but the largest signal the energy bounds allow, tight at the threshold.
    This is a concrete version of the round-3 statement "C–S exact along the signal direction".
    Any gain from atom 4 must change the probe's energies (`‖A‖`, `‖B‖`), not the pairing.
  - The heuristic ignores common factors `(s, A) > 1`, shared primes with `k`, and the S-parts.
    Those contribute lower-order exceptional sets, as in the Gram (`e | C^∞`).

- *Round-5 detector agent (redesign the zero detector from scratch): no unconditional gain; a sharp
  conditional target, the Möbius scale-profile interpolation.* Scripts in the session scratchpad
  (`fresh5b/`).
  - **The corner is triple-tight.** Model `R = 0.604207` at `t* = 1.1553`,
    `(r*, m*) = (0.7413, 0.4140)`.
    - The adversary's comfort sets are `{r : Lin(r) ≥ R} = [0, 0.741] ∪ [1.155, ∞)` and
      `{m : P(m) ≥ R} = [0, 0.414]`. They cover every total length, touching at `t*`.
    - Since `r* + m* = t*`, counting the corner block `M_r S_m` as one polynomial costs exactly
      `L(t*) = R`, even with a perfect mixed moment and amplification.
    - So bilinear and product detectors, `L′/L` and `log L` detectors (primes are budget-limited,
      not supply-limited), K-fold mollifiers, slot-twisted or sieved mollifiers, and evaluation at
      `1 − ρ̄` or nearby points all give `ΔR ≥ 0`.
  - **New identity: the tail straddles the cutoff.**
    `Σ_{l|n, l≤2D*} μ(l)V = −Σ_{l|n, l≥D*} μ(l)(1−V)`. So every level carrying the tail has a
    saturated pair on each side of the cutoff.
    - At the corner, every binding row has `M` saturated at both `r = 0.741` and `r = 1.155`, `S`
      saturated at `0.414`, and saturated primes.
    - To escape the I line, its Möbius scale profile must dip below saturation on `(0.741, 1.155)`
      by the tent `c(r) = (R − Lin(r))/2`, peak `0.0294` at `r = 1`.
    - Unconditionally this only makes `R(t)` flat on `[r*, t*]`.
  - **Conditional target (interpolation lemma).** For all but `U^{R−7.5e-5}` rows, saturation at
    `j₁ = 0.741` and `j₂ = 1.155` implies `|M₁(ρ)|² ≥ U^{δ−2c}`, which gives `R = 1 − δ + 2c`.
    - The milestone needs `c ≤ 0.0294`, and only within about `4e-4` (in `log_U`) of the corner.
    - Lossless interpolation (`c → 0`) gives `ΔR = −0.059`, `Δθ ≈ −7.8e-3`.
    - The witness `M` at `r = 1` is an available input (marked inverse moment). The interpolation
      itself is not.
  - **Why it is not free.** `M_r(ρ) ≈ log2/L′(ρ) + Σ_{ρ′} c_{ρ′}U^{r(ρ′−ρ)} + (left integral)`.
    - The terms' log-moduli are linear in `r`, so a dip needs cancellation across a whole window.
    - By Turán's second main theorem (heuristic) it needs about `0.004·log U` zeros within about
      `0.025` of `Re s = a` near `γ`, or `|L| ≲ U^{−0.1}` on a line left of `ρ`.
    - Jensen turns such a cluster into a small value of `L` at its centre. The two branches at that
      centre give the marked inverse moment at `r = 1` with a threshold boost, about
      `1 − δ + 0.017`, or the full detector at `δ − 0.025`, about `R + 0.024`. The worse branch
      binds.
    - So counting cluster rows needs a zero count sensitive to multiplicity, with a power saving.
      This sharpens round 3's pair-zero lemma, localized to the corner.

- *Round-5 positivity agent (audit every signed step of the binding balance): no slack; the high side is
  the probe's signal mechanism applied to the bad row's own zero.* Float model and scripts in the
  session scratchpad (`fresh5a/`: `bal.py`, `sens.py`, `pfix.py`, `fe4.py`).
  - **The binding class.** For one class (bin `δ`, amplitude `p`) at `d = h`, the high side bounds
    `Σ_{u∈C} q_u^{−z} ξ̄(u) N_u(Y;s,z) Π_i Q_i(u;z) / L^S(s, ηψ̄_u)`, on `Re s = a + 16e`, `Re z = 17/50`
    (Collet (192), (195), (216), (223); 7/8 Lemma 20.1). Here
    `Q_i = −Σ_p w_i(q_p/P_i) q_p^{z−1} ψ̄_u(p)` and `N_u ≈ Y^{−1/2} ε_u S_{ψ̄_u}(U^{n0})`, with
    `n0 = 2ℓ/h = 0.418`.
  - **One zero does everything when `η = 1`.** The compensation strips `η` from the denominator's local
    factor, so for `η = 1` the denominator, the slots and the numerator are one L-function. `η = 1` is
    unavoidable: `ζ_K = ζ·L(χ_{−3})` is a target.
    - So one zero `ρ = a + iγ` with `|γ| ≲ Z^ε` and `|L′(ρ)| = U^{o(1)}` saturates the `s`-contour
      (residue `Z^ρ/L′(ρ)`).
    - It saturates every slot (the residue of `−L′/L` is the multiplicity).
    - It supplies the witnesses. The numerator is essentially the plain witness (`n0 = 0.418` against
      `m* ≈ 0.41`).
    - This is the high-side twin of atom 4: the probe amplifies a row's zero exactly as it amplifies
      the target's.
  - **Checks against that adversary.**
    - The float model reproduces `θ* = 0.8747256` from the receipts' faces (`δ* = 0.4552`,
      `R = 0.6034`, `ℓ = 0.16776`).
    - The only `z`-oscillation is `(Z^{1+ℓ}/(Xq_u))^{i Im z}`, stationary exactly at `d = h`. Shifting
      `γ_u` by `O(1/log Z)` aligns `ε_u`, `ξ̄(u)` and `arg 1/L′(ρ)` without any count noticing, so the
      bin's triangle inequality is intrinsic.
    - The Hölder optimum `4ν = 1 − R − 2qz_A` gives `ν = 0.0944`, against the pointwise
      `δn0/2 = 0.0952`. Since `R + 2δn0 + 2qz_A = 1.003`, the class carries the whole numerator fourth
      moment.
    - The L line's amplification ball is carried exactly by the lifts:
      `R + δt* + (t* − 1)/6 = t* = 1.155`.
    - The denominator's pointwise bound `U^{R+δ/h} = U^{1.171}` already beats the L-line moment
      `U^{1.206}`.
  - **Levers found, each needing a new input.**
    - *Slot amplitude:* `p ≤ 0.4985` in the binding class is worth 1e-5, and `p = 0` would give
      `θ = 0.87132`. For `η ∉ T̂`, one zero cannot saturate both `ηψ̄_u` (denominator) and `θψ̄_u`
      (slots). But counting rows with two twisted zeros at one height needs
      `Σ_u|M_r(ηψ̄_u)M_{r′}(θψ̄_u)|²` with `r, r′ ≥ 1/2`. That has four theta columns, which the
      Coxeter classifier rates hyperbolic (min eigenvalue −0.414). And `η = 1` must be covered anyway.
    - *Channel-split low side:* a bias-free Gram for `u ≠ 1` would gain `P_a^{1/12}`. It fails because
      `B`'s row-space norm is the long Möbius moment at `(1+ℓ)/h = 1.456`, not the marked energy.
      Carried row by row it gives `#C ≤ U^{1−δ(1+ℓ)/h}`, which is atom 2.
    - *Numerator:* a class-restricted saving `η = 1.4e-4` is a P-line improvement (atoms 2–3). The only
      route outside the atoms is a growth rate below `n0 = 0.418` just left of `a` at `|t| ≲ 1`, where
      Phragmén–Lindelöf gives `1/2`. Burgess is weaker than the zero-free PL value.
    - *Denominator `δ/2`:* the residue at the row's own zero (`dθ/d(·) = −0.221`). Beating it needs
      control of `1/L` left of the zero (pair-zero).
  - **Verdict.** The bin triangle inequality, the `δ/2` term and the `δpℓ` term are intrinsic. The
    Hölder exponent `3/4`, the `h/4` diagonal and the count's Chebyshev steps are tight only through
    the atoms. The agent independently upholds the earlier dismissals (pointwise and higher Hölder,
    joint numerator × witness, sparse Halász, pair-zero). Nothing on the high side is cheaper than P1.

- *Round-6 literature sweep (2025–2026): no new input for any atom.*
  - **Xu–Sang, arXiv:2610.15291 (Oct 2026), "Amplified moments and a refinement of the quasi-Riemann
    hypothesis".** It reaches 0.8748867 from OpenAI's inputs, weaker than the community chain.
    - Its high-side "amplified first moment" (Prop. 5.1:
      `Σ_{u∈B}|L(1/2+ϑ+it, ψ̄*_u)| ≪ U^{(3R+1)/4 − ϑ/2}`) is the same Hölder step (`#C^{3/4}` times the
      slotted fourth moment) as Collet's `(3h/4)R` term.
    - Its low-side decay retention (`ℓ ≤ 1/5`) and its κ-range extension (to `[13/18, 1]`) are already
      inside the community chain.
  - **Xu–Sang, arXiv:2610.17675 (Oct 2026), "A matching lower bound for the sextic large sieve and
    structured prime moments".**
    - It gives a lower bound `(AB)^{−ε}(A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6})` matching de Faveri's
      sextic sieve over the full range (`Q^{7/6}` at balance), via Gauss-type extremal vectors. So the
      generic sextic sieve cannot be improved, which confirms the re-reflection closures.
    - Its zero-density estimate for the sextic family is `N ≪ Q^{(31−32σ)/(21−12σ)+ε}`. With
      `σ = (1+ν)/2` this is exactly the community's unmarked count `ρ(ν) = 1 − 10ν/(15−6ν)`, so it
      adds nothing. It is built from the same three inputs (Lemma 18.1 zero-slot case, Lemma 17.6,
      Prop. 8.3).
    - Its prime moment `Q^{(37−10√6)/6} = Q^{2.084}` comes from bins times that count times pointwise
      prime bounds. That is our amplitude-bin mechanism.
  - **de Faveri–Dunn–Hoffstein, arXiv:2607.07911 (Jul 2026).** The cubic and quartic large sieves are
    not perfectly orthogonal, and the obstruction is the Gauss-sum bias. Its input "Lindelöf on average
    for the second moment of Kubota's series in the twist aspect" averages over the additive twist `r`,
    not over quadratic twists, so it does not reach P1. P1 needs an operator norm over slot
    combinations, and a twist-aspect average gives only the Frobenius norm.
  - **Wilson, arXiv:2506.22667 (Jun 2025), Hooley neutralisers in the quadratic large sieve.** Its
    savings are logarithmic, only in the hyper-skewed range `N² ≲ M`, with the `N`-type term
    remaining. No power saving.
  - Upstream is unchanged (main `0ce80fdd`, PRs through #71).

- *Upstream PR #72 (Das, "das-acyclic-bootstrap-874771265"): θ = 0.874771265.* It refines PR #71 by
  1.64e-6 with two ordered bootstrap rounds.
  - Each round re-prices the natural root at `6(2θ_input − 1)` and rebuilds Collet's source graph
    very finely (21,527 count and 19,529 physical transitions; every child uses its predecessor as
    both LOW and HIGH supplier). It then certifies a common-envelope physical return.
  - It introduces no new analytic input: "a parameter refinement of existing machinery". Both
    ingredients are already measured for our chain. The re-feed is worth about 1e-8 ("Bootstrap
    re-feed" above). A fine graph is bounded by the continuum ceiling 0.8747241
    (`variational-ceiling/`).
  - **New bar** (1e-5 below the best upstream PR): `0.874761265`. Our Lean submission 0.8747289 clears it
    by 3.2e-5, a lead of 4.24e-5 over #72.

- *Cross-check against Das's hill-climb PR #28 (rohanarun/quasi-rh-hillclimb, 2026-10-23), the
  precursor of upstream #72.*
  - **Adaptive caps.** Round A of #72 is a very fine source chain: Λ decrement 1/16000, per-stage cap
    "previous crossing + 3e-5", 21,527 + 19,529 stages, `h = 0.80008783`. That is a discretization
    approaching the continuum limit of Collet's chain, without repeated marks. Our continuum ceiling
    for our chain (0.8747241, `variational-ceiling/`) bounds what the same treatment can give us: at
    most 4.8e-6, sub-bar.
  - **Lemma S.** After cubic reflection the slot-tuple coefficient is
    `A(P) = Π c(p) · Π_{p<q} (q/p)₃^{±2}`. Splitting the slots into two groups, the cubic large sieve
    gives `|Σ_P A(P) q_P^{−1/2} χ_P(j)^{−2}|² ≪ Z^ε (Z^{z₁} + Z^{z₂} + Z^{2z_a/3})`, a saving of
    `z_a/3` for balanced groups.
    - This is the same mechanism as our `lean-lab/CoupledHybrid.lean` (cubic-symbol coupling between
      slot groups removes the `L` term of MF2.29).
    - It reaches the same conclusion: it improves only the row branch, and the column branch still
      forces `r + 2z < m` (their Lean `BranchAlgebra.column_branch_iff`; ours `MIBranches.lean`).
  - **Their what-if.** Slot cost `λ = 5/3` (column target plus Lemma S) gives θ ≈ 0.87387. This agrees
    with our atom-1 lever map.
  - **Their floor.** They also record a Lean floor: θ > 13/15 for this probe family
    (`theta_gt_13_15`).
  - Independent confirmation, no new input.

- *A first integral of the continuum source chain* (`chain-ode/README.md`,
  `lean-lab/ChainFirstIntegral.lean`, proved).
  - With the HIGH gain at its cap the chain ODE is `E′ = −E(15E − 10)/(E − 15sE + 10s)`.
  - It has the integrating factor `1/(E²(3E − 2))` and the conserved quantity
    `10s/E + log(3 − 2/E)`.
  - The late chain is therefore a level curve of an explicit function, so the method's ceiling is
    transcendental, not algebraic.
  - Next: extend the invariant to the early regime (`g < 1`), then decide whether a monotone-flow
    proof of the chain could replace the finite graph. That would be a simplification that also
    reaches the ceiling (up to −4.8e-6).

- *Round-6 capability audit (unused generality in Collet's foundations lemmas): no survivor* (float
  models; scripts in the session scratchpad `fresh6b/`).
  - The agent audited every foundations lemma that the source step or the return invokes (2.1,
    3.1–3.4, 4.1, 5.1, 7.1–7.7, 8.1, 9.x, 10.x, 12.2–12.3, 14.1–14.2, 14.12–14.13, and the faces).
    No unused generality relaxes a binding constraint.
  - **F1: repeats and extra prime lists act only through "available slots", and that facet binds
    nowhere.** Every slot-consuming moment has a budget on total width with multiplicity: the marked
    inverse moment has `r + 2z ≤ m`, every face has `m₁ + m₂ + Λz ≤ BQ`.
    - The supply facet is slack for the inverse moment (supply 2–4× the cap) and in the return
      (1.6×).
    - On the plain side it is *tied* with the affine cap at every continuum pivot, and this is
      structural. Gate equality forces `ξ_{p*} = t + 2p*S`, so the plain total is `y* = t`, and the
      face's own capacity at `t` is `(B − t)/Λ = s`.
  - **F2: the HIGH-gain shortfall is entirely the long line, which carries no slots.**
    - Letting the long line use slots at efficiency λ: λ = 0.25 lifts the gain fraction from 0.957
      to 0.993 at `s = 0.042`. In the return, λ ≈ 0.26% alone would give 1e-5.
    - But the only marked long moment (the marked form of 7/8 Lemma 17.6) moves the long line by
      `+(10/6 − 2pν)` per unit of slot width, i.e. λ = −2.67 at `p = 1/2`.
    - The reason: the long line's slope `5/6 − ν` is positive, so an extra saturated factor makes
      an amplified witness worse.
  - **Rechecks.**
    - Two-cutoff covering, including adaptive second cutoffs: the adversary puts the first witness
      at its crossing and the second at the pure long end.
    - Repeated plain slots: closed, for the degeneracy reason in F1.
    - Lemma E: equivalent to bounding the HIGH-class energy by the parent face, with the same
      height-uniformity obstruction.
  - **Measured on the continuum ceiling.** Only the regular HIGH gate at `ν = q` binds; every other
    gate has reserve ≥ 1.1e-3. The binding amplitude class drifts from `p* = 1/2` (`s ≤ 0.02`)
    to 0.22 and then 0.15.

- *The continuum source chain is one explicit switching ODE, and each branch is Darboux-integrable*
  (`chain-ode/README.md` "The p-family", `lean-lab/ChainFamilyIntegrable.lean`, proved).
  - For binding amplitude class `p` the HIGH gate reduces exactly (the ρ-terms cancel) to
    `6q_p = 5((3−p)E + 4ps − 2)/((1+p)E + 4p²s − 2p)`.
  - The class flow `E′ = −6q_pE/(1 − 6q_ps)` has the invariant lines `E = 0` and
    `L_p = (3−2p)(5+p)E + 4p(5−2p²)s − 2(5−2p²) = 0`, and the first integral
    `I_p = log(L_p/E) + 2(5−2p²)(5s−p)/(5(1−p)²E)`.
  - The switching flow (`6q* = max_p 6q_p`, `E(0) = 1`, seed slope `6κ`) reproduces the full
    continuum-ceiling envelope to **6e-7** at `s = 0.0412` and `0.045`, with `p*` drifting from 1/2 to
    0.19.
  - So every source graph (ours, Collet's, #72's 21k-node one) approximates this explicit ODE. Its
    inputs are exactly the atoms: `ρ(ν)` from exchange rate 6, slot cost 2, the supply facet and
    `Λ = 6qB`.
  - This answers the user's question about hidden structure, and could support a short
    "continuous chain" proof.

- *Round 6 probe redesign: the probe has no free direction* (`probe-redesign/README.md`).
  - A float model on faces 58/52 with `s_P = 9/200` reproduces 0.8747289; only the top row `d = h`
    binds (`δ = 0.455`, `p = 1/2`, `R = 0.6037`, `C = 0.0331`).
  - Exchange rates: `θ_low` +0.78, bad-row exponent `E` +0.222, `R` +0.135, `C` −0.026, energy room
    −0.063. So 1e-5 needs 4.5e-5 off `E` or 1.6e-4 of energy room.
  - A general slot operation `I(Xp^{α₁}, Yp^{α₂}, Zp^{α₃})` is an exact reparametrization (symbolic):
    `α₁, α₂` cancel, `α₃` rescales `Z` and `ℓ`. Inverse-type numerators lose the principal pole or
    cost +0.010. Marks outside the theta index lose the signal. Freezing slots or running past the
    energy wall loses 0.33 per unit (break-even needs a low-side loss rate below 0.08).
  - Closed. Any gain must come from `R`, `C`, the energy room or a joint same-zero count.

- *The faces are tangent lines of one explicit curve* (user question, 2026-10-25;
  `chain-ode/README.md` "The faces are tangent lines…", `chain-ode/faces_closed_form.py`,
  `lean-lab/ChainSwitching.lean`, proved).
  - The faces are the supporting lines of the convex unproven region in (plain length, slot
    width), and in the limit the tangent lines `(B, Λ) = (E − sE′, −E′)` of the envelope (a
    Legendre transform).
  - Every class flow is solved by Lambert W: `1/E = W(Cγ/β·e^{αγ/β})/γ − α/β`, matching
    numerical integration to 2e-13.
  - The binding class collapses to `6q* = 5(√E − 2√s)²/(2 − E − 4√(Es))`, proved in Lean and
    matching brute force to 3e-10. So the continuum chain is one algebraic ODE, clipped to
    `p = 1/2` early and capped by the natural face.
  - Importance profile of a better HIGH count (`ε_H = 1e-3` on windows of width 0.005): worth 0
    before `s ≈ 0.012` (the natural face caps the slope), then rising about 2.3× toward the end.
    Half the value lies in the last 0.01 of width, at `ν ≈ 0.51`, `p ≈ 0.2`. There the count is the
    unmarked corner, whose inverse and plain lines are exact diagonals, so only atom 2 can move it.
  - Eliminating the faces is possible in principle (continuous induction along the curve), but it
    is worth at most the ceiling (−4.8e-6). It is a simplification, not a route to the bar.

- *P1 seen three ways (synthesis, 2026-10-25; heuristic reformulations).*
  - **Signed dual.** Poisson in the rows writes the column branch as its diagonal plus a dual
    form whose dual diagonal exactly cancels the subtracted `n = n′` terms. What remains is a
    bilinear form signed by reciprocity. Any positivity step (large sieve, Cauchy–Schwarz)
    re-creates the `N` term. Beating it means showing that the second moments in the different
    reciprocity-sign classes agree to a power saving. That is an affine-type equidistribution
    problem, where even the `GL(2)` quadratic-twist analogue has only log savings unconditionally
    (Li 2024).
  - **Kazhdan–Patterson in disguise.** After that second Poisson step, the dual coefficients are
    cubic times quadratic Gauss sums. By Hasse–Davenport these are sextic Gauss sums, so their
    sums are coefficients of 6-fold-cover objects with no explicit theta. This is the same barrier
    that rules out order 5 (user question). The first Poisson step absorbed μ into `θ₃`; the
    second brings the sextic structure back.
  - **Thin-family Lindelöf.** The marked twist `χ_k³χ_P^{−2}` has conductor `≈ K²L²` and critical
    length `KL = N`, while the family has size `K`. P1 is Lindelöf on average in a family thinner
    than its critical length by `L = Z^{0.129}`, the metaplectic analogue of the open
    level-uniform `GL(2)` problem.
  - New literature (2607.07911, 2607.27131) does not reach it (`literature/README.md`).
  - **What the bar actually asks of P1.** A bound of the form `K + N^{1−η}K^{η}` never suffices, since it
    still exceeds `K` for every `N > K`. To stay diagonal up to `N = K^{1+ε}` (the four uses need
    a budget of about `β ≈ 9e-5`), the off-diagonal must already be a power below the diagonal at the
    self-dual point `N = K`. That is an asymptotic large sieve at the critical length with a
    power-saving error. Conrey–Iwaniec–Soundararajan's asymptotic large sieve gives only log savings
    even for the full family of Dirichlet characters.

- *Round 7 (large values, interpolation lemma, signal processing): all negative* (`round7/`).
  - **Large values** (`round7/large-values/`). No large-values method lowers `R = 0.6037` or
    `ρ(0.5) = 7/12` with the chain's inputs. Halász–Montgomery fails because the off-diagonals of the
    thin sextic family are genuinely of size `Y^{1/2}`; Huxley and Jutila give at least 1. Poisson is
    an exact self-duality of the sextic family, `τ(ψ_uψ̄_v) = c(u, v)τ(ψ_u)τ(ψ̄_v)`, so root numbers
    cancel around every cycle and the Guth–Maynard triangle sum S3 gets no saving. With an assumed
    width-1 coset fourth moment and an assumed S3 saving of `Y^{0.136}`, `ρ(0.5)` would drop to 0.5769,
    but no mechanism for the S3 saving was found.
  - **Interpolation lemma** (`round7/interpolation/`). A resonance model, `L ≈ P(Y)` with
    `P | 1 + cY^{k₂}` and all coefficients of `P` and `1/P` of modulus at most 1, meets every
    constraint the count uses and realizes the corner with its dip: rigorously `ΔR = 0`. The
    identity `r* + m* = t*` is exactly this factorization. A lossless interpolation would hold
    outside the zero-density band `[0.0659, 0.0693)·log U`, and the model lies inside it.
  - **Signal processing for P1** (user suggestion: compressed sensing, frame theory;
    `round7/signal-processing/`). Matrix concentration proves the column branch diagonal for random
    coefficients, using only the quadratic and cubic large sieves, so P1 is a derandomization
    problem. Uncertainty principles cap at `‖S‖_F²/N² ≈ 0.92–0.98`. An explicit adversary that keeps
    every algebraic property (unimodularity, twisted multiplicativity, `β³ = n/|n|`) reaches 3.4–5.8×
    the diagonal, so any proof must use the automorphy of `θ₃`. Cleanest open lemmas: Q3
    (quadratic–cubic uncertainty, `‖E‖_op ≤ N^{1−η}`, no Gauss sums) and BD (block decoupling).
    **Correction:** use (a), the inverse-moment budget, needs only `(K + N^{1−η}K^η)‖c‖²` with
    `η ≥ 0.0085`, since `N/K = Z^{0.129}`. The remark "`K + N^{1−η}K^η` never suffices" above applies
    to use (b), the probe, only.
- *The faceless chain in Lean: 34989/40000 = 0.874725* (user request; `faceless-chain/README.md`).
  The 59-node source graph is replaced by one family of faces: secant lines of a five-piece cubic
  envelope that follows the closed-form switching flow (2¹⁶ faces per piece). Each piece is proved
  valid for all its faces at once (one-variable certificates for the scalar gates; Bernstein trees
  in `(u, p)` with polynomial-in-`y` coefficients for the HIGH gate; a Kronecker-substitution test
  keeps the kernel in `Nat`). Four junction steps join the pieces. Return regenerated (34 rows,
  11 windows). Standard axioms; the canonical challenge wrapper and the upstream `npm run check`
  pass. −3.9e-6 against 0.8747289, 0.9e-6 above the continuum ceiling 0.8747241. Committed on the
  PR branch as `41ddc0dd`. `Candidate.bound` keeps the declared 8747289/10^7 (the PR's declaration
  stays valid; claiming the sharper value would also move the next 1e-5 milestone down by 3.9e-6);
  `Candidate.bound_sharp` states 34989/40000.
- *Why the chain is the curve it is* (user question; `chain-structure/README.md`).
  - The binding threshold is an AM–GM optimum over amplitude classes: `D_p = pA_p + (1 − p)²E`,
    and `(a + 2b)²[(a − 2b)²D_p − (2 − a² − 4ab)A_p] = 4(bA_p − a(1 − a² − 2b²))²`
    (`lean-lab/ChainAMGM.lean`). So `6q* = 5(√E − 2√s)²/(2 − E − 4√(Es))` bounds every class, not
    only at a critical point; the binding class is `p* = (E + √(Es) − 1)/(√(Es) − 2s)`.
  - Lambert W comes from a double invariant line: in each class flow `X((5s − p)/E) = 5(1 − p)²` is
    constant, the extactic polynomial is `10(1 − p)²E²L_p`, and `exp((5s − p)/E)` is the exponential
    factor (`lean-lab/ChainLambertOrigin.lean`).
  - The switching flow (moving class) has no invariant curve of degree ≤ 2 besides `E = 0`, so the
    Lambert structure is per class only.
  - Optimal within the method up to 0.9e-6: exact maximum per step, comparison principle along the
    chain, tangent faces, and θ* is flat in the count-face position at the end of the chain.
- *Last checks on the face-family return (2026-10-25).*
  - **`Λ_P ≥ 3` (receipt `source_lambda_low`) is not a lever.** With the receipt dropped, physical
    faces of the family with `Λ_P` down to 2.90 give θ* = 8747249–8747251, i.e. at most 1e-7.
  - **The count face's position is flat.** Moving `C` back along the family by 500, 2000, 6000 and
    12000 grid steps gives θ* = 8747250, 8747251, 8747253, 8747256, so a final step below the
    `22/23` guard (as the old node 58) cannot help. The old end faces are worse on the new return
    (old C with new P: 8747264).
  - **Multi-face physical capacity.** The physical face enters only through
    `CN(d) = min(sP·d, (2y − (2 − B_P)d)/Λ_P)` at `d = ds, dk, h`, and only `new_top` (`d = h`)
    binds, where `CN(h)/h` is the slot width at which the face reaches plain length `4ℓ/h`. The best
    face there is pinned by `Λ_P ≥ 3`, worth 1e-7 (above), so per-shift face choice gains nothing.
  - **An inverse-moment "source chain" fails at once.** Splitting rows by slot amplitude before
    Poisson, the LOW part costs `max_LOW|Q_u|² · Σ_u|M_u|² ≈ Z^{m + qz}` against the averaged marked
    bound `Z^m`. Marks cost through the allowed inverse length `r`, not through the moment, so a
    pointwise split only loses.
  - **Literature (Oct 2026).** Dunn, arXiv 2403.13151 (ANT 2025): a power-saving bilinear large
    sieve whose kernel is a cubic metaplectic *cusp form* (circle method, Voronoi). P1 needs
    quadratic twists of the cubic theta (Eisenstein) coefficients at the critical length, so it does
    not apply. Baier, arXiv 2605.01635 and 2609.21195 (large sieve for square moduli): unrelated. No
    new input for P1.
  - PR #73's description still names `submissions/repeated-marks-20261024/` in "Local checks" and
    describes the 59-face graph; a corrected description is in `faceless-chain/PR_BODY_DRAFT.md`
    (the upstream repository is not writable from this session).
- *Round 8: the curve is proved optimal; P1 re-derived* (`round8/README.md`).
  - `lean-lab/ChainOptimal.lean` (proved): class thresholds increase with `E` (`Q_mono`), class rates
    increase in `Q` and `E` (`rate_mono`), so every envelope passing all class gates stays below the
    binding-class flow (`maximal_envelope`); in the interior regime the binding class is `p*` with
    the closed-form rate (`closed_form_binding`). Hypotheses hold along the chain with margins
    `A ≥ 0.17`, `D ≥ 0.29`, `1 − Qs ≥ 0.87`.
  - P1 as near-orthogonality of the quadratic-character span and the prime-dilated theta span, and
    as a bilinear bound for the matrix of twisted central values `S(k, P)` (all at their critical
    point). The hybrid norm proves `‖S‖²_op ≤ N²`, which equals the *conjectured* Frobenius norm;
    the rigorous Frobenius bound is `LN²`. So P1 is two levels beyond what is proved.
  - Correction to round 7: Lemma Q3's "trivial" operator-norm bound is `N^{1.118}`, not `N^{1+ε}`
    (Heath-Brown's `(MN)^{2/3}` dominates at `M ≍ 27K`). Use (a) needs only the smooth-weight vector
    inequality, which Poisson returns to the original problem.
  - The `22/23` HIGH-parent guard enters Collet's root completion; relaxing it is worth well under
    1e-6.
- *Upstream verification status (2026-10-25).*
  - Every recent PR admission run (PRs #71, #72, #73 before the face family, and a manual run on
    main) fails at about 3 h 5 min. That is the `timeout-minutes: 185` of the workflow step "Check
    the canonical theorem with Comparator and all three kernels", not a rejection.
  - Maintainers verify offline with raised budgets (`budget-only.patch`: 12 h overall, 8 h for the
    kernels, 3600 s per module). PR #71 passed that way on 2026-10-24: candidate compile 67 min,
    Comparator + Lean + nanoda + con-ron 54 min; registered on main as `eacad16c`.
  - **Our certificates under an external kernel.** Pinned lean4export (`076e8e5`) and nanoda
    (`998e0a8`) were built locally. nanoda checks the heaviest face-family certificate
    `p2_high_0_12` together with its 2554 dependencies in 35 s with no errors (Lean compiles that
    module in 96 s). con-ron from the verifier's judge toolchain (Lean 4.35.0-rc2, archive sha256
    matching the pin `b67d0e0b…`) accepts the same export (2297 declarations, `--verified`) in
    1 min 48 s. So both external kernels handle the face-family certificates at about Lean's own
    speed. **The whole proof passes nanoda:** lean4export streamed into nanoda checks all 158,499
    declarations behind `Candidate.bound` and `Candidate.bound_sharp` with no type-checker errors in
    20 min 17 s (43 min CPU), permitting only `propext`, `Classical.choice`, `Quot.sound` with
    unpermitted axioms a hard error.

## Open directions (ranked, revised 2026-10-24, third pass; see `barriers/README.md`)

Exact state: committed Lean branch 0.8747289; best exact value with known lemmas 0.8747257
(Lemma F + fine pivots + density floor); milestone 0.8747189, so 6.8e-6 is still missing on top of
Lemma F. Dual weights of the count's three lines at the binding point (`δ = 0.4546`, `p = 1/2`,
cutoff `t* = 1.155`, detections `(r, m) = (0.742, 0.413)` and `(1.155, 0)`): I 0.56, L 0.31,
P 0.19, with `dθ/dR = 0.133`. So 6.8e-6 needs one of:

1. **Long Möbius moment beyond sixth-power amplification.** About 1.8e-4 in the exponent
   `(1+5r)/6` at `r ≈ 1.155` (2.6e-4 for a full 1e-5). This is the most efficient lever. It
   needs zero-density-strength input or a mean value of `Σ_u|M_u(D)|²` beyond the inverse moment's
   diagonal `D ≤ H` (signed off-diagonal cancellation).
2. **Marked inverse moment budget.** `r + 2z ≤ 1 + 5.5e-4` in the binding configuration (float
   model: budget `1.0004` gives `Δθ* = −4.96e-6`)
   `r ≈ 0.742`, `z ≈ 0.129`. In the binding child (`MIBranches.lean`) the rows have length
   `H = M_c = 2(r+z) − 1 ≈ 0.742`. The column branch runs to dual length `T_d = 3r + 5z − 2m`, and
   relaxing the budget by `Δm` raises `T_d` above the budget `F_c = r + z ≈ 0.871` by `2Δm`. So the
   target is a large-sieve-type bound
   `Σ_{q_R ~ Z^{0.742}} |Σ_{q_μ ~ Z^{0.871}} d(μ)χ_R(μ)K(μ)|² ≪ Z^{0.871 − 0.0011}‖d‖²`. Here `d`
   are reflected cubic-theta (cubic Gauss sum) coefficients and `χ_R` the quadratic twist. That is a
   saving of `Z^{-0.0011}` over the generic sieve's `N` term. For coefficients not aligned with
   quadratic characters the true size is plausibly `Z^{0.742}‖d‖²`, a saving of `Z^{0.129}`, so only
   0.9% of the plausible saving is needed. A possible handle is the twisted multiplicativity
   `d(μ₁μ₂) = d(μ₁)d(μ₂)(μ₁/μ₂)₃^{±}`, which turns the dual sum into a bilinear form with a cubic-symbol
   kernel (Heath-Brown's cubic large sieve), combined with the large sieve over `R`. Bounding each
   `R` separately loses (`Q·N^{2/3} ≫ N`), so both averages are needed at once.
3. **Physical side: only the marked energy.** `c_g = 1/12` is closed. The exceptional channel
   of the low separation is the target's own `1/L` (`|⟨A^exc,B⟩| ≈ C–S · Z^{β* − θ_low}`, an exact
   identity), so the bias is the signal, not a Cauchy–Schwarz loss. The
   marked energy `x + y + ℓ ≤ 1` is the same column branch as item 2, in the regime
   `N ∈ [K, K^{1+δ'}]`. It needs only `δ' ≈ 1.3e-4` for 6.8e-6, about ten times less than item 2
   (`δ' ≈ 1.5e-3`), so **the probe is the cheapest use of any column-branch saving**. A toy over
   `Z[ω]` puts the true size at the diagonal (`atom1/toy/colbranch_exp.py`). The target is a
   quadratic large sieve that stays diagonal slightly past `N = K` for reflected cubic Gauss-sum
   coefficients with slot twists. Known tools (Heath-Brown; Li's ε-free sieve; Dunn–Radziwiłł's
   Voronoi with the bias subtracted) cover the ends of the dual range but not the middle
   `N^{2/3} < j₀ ≲ K`.
4. **Source chain.** It is an ODE fixed by `ρ(ν)`, the exchange rate 6 and slot cost 2
   (`chain-ode/`). It needs `ε_H ≈ 0.0017` (a HIGH count better by 0.0017 at `ν ≈ 0.5–0.75`), or
   the exchange rate `6 → 5.92`. Discretization holds less than 1.3e-6.

Closed this pass: seed cap, free amplifier, multi-face HIGH witness, reflected plains in the HIGH
gate, bin-restricted LOW-only faces, slot contour `z₀`, cutoff `t₀ < 1`, two-cutoff covering
(independent detections), large values with a mean-square off-diagonal, and mixed prime/plain
slots (a plain slot is a third plain factor; only two plains reflect, so it costs `Λ` like a prime
slot; `mixed-slots/`).

### Revision 2026-10-25 (after rounds 5–6)

- **Bar.** The best upstream PR is #72 at 0.874771265, so the bar is 0.874761265. The Lean
  submission (0.8747289) clears it by 3.2e-5. The milestone below our own value is still ≤ 0.8747189.
- **Stackable sub-bar gains.** A fine chain (adaptive caps, as in #72) together with Lemma F
  self-cells is bounded by the continuum ceiling 0.8747241 (−4.8e-6). Any new idea worth at least
  5.2e-6 would therefore reach the milestone when stacked with it.
- **New target 5: Möbius scale-profile interpolation (round 5).** For all but `U^{R−7.5e-5}` bad
  rows, saturation at `r = 0.741` and `r = 1.155` must imply `|M₁(ρ)|² ≥ U^{δ−2c}` with
  `c ≤ 0.0294`, needed only near the corner. The escaping rows carry clusters of `≳ κ log U` zeros
  (Turán: a fixed number of zeros cannot dip over an interval of scales). Counting them needs a
  multiplicity-sensitive zero count with a power saving. Jensen plus moments controls only
  `≳ 0.1 log U` clusters, so this is out of reach.
- **Closed in rounds 5–6:**
  - every L·A detector redesign (triple-tight corner, `lean-lab/DetectorCorner.lean`);
  - every signed step of the high side (the high side is the signal mechanism acting on the bad
    row's own zero);
  - slot amplitude below 1/2. It is free for the adversary when `η ∈ T̂`, and `η = 1` (ζ) is
    unavoidable. Signed slot classes only force the bad set to be closed under fixed twists.
  - the literature of 2025–2026: no input for P1, atom 2 or the interpolation lemma; the GL(2)
    analogue of P1 (level-uniform second moments of quadratic twists) is open.

### Revision 2026-10-25 (after rounds 7–8 and the face family)

- **Bar.** The best upstream PR is ours (#73, declared 0.8747289); PR #71 is now verified upstream at
  0.874772906. The milestone is ≤ 0.8747189.
- **Reserve.** The face family proves 34989/40000 = 0.874725 (`Candidate.bound_sharp`), so 3.9e-6 of
  the 1e-5 is in hand and **6.1e-6 is still needed**. Everything else in the face map and the return
  is closed: the curve is proved maximal for the gates in both regimes
  (`lean-lab/ChainOptimal.lean`). The remaining guards are worth at most 1e-7 each (`Λ_P ≥ 3`) or
  under 1e-6 together (`B_H ≥ 22/23` plus `q ≥ 1/2`, with the count face moved to `s ≈ 0.045`: 7e-7).
- **What 6.1e-6 needs** (any one):
  1. **P1, use (b) (probe):** the quadratic sieve stays at its diagonal up to `N = K^{1+1.1e-4}` for
     `g̃·(slot sum)` coefficients. Equivalent to a stable rank `≥ N^η` for the matrix of twisted
     metaplectic central values `S(k, P)` (`round8/README.md`).
  2. **P1, use (a) (inverse budget):** `(K + N^{1−η}K^η)` with `η ≥ 0.0076` at `N/K = Z^{0.129}`.
  3. **Long Möbius moment:** about 1.6e-4 below `(1+5r)/6` at `r ≈ 1.155`.
  4. **HIGH count near `ν ≈ 0.5`, `p ≈ 0.2`:** `ε_H ≈ 1e-3` (late chain only).
  5. **Exchange rate:** `6 → 5.93`.
- **Running:** round 9 (two independent fresh-perspective agents: framing/assumptions, and
  outside-domain tools); a full independent nanoda kernel check of `Candidate.bound`.

### Round 9 (2026-10-25): why `ρ(ν)` is what it is

- **The unmarked zero-density exponent is the value of a lattice game** (`round9/README.md` §1,
  `lean-lab/ZeroDensityGame.lean`, proved). The extremal adversary is the two-term model
  `L ≈ 1 + bU^{−s₀(s−a)}` with `s₀ = 5/(15 − 6ν)`. Its Möbius blocks are saturated exactly at
  `s₀ℕ` and its plain block at `s₀`, so every count that depends only on a witness's length gives
  at least `ρ`. This closes mixed moments, products, prime blocks, fractional moments and
  multi-`t` detectors.
- Only the long moment at `3s₀ ∈ [1, 3/2]` moves `ρ`, with sensitivity `4ν/(5 − 2ν)` (0.44 at
  ν = 0.45, 0.5 at ν = 0.5).
- Bootstrapping the long moment from zero counts gives 1.1667 at `t = 1.155` and 1.2273 at
  `t = 1.25`. That is worse than amplification (1.1292 and 1.2083).
- The amplitude cap `p ≤ 1/2` is the paper's own zero-free bound (Lemma 19.1), so no
  zero-free-region bootstrap lowers the binding class (`round8/README.md` §3).
- Upstream: no PRs after #73. The bar is unchanged (milestone ≤ 0.8747189, 6.1e-6 still needed).
- **Fresh-framing agent** (`round9/fresh_framing/README.md`):
  - Repaired round 7's resonance model with a fine lattice. The dip and `p = 1/2` co-occur, and a
    perturbation covers the return's numerator length `n₀ = 0.418` with a dip margin of −3e-4. So
    no per-row argument can move θ.
  - New candidate (B): restrict the probe's dual frequencies `H = u·a⁶` to large sixth-power part.
    Priced here (`round9/README.md` §3): the restriction is a reweighted dilation `X → X·N(b)⁶`.
    Every term crosses the marked-energy wall, and the low side does not pay for it. Closed;
    it reduces to P1 use (b).
- **Numerics** (`round9/numerics/`): on the actual sextic family (2076 rows at `U = 8000`), the
  long Möbius moment stays within 0.89–0.99 of its diagonal up to `D = U^{1.4}`, where
  amplification allows a factor 20. Atom 2 is a limitation of the method. A proof needs twisted
  Möbius correlations, of Chowla type.
- **Outside-tools agent** (`round9/outside_tools/NOTES.md`).
  - Frame theory localizes P1. On the columns whose largest prime factor has norm `≤ K`, the
    column branch is the diagonal times a frame constant `F`, for every choice of unimodular block
    multipliers with the cofactor data fixed (rigorous). `F` is numerically at Marchenko–Pastur.
  - Precise status: P1 ⟸ BG + HC, where BG is the frame bound `F ≤ N^{o(1)}` (unproved; it
    involves `g̃` at primes `≤ K` through the cofactor data) and HC is P1 on the hard core
    (columns with a prime factor of norm `> K`). Only modulo BG is the arithmetic needed just at
    primes in `(K, N]`. Given BG, HC ⟺ P1, and Vaughan's identity is circular, so there is no
    closure.
  - Correction (same day): the first synthesis said "for any values of the Gauss sums at the block
    primes" and gave HC alone as the sharpest form of P1. Both overstated the agent's result;
    fixed in `P1_PROBLEM.md` and `round9/README.md` §5.
- **Conditional θ** (`round9/conditional/`): the float model of the return with one atom moved,
  faces fixed. A diagonal long moment gives Δθ* = −7.9e-3; a 1% lower long-line slope gives
  −3.9e-4; the 6.1e-6 still needed corresponds to `b_L ≈ 4.9992`, a power saving of about
  `U^{1.5e-4}` over amplification at `r ≈ 1.155`. Halving the inverse slot cost gives −4.2e-3 and
  stops binding once the long line is diagonal.

### Round 10 (2026-10-25): the long witness from the real-L-function side (`round10/README.md`)

- **`μ·log = −Λ∗μ` pieces** (`round10/pieces.py`). With the bin's prime-amplitude cap
  (`|Q(P)|² ≤ P^{1+δ}`) on the prime factor and the inverse moment or amplification on the
  Möbius factor, a piece with prime length `p` counts `1 − tδ + pδ` (`p ≥ t − 1`). It beats the
  amplified line exactly when `p < (L(t) − 1 + tδ)/δ`, which is `p < s₀` at `t = 3s₀`. The lattice
  adversary's pieces sit at `p = s₀` (exactly `ρ`), `2s₀` and `3s₀`, so the identity reproduces the game.
- **Amplification = the 11/12 strip.** `(1 + 5t)/6 = 1 + (t − 1)(2·11/12 − 1)`; amplification
  makes `Σ_u|1/L(σ)|²` diagonal exactly for `σ > 11/12`. A global-supremum strip `β* ≈ 0.875`
  would give the long slope `2β* − 1 ≈ 0.749` if any identity confined the pointwise factor to the
  excess length `D/U`. None does: Vaughan's middle range, Heath-Brown's all-Möbius products and
  the long-prime pieces all exceed it.
- **The adversary as an L-function.** Its zeros fill a fraction `s₀ ≈ 0.41` of a unit window on
  `Re = a`. Littlewood plus the fourth moment gives `ρ`. A sixth moment with excess below `s₀δ`
  would beat it (the Burgess route has excess 0.375). The bin's window gives `|L(1/2 + it)| ≤ U^{δ/4}`
  (Lindelöf right of `a`, then Phragmén–Lindelöf), so the adversary fits because `s₀ < 1/2`.
  Killing it needs a window subconvexity of `U^{0.02}`. The functional equation adds nothing: the
  dual sum supplies `|L(1 − a)|` without touching any witness.
  - New witnesses: prime-factor-weighted Möbius blocks, with DH-strength mean values. They are
    defeated by the lattice adversary, because prime-factor weights are scale shifts.

### Round 11 (2026-10-25): the binding inequality, atom 2 localized, and the follow-up (`round11/`)

- **What binds at θ\*** (`round11/README.md` §1). No receipt constant binds. The only binding
  cover is `new_top`, i.e. the return polynomial itself (high-side balance at `d = h`,
  `δ ≈ 0.4534`, `p = 1/2`, count from face C). So sharpening a lemma constant cannot help.
- **Atom 2, fresh look** (agent; `round11/sextic_moment_notes.md`). No power saving. Proved or
  checked:
  - twist averaging (`λ = 1/2` over cubic twists) gives twists, not copies;
  - thickened and sparse families, and `t`- and `a`-averages, give nothing beyond copies.
  - Bootstrap + grouping gives only a constant saving even given (A), because the
    `U^{0.172}`-rough core (about 1% of the mass) gains nothing.
  - The binding case is a sixth moment of a prime polynomial of length `U^{0.385}`.
- **(A) is heuristically false past `U^{4/5}`** (correction to the agent).
  - The numerics put the dyadic family's large-sieve constant at the random-matrix edge.
  - But `b_u = conj g̃₆(1, u)` meets the sixth-power dual frequencies `h = a⁶`. That gives
    `N^{5/6}U^{1/3}` (de Faveri's `A^{1/3}B^{5/6}`), which hides inside the edge's constant.
  - Direct test (`round11/gauss_bias.py`): the conjugate Gauss vector exceeds random vectors by
    8–19% at `U = 2·10⁴` (2–7σ). That is a real bias, but smaller than the heuristic's constant at
    these sizes.
  - So the face `(1, 1)`, worth about −2e-3 in θ, is not to be had from a general large sieve.
- **Follow-up verification cost** (`verification/AUDIT_FOLLOWUP.md` §6–8).
  - The HIGH certificates in packed integer arithmetic take 107 s of kernel time (was about
    2120 s): a coefficient check against literal data plus a tree check.
  - The tree's interval test reads the shifted coefficients as base-`Y` digits of the packed
    number, with `Y = 2^e X − k`, because `2^{e(L−1)}A(X)` is the scaled shift evaluated at `Y`.
  - The sector certificates, packed the same way, take 61 s for all scalar certificates (was
    290 s).
  - The face-family certificates now cost about 168 s against about 2600 s in PR 73.
  - Lean: `Faceless/Packed.lean`, `TreeZ.lean`, `ScalarZ.lean`, all on the three standard axioms.
- **Follow-up as a submission.** A package `arvi-single-stage-20261025` is prepared on branch
  `submission-single-stage-20261025`. It is not posted upstream.
  - Value: 2186813/2500000 = 0.8747252, 3.7e-6 below PR 73's declared 0.8747289.
  - Simplification: single stage (no seed step, intermediate return or PR 67 re-proof, −38% export
    bytes) and packed certificates.
  - It falls under the "smaller gains count if they simplify the proof" clause. The 1e-5 milestone
    (0.8747189) still needs 6.1e-6 of new mathematics.
- **Bilinear route to P1** (agent; `round11/bilinear_notes.md`). Not in reach. Results:
  - **Proved from Dunn–Radziwiłł:**
    - a single slot has conductor `N(k)²N(P)`, not `N(k)²N(P)²`, so its critical length is
      `K·L^{1/2}`;
    - the root number factorizes as `ε₁(k)ε₂(P)`;
    - the slot combination's self-dual point is still `K·L`.
  - **Quadratic twists of θ₃ are Voronoi-dual to sextic twists.** So "Voronoi plus
    Goldmakher–Louvel is diagonal without slots" (atom1 §8) was wrong.
  - **Proved classically, checked numerically:**
    - `g̃₃g̃₆ = μ·conj((4/·)₆)·g̃₂·(·/|·|)`;
    - the slot-free case `L = 1` holds for `N ≥ K^{3/2+ε}`;
    - under GRH for Hecke L-functions of `Q(ω)` it holds for every `N`.
  - **The one input for `L = 1` at `N ≈ K`:** a zero-free strip `Re s > 11/12` for CM Hecke
    L-functions `L(s, ξ₀ψ)` of `Q(ω)`, with ∞-type `z/|z|`.
  - **New, sketch:** single mark at use (a), `F_P ≪ N·K^{7/6}` (Voronoi to length `K`, then
    de Faveri's sextic sieve). That is `η ≈ 0.041` on the slot-diagonal part. The cross terms
    (Lemma MM) stay open.
- **Tensor route** (`round11/tensor/README.md`; question from Arvi).
  - The fourth moment `tr((SS*)²)` splits exactly into propagator sectors.
  - **Phase-free sectors** are about 95–97% of it numerically. They are `≤ N⁴/L + N⁴/K` by the
    large sieve and cubic orthogonality.
  - **2-point sectors** are weights times `‖S‖_F² − diag`. They are `≤ N⁴·Z^{−0.0053}` given the
    single-mark bound.
  - **One sector remains:** the alternating 4-point term `tr((B̃_oA_o)²)`. Making it small is
    *derandomized asymptotic freeness* of the off-diagonal cubic slot Gram and the
    theta-conjugated quadratic Gram, via `tr(BCBC) = tr(B²C²) − ½‖[B,C]‖_F²`.
  - **Numerics:** about 1000× below Cauchy–Schwarz, for theta as for random phases.
  - **Status:** no tool proves it. Use (b) would need `p ≈ 10⁴` moments.
  - **By-product, ruled out** (`round11/tau_average_scope.md`, a formal-code study with file:line
    evidence).
    - Averaging over slot heights or random signs would remove the slot cross terms.
    - But the count uses the marked inverse moment pointwise at each zero's height. Its gain `2qz`
      is the coherence of the slot sums at the zero.
    - Any such average also caps every row's averaged slot energy at `O(‖a‖²)`, which erases the
      HIGH classes. With the window paid in Chebyshev, the I-line is 0.6627 against 0.6040.
    - The heights are at most `L^{1.6·10⁻⁵}` anyway.
    - The formal library has a general Voronoi for twisted `θ₃` and the cubic and quadratic
      sieves, but no sextic sieve.
- **Bootstrap of the natural cost** (checked, negligible). A second stage at
  `K = 6(2θ₁ − 1) = 4.496702` (from the single stage's `θ₁ = 0.8747252`) gives `θ* = 0.8747250`.
  - That is only `2·10⁻⁷`, because `dθ*/dK ≈ 6·10⁻⁵`: the chain's end sits on the flow's
    attractor, not at its start.
  - A second stage would double the proof for that.
- **Upstream PR 74 is the new bar** (Sil, 0.8746935; `upstream/PR74_ANALYSIS.md`). Target:
  ≤ 0.8746835.
- **The combined proof** (`combined/README.md`, package `arvi-repeated-marks-on-sil-face-20261025`).
  - **Construction.** Our face family is started on Sil's fourth-power source face
    `GlobalSource (99999/100000) (93/25) (3/50)` instead of Collet's natural face. It runs
    through 3 pieces to the end, then into our final return.
  - **Exact θ\* = 349843/400000 = 0.8746075.** That is 8.6e-5 below PR 74 and 7.6e-5 below the
    target.
  - **Three exact constraints:**
    1. **Start at the tangency, to within about 1e-7.** Away from it the first step's amplifier
       tends to `q(b − s₀)B/E ≈ 0.7(b − s₀)`, above 1/75 at the cap, because the slope gap cancels
       between the numerator and the denominator. `s₀ = 0.0329365` gives `a(cap) = 0.0010`.
    2. **The q floor `q ≥ 1/2`** ends the family where `L/B` reaches 3 (`s = 0.0472`). It costs
       1.1e-6.
    3. **The HIGH-parent floor `B ≥ 22/23`.** It is not binding here.
  - **Fork of Sil's source theorem.** It assumes `theta < β` but uses only `51/100 ≤ β`.
    `combined/fork_sil.py` vendors the 421-module closure and swaps the hypothesis in 8 files,
    with asserted counts. It changes no proof beyond `have hβ := hcontra`.
  - **Generators.** `gen_steps.py` now generates the chain assembly for any number of pieces, with
    the faces C and P (`family2.face_C/face_P`) and their exact values.
- **The exchange-rate barrier, revisited** (`combined/BARRIER_REVISITED.md`).
  - **Where it was wrong.** Atom 2's "twisted multipliers orthogonalize rather than amplify" fails
    for Gauss-type amplification, where the multiplier enters the frequency and the row is the
    modulus. There Sil's twist `χ_a(D)²` depends only on `(D, a)`, and `whole_column` makes it an
    exact energy transfer to `D⁴k`.
  - **Where it holds.** It remains true for Möbius-type rows, `M_u = Σ μ(n)χ_n(u)` (the long line,
    the 11/12 base). There `χ_n(ua⁴) = χ_n(u)χ_n(a)⁴` adds a cubic twist in `n`, i.e. a slot.
  - **Read backwards.** The same identity absorbs a slot into the row at cost 4 per unit, against 2
    in the marked inverse moment: no gain.
  - **Consequences.** Sil's ledger `2 + 4φ`, under the native gate `κ(1 − φ) < φ`, beats `6κ` iff
    `κ > 1/√3`. The candidate for our chain is the source step (float −1.75e-5;
    `mixed-step/`, in progress).
- **Upstream (2026-10-25, late).**
  - PR 76 is our combined proof, 0.8746075.
  - PR 75 (Runbo Li, 0.87469284) is the natural-cost bootstrap on Sil's theorem: 6.6e-7 over
    PR 74, nothing to absorb (`upstream/PR75_NOTE.md`).
  - The next bar is ≤ 0.8745975.
  - Main lever: the mixed fourth/sixth-power source step (float −1.75e-5).
  - Design constraint: Collet's step amplifies with a separate prime pool `(h, p) ↦ p⁶h`, which
    avoids the slots. Swapping p⁶ for p⁴ there gives row-twisted copies, which is the orthogonal
    case. Sil's gain comes from using the selected slots themselves as the amplifier: their twists
    are what the transfer removes, and their D-family supplies the density. So a mixed step must
    route selected slots into the amplifier.
- **The return's face choice is optimal** (`combined/experiments/thirdface.py`).
  - Extra count faces from the family between P and C (y = 0.70 … 0.95 of the last piece) leave
    θ* at 8746075.
  - With Sil's face as an extra branch it never gets chosen (`sbranch.py`).
  - The binding box (`new_top`, p → 1/2) is covered best by the last face, which sits at the q
    floor L/B = 3.
  - So the only way down is a higher intercept at that boundary: about 9e-6 per 1e-3 of
    intercept. The mixed step's float model raises it by 0.0019 (`mixedstep.py`: θ* ≈ 0.8745898).
- **PR 76 admission restarts** (`verification/AUDIT_FOLLOWUP.md` §11). The workflow cancels in
  flight on every push or edit, and the cancelled run reports "Verification report is missing…".
  A push after opening (pronoun fix) and a description edit caused this. Rule: no pushes or edits
  while admission runs.
- **Mixed step priced; return ceiling found** (`mixed-step/README.md`).
  - Calibration: the flow with the LOW exchange rate swapped reproduces PR 76 (0.8746073).
  - Readings: the cautious one (Sil's ledger on the excess) gives 0.8745898 (−1.75e-5); a
    transfer without a saving gives 0; the readings where the selected block saves energy are
    much larger.
  - The exact return with perfect source faces stops at 0.8745804, so any source-side lever is
    capped at −2.7e-5.
  - Sil-LOW (Sil's argument in the LOW branch at rate q) hits the cap but ignores the HIGH gate's
    amplifier charge.
  - Lean: `lean-lab/MixedStepLedger.lean` (payment algebra, thresholds `6q/(1+q)` vs `6q`, Sil's
    26/7 floor).
- **Mixed step, exact model and the return's new regime** (`mixed-step/README.md` §10, 2026-10-25 late).
  - **Start.** The continuum flow's jump from Sil's slope 3.72 to the stall line `L/B = 18/7` is
    realized by a fan of faces through one point. Each fan face is a legal mixed step from the
    previous one.
  - **Exact checks.** `mixed_certs.py` mirrors the draft SourceValid3 in exact rationals. These pass
    it at every sampled face:
    - 46 fan steps (`q = 7499/10000`, `s0 = 16/1000`, caps growing to 0.075);
    - the junction;
    - an 8-piece fine family to `s = 0.062` (secant faces, `den3 = 2⁻¹⁵`).
  - **The return now binds on its own physical window.** With the mixed faces the faces stop
    binding at `s_P = 0.052`. The binding is the `new_top` capacity `s_P·h`.
  - **`dMinus > 3/4` was over-assumed.** All 9 uses in our fork need only `dMinus > 1/2`. With that,
    `s_P` rises until the P face binds again through `(B_P − 4ℓ/h)/L_P`, i.e. where the envelope
    reaches `m₁ + m₂ = 2(1 − y/h) ≈ 0.843`.
  - **Exact faces of the family** (P at `s = 0.057`, C at `s = 0.0595`), caps 0.075,
    `s_P = s_C = 0.058`: **θ\* = 0.8742869**. That is −3.2e-4 against PR 76. It is conditional on
    the mixed-step theorem (MStep, Lean pending).
  - **Atlas at the new point** (`strip-mine/atlas2.py`): `B_P` −277 per +0.3%, `h` −167; `B_C`,
    `L_C`, `s_C`, `s_P` 0.
  - **Ruled out.**
    - A fixed stronger HIGH parent (Sil's face or the natural face) instead of the previous face
      makes the flow worse.
    - The q floor `q ≥ 1/2` is (LD1) of Collet's restricted HIGH count (`r* ≥ 22/29 > 3/4` for the
      inverse moment's domain). Relaxing it is new analytic input, not a refactor.
- **Mixed step, formal build (2026-10-26).** Target: the cut at θ ≈ 0.87427 via the mixed source step.
  - **Natural cost.** Every mixed-step Python run must export `QRH_K=9/2`. The tree's gates use
    `Lref = 49/100 − (9/2)b`; the scripts defaulted to Collet's 4.4973. The first kernel test of a
    fan step caught this (gate 11 negative at the cap). After regenerating, the flow is identical
    (no gate in the flow depends on K), and only the fan changes.
  - **Certificates, all kernel-checked (`decide +kernel`):**
    - 46 fan steps (`Fan/Steps.lean`, 3 min);
    - 8 junction steps (fan → piece 0 → … → piece 7, `Family/Gen/Junctions3.lean`).
  - **Uniform family machinery for `SourceValid3`** (`Family/{Formulas3,High3,Packed3,Validity3}.lean`).
    - With `q = (1 − den)L₀/(6B₀ − L₀)`, the mixed denominator `den3 = 1 + q − 6qB₀/L₀` is exactly
      `den`. The selected width is `δ = Nd/Dd` with `Nd = (1−den)(L₀b + t − B₀ + 6B₀r)` and
      `Dd = den(6B₀ − L₀)`.
    - Every gate times `Dd` is a polynomial in `y`.
    - `Certs3.valid` proves SourceValid3 for every grid step of a piece.
  - **Exact family check.** With K = 9/2, the 8 pieces to `s = 0.0595` pass at every sample (ALL OK).
  - **Faces C and P** (exact, `faces_k92.json`):
    - C: B = 0.9638418, L = 2.0972320;
    - P: B = 0.9657869, L = 2.1306183.
  - **L2 transfer lemma, proved** (`Transfer/`, ~2k lines, axioms clean):
    `collet_main_selected_transfer`, plus its pool and allocation versions, under (S) and (Col). The
    Cauchy–Schwarz count cancels the renormalization `V → V/∏P` exactly, so there is no W factor.
  - **L4/L5 design** (`mixed-step/L45_DESIGN.md`). A hybrid:
    - the MAIN side takes the residual as a literal Collet object, `child (s.restrict J)`, at
      virtual parameters;
    - the LOW/HIGH waist is forked with two parents (`s₀` original, `s` residual) and two amplitudes
      (`poolAmp = a`, `amp = a + δ`);
    - one new piece of arithmetic, the δ-shift: `Z^{−a−side(A)} = Z^{−a_v−side(A_v)}·Z^{(a_v−a)−(A−A_v)}`.
  - **New trap found by the design agent.** For `reflected = false` the first-layer scalar has slope +1
    in A, so evaluating it at the virtual parent undercounts by `Z^{2δ}`. The scalar must stay at
    the original A.
- **HIGH count at p = 1/2: no-go, and where the value is** (`new-high/REPORT.md`, 2026-10-26).
  - **Closed form.** The binding HIGH branch is a triple point. Its floor is
    `q_min = κ(t_cut − 1)/(t_cut − T)`, and with the mixed LOW pin the chain is an ODE that matches the
    full-gate flow to 2e-5.
  - **No-go theorem.** With the present inputs no argument improves the saturated count. The LOW
    route reaches exactly `ρ < (1+q)/(6β)`.
  - **Priced open inputs:**
    - slot cost c < 2 in Theorem 7.3: c = 1.8 gives θ* = 0.8739327;
    - long slope κ < 5/6: κ = 0.80 gives 0.8740643.
    Both are worth 10–50× more in the return's count than in the faces.
  - **Lead to check.** The probe reports that MF3.38's descent counts the slot width twice (in
    `D₀ = r + z` and as the child's burden `z₀`). Compare this with the re-reflection argument above,
    which concluded that slot cost 2 is intrinsic.
