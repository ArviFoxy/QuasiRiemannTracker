# Research log

Goal: lower θ in "every Dirichlet L-function is nonvanishing on Re s > θ" by at least 1e-5 against
the best upstream PR (smaller gains count only if they simplify or clarify the proof).

| reference | θ | note |
|---|---|---|
| upstream PR #70 (Mark Lewko), best upstream PR | 0.874772906 | checked 2026-10-24 |
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

## Open directions (ranked)

1. **Column branch of MI / long Möbius moment beyond amplification.** Both need cancellation in sums
   of cubic Gauss sums twisted by quadratic characters (Type II bilinear structure as in
   Dunn–Radziwiłł's proof of Patterson's conjecture). A power saving of 2.5e-4 at r = 1.155 in the
   long Möbius moment would already give 1e-5.
2. **Joint same-zero witness moments** (catalogue G137, OPEN).
3. **Sparse-image large sieve for the long branch.**
