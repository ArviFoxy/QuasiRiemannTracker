# τ-averaging and slot-sign randomization in the count: formal scope (round 11, 2026-10-25)

Question (LOG.md:1563). Can the count average its marked inverse moment over the slot Mellin
height (or over random slot signs), so that the slot cross terms `P ≠ P′` drop and the single-mark
bound `F_P ≪ N·K^{7/6+ε}` (bilinear_notes.md §6) is enough? This note is a read-only survey of the
Lean code; it edits nothing else.

**Paths.** `OAI/` = `/home/user/lean-env/qrh/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/`,
`HC/` = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/`,
`FORK/` = `/home/user/lean-env/qrh/Submissions/arvi_single_stage_20261025/`.
`openai_baseline` and `hailey_collet_1252270103` are symlinks into
`/home/user/QuasiRiemannTracker/submissions/*/src/Submissions/`. A plain `grep -r` run from
`Submissions/` skips them, so use `grep -R`.

**Lean checks** (lean 4.34.1 with the existing oleans; scratch files
`/home/user/lean-env/qrh/Scratch/TauScopeChecks.lean` and `TauScopeAxioms.lean`).
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
- `Candidate.bound` (FORK, θ = 2186813/2500000);
- `padded_source_energy`, `InverseMoment.hybridRow_energy`;
- `CubicSieve.sieveNorm_sharp`, `CanonicalQuadraticSieve.finite_family_quadratic_large_sieve`;
- `inverse_fiber_count`, `replicated_inverse_source_field`.

`QRH.RepeatedMarks.Source.nf_step2 : NFStep2` is a proved term. `grep -R` finds no `sorry` and no
`axiom` in the three packages.

## Verdicts

| Q | verdict |
|---|---|
| 1 | Theorem 7.3 is a **proved Lean theorem about character sums**. It holds for arbitrary slot coefficients with `‖·‖ ≤ 1`, and its column branch is the formal hybrid norm. The count applies it **pointwise** in the slot height. In the final count all slots of a batch share one slot point `z`. In the source chain the slot heights depend on the row. Every height is `≤ Z^{2τ}` with `2τ ≤ 10⁻⁸`, far below `L`. Only the exponent bookkeeping is a "budget" layer. |
| 2 | **BLOCKED.** Any average that removes `P ≠ P′` (heights `T ≫ L` by Montgomery–Vaughan, or random signs) also caps each row's averaged slot energy at `O(‖a‖²)`. That erases the amplitude classes `q > 0`, which are the whole gain of the marks in the count. The averaged *moment* is in fact trivially diagonal: it needs no reflection and no single-mark lemma. The missing input is pointwise control in the slot height, and no average supplies it. |
| 3 | (a) **Formalized:** a general Voronoi/reflection identity for θ₃ twisted by sextic characters of an arbitrary finite prime family. It allows exponents `j < 6`, including `j = 3` (quadratic) and `j = 4` (slot, which gives a Ramanujan sum). The local dual twists are evaluated. (b) **Formalized:** the cubic sieve (Heath-Brown), the quadratic sieve over `Z[ω]` and the hybrid norm, all for general vectors. **Not formalized:** any sextic large sieve. The long line `U^{1/6}N^{5/6}` is formalized only for Möbius polynomials of the Hecke family. |
| 4 | **No formalized bound gives any power saving for `F_P`.** Two pieces are needed. The Voronoi step is mostly an instantiation (moderate work). A sextic large sieve at `Q = M = K` with exponent `< 1.172` does not exist in Lean (large work, comparable to the cubic sieve). Even then the result is a standalone lemma: the count needs the cross terms (Lemma MM), and Q2 rules out averaging them away. |

## 1. Where the count uses the marked inverse moment

### 1.1 The theorem (proved, arbitrary bounded slot coefficients)

- **OAI.** `padded_source_energy`, `OAI/Dictionary/InverseMarkedReferencePaddedEnergy.lean:15–42`.
  - Hypotheses: `∀ coeff i P` with `‖coeff i P‖ ≤ 1` (line 27), the caps `r+2Σℓ < 1` and
    `2r+8Σℓ < 3` (line 37).
  - Conclusion: `Σ_u |Σ_{slot tuples x} ∏ coeff · (Möbius polynomial at ∏x)(u)|² ≤ C·U^{1+εm}(1+|θ|)^{2deg}`.
  - This is Theorem 7.3 with `m = 1`. Its core is `original_source_energy`
    (`…/InverseMarkedReferenceSourceEnergy.lean:33`).
- **Column branch = hybrid norm, as a theorem.** `InverseMoment.hybridRow_energy`
  (`OAI/Descent/Sharp.lean:83–94`).
  - Statement: `Σ_k |hybridRow|² ≤ C(KNBL)^ε (K+NB)·B·(N+L+(NL)^{2/3})` for any `a P` with
    `‖a P‖ ≤ 1` and any `β(n,b)` with `‖β‖ ≤ 1`.
  - Here `hybridRow` is `Σ_{n,b} Σ_P a(P)N(P)^{-1/2}β(n,b)·quadraticRow(k,nb)·inverseCubicKernel(P,n)`
    (`OAI/Descent/Reconstruction.lean:12–16`). This is MF2.29 (atom1/README.md §1).
  - It is applied in `actual_reflected_branch_energy` (`OAI/Reflection/Energy.lean:46–72`).
    There `a` is the reflected slot phase and `β` is the reflected cusp column (θ₃ coefficients
    at the cusp). The proof uses only `‖·‖ ≤ 1` for both.
  - The factorization of the reflected coefficient is `mixed_coefficient_hybrid`
    (`OAI/Reflection/Coefficient.lean:48–64`).
- **HC versions.**
  - `weighted_deleted_source_energy` (`HC/Cycle25/Assembly/Count/MomentInverseMarkedReferenceDeletedEnergy.lean:46–64`).
    The slot point needs only `Re ζ ≤ 1` (line 55), and `C` is uniform in `Im ζ`.
  - `weighted_fiber_reference_energy` (`…FiberEnergy.lean:19–37`).
  - `weighted_source_batch_inverse_marked` (`…MomentDetectorInverseMarkedField.lean:26–45`).
  - All are packaged in `weighted_source_batch_inverse_fields`
    (`HC/Record12518109Count/PhysicalDirect/InverseFields.lean:27–52`).
- **Row-dependent slot heights (source chain).** `annular_rowwise_inverse_marked_energy`
  (`HC/Record12518109Gain/Upstream/ActualRowwiseMarkedInverse.lean:20–44`).
  - Slot weights are `annularWeight(…, choice u + vslot i)` with `|choice u| ≤ height`.
  - It follows from the common-height bound by interpolation over `[−height, height]`, at cost
    `(1+4·height)·Hcost` (line 104), i.e. linear in the window.
  - FORK uses it for repeated marks: `actual_free_inverse_energy`
    (`HC/Record12518109Gain/ActualSourceFields.lean:33`) feeds `replicated_inverse_source_field`
    (`FORK/Source/SourceFieldsK.lean:28–43`).

### 1.2 How the count applies it (pointwise)

- **Interface.** The moment enters as the field `inverse_marked` of the Prop-structure
  `Fiber.Moments` (`OAI/Hecke/DetectorRawFiber.lean:62–71`).
  - The slot factor is `physicalProduct = ∏_s physical(…, external s, U, u, s)` (lines 58–60).
  - `physical` is `canonicalPrimeAmplitude u W b D z = D^{-1/2} Σ_P conj(ψ_u(P)) W(N(P)/D)(N(P)/D)^{z−1}`
    (`OAI/Hecke/DetectorPhysicalSelection.lean:12–14`; `OAI/Hecke/PrimeRow.lean:69–73`).
  - The slot weights do not depend on the row. The point `z = external s` is one number per slot
    per batch.
- **Chebyshev.** `inverse_fiber_count` (`OAI/Hecke/DetectorInverseFiberCount.lean:18–72`).
  - Rows of a fiber share amplitude bins at that same `z`, which gives
    `|∏Q_s(u;z)|² ≥ U^{2qz−δ·mesh}` for every row (`select_physical_product`,
    `DetectorPhysicalSelection.lean:32–54`).
  - The Möbius factor is moved to each row's own zero by a Sobolev step that is uniform over
    `σ∈[0,1]` and `|t| ≤ height` (`inverse_energy`, `OAI/Hecke/DetectorFiberEnergy.lean:13–37`,
    factor `12(1+height)`). The slot factor stays fixed during this step.
- **I-line.** `count_from_raw_moments` (`OAI/Hecke/DetectorCountFromMoments.lean:67–75`).
  - The marks are taken at full budget, `z = (1−r)/2 − ν` (`OAI/Hecke/DetectorBranchBudget.lean:50–53`).
  - This gives `I(r) = 1 − δ(p + (1−p)r)`.
  - The FORK budget layer is pure algebra: `inverse_at_branch_crossing`
    (`FORK/FinalReturn/CountAdmission.lean:40–45`) and `AdmittedWindow.inverse_crossing`
    (`HC/Record1252270103Return/AdmittedWindow.lean:37–38`).
- **FORK final count.** `physical_source_amplitude_count`
  (`FORK/ReturnD/PhysicalDirect/PhysicalSourceCount.lean:30–55`).
  - It holds for each `z` with `Re z = 17/50` and `|Im z| ≤ Z^{2τ}` (line 46).
  - All slots and rows share the slot point `fun _ => z` (lines 48–49).
  - Its hypothesis `SourceMomentBound` (`FORK/ReturnD/PhysicalDirect/MomentGates.lean:44–51`) is
    proved by `actual_source_moments` (`FORK/ReturnD/PhysicalDirect/SourceMoments.lean:146–161`).
- **Where `z` comes from: the high side is a double contour integral.**
  - The central rows equal `∫∫_{szRectangle(H)}` of `sourceSZWeight(s,z)·integratedDyadValue(s,z)`,
    with `s = a+16e+iq₁`, `z = 17/50+iq₂` and `H ≤ (3i+2)Z^τ`.
  - The weight contains `exp((s+z−1)²)`, which is Gaussian in `q₁+q₂`
    (`HC/Cycle25/Numerator/Imported/FullWReconstruction.lean:15–17, 83–100`).
  - `RawSourceDyadBound` bounds the integrand separately at each `q`
    (`FORK/ReturnD/PhysicalDirect/SourceActual.lean:37–56`).
  - `actual_raw_source` then applies the count at `z = 17/50 + iq₂` for that same `q`
    (lines 109–113).
  - So the slot height is integrated, but only against a Gaussian-type weight over a window of
    size `Z^{O(τ)}`, and the count is used pointwise inside the integral.
- **Source chain (HIGH inverse cap, repeated marks).** `FiberMomentsK.inverseRep`
  (`FORK/Source/FiberK.lean:56–67`) and hypothesis `hIM` of `fiber_exponent_class`
  (`FORK/Gain/FiberClass.lean:33`). The budget is the same, `r+2z < 1`, and the row-dependent
  slot heights are again used pointwise.

### 1.3 Height range `T` against `L`

- **Zeros:** `|Im ρ| ≤ 3iT` with `T = Z^τ` (`OAI/Hecke/DetectorWitnessRows.lean:17`). The moments
  are needed for `|t| ≤ height = Z^{2τ}`.
- **Size of τ:** `HeightAdmissible` requires `2τ ≤ D.t` (`FORK/ReturnD/Transport/FinalHeight.lean:22–24`),
  and `D.t ≤ 10⁻⁸` (`HC/Record1252270103Return/GenericData.lean:49`). So the slot heights satisfy
  `|Im z| ≤ Z^{10⁻⁸}`.
- **Size of L:** the marks have total length `(1−r)/2 ≈ 0.129` in units of `log U`, with
  `U = Z^d` and `d ≥ 1/200`. So `L ≥ Z^{6.4·10⁻⁴}`, and **`T ≤ L^{1.6·10⁻⁵}`**.
- **Slot structure:** each slot is tiny (length `≤ t/200`, `GenericData.lean:41`). A mark is a
  product of many slots, and in the hybrid norm `P` runs over squarefree slot tuples with
  `N(P) ∈ [L, 2L]`.
- **No room to widen:** every bound carries `(1+height)^J` (e.g. `SourceMoments.lean:45–48`), so
  heights must stay `Z^{o(1)}`.

### 1.4 Hypotheses vs theorems

Analytic inputs enter at the interfaces as Prop-valued fields or hypotheses:
- `Fiber.Moments`, `SourceMomentBound`;
- `UnitFaceSource` (`HC/Record12518109Existence/UniformSource.lean:19–33`);
- `WeightedAffineFineInput`, `NFStep2`.

Each one is discharged by a proof. The final theorem uses only the three standard axioms. So the
column branch is a real character-sum theorem (the hybrid norm built on the formal sieves), and it
is consumed through exponent algebra.

## 2. Can τ-averaging or slot-sign randomization be inserted? BLOCKED

**(a) What the count needs.** The count needs the moment at the same slot point where each counted
row's slot amplitude is known (§1.2):
- the fixed point `z` of the batch in the final count;
- the row's own `choice u + vslot s` in the source chain.

The HIGH-row gain `2qz` is a statement about anomalously large slot sums, `|Q_u(z)|² ≈ U^{2qz}·‖a‖²`,
at that point.

**(b) Averaging erases the gain itself (PROVED, elementary).**
- Each `Q_u` is a Dirichlet polynomial in `Im z` with integer frequencies `N(P)`, each norm
  occurring a Z-independent number of times (conjugates `P`, `P̄`; slot tuples).
- Montgomery–Vaughan then gives, for every row `u`:

  `(1/2T)∫_{|τ|≤T} |Q_u(z₀+iτ)|² dτ ≤ C(1 + L/T)·‖a‖²`.

- Random signs give the same: `E_ε|Σ_P ε_P a(P)ψ_u(P)|² = ‖a‖²`.
- So any average strong enough to remove `P ≠ P′` also forces the averaged slot energy of
  *every* row down to `O(‖a‖²)`. That is amplitude class `q = 0`: no HIGH row can be detected.
- **Uncertainty principle.** A zero makes `Q_u` large only on a Z-independent window around its
  height, because `W` has Mellin decay. If a row is known to be large at `z₀`, averaging over a
  window `T ≥ L` costs a factor `T` in Chebyshev. The I-line becomes
  `1 − δr − 2qz + z`. Since `2q ≤ δ < 1`, its best value is at `z = 0`: averaged marks are worse
  than no marks.
- **At the binding** (`δ = 0.4546`, `p = 1/2`, `r = 0.742`): the current `I = 0.6040`, the best
  τ-averaged value is `0.6627`. The target is a gain of about `10⁻³`.

**(c) The averaged moment is trivial.** `M_u` does not depend on the slot height, so

  `∫_{|τ|≤T} Σ_u |M_u Q_u(z₀+iτ)|² ≤ C(T+L)‖a‖² Σ_u |M_u|² ≪ (T+L)‖a‖²U^{1+ε}`.

This uses only the unmarked inverse moment, which is diagonal for `r < 1`. It needs no budget, no
Poisson step, no reflection and no single-mark lemma. Bounding the column branch by
`Σ_P|a(P)|²F_P` is just a lossy way to bound the same average. Round 9's dismissal
(round9/fresh_framing/README.md:71) therefore stands, but for a different reason. The reason is not
"Frobenius = N-term": the count is pointwise in the slot height, and averaging destroys the slot
gain. The by-product in LOG.md:1563 does not survive.

**(d) The range is not available anyway.** `T ≤ Z^{2τ} ≤ L^{1.6·10⁻⁵}` (§1.3). The high-side
weight `exp((s+z−1)²)` is Gaussian, and widening the window costs `(1+height)^J` in every input.
The row-height interpolation (`ActualRowwiseMarkedInverse.lean:96–104`) also costs the window
length linearly.

**(e) Random signs fail for an extra reason.** HIGH rows are defined by bins of the *actual* slot
sums at `z` (`HC/Record1252270103Return/RetainedBatches.lean:42–58`). Signs `ε_P` destroy the
explicit-formula coherence, so the signed sums are not large on those rows. A bound averaged over
signs says nothing about `ε ≡ 1` unless the cross terms are controlled, which is exactly Lemma MM.

**(f) Fixed characters do not help.** The only character freedom in the slots is the ray class
mod a fixed `rayM`. Averaging over it separates `O(1)` classes, not `P ≠ P′`.

## 3. Formalized ingredients the single-mark lemma would need

### (a) Theta reflection / Voronoi

`EisensteinTheta.lean` is only the Gaussian/Epstein theta of the lattice (lines 13–37). No file is
named Voronoi. The real ingredients:

- **Cubic theta as a residue.** `cubicEisensteinResidue` (`OAI/Eisenstein/ScatteringCoefficients.lean:83`).
- **Expansion at every cusp.** `three_cusp_decomposition` (`OAI/Cusp/ResiduesModThree.lean:251–254`):
  any `M ∈ SL₂(Z[ω])` equals level-two × one of three cusp representatives × upper triangular.
- **Coefficient bound** at squarefree × cube indices: `three_cusp_coefficients_squarefree_cube_bound`
  (`OAI/Eisenstein/RamifiedValuation.lean:329–335`).
- **Reflection identity.** `marked_reflected_source` (`OAI/Reflection/MarkedDualSource.lean:43–63`),
  through `mixed_smoothed_eq_reflected` (`OAI/Descent/ReflectedDual.lean:27, 46`).
  - It is an exact identity for the θ₃ sum `completedT`. Its coefficients are the squarefree cubic
    Gauss sums `squarefreeGaussCoefficient` (`OAI/Arithmetic/IdealMobius.lean:419–422, 457–472`).
  - The twist is `φ·∏_i (·/p_i)₆^{j_i}`, `j_i < 6` (`OAI/Descent/MixedRow.lean:15–20`), over any
    pairwise coprime primary prime family. `φ` is periodic mod a fixed `Q`.
  - The dual side sits at the cusp `a₀/(c₀∏p_i)`, with Mellin–Barnes kernel `paperKernel`
    (`OAI/Mellin/ReflectedKernel.lean:164–165`; bounds from line 307 on).
- **Local dual twists.** `bracket` (`OAI/CubicSieve/LocalBrackets.lean:437–441`): for `j ∉ {0,4}`
  it is `(χ^{j+2})⁻¹`, so `j = 3` gives `χ`, i.e. `(·/k)₆`. This matches bilinear_notes (C2).
  `j = 4` gives a Ramanujan sum: `actual_bracket_four_divisibility_split`
  (`OAI/GaussSum/ReflectionBrackets.lean:141–147`), so the dual is supported on `P | n` plus a
  `−1/√N(P)` term. This matches (C1).
- **Supporting tools.** Lattice Poisson: `affine_lattice_poisson` (`OAI/Poisson/EisensteinLattice.lean:125`).
  Fourier expansion of periodic twists: `fixedThetaTwist_fixed_fourier`
  (`OAI/Eisenstein/FixedThetaTwists.lean:97–108`).
- **Generality.** `S(k,P) = θ₃ ⊗ χ_k ⊗ conj(·/P)₃` lies in scope as a sextic twist with exponent
  3 at each prime of `k` and exponent 4 at `P`.
  - What is missing is a stand-alone, k-uniform corollary.
  - UNVERIFIED: whether the cusp phases (`A4BadPhase`, `fixedFactor`, `s.upper`) split into a
    row phase times a k-independent column. Also the uniformity of the kernel bounds.

### (b) Large sieves

- **Cubic (Heath-Brown).** `CubicSieve.sieveNorm_sharp` (`OAI/CubicSieve/Sharp.lean:55–57`):
  `‖[(J/I)₃]‖²_op ≤ C(MN)^ε(M+N+(MN)^{2/3})`, over squarefree ideals with primary generator
  (`Ideal.lean:14–17, 150–161`).
  - General vectors: the energy form is `ideal_energy_bound`, `Ideal.lean:161`.
  - Proof: `HasCubicExponent 2` (`Growth.lean:9–14`) improved by
    `step ξ = (6ξ−4)/(3ξ−1) → 4/3` (`HeathBrownIteration.lean:14, 74–83`;
    `ExponentImprovement.lean:79`; `Sharp.lean:8`).
- **Quadratic over `Z[ω]`.** `CanonicalQuadraticSieve.sieveNorm_sharp` and
  `finite_family_quadratic_large_sieve` (`OAI/QuadraticSieve/LogarithmicLoss.lean:474–500`):
  `≤ C(MN)^ε(M+N)‖a‖²` for any `a`, with squarefree, λ-free, odd moduli
  (`CoprimeBilinearBound.lean:522–541, 576–579`). The quadratic row is the sextic row cubed.
- **Hybrid norm:** `hybridRow_energy` (§1.1).
- **Sextic:** none. A `grep -R` for sextic sieve or energy statements finds only symbol algebra.
- **Long line.** `no_slot_endpoint` (`OAI/Hecke/InverseAmplificationEndpoint.lean:11–28`):
  `Σ_{N(u)≤U} |M_u(U^r)|² ≤ CK·U^{max(1,(1+5r)/6)+ε}` (exponent `sourceExponent`,
  `InverseAmplificationBudget.lean:10`), used in `no_slot_inverse_count`
  (`DetectorNoSlotInverseCount.lean:14–42`).
  - It holds only for the Möbius polynomial `polynomial (data.character u) true …` of the Hecke row
    family.
  - Its inputs are `RawMoment`, the diagonal at row scale `H ≥ D^{1+c}` for that polynomial
    (`InverseAmplificationRaw.lean:11–16`), and Möbius prime deletion (`prime_column_energy`,
    `InverseAmplificationEnergy.lean:11–16`).
  - Only the counting shell `finite_amplification` (lines 43–50) is generic.

## 4. Feasibility of `F_P ≤ N^{2−η′}` (saving `≥ Z^{0.0011}`)

- **Target.** After Voronoi the dual length is `K²L/N = K`, so `F_P ≍ L·K·Δ₆(K,K)`, where `Δ₆` is
  the sextic sieve constant. The goal `F_P ≤ N²Z^{−0.0012}` becomes `Δ₆(K,K) ≤ K^{1.172}`.
  de Faveri's `K^{7/6}` passes (per the notes; UNVERIFIED here).
- **No formal shortcut:**
  - the quadratic sieve on `S(k,P)` gives exactly `N²`, the N-term;
  - the cubic sieve does not apply to quadratic or sextic rows;
  - the hybrid norm gives `N²`;
  - the long line applies only to Möbius vectors.
- **The long line for general vectors** at `U = N = K` would need a diagonal sextic sieve on the
  amplified family (rows `KV⁶ ≥ K^{1+c}`). That is not formalized. For the theta vector it is
  limited by the sixth-power Gauss bias, i.e. by Möbius sums of CM Hecke characters
  (bilinear_notes §4(c)–(e)). Bounds for unimodular entrywise (Hadamard) products such as
  `χ₂·χ̄₃` give nothing beyond the trivial bound.
- **New formalization needed:**
  1. **Voronoi for `S(k,P)`** (moderate). Instantiate `marked_reflected_source` for the family
     `primes(k) ∪ {P}`, uniformly in `k`, together with the bracket and phase bookkeeping, the
     inclusion–exclusion over `A` (`2^{ω(k)+1}` terms) and kernel bounds at the dual scale. The
     existing reflection pipeline is built for Poisson in `u` (`Reflection/` 266 files and 23k
     lines; `Descent/` 419 files and 41k lines), not for a k-indexed family.
  2. **A sextic large sieve at `Q = M = K`** with exponent `< 1.172` (large). For comparison,
     `CubicSieve/` is 91 files and 37k lines and `QuadraticSieve/` is 36 files and 24k lines.
- **Payoff.** Even with both, the lemma controls only the slot-diagonal part `Σ_P|a(P)|²F_P`. The
  count cannot use it without Lemma MM (§2). It is feasible as a standalone formal lemma with large
  effort, and blocked as a route to the bar.

## UNVERIFIED

- The details and the exact exponent of de Faveri's sextic sieve (taken from bilinear_notes.md:89
  and atom1/README.md:79).
- Whether the cusp phases in `mixedReflectedValue` split into a row phase times a column for
  varying `k`.
- The uniformity of the `paperKernel` bounds in the range needed.
- The exact `τ` and `d` at the binding instance; the bounds used above are the structural ones
  `2τ ≤ 10⁻⁸` and `d ≥ 1/200`.
