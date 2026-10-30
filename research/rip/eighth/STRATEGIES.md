# Plain eighth moment of the thin sextic family: proof strategies (fresh look, 2026-10-30)

Scripts: `strat_exponents.py` computes every exponent in this note; `strat_tail.py` gives the numerics of §9. No other
repository file was modified and nothing was committed. Tags: [read] = repository file, or an arXiv abstract I opened
(numbers given); [derived] = argument written here; [numerical]; [conjecture].

## 0. Summary

**Target.** T_η(μ): Σ_z Φ(N(z)/Z)|A(z)|⁴ ≪ Z^{1+2η+ε}N², with A = X₁X₂, N₁ = N₂ = M = Z^{μ/2} ≤ Z^{1/2} and N = M².
- The full target is η = 0.
- D1 needs η = 0 on μ ∈ [0.75, 0.87], the window of `fresh-look/second/directions.md`. The brief asks for μ up to 0.93.

**Three findings.**
1. **The target is a pointwise statement past the row count (Prop. 0) [derived].**
   - T_η(μ) forces |A(z)|² ≤ Z^{1/2+η+ε}·N for every single row.
   - So "Hölder needs max/mean ≤ Z^{1/2}" (the recorded dead end) is not a feature of Hölder: every proof must deliver it.
   - For μ > 1/2 this is a real pointwise bound. The project's zero-free half-plane (H1, κ = 2θ − 1 = 0.7468) gives it
     only for μ ≤ 1/(2κ) = 0.670.
   - On the whole D1 window the target implies the pointwise bound that a zero-free half-plane
     Re s > (1 + 1/(2μ))/2 would give: 0.833 at μ = 0.75, 0.769 at μ = 0.93, against θ = 0.8734.
   - At μ = 1 the target is the **eighth** moment Σ_z|L(½,χ_z)|⁸ ≪ Z^{1+ε}, not the fourth (correction to the brief). It
     implies |L(½+it,χ_z)| ≪ Z^{1/8+ε} for every z, which is sub-Weyl.
2. **Best partial result: S1, stratification by the rightmost zero (Prop. 1) [derived].**
   - Inputs: Littlewood's local Lindelöf bound, the family zero count ρ(ν) and the plain fourth moment.
   - Result: 2η(μ) = sup_{0≤ν≤κ} min(μν, ρ(ν) − 1 + 2μν).
   - This proves the full target for μ ≤ 1/3 (de Faveri: μ ≤ 1/4), and η(0.93) = **0.340**, against de Faveri's 0.442
     and Hölder's 0.347.
3. **A barrier (Prop. 2) [derived, model].**
   - The round-9 lattice adversary, with spacing equal to the plain length m = μ/2, satisfies every input now available:
     H1–H3, the count, de Faveri, Burgess, Littlewood, and PR 93's joint count.
   - Its eighth moment has η = 0.338 at μ = 0.93, so S1 is optimal to within 0.0014.
   - It has η > 0 at **every μ > 1/2**, even when all counts are capped at density-hypothesis (DH) strength.
   - So no combination of the current inputs can prove T₀(μ) for any μ > 1/2. D1-by-dispersion needs a new kind of input.
   - "Combination" means arguments that use the inputs only through the lengths of the saturated objects. That is the
     sense of round 9's "every count that depends only on a witness's length".

**Ranking of strategies.**

| rank | strategy | gives | status |
|---|---|---|---|
| 1 | S1: zero stratification (Littlewood + count + fourth moment) | T₀ for μ ≤ 1/3; η(0.93) = 0.340 | proved modulo the project's H1–H3 (§3) |
| 2 | S2: Heath-Brown/de Faveri recursion for plain vectors, Patterson terms via DH | T₀ for μ ≤ 3/8, or μ ≤ 1/2 (within the row count only) | one missing lemma P_r (§5) |
| 3 | S3: sixth moment past the row count, plus sup | η = (ε₆ + κμ/2)/2 | needs ε₆ ≤ 0.153 for η ≤ 1/4 (that is D4); the adversary has ε₆ = 0.329 |
| 4 | S4: better edge count near θ | S1 with R(κ) ≤ 0.111 gives η ≤ 1/4 | needs a below-DH count at the edge |
| 5 | MDS, Kuznetsov, amplification, thinness, decoupling | nothing | dead, with numbers (§7) |

**Missing lemma.** For μ > 1/2 the target is equivalent (Littlewood plus layer-cake) to a joint plain–zero count:
- J(ν; m) := #{z : L(s,χ_z) has a zero with Re ≥ (1+ν)/2 and |X_m(z)|² ≥ M^{1+ν}} ≪ Z^{1+2η−2μν}, for ν ∈ (2η/μ, κ].
- At η = 0 this is stronger than DH, and the adversary shows the current inputs cannot reach it.
- The weakest version that still matters, η = 1/4 at μ = 0.93, needs J(κ; 0.465) ≪ Z^{0.111}. Available today:
  Z^{0.287–0.290}.

## 1. Setup and inputs

- Rows: squarefree z with N(z) ~ Z, coprime to 6. Then χ_z(n) = χ_z(−1)λ_z(n) on primary n, where λ_z is a Hecke character
  of conductor z(1−ω)^c, with norm ≍ Z (`moments_probe/PRIMEROWS.md` §2) [read].
- X(z) = Σ_n W(N(n)/M)χ_z(n), with W smooth and compactly supported in (0, ∞). We have
  X(z) = χ_z(−1)(2πi)⁻¹∫_{(2)}L(s,λ_z)E₃(s)M^sW̃(s)ds, where E₃ is a bounded Euler factor at 1 − ω.
- **H1** [read: brief; `directions.md`, θ = 0.87341198]: no zero with Re s > θ, |Im s| ≤ Z^ε + 3. We write κ = 2θ − 1 = 0.74682.
- **H2** [read: `round9/README.md`, `lean-lab/ZeroDensityGame.lean`]:
  #{z : a zero with Re ≥ (1+ν)/2, |Im| ≤ Z^ε} ≪ Z^{ρ(ν)+ε}, with ρ(ν) = (15 − 16ν)/(15 − 6ν).
  - This is Xu–Sang's (31 − 32σ)/(21 − 12σ).
  - arXiv 2610.17675 (abstract read) states a low-height zero-density estimate. I did not check the exponent in the paper.
  - ρ(κ) = 0.290, and ρ < 0 beyond ν = 15/16.
- **H3** [read: brief, `mixed-slots/README.md`]: Σ_z|A|² ≪ Z^{1+ε}N for μ ≤ 1.
  - Reflecting any factor longer than √Z extends this to all lengths.
  - No reflection shortens the eighth moment: every factor here has N_i ≤ √Z, so the dual lengths Z/N_i are longer.
    T(μ) is irreducibly past the row count for μ > 1/2.
- **dF**: Θ₆(A,B) ≪ (AB)^ε(A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6}). Xu–Sang (arXiv 2610.17675, abstract read) prove a
  matching lower bound "matching de Faveri's upper bound". I did not locate de Faveri's paper.
- **Bu**: Burgess for the short sums, if available over Z[ω] [conjecture as stated here]: |X|²/M ≤ Z^{3/8} at M = Z^{0.465}.
- **Lemma L (local Littlewood)** [derived; standard argument].
  - Statement: if L(s,λ) ≠ 0 for Re s > σ₁ and |Im s| ≤ T + 3, then |L(σ+it)| ≤ exp(C_ε(log qT)^{1−c_ε}) for σ ≥ σ₁ + ε and
    |t| ≤ T.
  - Proof: log L is analytic on D(2+it₀, 2 − σ₁ − ε/3), and log|L| ≤ C log qT there (convexity). Borel–Carathéodory
    bounds |log L| by C′ε⁻¹log qT on a slightly smaller disc. Hadamard's three circles, between radius 3/4 (where
    |log L| = O(1)) and that disc, gives the power (log qT)^{a}, a < 1.
  - Corollary: |X(z)| ≪ M^{β_z+ε}Z^{o(1)}, where β_z = max(½, sup{Re ρ : |Im ρ| ≤ Z^ε + 3}). Shift the integral to
    Re s = β_z + ε and truncate at |t| ≤ Z^ε, since W̃ decays faster than any power.

## 2. Prop. 0: the target is pointwise past the row count [derived]

**Proof.** Every term is nonnegative, so |A(z₀)|⁴ ≤ Σ_z|A|⁴ ≪ Z^{1+2η+ε}N² for each z₀.

**Consequences** (balanced; the implied bound is |X|²/M ≤ Z^{1/4+η/2}):
- **The row count.** For μ ≤ 1/2 the implied bound is weaker than the trivial |A|² ≤ N², so the target there is a pure
  large-sieve (off-diagonal) statement. For μ > 1/2 it has pointwise content.
- **Against H1.** The best pointwise bound from H1 is |X|²/M ≤ M^κ (Lemma L with σ₁ = θ; interpolating towards σ = ½
  does not help when M ≤ √Z).
  - So |A|²/N ≤ Z^{κμ}, and any proof of η < κμ − 1/2 proves a pointwise bound beyond H1. This threshold is 0.060 at
    μ = 0.75, 0.150 at 0.87 and 0.195 at 0.93.
  - The target needs |X|² ≤ M^{1+1/(2μ)}: the bound of a zero-free half-plane at (1 + 1/(2μ))/2.
- **Without H1.** The best pointwise bound is trivial or Burgess. Any proof of η < 1/4 at μ = 0.93 would be sub-Burgess
  at length q^{0.465}, and η < 1/6 would be beyond the bound that Weyl subconvexity gives.
- **At μ = 1.** Apply the target to the two weights V(x)x^{−½−it} of the approximate functional equation. Both pieces are
  plain sums at rows z and z̄. Then |X| ≤ Z^{3/8} gives |L(½+it,χ_z)| ≪ Z^{1/8+ε} for every z, which is sub-Weyl (Weyl
  would be 1/6).
- **Same picture for η > 0.** `strat_exponents.py`, Table 1, columns pw-bar and pw-bar unc.

## 3. S1: stratification by the rightmost zero (best partial result) [derived]

**Prop. 1.** Assume H1, H2 and H3. Then T_η(μ) holds with 2η(μ) = sup_{0≤ν≤κ} min(μν, ρ(ν) − 1 + 2μν).

**Proof.**
1. Split the rows into classes C_j = {ν_j ≤ 2β_z − 1 < ν_{j+1}}, with ν_j = jε′. By H1, j ≤ κ/ε′.
2. On C_j we have |A|² ≤ N^{1+ν_{j+1}}Z^{O(ε)} (Lemma L) and |C_j| ≤ Z^{ρ(ν_j)+ε} (H2).
3. So Σ_{C_j}|A|⁴ ≤ min(max_{C_j}|A|²·Σ_z|A|², |C_j|·max_{C_j}|A|⁴) ≤ Z^{O(ε)}·min(N^{1+ν_{j+1}}·ZN, Z^{ρ(ν_j)}N^{2+2ν_{j+1}}).
4. Sum over the O(1/ε′) classes. ∎

**Corollaries.**
- **Full target for μ ≤ 1/3.** ρ(ν) − 1 + 2μν = ν(2μ − 10/(15 − 6ν)) ≤ ν(2μ − 2/3) ≤ 0. H3 is not even needed.
- **Reduction.** T_η(μ) follows from H1, H3 and N_fam(σ) ≪ Z^{1+2η−2μ(2σ−1)} on σ ∈ (½ + η/μ, θ].
  - At η = 0 this needs a count below DH for every μ > 1/2.
  - At η = 0 and μ = 0.93 it needs no zeros at all with Re ≥ 0.769.
  - With DH counts, S1 gives T₀ for μ ≤ 1/2 and η(0.93) = 0.321.
- **Without H1** (the count caps ν at 15/16): η(0.93) = 0.372.

**Table** (η; `strat_exponents.py`, Table 1):

| μ | de Faveri | Hölder + Burgess | Hölder + H1 | **S1** | S1, DH count | barrier (Prop. 2) |
|---|---|---|---|---|---|---|
| 1/3 | 0.028 | 0.167 | 0.124 | **0** | 0 | 0 |
| 0.5 | 0.083 | 0.250 | 0.187 | **0.042** | 0 | 0 |
| 0.6 | 0.167 | 0.295 | 0.224 | **0.097** | 0.075 | 0.083 |
| 0.75 | 0.292 | 0.344 | 0.280 | **0.205** | 0.187 | 0.192 |
| 0.87 | 0.392 | 0.367 | 0.325 | **0.295** | 0.276 | 0.290 |
| 0.93 | 0.442 | 0.375 | 0.347 | **0.340** | 0.321 | 0.338 |
| 1.0 | 0.500 | 0.375 | 0.373 | **0.373** | 0.373 | 0.373 |

All entries except de Faveri use H3. The Hölder + Burgess column is the unconditional comparison, provided Burgess holds
over Z[ω].

## 4. Prop. 2: S1 is the end of the current inputs [derived, model]

**The adversary.**
- Take the round-9 two-term model L ≈ 1 + bU^{−s(w−a)}, with a = (1+ν)/2 and spacing s ∈ [1/4, 1/2] (`round9/README.md`).
- Its Möbius blocks are saturated at ks, its plain block at s, and nothing else.
- Let Z^{c} rows follow it, with c = min(1 − 2νs, 1 − ν·s⌊1/s⌋, (1+5y)/6 − νy at y = s⌈1/s⌉, ρ(ν)). These are the P, I and
  L lines and H2.

**Consistency with the inputs** (μ = 0.93, s = m = 0.465, ν = κ, c = 0.2873; `strat_exponents.py` checks each):

| input | adversary | bound |
|---|---|---|
| H3, length m | 1.912 | 1.930 |
| dF, 4th / 6th / 8th moment | 1.912 / 2.724 / 3.536 | 2.073 / 2.891 / 3.743 |
| Bu, \|X\|²/M | 0.347 | 0.375 |
| H2 | 0.287 | 0.290 |

- H1 and Lemma L hold by construction: the zeros sit on Re = a ≤ θ.
- PR 93's joint count (DH strength for slot slope > 1/2) does not apply. The model's −L′/L is supported on n ≈ U^{ks}, so
  its prime sums at slot lengths below s cancel and its rows are not slot-selected.

**Eighth moment.**
- With s = m its rows have |X|² = M^{1+ν}, so Σ|A|⁴ ≥ Z^{c}N^{2+2ν}, i.e. 2η ≥ c − 1 + 2νμ.
- At μ = 0.93: 2η ≥ 0.6764 (η = 0.338), against S1's 0.6791. The two-frequency model gives the same 0.2873.
- Table 1b: η_adv = 0 for μ ≤ 1/2. It is 0.017 at 0.52, 0.083 at 0.6, 0.192 at 0.75 and 0.373 at 1.
- With every count capped at 1 − ν (DH) it is still 0.015 at μ = 0.52 and 0.321 at 0.93.
- Mechanism: a DH count Z^{1−ν} of rows whose plain block is Littlewood-saturated leaves the excess ν(2μ − 1).

**What can break it.** The proof must use an input this model violates:
- (a) a sixth moment past the row count with ε₆ < 0.329 at m = 0.465 (S3);
- (b) an edge count R(κ) below the model's 0.287 (S4);
- (c) a pointwise bound below Littlewood for rows whose zeros sit near the edge;
- (d) an argument against two-term resonance on many rows at once, i.e. one that uses the Euler product.

## 5. S2: plain vectors in the Heath-Brown/de Faveri recursion (within the row count)

This is the only route to T₀ for 1/3 < μ ≤ 1/2 that needs no zero-density input. The barrier allows T₀ there.

**Chain** (b = W₁ * ⋯ * W_r plain, length L = ΠN_i; the eighth moment is r = 4, L = N²):
1. **Positivity.** Extend the rows to all z with a smooth weight [standard].
2. **Reciprocity and Poisson in z modulo nn′.** The diagonal, nn′⁵ ∈ K^{*6}, is Z‖b‖²(1 + o(1)): sixth-power
   coincidences are rare. Here thinness costs nothing [derived].
3. **CRT plus reciprocity.** The Gauss sum is ±g(k,n)·conj g(k,n′), because the cross factor (n′/n)₆·conj (n/n′)₆ is a
   sign. Off-diagonal ≈ (Z/L)·Σ_{0<N(k)≤K}|G_b(k)|², with K = L²/Z and G_b(k) = Σ_n b_n g̃₆(k,n) [derived].
4. **Where the main terms sit.** Write k = k₀j⁶; rows with small k₀ have multiplicity (K/N(k₀))^{1/6}.
   - For general b aligned with conj g̃, these rows give (Z/L)K^{1/6}L² = Z^{5/6}L^{1/3}‖b‖². That is de Faveri's
     A^{5/6}B^{1/3} term, which Xu–Sang show is attained.
   - The generic rows recurse, with the vector b·g̃, into the dual term A^{1/3}B^{5/6} [derived].
5. **Plain b.** Assume **Lemma P_r**: G_b(k) = M_b(k) + O(L^{1/2+ε}N(k)^{1/4+ε}), with Σ_{N(k)≤K}|M_b(k)|² ≪ L^{4/3}K^{1/6+ε}.
   - The main terms give Z^{5/6}L^{2/3} ≤ ZL.
   - The errors give Z·K^{3/2} = L³Z^{−1/2} ≤ ZL iff L ≤ Z^{3/4}.
   - So the plain large sieve is diagonal for L ≤ Z^{3/4}, which gives T₀(μ) for μ ≤ 3/8 unconditionally.
   - With an error O(L^{1/2+ε}N(k)^{ε}) it is diagonal for L ≤ Z, i.e. μ ≤ 1/2 [derived; the bookkeeping of
     non-squarefree n and k is not done].
6. **New step: P_r for r = 4.**
   - The case r = 1 is Kubota–Patterson: the pole at s = 2/3 of the sextic Kubota series.
   - For r ≥ 2, twisted multiplicativity gives cubic cross-symbols (n_i/n_j)₃ = (n_i/n_j)₆² (a sextic symbol squared).
     Absorbing them into the frequency, g₆(k,n)(m/n)₃ = g₆(km⁴, n), inflates N(k) to N(k)L⁴ and destroys the error term.
   - So P_r needs the type-A_r Weyl-group multiple Dirichlet series on the 6-fold cover (Brubaker–Bump–Friedberg) and its
     convexity bound.
   - By DH (`lean/arvi_primeface/Duplication.lean`), the squarefree part is a cubic series twisted by the angular
     character J(χ², χ²)/√p and the quadratic Gauss sign.
   - That angular K-type removes the cubic Patterson pole (`LOG.md`, "its Patterson pole is absent here because α is a
     nontrivial K-type"). So M_b lives on the sixth-power multiplicities, as step 4 needs [conjecture].

**Side effects if P_r holds.**
- It gives the three-plain moment at c_S = 1 (barrier table; about 9e-5 per `mixed-slots/`).
- It gives a DH-strength count near σ = ½, which by Prop. 1 pushes S1's full-target range from μ ≤ 1/3 to μ ≤ 1/2.

**Limit.** S2 cannot go past the row count at η = 0 (Prop. 0). Dunn–Radziwiłł-type corrected sieves (arXiv 2109.07463,
abstract read: conditional on GRH) live in the same range B ≤ A^{c}, c < 1. Plain vectors are their Type-I case, where the
main terms come from Kubota series and no GRH is needed.

## 6. S3 and S4: the two quantitative new inputs

**S3 (sixth moment past the row count).**
- Bound Σ|X|⁸ ≤ max|X|²·Σ|X|⁶ with H1 for the sup: 2η = ε₆ + κμ/2.
- At m = 0.465 this beats S1 iff ε₆ < 0.332, and gives η ≤ 1/4 iff ε₆ ≤ 0.153.
- ε₆ = 0.153 is pointwise-consistent: |X|²/M ≤ Z^{0.384} > M^κ = Z^{0.347}. So S3 at that strength is a pure
  large-values statement and needs no pointwise progress.
- It is weaker than D4's target (ε₆ ≤ 0.10, `directions.md`). D4 would therefore imply η(0.93) ≤ 1/4.
- de Faveri gives only ε₆ = 0.496, which is worse than the N-term level 0.395. The adversary has ε₆ = 0.329.

**S4 (edge count).**
- S1 gives η(0.93) ≤ 1/4 iff R(ν) ≤ 1.5 − 1.86ν on [0.538, κ]. That means 0.384 at ν = 0.6 (XS: 0.474), 0.198 at 0.7
  (0.352) and 0.111 at κ (0.290).
- The model's count at the edge is set by the long line at y = 3m = 1.395. Bringing it to 0.111 needs the amplified
  exponent (1 + 5y)/6 = 1.329 lowered to 1.154. That is λ = 0.611 in U + D^{1−λ}U^λ; the project's bar is 0.168.
- DH (0.253 at the edge) is not enough either. S4 is hopeless.

## 7. Dead routes (with the number that kills each) [derived]

- **Multiple Dirichlet series / moments of L(½,χ_z).**
  - At μ ≈ 1 the target is the eighth moment of L, i.e. 8 natural columns. The plain fourth moment is already the affine
    D̃₄ (`LOG.md`, FE-group table); eight columns are far into the hyperbolic regime.
  - Prop. 0 makes it sub-Weyl at μ = 1.
  - Even the quadratic analogue Σ_d|L(½,χ_d)|⁸ ≪ D^{1+ε} is known only under GRH, e.g. by Soundararajan's method [read:
    my knowledge; Gao–Zhao arXiv 2508.14534 (abstract read) is also under GRH].
- **Amplification.**
  - To beat max|A|² ≤ N^{1+κ} at one row, the amplifier must have length > 1 − κμ = 0.305 at μ = 0.93.
  - The best conceivable face (μ + s ≤ 1) allows 0.07.
  - Thin families have no neighbours: the off-diagonal characters χ_zχ̄_z′ have conductor Z², and the sums have length
    ≤ Z^{0.93}, outside the range where Burgess saves enough.
- **Kuznetsov / spectral.** Every off-diagonal is a Gauss sum S(r,0;c), never S(m,n;c) (`LOG.md`). There is no
  Kuznetsov formula on the 6-fold cover. Past the row count a spectral bound would also have to be pointwise (Prop. 0).
- **Thinness / sixth-power coincidences.** They fix the diagonal (§5, step 2). But with square-root cancellation in the
  Poisson dual the off-diagonal is (Z/N²)(N⁴/Z)N² = N⁴, exactly the N-term. One needs cancellation beyond square root on
  the dual vector b·g̃, which is the original problem again (Poisson twice is the identity, `lean-lab/FEGroup.lean`).
- **Root-number first moment.** Writing |A|² = (N/N𝔣)ε̄_z²·X₁Ỹ₁X₂Ỹ₂ turns Σ|A|⁴ into a first moment of ε̄_z² against a
  length-Z^{3.86} polynomial. Heath-Brown–Patterson-type savings then need conductor ≤ Z^{2}: none.
- **Hölder / pointwise.** These are at most the zero-free Hölder bound, 0.347. S1 is their correct generalization.
- **Probabilistic decoupling.** The rows are deterministic. Decoupling X₁ from X₂ is just Cauchy–Schwarz to the balanced
  case.

## 8. Consequences for D1

- The dispersion inequality needs η = 0 exactly: Δ ≥ Z, so the face carries the s-independent excess Z^η.
- By Props. 0 and 2, η = 0 on the window μ ∈ [0.75, 0.87] needs a new pointwise or super-density input, while S1 gives
  0.21–0.30.
- The eighth moment is at least as strong as moving the project's pointwise plain bound from κ = 0.747 to
  1/(2μ) = 0.57–0.67. **Recommendation:** deprioritize D1-by-eighth-moment.

**Side remark** [derived; pricing left to the project's model].
- The same stratification applied directly to F = Σ|A|²|Q|² uses |Q|² ≤ ‖a‖²Z^{sν} on class ν (explicit formula). The
  excess is ℓ(μ,s) = sup_ν min(sν, ρ(ν) − 1 + (μ+s)ν).
- On the window this is 0.044 at (μ,s) = (0.76, 0.14) and 0.080 at (0.865, 0.14). That is below the H1-pointwise pool
  loss κs = 0.105, and below Dismissed.lean's Hölder loss 2sκμ (Table 2).
- It is diagonal only for μ + s ≤ 2/3, so it gives no new diagonal face.
- With S1, the Hölder-decoupling route of `lean/arvi_primeface/Dismissed.lean` has effective τ = 0.23–0.29 at μ = 0.76.
  That is below the 1/2 threshold, but there is no gain at μ = 0.865.

## 9. Numerics (`strat_tail.py`, same family and weights as `eighth_probe.py`) [numerical]

| B (= Z) | μ | κ₈ (reproduces `eighth_1.log`) | max\|A\|²/mean | Z^{1/2} | share of Σ\|A\|⁴ in top 1% of rows |
|---|---|---|---|---|---|
| 3·10⁴ | 0.93 | 6.06 | 34 | 173 | 0.52 |
| 10⁵ | 0.93 | 6.76 | 57 | 316 | 0.54 |
| 3·10⁵ | 0.93 | 7.44 | 82 | 548 | 0.58 |
| 3·10⁵ | 1.00 | 7.12 | 94 | 548 | 0.57 |

- The pointwise condition of Prop. 0 holds in the data with a margin of about 6.
- The eighth moment is a large-values quantity even numerically: the top 1% of rows carry 42–58% of it for μ ≥ 0.6.
- The multiplicative surrogate has heavier tails (max/mean up to 157).
- Numerics cannot rank the strategies: the S1/adversary rows (zeros off the line) do not occur at these sizes.

## 10. Lean 4 / Mathlib candidates

All are in exponent form, like `arvi_primeface/Dismissed.lean` and `Exponents.lean`.
1. **Prop. 0.**
   - Statement: for b : ι → ℝ≥0 on a Fintype, Σ b² ≤ C gives b z ≤ √C.
   - Exponent corollary: if 1 + 2η + 2μ bounds log_Z Σ|A|⁴, then log_Z|A z|² ≤ 1/2 + η + μ for every z.
   - Window lemma: (3/4)·κ′ > 1/2 with κ′ = 3739558/5000000. One line of norm_num.
2. **Class-sum lemma** (Finset). Suppose the rows are partitioned by cls : ι → J, with #cls⁻¹(j) ≤ c j, g ≤ M (cls z)
   and Σ g ≤ S. Then Σ g² ≤ Σ_j min(M j·S, c j·M j²).
3. **S1 exponents.**
   - ρ(ν) − 1 + 2μν ≤ 0 for μ ≤ 1/3 and ν ∈ [0, 1] (nlinarith after clearing 15 − 6ν > 0).
   - The reduction R ν ≤ 1 + 2η − 2μν implies min(μν, R ν − 1 + 2μν) ≤ 2η.
   - min(…) ≤ 0.68 on [0, κ] at μ = 93/100, by a case split at the crossing.
4. **Barrier arithmetic.** At ν = κ and s = 93/200: c = (1 + 15s)/6 − 3sκ < min(1 − 2κs, ρ(κ)), and c − 1 + 2κμ > 0.676.
5. **Lemma L.** Abstract form: f analytic and zero-free on {Re > σ₁, |Im − t₀| < 3}, with |f| ≤ e^{H} there and
   |log f(2 + it₀)| ≤ C, gives |log f(σ + it₀)| ≤ C_ε H^{1−c_ε}.
   - Mathlib (local checkout) has `Complex.borelCaratheodory`
     (`Mathlib/Analysis/Complex/BorelCaratheodory.lean`), three lines
     (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`), and the logarithm of a zero-free function
     on a simply connected open set (`exists_continuousOn_eqOn_exp_comp`, `BranchLogRoot.lean`).
   - Three circles has to be derived from three lines through exp. Medium effort.

Items 1–4 together with Lemma L as a hypothesis give a formal reduction: (H1, H2 as a function bound, H3, Lemma L) ⟹
T_η(μ) with the S1 exponent.

## 11. Files

- `strat_exponents.py`: Table 1 (all routes), Table 1b (adversary for all μ, with XS and DH caps), the adversary's
  consistency checks, the requirements for η ≤ 1/4, Table 2 (twisted-moment side remark) and Table 3 (counts S1 needs).
  Runs in about 2 s.
- `strat_tail.py --B 30000 100000 300000 --mu 0.6 0.8 0.93 1.0`: the §9 table. Runs in about 13 s.
