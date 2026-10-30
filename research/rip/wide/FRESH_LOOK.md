# Fresh look: randomized dictionaries for the K-wall (agent report, 2026-10-30)

Brief: RIP program (4). Arvi's proposal is a randomized dictionary of *different*, wide atoms whose RIP holds on
a positive measure of operators and which is tied to the sextic rows by coherence bounds.

Files:
- scripts `wide_tests.py` (the runs) and `wide_tables.py` (the §3 tables), in this directory;
- results `wide_B*_s*.json`, here;
- run logs in `$SCRATCH/wide/` (regenerable, with the seeds in the file names).

The other files here (`README.md`, `wide_probe.py`, `wide_B3000_L3000.log`) belong to the wide-features run and
are untouched. Evidence tags are as in the journal.

**Notation.**
- Rows z ∈ F (R of them); sources n ≤ L (S of them).
- G is the row Gram, G_W its restriction to W, D_W = diag(G_W).
- ρ_W = D_W^{−1/2} G_W D_W^{−1/2} has unit diagonal, and E_W = ρ_W − I.
- |W| = B^{1−δ} with δ ∈ [0.45, 0.48].
- The target is ‖G_W‖ ≤ B^γ L, with γ ≈ 0.015 at the corner.

## 0. Bottom line

1. **No randomized dictionary can carry the degree-1 part across by coherence (§1).** Four small transfer
   lemmas, each elementary and formalizable:
   - cross-coherence carries no information;
   - a factorization tie is a Gram domination (Douglas);
   - a Gram mixture satisfies Jensen in the *right* direction, but with independent rows it collapses to its
     mean dictionary;
   - a product (tensor) certificate is never better than plain Gershgorin on the rows. This sharpens
     `TensorAmplify`.

   The "other data of the row" fare no better. After Poisson, the row Gauss sums enter only as a diagonal
   unitary, and the pair-dependent phase is a reciprocity sign of bounded complexity. So at L = B the
   off-diagonal Gram is its own conjugate, up to O(1) residue classes (§1.5). [derived]
2. **What does transfer is a fixed-order moment, and the useful order is four, centered (§1.6).**
   - On the fixed support W, tr(E_W⁴) ≤ B^{4γ} implies the target.
   - This bound has room exactly when δ > 1/3, which is the whole range of the `arvi_kwall` barrier
     (1/3 ≤ δ < 1/2).
   - Mean-square coherence (order 2) is exactly the √-barrier.
   - Uncentered traces need order ≈ (1 − δ)/γ ≈ 35.
3. **Best design: D1 (§2).** The slot-conditioned random multiplicative dictionary proves the fourth-moment bound
   in the model, with margin B^{3δ−1}. Its chain to the sextic rows needs one inequality:

   **(M₄)**  Σ_{z₁,z₃∈W} | Σ_{z₂∈W∖{z₁,z₃}} G(z₁,z₂) G(z₂,z₃) |² ≤ B^{4γ} L⁴,

   i.e. the two-step correlations of the off-diagonal Gram on W are small (‖(G_W − D_W)²‖_F ≤ B^{2γ}L²).
   - Square-root pointwise coherence (GRH strength) gives (M₄) only for δ ≥ 1/2 − γ ≈ 0.485.
   - At the binding δ ≈ 0.452, the non-backtracking 4-cycles must cancel by a further B^{0.13}.
4. **Numerics (§3) [numerical].** B = 3000 and 12000, slot-selected W with |W| between B^{0.47} and B^{0.67}.
   - **The (M₄) quantity sits at the random-matrix scale.** tr(E_W⁴) is within a factor 0.93–1.6 of 2|W|³/S². The
     excess is the slot spike, which the model shares: sextic/model lies in 0.77–1.08.
   - **Row mean-square coherence on W is |W|/S on average** (0.96–1.24 times that; the maximum is at most twice).
   - **The 4-cycles cancel to 0.08–1.4% of their no-cancellation size.**
     - They match the model at B = 12000, for 10 and for 20 slot primes.
     - At B = 3000 with 14 slot primes of norm 80–160 they reach about 2× the model (2–2.6σ). That excess does not
       recur at B = 12000.
   - **The top eigenvalue stays within ±4% of the slot-conditioned multiplicative model.** The sign depends on the
     slot.
   - **i.i.d. "wide" modulations are not a safe comparison class.** The model with the quadratic part exact times
     i.i.d. cube roots (a random Schur multiplier) sits 1.6–4% below every multiplicative model. In 11 of 16 cases at
     B = 3000 the sextic is above 90% of its samples.
5. **Framing (§4).**
   - The object that needs control is the centered two-step correlation (G_W − D_W)², not a dictionary.
   - The assumption that would make this easy if false is that W is cut out by the same Frobenius data as the
     rows. What is needed is only *fourth-order* decorrelation between W and the Gram.
   - Every pairwise certificate (degree ≤ 2 in the rows: coherence, products, amplify–reflect, kernels κ(G)) stops
     at |W| ≲ √L. Centered moments cannot take the amplifier majorant, which is why amplify–reflect stalls.

## 1. What a random dictionary can transfer [derived]

### 1.1 Cross-coherence carries no information

Let x_z (z ∈ W) be unit vectors in ℂ^S whose entries all have modulus S^{−1/2} (the normalized rows, up to the
coprimality mask).
- The standard basis is orthonormal, so it has RIP constant 0 at every order.
- Its cross-coherence with the rows is S^{−1/2}, the minimum possible for an orthonormal basis (Parseval).
- So "D has RIP and is incoherent with the rows" holds for every such family. That includes families with
  ‖X_W‖² = |W| (all x_z equal).
- No bound on ‖X_W‖ follows. A tie must carry phases, not moduli.

The other readings of "coherence":
- self-coherence of the rows stops at √ (`coherence_order_barrier`);
- product coherence is §1.4.

### 1.2 A factorization tie is a Gram domination

**Douglas (1966).** X_W = A·Y_W with ‖A‖ ≤ c if and only if X_W^* X_W ≼ c² Y_W^* Y_W.
- So "the sextic atoms are a bounded image of random atoms" means ρ_W ≼ c² H_W for one realization H_W of the
  model Gram.
- For any model whose rows are independent given the slot data, H_W concentrates at I + Λ_W, where Λ_W is the
  low-rank slot-smooth Gram.
- Domination by I + Λ_W is the diluted-bias statement of RIP (1) itself.
- So a factorization tie is never weaker than the target.

### 1.3 Gram mixtures: Jensen goes the right way, independence kills them

- **(a) Dictionary mixtures.** If E_ω M_ω = M, then E‖M_ω a‖² ≥ ‖Ma‖² (Jensen): a mixture of dictionaries that
  averages to M never certifies less energy than M.
- **(b) Gram mixtures.** If E_ω M_ω M_ω^* = G, then ‖G_W‖ = sup_b E‖M_{ω,W}^* b‖² ≤ E‖M_{ω,W}‖², the right
  direction. Convexity does *not* rule these out. Random source sub-selection (E[M P_ω M^*]/ν = G) is one.
- **(c) Independent rows.** If the rows of M_ω are independent across z (needed for a positive-measure RIP
  proof), then for z ≠ z′, G(z,z′) = ⟨E u_z, E u_{z′}⟩.
  - The whole off-diagonal Gram is the Gram of the *mean* rows, so ‖G_W‖ ≤ L + ‖(mean dictionary)_W‖².
  - The randomness drops out.
  - For the slot-conditioned model, the mean rows live on slot-smooth sources, so the sextic Gram is *not* such a
    mixture.
  - With dependent rows (source sub-selection), a random-RIP theorem (Rudelson–Vershynin) needs G_W ≈ L·I as a
    hypothesis.

So dictionary mixtures fail by convexity, and Gram mixtures fail for a different reason: dependence or
mean-inducement.

### 1.4 Product certificates never beat plain Gershgorin (sharpens `TensorAmplify`)

Setup:
- x_z, y_z are unit vectors with pairwise coherence ≤ μ_x and ≤ μ_y on W;
- e is a unit vector with |⟨e, y_z⟩| ≥ w on W;
- m = |W| − 1.

Product Gershgorin plus `tensor_ge_amplified` certifies Σ_{z∈W} |⟨a,x_z⟩|² ≤ U_prod ‖a‖², with
U_prod = (1 + m μ_x μ_y)/w².

The y-Gram caps the detection: |W| w² ≤ Σ_W |⟨e,y_z⟩|² ≤ 1 + m μ_y. Hence

  U_prod ≥ (m+1)(1 + m μ_x μ_y)/(1 + m μ_y).

The right side decreases in μ_y. At μ_y = 1 it equals 1 + m μ_x = U_plain, the plain Gershgorin bound. **So
U_prod ≥ U_plain for every second factor and every detection vector.**

For slot monomials of width ks:
- μ_y = B^{−ks/2} and w² = B^{−(1−δ)ks};
- the optimum is ks = 0, because the amplification costs 1 − δ per unit of width and coherence gains only 1/2;
- the exponent (1 − δ)(1 − 2δ) in `TensorAmplify` is the choice ks = 1 − 2δ;
- that is worse than plain Gershgorin with square-root row coherence, which gives γ = 1/2 − δ.

Products relabel which coherence is assumed; they never certify more. The "bounded coherence" that matters is
the rows' own, inside W.

### 1.5 Gauss sums: the involution

Take coprime primary z, z′ and a smooth weight w. Poisson over Z[ω] (library
`canonical_compact_radial_poisson_normalized`) gives, up to bounded ramified twists,

  G_w(z,z′) = (L/√N(zz′)) · ε(z,z′) · Ğ(z,z′),   Ğ(z,z′) = Σ_h conj(χ_z(h)) χ_{z′}(h) ŵ(L N(h)/N(zz′)),

where Ğ is the *conjugate* Gram at dual length N(zz′)/L.

The phase ε(z,z′) is the normalized Gauss sum of χ_z χ̄_{z′}. It factors in two steps.
- By twisted multiplicativity (CRT), g(ψ₁ψ₂) = ψ₁(z′) ψ₂(z) g(ψ₁) g(ψ₂), and g(χ̄) = χ(−1) conj(g(χ)). This gives
  ε(z,z′) = (z′/z)₆ conj((z/z′)₆) · χ_{z′}(−1) · g̃(z) conj(g̃(z′)).
- By sextic reciprocity (Hilbert reciprocity), (z/z′)₆ = s(z,z′) (z′/z)₆. Here s = ±1 is a product of Hilbert
  symbols at the places above 2 and 3, so it depends only on z and z′ modulo a fixed power of 6.

So the pair factor is the sign s, not a residue symbol, and

  G_W − D_W = (L/√N(zz′)) · D_g̃ (S ∘ Ğ_off) D_g̃^*,   S(z,z′) = s(z,z′) χ_{z′}(−1)   (block-constant on O(1)
  classes).

Consequences:
- **Row Gauss sums drop out.** The g̃(z) form a diagonal unitary, which changes no restricted norm or spectral
  moment on a fixed W.
  - So Heath-Brown–Patterson equidistribution of Gauss sums, as a source of randomness, buys nothing.
  - RIP (4)'s escape (a) through Gauss sums is closed.
- **The involution.** At L ≈ B, split W into its O(1) classes. On each block, G_W − D_W equals ± its own conjugate
  Gram, up to the diagonal unitary, the weight change w → ŵ and the dyadic scale of N(zz′).
  - This is the reflection rule's self-duality as a matrix identity. Poisson maps any spectral statement about
    G_W − D_W at L = B to itself, so Poisson plus positivity stalls exactly there.
  - Random multiplicative models are not periodic and do not satisfy it.
- **Where the bias lives.** The known bias of the full family is the theta-type bias on the *source* side: source
  vectors correlated with the sources' own Gauss sums. It is not a property of pairs of rows, so no pair-level
  random phase can model or cure it.
- The other two forms of escape (a) are also closed:
  - the Archimedean factor N(n)^{−it} only ranges over B^ε heights, so it adds no randomness;
  - Frobenius data beyond L amounts to an amplifier of length ≥ B², i.e. the closure.

### 1.6 Fixed support: which moment, of which order

For a single W there is no union bound over supports. Two kinds of moment bound are available.

- **Uncentered.** tr(ρ_W^p) ≤ C|W| gives ‖ρ_W‖ ≤ (C|W|)^{1/p}, i.e. γ = (1 − δ)/p. At δ = 0.45:

  | p | γ | compared with the barrier 1/6 |
  |---|---|---|
  | 3 (GM-type order) | 0.18 | worse |
  | 4 | 0.14 | first to beat it |
  | 37 | ≤ 0.015 | reaches the target |

- **Centered.** In the random model, tr(E_W^{2q}) ≈ Cat_q |W|^{q+1} L^{−q} (Marchenko–Pastur near 0). A bound
  C_q B^ε |W|^{q+1} L^{−q} gives ‖E_W‖ ≤ (C_q B^ε |W|)^{1/(2q)} √(|W|/L), which is o(1) once
  |W| ≤ L^{q/(q+1) − ε}.
  - q = 1 (mean-square coherence) certifies |W| ≲ √L: the barrier.
  - **q = 2 certifies |W| ≲ L^{2/3}, i.e. every δ > 1/3.** Only tr(E_W⁴) ≤ B^{4γ} is needed. The model value is
    ≈ 2|W|³/L² = 2B^{1−3δ}, so the slack is B^{3δ−1+4γ}, about B^{0.41} at δ = 0.45.
  - At every order 2q, the closed-walk sum needs a saving of B^{1/2−δ−γ} *per step* beyond square-root coherence.
    The order changes the slack, not the per-step price.

## 2. Designs, ranked

### D1 (most promising): slot-conditioned multiplicative dictionary, certified by the centered fourth moment

**1. Atoms.**
- For each row z and each split prime ideal π with N(π) ≤ L, set v(z,π) = χ_z(π) if π is a slot prime or π | z.
  Otherwise v(z,π) is an independent uniform sixth root of unity.
- The row is u_z(n) = χ_z(−1)^{ω(n)−1} ∏_{π|n} v(z,π). A primary source is n = (−1)^{ω(n)−1} ∏ π, which the script
  checks against the direct symbols.
- Each atom is a random completely multiplicative function on all sources: wide, not localized in frequency.
- The slot values are exact, so T and W are literally the same sets.
- A variant, BRM-S, randomizes (π/ρ)₆ per row prime ρ instead of per row, so rows that share prime factors stay
  correlated, as in the family.

**2. RIP by positive measure (model) [derived; standard tools].**
- Given the slot σ-algebra, the rows are independent. E[u_z u_z^*] is block-diagonal over rough parts, and its
  slot-smooth blocks carry the slot's own large values. That is the fixed-point term |W|·(slot energy), which is
  ≈ L at L = B.
- E[tr(E_W⁴) | slot data] is an exact walk count: a closed 4-walk contributes only if each row's two steps have
  equal rough parts. So it is ≤ C(|W|³/L² + tr((Λ_W/L)⁴)), with Λ_W the slot-smooth mean. The second term is the
  fourth moment of the slot's own large values; at the fixed point it is B^{o(1)}. [sketch]
- By Markov, at least half of all assignments have ‖E_W‖ ≤ (2 E tr)^{1/4} = B^{o(1)} for δ > 1/3.
- There is no union bound and no matrix exponential. In the counting style of `RandomRIP.lean`, this is a
  Füredi–Komlós walk count plus `card_filter_le_sum_div` (already in `WideFeatures.lean`).
- Conditional Hoeffding with flat RIP (`RandomRIP.lean`) does *not* transfer here: its entries are independent
  signs, while a row here is a multiplicative chaos (a product over the prime factors of each source). The moment
  route avoids it.

**3. Arithmetic input: (M₄) [conjecture].** For W selected by the slot at slope δ ∈ (1/3, 1/2), with
L ≤ B^{1+o(1)}:

  Σ_{z₁,z₃∈W} |Σ_{z₂∈W∖{z₁,z₃}} G(z₁,z₂) G(z₂,z₃)|² ≤ B^{4γ} L⁴.

- **Fourier form.** It equals Σ_{n₁..n₄ ≤ L} ∏_i Ŵ(n_i/n_{i−1}) minus diagonal terms, with
  Ŵ(n/n′) = Σ_{z∈W} χ_z(n) χ̄_z(n′). So it is a multiplicative energy of order 4 for the Fourier transform of W on
  source ratios.
- **Sizes.**
  - Model value: ≈ 2|W|³L² = 2B^{1−3δ} L⁴.
  - Square-root pointwise coherence alone gives |W|⁴L² = B^{2−4δ} L⁴, enough only for δ ≥ 1/2 − γ.
- **(M₄a), the backtracking part.**
  - It needs row mean-square coherence on W: Σ_{z′∈W} |G(z,z′)|² ≤ B^{2γ} L² |W|^{−1/2}, against a model value of
    |W|L (slack B^{(3δ−1)/2}).
  - This is RIP (1)'s twisted-form decorrelation, restricted to the |W| test vectors a = χ̄_z. Amplification
    cannot give it: lengthening past L = B creates the N-term.
- **(M₄b), the non-backtracking 4-cycles.** At δ = 0.452 they must cancel by B^{0.13} beyond square-root coherence.
- **Status.**
  - Nothing at this strength is known for thin families with multiplying conductors.
  - Guth–Maynard bound an order-3 trace through an energy estimate for the large-value set, in the additive group
    of frequencies. (M₄) is the order-4 centered analogue in the multiplicative group of source ratios.
  - (M₄) is a spectral statement about G_W − D_W, so the §1.5 involution maps it to itself, and Poisson cannot
    reduce it to anything easier.
  - Centered moments are not monotone in the rows (§4), so the slot amplifier cannot be inserted either.

**4. Chain to the sextic rows (checked for circularity).**
1. ‖G_W‖ ≤ max_z G(z,z) + ‖G_W − D_W‖ ≤ L + tr((G_W − D_W)⁴)^{1/4}.
2. (M₄) bounds this by L(1 + B^γ).
3. Hence Σ_{z∈W} |Σ_n a_n χ_z(n)|² ≤ 2B^γ L ‖a‖² at L = B.
4. Amplification gives the corner X_eff ≈ 0.96, as `Dilution.lean` does from n(1) ≤ 1.
5. For the zero count directly: R ⊂ W, and E_R is a principal submatrix of E_W, so ‖E_R‖ ≤ ‖E_W‖. The
   Halász–Montgomery count |R|U² ≤ ‖a‖²(L + ‖G_R − D_R‖) inherits the bound.

The chain is not circular.
- (M₄) is a single finite sum over W⁴ and assumes no operator bound.
- It is *stronger* than the target: the target implies (M₄) only with an extra factor |W|. That is the price of
  any moment certificate.
- The random dictionary is not a step in the chain. It supplies:
  - the proof that the certificate is sharp for model-typical W;
  - the calibration of (M₄), with slack B^{3δ−1}.

  By §1, nothing more can be asked of it.

**5. Numerics.** §3, tables A–C.

**6. Lean plan (Mathlib only, counting style).**
- (i) `moment_cert`: for Hermitian E, ‖E‖⁴ ≤ tr(E⁴). For a PSD Gram with diagonal ≤ L,
  ‖G_W‖ ≤ L + tr((G_W − D_W)⁴)^{1/4}.
- (ii) `walk_count`: in the counting measure over assignments v : W × (non-slot primes) → ZMod 6, the sum of
  tr(E_W⁴) is the number of row-balanced closed 4-walks. Prove this and bound it.
- (iii) Markov via `card_filter_le_sum_div`.
- (iv) The §1 lemmas:
  - cross-coherence: a two-line example;
  - Douglas, in finite dimension;
  - Gram mixtures with independent rows;
  - `product_ge_plain` (§1.4), from `gershgorin_rip` and the detection cap.

  Each is short. Together they record that the transfer must go through (M₄).

### D2: Hadamard-split hybrid (quadratic part exact, cubic part random)

- **Atoms.** y_z = q_z ⊙ ω_z, where q_z = (·/z)₂ is exact and ω_z is a random cubic multiplicative function,
  exact at the slot primes. Recall χ₆ = χ₂ χ̄₃.
- **RIP.** The rows are independent, and matrix Chernoff gives the fixed point. The quadratic family is provably
  diagonal for all vectors: Heath-Brown, Acta Arith. 72 (1995), over ℚ; Goldmakher–Louvel (2013) over number
  fields. [derived]
- **Tie.** M₆,W = M₂,W ∘ conj(M₃,W): the sextic is the hybrid at ω = cubic. The missing inequality is "the cubic
  residue matrix acts on M₂,W like a random Schur multiplier". That is *equivalent* to the target: a reformulation,
  not a reduction.
- **Value.** It places the difficulty in the cubic half of the atoms. The quadratic half is provably harmless.
- **Numerics.**
  - Keeping the quadratic half exact changes nothing: HYB tracks RMM-S within noise.
  - The i.i.d. Schur model (SCHUR, the Bandeira–van Handel / Latała–van Handel–Youssef regime, where its RIP is a
    theorem) sits 2–4% below every multiplicative model. The sextic exceeds it at 3–5σ for 10 or 14 slot primes and
    is comparable to it with 4 slot primes.
  - So a transfer theorem must compare with multiplicative models, not with "wide i.i.d." ones.

### D3: product (tensor) designs

By §1.4 these are dominated by plain Gershgorin. With square-root row coherence on W, the best they give is
γ = 1/2 − δ, which reaches 0.015 only at δ ≥ 0.485. That coherence is GRH strength for character sums of length B
and conductor B², which a zero-density argument cannot assume. Recommendation: retire products as certificates
and keep them only as bookkeeping for amplification.

### D0: wide features of degree ℓ ≥ 2 (RIP (4))

- Confirmed here (B = 3000, every tested W and L): the Hadamard powers satisfy ‖ρ_W^{∘m} − I‖ ≤ 0.14 for m = 2
  and ≤ 0.011 for m ≥ 3, against 0.3–2.5 for m = 1. Sextic and models agree.
- Degree 2 is provably diagonal (Θ₆ at length L²).
- §1.3(c) and §1.4 show the degree-1 part cannot be reached this way.

## 3. Numerics [numerical]

`python3 -I wide_tests.py B L P0 nsamp seed models hadamard rho-list`. Settings:
- W is the top ρR rows by |T|, with T summed over split slot primes of norm in [P0, 2P0], as in `../zfamily.py`.
- Grams are unit-diagonal normalized.
- The factorized sextic table is checked against direct symbols on every run.
- "P(model ≥ sextic)" is the fraction of model samples whose top eigenvalue is at least the sextic one.

Runs behind the tables (each B = 3000 run takes about 1–2 min, each B = 12000 run about 5 min, on 4 shared cores):
- `wide_tests.py 3000 3000 P0 30 4P0 RMM,BRM,SCHUR 0 0.25,0.1,0.075,0.05`, for P0 = 20, 40, 80;
- `wide_tests.py 3000 2160 40 30 51 RMM,BRM,SCHUR 0 0.25,0.1,0.075,0.05`;
- `wide_tests.py 12000 12000 40 12 52 RMM,BRM 0 0.15,0.04,0.015`;
- `wide_tests.py 12000 12000 100 10 53 RMM 0 0.04,0.015`.

The Hadamard powers (D0) and the HYB model (D2) come from first-pass runs with `hadamard = 1` and model HYB, at
L ∈ {2160, 3000, 6000} and B = 12000 (logs in `$SCRATCH/wide/v1/`).

**Table A: typicality of the sextic rows on slot-selected W (top eigenvalue of the unit-diagonal Gram).**

| B | L | P0 (slot primes) | \|W\| | log_B\|W\| | sextic | MP edge | random W | RMM-S | P(RMM ≥ sextic) | BRM-S P | i.i.d. Schur | P(Schur ≥ sextic) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 3000 | 2160 | 40 (10) | 212 | 0.67 | 2.661 | 2.663 | 2.574 ± 0.021 | 2.600 ± 0.031 | 0.03 | 0.07 | 2.557 ± 0.032 | 0.03 |
| 3000 | 2160 | 40 (10) | 84 | 0.55 | 1.904 | 1.950 | 1.886 ± 0.030 | 1.917 ± 0.029 | 0.63 | 0.67 | 1.861 ± 0.025 | 0.07 |
| 3000 | 2160 | 40 (10) | 63 | 0.52 | 1.770 | 1.804 | 1.717 ± 0.023 | 1.773 ± 0.031 | 0.60 | 0.53 | 1.718 ± 0.024 | 0.00 |
| 3000 | 2160 | 40 (10) | 42 | 0.47 | 1.542 | 1.644 | 1.568 ± 0.028 | 1.602 ± 0.033 | 1.00 | 1.00 | 1.562 ± 0.023 | 0.73 |
| 3000 | 3000 | 20 (4) | 212 | 0.67 | 2.377 | 2.356 | 2.285 ± 0.027 | 2.350 ± 0.030 | 0.23 | 0.23 | 2.271 ± 0.031 | 0.00 |
| 3000 | 3000 | 20 (4) | 84 | 0.55 | 1.736 | 1.789 | 1.720 ± 0.014 | 1.786 ± 0.032 | 0.97 | 1.00 | 1.719 ± 0.019 | 0.17 |
| 3000 | 3000 | 20 (4) | 63 | 0.52 | 1.615 | 1.671 | 1.604 ± 0.020 | 1.669 ± 0.031 | 0.97 | 1.00 | 1.600 ± 0.023 | 0.27 |
| 3000 | 3000 | 20 (4) | 42 | 0.47 | 1.483 | 1.536 | 1.456 ± 0.022 | 1.529 ± 0.029 | 0.97 | 0.97 | 1.470 ± 0.020 | 0.27 |
| 3000 | 3000 | 40 (10) | 212 | 0.67 | 2.352 | 2.360 | 2.282 ± 0.016 | 2.312 ± 0.027 | 0.07 | 0.03 | 2.271 ± 0.018 | 0.00 |
| 3000 | 3000 | 40 (10) | 84 | 0.55 | 1.783 | 1.786 | 1.716 ± 0.023 | 1.759 ± 0.020 | 0.13 | 0.20 | 1.717 ± 0.021 | 0.00 |
| 3000 | 3000 | 40 (10) | 63 | 0.52 | 1.633 | 1.667 | 1.606 ± 0.022 | 1.647 ± 0.019 | 0.73 | 0.87 | 1.598 ± 0.022 | 0.10 |
| 3000 | 3000 | 40 (10) | 42 | 0.47 | 1.479 | 1.536 | 1.478 ± 0.019 | 1.504 ± 0.021 | 0.87 | 0.87 | 1.462 ± 0.018 | 0.13 |
| 3000 | 3000 | 80 (14) | 212 | 0.67 | 2.381 | 2.353 | 2.287 ± 0.013 | 2.306 ± 0.022 | 0.00 | 0.00 | 2.268 ± 0.022 | 0.00 |
| 3000 | 3000 | 80 (14) | 84 | 0.55 | 1.812 | 1.782 | 1.723 ± 0.021 | 1.761 ± 0.026 | 0.03 | 0.00 | 1.718 ± 0.017 | 0.00 |
| 3000 | 3000 | 80 (14) | 63 | 0.52 | 1.685 | 1.665 | 1.598 ± 0.028 | 1.647 ± 0.025 | 0.03 | 0.03 | 1.601 ± 0.018 | 0.00 |
| 3000 | 3000 | 80 (14) | 42 | 0.47 | 1.504 | 1.531 | 1.471 ± 0.009 | 1.502 ± 0.028 | 0.47 | 0.43 | 1.465 ± 0.022 | 0.03 |
| 12000 | 12000 | 40 (10) | 506 | 0.66 | 2.040 | 1.994 | 1.959 ± 0.011 | 2.035 ± 0.014 | 0.50 | 0.17 | – | – |
| 12000 | 12000 | 40 (10) | 135 | 0.52 | 1.486 | 1.470 | 1.439 ± 0.006 | 1.518 ± 0.016 | 1.00 | 0.92 | – | – |
| 12000 | 12000 | 40 (10) | 50 | 0.42 | 1.303 | 1.277 | 1.249 ± 0.012 | 1.312 ± 0.013 | 0.75 | 0.42 | – | – |
| 12000 | 12000 | 100 (20) | 135 | 0.52 | 1.480 | 1.473 | 1.443 ± 0.007 | 1.471 ± 0.010 | 0.20 | – | – | – |
| 12000 | 12000 | 100 (20) | 50 | 0.42 | 1.260 | 1.277 | 1.246 ± 0.008 | 1.273 ± 0.010 | 0.90 | – | – | – |

**Table B: the centered fourth moment tr(E_W⁴) and its split (design D1, inequality (M₄)).**

| B | L | P0 | \|W\| | tr(E_W⁴) | 2\|W\|³/S² | sextic/RMM (q = 2) | backtracking: sextic / RMM | 4-cycles: sextic / RMM ± sd | 4-cycles / no-cancellation | row msq: mean, max / (\|W\|/S) |
|---|---|---|---|---|---|---|---|---|---|---|
| 3000 | 2160 | 40 | 212 | 81.2 | 67.7 | 1.05 | 64.2 / 63.4 | 17 / 13.7 ± 1.2 | 0.0044 | 0.97, 1.20 |
| 3000 | 2160 | 40 | 84 | 4.42 | 4.15 | 0.98 | 3.95 / 4.08 | 0.472 / 0.449 ± 0.11 | 0.0052 | 0.98, 1.26 |
| 3000 | 2160 | 40 | 63 | 1.72 | 1.75 | 0.92 | 1.63 / 1.73 | 0.0899 / 0.152 ± 0.052 | 0.0033 | 0.97, 1.29 |
| 3000 | 2160 | 40 | 42 | 0.515 | 0.533 | 0.93 | 0.506 / 0.52 | 0.00833 / 0.0359 ± 0.023 | 0.0015 | 0.97, 1.35 |
| 3000 | 3000 | 20 | 212 | 40.7 | 34.7 | 1.00 | 34.1 / 34.6 | 6.56 / 6.27 ± 0.58 | 0.0032 | 0.99, 1.18 |
| 3000 | 3000 | 20 | 84 | 2.34 | 2.18 | 0.93 | 2.21 / 2.29 | 0.134 / 0.22 ± 0.062 | 0.0027 | 1.01, 1.33 |
| 3000 | 3000 | 20 | 63 | 0.962 | 0.927 | 0.90 | 0.907 / 0.996 | 0.0556 / 0.0765 ± 0.031 | 0.0037 | 0.99, 1.33 |
| 3000 | 3000 | 20 | 42 | 0.259 | 0.276 | 0.77 | 0.249 / 0.315 | 0.0105 / 0.0205 ± 0.013 | 0.0042 | 0.96, 1.24 |
| 3000 | 3000 | 40 | 212 | 39.7 | 35.1 | 1.04 | 33.4 / 32.9 | 6.34 / 5.34 ± 0.5 | 0.0032 | 0.98, 1.18 |
| 3000 | 3000 | 40 | 84 | 2.35 | 2.15 | 1.02 | 2.04 / 2.13 | 0.308 / 0.173 ± 0.045 | 0.0066 | 0.97, 1.26 |
| 3000 | 3000 | 40 | 63 | 0.915 | 0.907 | 0.94 | 0.859 / 0.915 | 0.0558 / 0.0602 ± 0.022 | 0.0039 | 0.97, 1.32 |
| 3000 | 3000 | 40 | 42 | 0.257 | 0.276 | 0.88 | 0.255 / 0.279 | 0.00248 / 0.0128 ± 0.0066 | 0.0009 | 0.96, 1.49 |
| 3000 | 3000 | 80 | 212 | 37.6 | 34.4 | 1.00 | 32.4 / 32.5 | 5.21 / 5.08 ± 0.42 | 0.0027 | 0.97, 1.16 |
| 3000 | 3000 | 80 | 84 | 2.38 | 2.12 | 1.03 | 2.07 / 2.13 | 0.31 / 0.172 ± 0.053 | 0.0067 | 0.99, 1.28 |
| 3000 | 3000 | 80 | 63 | 0.981 | 0.896 | 0.99 | 0.842 / 0.924 | 0.139 / 0.0667 ± 0.03 | 0.0100 | 0.97, 1.27 |
| 3000 | 3000 | 80 | 42 | 0.284 | 0.267 | 0.98 | 0.249 / 0.276 | 0.0351 / 0.0143 ± 0.012 | 0.0137 | 0.97, 1.25 |
| 12000 | 12000 | 40 | 506 | 32.9 | 29.2 | 1.00 | 29.2 / 29.4 | 3.75 / 3.64 ± 0.16 | 0.0009 | 1.00, 1.17 |
| 12000 | 12000 | 40 | 135 | 0.694 | 0.548 | 0.99 | 0.643 / 0.647 | 0.0505 / 0.0503 ± 0.0099 | 0.0022 | 1.08, 1.40 |
| 12000 | 12000 | 40 | 50 | 0.0459 | 0.0286 | 1.08 | 0.0439 / 0.0397 | 0.00205 / 0.00273 ± 0.0011 | 0.0035 | 1.24, 1.98 |
| 12000 | 12000 | 100 | 135 | 0.592 | 0.562 | 1.01 | 0.562 / 0.56 | 0.0296 / 0.0273 ± 0.0049 | 0.0015 | 1.00, 1.26 |
| 12000 | 12000 | 100 | 50 | 0.0306 | 0.0286 | 0.98 | 0.0303 / 0.0304 | 0.000291 / 0.00102 ± 0.00046 | 0.0008 | 1.03, 1.44 |

**Table C: moment certificates against the true top eigenvalue (model moments, RMM-S).**

| B | L | P0 | \|W\| | (E tr H^p)^{1/p}/top, p = 4 | p = 12 | p = 35 | uncentered tr ratio sextic/RMM, p = 35 | centered 1 + tr(E⁴)^{1/4} / top |
|---|---|---|---|---|---|---|---|---|
| 3000 | 2160 | 40 | 212 | 2.07 | 1.12 | 1.00 | 1.88 | 1.50 |
| 3000 | 2160 | 40 | 84 | 1.91 | 1.12 | 1.02 | 0.73 | 1.29 |
| 3000 | 2160 | 40 | 63 | 1.84 | 1.11 | 1.01 | 0.69 | 1.21 |
| 3000 | 2160 | 40 | 42 | 1.83 | 1.14 | 1.05 | 0.33 | 1.20 |
| 3000 | 3000 | 20 | 212 | 2.16 | 1.15 | 1.01 | 1.02 | 1.48 |
| 3000 | 3000 | 20 | 84 | 2.02 | 1.16 | 1.05 | 0.40 | 1.29 |
| 3000 | 3000 | 20 | 63 | 1.96 | 1.15 | 1.05 | 0.38 | 1.23 |
| 3000 | 3000 | 20 | 42 | 1.86 | 1.14 | 1.05 | 0.30 | 1.16 |
| 3000 | 3000 | 40 | 212 | 2.17 | 1.15 | 1.01 | 1.52 | 1.49 |
| 3000 | 3000 | 40 | 84 | 1.96 | 1.12 | 1.00 | 1.52 | 1.26 |
| 3000 | 3000 | 40 | 63 | 1.93 | 1.13 | 1.02 | 0.78 | 1.21 |
| 3000 | 3000 | 40 | 42 | 1.86 | 1.13 | 1.03 | 0.54 | 1.16 |
| 3000 | 3000 | 80 | 212 | 2.14 | 1.13 | 0.99 | 1.85 | 1.46 |
| 3000 | 3000 | 80 | 84 | 1.92 | 1.10 | 0.99 | 2.04 | 1.24 |
| 3000 | 3000 | 80 | 63 | 1.87 | 1.10 | 0.99 | 1.64 | 1.18 |
| 3000 | 3000 | 80 | 42 | 1.83 | 1.11 | 1.01 | 0.97 | 1.15 |
| 12000 | 12000 | 40 | 506 | 2.84 | 1.25 | 1.03 | 1.07 | 1.66 |
| 12000 | 12000 | 40 | 135 | 2.46 | 1.22 | 1.05 | 0.74 | 1.29 |
| 12000 | 12000 | 40 | 50 | 2.10 | 1.17 | 1.02 | 0.96 | 1.12 |
| 12000 | 12000 | 100 | 135 | 2.45 | 1.21 | 1.03 | 1.09 | 1.27 |
| 12000 | 12000 | 100 | 50 | 2.16 | 1.19 | 1.03 | 0.90 | 1.13 |

**Reading [numerical].**
- **(M₄) holds at the random-matrix scale.** tr(E_W⁴)/(2|W|³/S²) lies in [0.93, 1.6]. The excess over 1 is the slot
  spike, which the model has too: the ratio sextic/RMM-S lies in [0.77, 1.08].
- **(M₄a): row mean-square coherence on W.** Its mean is (0.96–1.24)·|W|/S and its maximum is at most 2·|W|/S. That
  is square-root coherence on average, with no excess from slot selection.
- **(M₄b): the non-backtracking 4-cycles.** They are 0.08–1.4% of their no-cancellation size.
  - They agree with the model at B = 12000 for both slots, and for small slots at B = 3000.
  - With 14 slot primes at B = 3000 they are about 2× the model (2–2.6σ). This is the only systematic deviation
    found, and it is absent at B = 12000 with 20 slot primes of norm 100–200.
- **Top eigenvalue.** It is within ±4% of RMM-S everywhere. The sign changes with the slot: below the model for
  4 slot primes, typical for 10, and up to 3% above for 14 at B = 3000.
- **The i.i.d. Schur model** sits 1.6–4% below the multiplicative models. P(Schur ≥ sextic) ≤ 0.1 in 11 of the 16
  B = 3000 cases.
- **Certificates (Table C).**
  - At these sizes the uncentered p = 35 certificate is within 5% of the truth, and the centered fourth-moment
    certificate within 12–66% (its |W|^{1/4} constant).
  - Asymptotically only the exponents matter (§1.6): p = 35 costs |W|^{1/35}, and the fourth moment costs nothing
    for δ > 1/3.
- **Caveat.** B ≤ 12000 cannot tell a B^{−0.13} saving from a constant, and the slots here are wide
  (s ≈ 0.4–0.6, against s ≈ 0.03 at the corner). The numerics say (M₄) is what happens at accessible sizes, not
  that it is provable.

## 4. Framing: which object needs control

**The object.** Not a dictionary, but the centered two-step correlation (G_W − D_W)². It is the lowest-order
object with room beyond √, and it has room exactly for δ > 1/3.

**The assumption that, if false, would make this easy: that W is cut out by the same Frobenius data that
builds the rows.** If W were independent of the rows, matrix Chernoff with Θ₆ would finish at once (RIP (2)). The
analysis here adds how *little* independence is needed.
- Pairwise information never suffices. Everything tried so far is of degree ≤ 2 in the rows:
  - coherence and Gershgorin;
  - products (§1.4);
  - amplify–reflect from Θ₆ (Gram entries twisted by slot monomials);
  - kernels κ(G).

  Each of these stops at the √-barrier.
- Fourth-order decorrelation suffices: the closed 4-walks of (M₄) cover all of δ > 1/3, with slack B^{3δ−1}.
- So the obstruction is exactly the degree-4 interaction between W and the Gram.

A second, independent relaxation: the leaf only needs the product vectors S₁S₂∏T_k. Dropping "for all a" turns the
target into a weighted fourth moment of short sums over W. That is the journal's D1 face, where the √-barrier is
absent but other walls remain.

**Why amplify–reflect cannot produce a beyond-√ certificate [derived].** Two facts point in opposite directions:
- Uncentered moments are monotone in the row weights: for PSD G and 0 ≤ D ≤ D′,
  tr((D^{1/2} G D^{1/2})^p) ≤ tr((D′^{1/2} G D′^{1/2})^p). So the amplifier majorant 1_W ≤ |T|^{2k}/V^{2k} can be
  inserted, but the certificate pays |W|^{1/p} (§1.6(a)).
- The efficient certificate is the centered moment tr((G_W − D_W)⁴), and it is not monotone, because G_W − D_W is
  indefinite. No majorant can be inserted into it, so it needs genuinely W-restricted information.

Amplify–reflect works only with monotone, uncentered quantities, and that is why it stalls. A first step that
uses W itself is unavoidable.

**Kadison–Singer and paving [MSS (2015) with dummy-vector completion, plus Θ₆; existence only].**
- Apply MSS (Weaver's form, completing with dummy vectors to the identity) to u_z/‖M‖. Every r-part split has
  parts with ‖G_{F_j}‖ ≤ (√(‖M‖²/r) + √L)² ≤ (√(B^{7/6}/r) + √L)².
- With r = B^{1/6}, F splits into B^{1/6} parts with ‖G_{F_j}‖ ≤ 4L at L = B.
- The K-wall therefore asks whether the slot-selected W lines up across such a paving.
- The interlacing method is existential and cannot target a given W.

**k-wise independence and Weil.**
- The slot data is k-wise independent for k ≤ 2/s (Pólya–Vinogradov). Degree-2 threshold functions are fooled by
  bounded independence (Diakonikolas–Kane–Nelson, FOCS 2010). So |W| matches the model, but that is a degree-0
  test.
- (M₄) is a test of conductor up to L⁸, far beyond B². No Weil/Pólya–Vinogradov-based derandomization reaches it.

**Other tools that do not apply.**
- Golfing (Gross), Candès–Romberg incoherence and leverage-score sampling control *random* samples of a system
  known to be near-orthogonal. Here the full system is not proved near-orthogonal (Θ₆) and W is not random.
- Expander or strongly-Rayleigh matrix Chernoff (Garg–Lee–Song–Srivastava, STOC 2018; Kyng–Song, FOCS 2018) would
  apply to walk- or determinantal-sampled W. Slot selection is neither.

## 5. Summary

- **Best design.** D1: the slot-conditioned random multiplicative dictionary on the fixed support W, certified by
  the centered fourth moment. Its random side is provable and formalizable in the counting style. Its
  certificate has room for every δ > 1/3.
- **The single missing inequality.** (M₄): Σ_{z₁,z₃∈W} |Σ_{z₂} G(z₁,z₂) G(z₂,z₃)|² ≤ B^{4γ}L⁴, i.e. the
  non-backtracking 4-cycles of the sextic Gram on the slot-selected set cancel by B^{1/2−δ−γ} per step beyond
  square-root coherence (B^{0.13} in total at δ = 0.452), plus row mean-square coherence on W.
- **Confidence.**
  - High that §1 is right: the lemmas are elementary and Lean-ready.
  - Medium-high that (M₄) is the right lowest-order target, i.e. that nothing of degree ≤ 2 in the rows can work.
  - Low that (M₄) is provable with 2026 tools. No thin-family, multiplying-conductor analogue of Guth–Maynard's
    energy bound exists.
  - The numerics say (M₄) is true with room.
