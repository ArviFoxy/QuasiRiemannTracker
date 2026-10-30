# New-mathematics directions for θ (opus_fresh2, 2026-10-30) — final report

Target: Δθ ≤ −3e-4 below #97 (0.87341198), i.e. θ ≲ 0.87311, by new theorems that can later be formalized.
Evidence tags: [read] (repo or literature read; "search" = abstract/search result only), [derived] (own derivation,
not formal), [numerical] (float model or computation), [conjecture].
Value models: `base_models/` (combo.py, count_shift.py, worth.py) and new scripts in
`models/` (pclass.py, drange.py, jointcut.py, jointcut2.py, jointcut3.py, faceL.py, ejoint.py + ejoint.log).
All prices come from the float model of the newTop row. It reproduces #97 = 0.87341197 and the bank 0.87338228.
They are first-order guides, not certificates.

## 0. Ranked summary

| rank | direction | needed for −3e-4 | for −5e-5 | plausibility | first step |
|---|---|---|---|---|---|
| 1 | **D1** A face proved outside Sil's packing: twisted fourth moment of the sextic family by Poisson + Patterson-corrected prime dispersion (no native steps, hence no K-wall and no root-reference gate) | Λ ≤ 1.82 in both faces (5/3 gives −4.9e-4) | Λ ≤ 1.97 | moderate-low | exponent ledger; effective-Λ numerics; HD lemma in Lean |
| 2 | **D2** P1 in its weakest form: power saving in the cross-correlation (X) for *fixed* distinct indices P ≠ P′, which yields the joint hybrid-norm extension e | e ≈ 2.4e-3 (Z-units); ≈ η₀ ≥ 0.01 if the dependence on N(P) is ≤ N(P)² | e ≈ 1.8e-4 | low | K-scaling of G_{PP′}(K) at the self-dual point |
| 3 | **D4** Sixth moment of the thin family: window form (plain word) or packet form (Hölder-6 on the high side) | ε₆ ≈ 0.10 (window) or μ₆ ≤ 1.144 (packet) | ε₆ ≈ 0.115 / μ₆ ≤ 1.152 | low | test whether the packet's sixth moment shows the N-term (it is genuine for full families mod q, not forced for thin ones) |
| 4 | **D3** Count-side sub-√ joint count (twin of the K-wall) | DH-strength J valid down to slot slope ν₀ ≈ 0.33 | ν₀ ≈ 0.41 | low | pricing rule only (R1) |
| 5 | **D5** Zero-configuration rigidity (Turán–Nazarov at the rightmost zero) | only together with D4 or B2 | – | moderate as a lemma, ~0 value alone | formalizable complex analysis |
| 6 | **D6** Long word through the theta side (B2) | λ = 0.23 alone (or 0.20 with c = 1.95 everywhere) | λ = 0.1717 | very low | none recommended |
| 7 | **D7** Function-field laboratory for D1/D2 | support | – | – | exact large-degree computations over F_q[T] |

Context, not new math: #96's two-slot probe. T96 prices it at 0.8656 with de Faveri + the K-chart (dpx) alone
(−7.8e-3). That is 26× the target and larger than any lever here. "No port" is a verification decision, not a
mathematical one.

## 1. What a new theorem must deliver (prices, Δθ against #97)

| lever (theorem type) | −5e-5 | −3e-4 | source |
|---|---|---|---|
| uniform count shift ΔR on δ ∈ [0.36, 0.53] | −0.0004 | −0.0024 | count_shift.py |
| inverse slot cost c_I (P1, use (a)) | 1.9882 | 1.85 | combo.py |
| slot cost in all three places | 1.9936 | 1.90 | combo.py |
| face Λ, count + physical (B = 0.99999) | 1.97 | 1.82 (1.80: −3.3e-4; 5/3: −4.9e-4) | faceL.py |
| long slope, pivot t = 1 (B2) | 0.8283 (λ = 0.1717) | 0.77 (λ = 0.23) | combo.py, pivot.py |
| combinations | – | c = 1.95 everywhere + long 0.80: −3.3e-4; Λ = 1.9 + long 0.80: −3.25e-4 | combo.py, faceL.py |
| joint hybrid-norm diagonal extension e (probe + inverse + long, Z-units) | 1.8e-4 | 2.4e-3 | ejoint.py: e = 1e-4/3e-4/5e-4/1e-3 → −4.1e-5/−6.4e-5/−8.7e-5/−1.44e-4 |
| DH-strength joint count J(ν,ν) = 1 − ν for slot slope ν = 2pδ > ν₀ | ν₀ ≈ 0.41 | ν₀ ≈ 0.33 | jointcut3.py |
| count drop (any size ≥ 0.01) only for slot-amplitude classes p ≥ p₀ | p₀ ≈ 0.488 | p₀ ≈ 0.43 | pclass.py |
| Hölder-6 line on the high side, packet sixth moment μ₆ | ≈ 1.152 | ≈ 1.144 (break-even ≈ 1.15) | R3_return §3.3 [read] + dθ/dμ₆ ≈ 0.2145·d/6 [derived] |
| window sixth moment of the family, excess ε₆ (plain word) | ≈ 0.115 | ≈ 0.10 | journal thresholds [read] + dual weight 0.25 [derived] |

Notes:
- The e-lever at the selected-leaf binding is about 5× weaker than R3_return's older-baseline price (slope −0.114 per
  unit e beyond the bank, against −0.55 there). Use ejoint.py, not R3, for this lever.
- count_shift.py prices from the #97 design. combo.py, faceL.py and ejoint.py price from the bank design (−2.97e-5
  already included).

## 2. Three reframings that change where a theorem can act [numerical + derived]

**R1. The √-barrier sits in the slot slope ν = 2pδ. A sub-√ count theorem is capped unless it is paired with PR 93's
joint count above √.** (drange.py, jointcut*.py)
- The newTop landscape E(δ) is flat between the binding δ* = 0.453 and δ = 0.5. Any count improvement restricted to
  δ < 1/2 is worth at most **−7.3e-5**, because the binding moves to δ = 0.500.
- Restricted to ν ≤ 1/2, it is worth at most −7.6e-5 (binding at δ = 0.501, p = 1/2).
- If the return *also* uses PR 93's DH-strength joint count J(ν,ν) = 1 − ν for ν > 1/2 (a library result), the same
  ν ≤ 1/2 improvement regains the full uniform-shift value: −3.0e-4 for 0.0024 and −1.24e-3 for 0.01. The joint count
  alone is worth 0 today (the binding has ν = 0.453).
- Rule: any sub-√ count theorem must be priced together with that J consumption, never alone.
- A DH-strength joint count extended below √ is worth −8.8e-5 at ν₀ = 0.40, −2.3e-4 at 0.36 and −3.3e-4 at 0.33.
  An extension to "just below 1/2" is worth nothing.

**R2. The binding is a corner in the slot-amplitude class p, and the corner's adversary is round 10's.** (pclass.py)
- E increases with p, through the probe's main-slot term δpℓ.
- Any count drop ≥ 0.01 for the classes p ≥ p₀ moves the binding to p₀⁻. It is worth ≈ 4.1e-3·(1/2 − p₀):

  | p₀ | 0.499 | 0.49 | 0.45 | 0.40 | 0.35 |
  |---|---|---|---|---|---|
  | Δθ | −2.1e-5 | −8.2e-5 | −2.5e-4 | −4.6e-4 | −6.7e-4 |

  The size of the drop is irrelevant (DH and −0.01 give the same θ).
- Is there a mechanism making near-saturated rows rarer? A model check [derived, model-level] uses boundary-zero
  Dirichlet-polynomial models L = (s − ρ)·D(s) with D = 1 + Σ d_x U^{−x(s−a)}.
  - **For.** At the rightmost zero, all three profiles (slots, Möbius, plain) are positive renewal measures. A slot
    deficit ≤ δ(1/2 − p) per unit width forces Möbius saturation at every scale up to δ(1/2 − p)·(scale gap), which is
    ≤ 0.005 at p = 0.44. That would put every p ≥ 0.44 row at I(0.95) ≈ 0.56 < 0.60.
  - **Against.** The model also shows the escape: D near-critical (Σ|d_x| → 1) with all frequencies above the slot
    band (x > 0.17). The slots then stay saturated (p = 1/2) while the Möbius profile alternates.
    - With x ≈ 0.25 the Möbius blocks are unsaturated on (0.76, 1] and saturated at 0.75 and 1.14. That defeats every
      inverse word below 0.60 (I(r) < 0.601 needs r > 0.762). The row is then counted only by the long word, and only
      a fraction c ≈ 0.25 of its local zeros sits on the rightmost line. Littlewood with any 2k-th moment (k ≤ 3) gives
      1 − kcδ ≥ 0.66, so no moment method reaches it.
    - F1-type rows (plain block at s₀ saturated) need a frequency at s₀, hence c ≥ s₀ ≈ 0.38. They are within reach of
      a window sixth moment (D4).
  - So class refinement reduces to round 10's wall. F2-type corner rows need B2; F1-type corner rows need D4. This is
    recorded so the p-corner is not re-priced as free.

**R3. First moment versus second moment.**
- Of the remaining walls, only the faces' prime slots admit first-moment (dispersion) technology of Dunn–Radziwiłł type.
- P1 and B2 are second moments at a self-dual point, of affine type. The GL(2) analogue of P1's weakest form is a mixed
  central moment of quadratic twists of two distinct fixed forms. Petrow (arXiv:1208.4069) calls it out of reach
  [read: search]; Zhou (arXiv:2503.14680) recently did the derivative version unconditionally [read: abstract].
- The K-wall is beyond-√ RIP, which the main thread is working on.
- The ranking above follows this classification.

## 3. Directions

### D1 (rank 1). A face proved outside Sil's packing: the twisted fourth moment of the sextic family

**(1) Statement (F_Λ) [conjecture].**
- Rows: squarefree z ∈ Z[ω] with (z, 6) = 1 and weight Φ(N(z)/Z^M). Write χ_z = (·/z)₆.
- Plain sums: X_i(z) = Z^{−m_i/2} Σ_{n primary} χ_z(n) W(N(n)/Z^{m_i}) for i = 1, 2.
- Slot pool: Q(z) = ‖a‖^{−1} Σ_P a_P χ_z(P), over products of j ≤ J distinct primes with ΠN(P_i) ~ Z^s. The weights are
  the zero-forced ones: a_P = Π W_i(N(P_i)/Z^{w_i})·N(P_i)^{−it}·ψ(P_i), with |t| ≤ Z^{o(1)} and ψ a fixed Hecke
  character of bounded conductor.
- Claim: Σ_z Φ·|X₁X₂Q|² ≪_ε Z^{M+ε} whenever m₁ + m₂ + Λs ≤ BM, with B = 1 − 1e-5 and Λ = 1.82.
- Window: m₁ + m₂ ∈ [0.75, 0.87]M and s ≤ 0.14M (count face at plain length 0.76, physical face at 0.865).
- Benchmarks: Sil's chain proves Λ = 2.0001; the ideal face is Λ = 1.

**(2) Price** (faceL.py, both faces).

| Λ | 1.97 | 1.90 | 1.82 | 1.80 | 5/3 |
|---|---|---|---|---|---|
| Δθ | −5.1e-5 | −1.6e-4 | −3.0e-4 | −3.3e-4 | −4.9e-4 |

Λ = 1.9 with long slope 0.80 gives −3.25e-4.

**(3) Mechanism and why it could be true.**
- **No K-wall, no reference gate.** It bypasses both of Sil's walls. The K ≥ 1/2 overshoot 6KB/(1+K) and the
  root-reference gate P + 2S + 9u/2 < 1 belong to the inductive native step, not to the moment. A direct theorem
  replaces the end face in the return.
- **The smooth part is free.** The unslotted plain fourth moment is already diagonal up to total length M (OpenAI
  Lemma 18.1 at z = 0) [read]. The whole question is the price of the prime factor.
- **HD reduction [derived].** For a split prime π with N(π) = p and χ = (·/π)₆:
  - Davenport–Hasse with the quadratic character gives g(χ)g(χ⁴) = χ̄(4)g(χ²)g(χ³).
  - Since g(χ⁴) = conj g(χ²) and g(χ²)² = J(χ²,χ²)·conj g(χ²), this gives
    **g̃₆(π) = χ̄(4)·(J(χ²,χ²)/√p)·conj(g̃₃(π))·g̃₂(π).**
  - Here J/√p is an angular Hecke-character value (Eisenstein: the cubic Jacobi sum is a primary generator of π), and
    g̃₂(π) is a sign of bounded conductor.
  - So prime sums of sextic Gauss sums are prime sums of cubic Gauss sums twisted by Hecke characters.
  - Heath-Brown–Patterson (J. reine angew. Math. 1979) bound those by X^{5/6+ε}. That is Dunn–Radziwiłł's cancellation
    axiom with η = 1/3, and the journal checked that η ≤ 1/4 is only a convenience there.
  - The "sextic theta has no explicit coefficients" obstacle therefore does not touch the prime variable. It affects
    only the main terms of the smooth variables.
- **Primes do break √ in the cubic family.** Dunn–Radziwiłł (arXiv:2109.07463, Ann. Math. 200 (2024), number checked):
  the cubic large sieve corrected by Patterson's main term is diagonal for such prime vectors up to B ≈ A^{3/5}. That is
  a prime cost ≈ 5/3 < 1.82 (journal's sharper reading of Props 8.1/9.2). Their GRH step survives the bootstrap's
  quasi-GRH(7/8) (journal).
- **Classical analogue.** Twisted fourth moments of Dirichlet L-functions with power saving: Blomer–Fouvry–Kowalski–
  Michel–Milićević (arXiv:1411.4467) and Zacharias (arXiv:1611.09582) [read: search]. In full families the twist costs
  1; the thin family's extra cost is the Gauss-sum bias.
- **Numerics** (journal, RIP program (2)) [read]: the sextic Gram matrix is Marchenko–Pastur, and slot large-value
  sets act like random sets. The truth is far below Λ = 2.

**(4) First steps.**
- **(a) Exponent ledger** (paper, about 2 weeks).
  1. Poisson in z.
  2. Keep X₁X₂ as a *Type I factor* of length Z^{m₁+m₂} and the prime pool as the free, cancelling variable. Do not
     reflect the smooth variables first (see the risk below).
  3. Voronoi for the sextic Kubota series in the smooth variable only. By the HD reduction this is a cubic Kubota series
     twisted by a quadratic character of conductor N(k)².
  4. D–R Prop 9.2-type dispersion for the pool.
  5. Write every term as Z^{f(m₁, m₂, s, M)} and solve for s_max(m₁ + m₂).

  Go/no-go: continue only if (M − m₁ − m₂)/s_max ≤ 1.85 on the whole window.
- **(b) Numerical effective Λ** (about 1 day, with `rip/zomega.py`; never measured, since grep finds no
  twisted-fourth-moment numerics in the repo).
  - Rows N(z) ∈ [B, 2B] with B = 3·10³ to 2·10⁴.
  - X₁ = X₂ smooth of length B^m, with 2m ∈ {0.6, 0.7, 0.8}. Q over split primes with N(P) ~ B^s.
  - Measure F(m, s) = Σ_z|X₁X₂Q|²/(R·Σ|c|²) as a function of s.
  - Controls: Q replaced by a smooth sum (cost 1 expected); random unimodular weights on the same primes; the
    Patterson-biased vector conj g̃₆(P) (the Θ₆ extremal).
  - The slope at which F leaves O(1) is an empirical Λ.
- **(c) First Lean lemma:** the finite-field HD identity above (Mathlib has Gauss and Jacobi sums), then its
  twisted-multiplicative extension g̃₆(n) = ξ(n)·conj g̃₃(n) on squarefree n, with ξ a unitary Hecke-type factor.

**(5) Main risk.**
- **The dead zone.** If the smooth factors are reflected (sextic Kubota FE) while the prime pool is present, the pool
  modulates the dual and raises its conductor by N(P)². That is the dead zone of STRUCTURE §3. It is why the natural
  face (Lemma 18.1 with slots) costs 6κ ≈ 4.5, and why target 1 ("D–R for smooth × prime") is open. The ledger must
  show that dispersion can be done before reflection.
- **Main-term interaction.** The Kubota-pole main terms of the smooth variables can meet Patterson's prime bias
  A^{2/3}B^{4/3} in cross terms.
- **Twist uniformity.** Heath-Brown–Patterson must hold uniformly in the twist for conductors up to Z^{0.8}.
- **Lean.** The metaplectic Eisenstein theory beyond cubic Kubota basics is missing.

### D2 (rank 2). P1 in its weakest form: near-orthogonality of index-twisted theta columns

**(1) Statement (X_fix) [conjecture].**
- For fixed distinct primary primes P ≠ P′ and K → ∞, set
  S(k, P) = Σ_n g̃₃(n)χ_k(n)·conj((n/P)₃)·W(N(n)/(K·N(P))), with k squarefree and not a square.
- Claim: |Σ_{N(k)≤K} S(k,P)·conj S(k,P′)| ≪ K^{1−η₀}·N·(N(P)N(P′))^A for some η₀ > 0 and A < ∞.
- By Schur this gives P1 use (b) (P1_PROBLEM): the quadratic sieve for theta-structured columns stays diagonal up to
  N = K·Z^e, with slot primes of norm ≤ Z^e and e ≤ 0.742·η₀/(1 + A).
- The extension e relaxes three places at once (R3_return §3.4): probe x + y = 1 − ℓ + e, inverse budget
  r + 2z ≤ 1 + e/h, and the RawMoment gate.

**(2) Price** (ejoint.py, re-priced at the bank).

| e (Z-units) | 1e-4 | 3e-4 | 5e-4 | 1e-3 |
|---|---|---|---|---|
| Δθ vs #97 | −4.1e-5 | −6.4e-5 | −8.7e-5 | −1.44e-4 |

- −5e-5 needs e ≈ 1.8e-4, and −3e-4 needs e ≈ 2.4e-3 (linear, slope −0.114 beyond the bank).
- With A = 2 that means η₀ ≈ 7e-4 and η₀ ≈ 0.01 respectively.
- This is the cheapest form of the P1 atom. The slot-summed use (a) needs η ≈ 0.1 for c_I = 1.85.

**(3) Mechanism.**
- **No main term.** For P ≠ P′ the "Rankin–Selberg diagonal" is absent: the n = m terms are ≈ KL ≪ KN because
  (n/PP′)₃ cancels, and the twisted Kubota series are entire (P1 deep-dive [read]). (X_fix) asks a moment *without* a
  main term to be power-small.
- **Spectral route [conjecture].** After quadratic Poisson in k, the n, m sums become cubic exponential sums tied to
  cubic Kloosterman sums (Louvel, arXiv:1107.0197 [read: search]). Kuznetsov on the cubic cover (Livné–Patterson;
  Dunn's metaplectic large sieve, arXiv:2403.13151 [read: search]) separates the residual (θ₃) part, which should be
  orthogonal for distinct index twists, from a cuspidal part controlled by a spectral gap.
- **Single columns are already fine.** Each column is diagonal on its own: #96's Thm N1 (index conductor N(P)¹) gives
  F_P ≲ KN [read].

**(4) First steps.**
- **(a) Numerics** (new: rounds 7–9 measured the operator norm and stable rank of the slot-summed matrix, not single
  cross-correlations at fixed indices).
  - Compute G_{PP′}(K) for the 6–10 smallest split primes, with K up to 2·10⁴ and N = K·N(P) (the self-dual point).
  - Take g̃₃ exactly at primes and extend by g̃(nP) = g̃(n)g̃(P)·conj((n/P)₃).
  - Fit |G_{PP′}|/√(G_{PP}G_{P′P′}) ~ K^{−η}. Random behaviour predicts η = 1/2.
- **(b) Literature:** read Zhou's and Li's methods and find what fails without derivatives in the metaplectic case.
- **(c) Lean:** state Thm N1 against the baseline's `kubota_mul` / Eisenstein machinery.

**(5) Main risk.**
- It is still an affine-type moment (journal: determinant-0 Cartan matrix), and its GL(2) analogue is open.
- Its quadratic twist lives on the 6-fold cover, where no Kuznetsov formula exists.
- Even full GRH gives only log savings for number-field fourth moments of quadratic L-functions (Shen; Shen–Stucky
  [read in journal]). The bootstrap's quasi-GRH is therefore no route.

### D4 (rank 3). Sixth moments of the thin family

**(1) Statements [conjecture].**
- **(W) Window form:** Σ_u ∫_{|t−γ|≤1} |L(1/2+it, ξ_u)|⁶ dt ≪ U^{1+ε₆} with ε₆ ≤ 0.10. It acts through the plain word:
  F1 rows carry |L|² ≥ U^{δs₀} on a window.
- **(H) Packet form:** the packet's sixth moment has μ₆ ≤ 1.144. It acts through the high side's Hölder-6 line.

**(2) Price.**
- (W): ε₆ ≈ 0.10 for −3e-4 and ≈ 0.115 for −5e-5 [derived, first order]. The journal threshold to beat the LP at all is
  0.118 at δ = 0.452 and 0.108 at δ = 0.426.
- (H): μ₆ = 1.144 for −3e-4.

**(3) Mechanism.**
- In a full family mod q, the sixth moment of short sums of length q^{0.43} has a *genuine* excess q^{0.29}:
  n₁n₂n₃ ≡ m₁m₂m₃ mod q has ≈ N⁶/q solutions [derived].
- In the thin family {χ_u : N(u) ≤ U} the analogue of "≡ 1 mod q" is "is a sixth power", which is rare. So the N-term
  is not forced there, and Lindelöf on average is the plausible truth.
- Available today: ε₆ ≤ δ/2 ≈ 0.23 (per-row zero-free region × diagonal fourth moment). Burgess gives 0.375.

**(4) First step.** Compute Σ_u|S′_u|⁶/(R·N³) for packets of length B^{0.43} in the actual family (`rip/`). If the
excess 3m − 1 is visible, (H) is false and only (W) remains.

**(5) Risk.** Unknown even for the quadratic family at these lengths unconditionally. It would beat the ζ analogue
(∫|ζ|⁶ ≪ T^{5/4}).

### D3 (rank 4). Count-side sub-√ joint count, the twin of the K-wall: pricing guidance

- **Statement [conjecture]:** PR 93's DH-strength joint count J(ν,ν) = 1 − ν holds for rows selected by slots of slope
  down to ν₀. Today ν₀ = 1/2.
- **Price:** ν₀ = 0.41 for −5e-5 and ν₀ = 0.33 for −3e-4. Any such theorem also needs R1's pairing (J consumption for
  ν > 1/2 in the return).
- **Angle for the main thread:** if the RIP program yields a selected norm at slope ν, plug it into the joint count of
  the *count*, not only into the faces. Note that "just below 1/2" is worthless in the count.
- **Risk:** Guth–Maynard for thin families of varying moduli.

### D5 (rank 5). Zero-configuration rigidity (joint profile theory)

- **Statement [conjecture].**
  - At the rightmost zero, the Möbius, slot and plain profiles are the scale-Fourier transforms of 1/L, −L′/L and L on
    Re s = a + 2e.
  - Suppose slot deficits are ≤ κ_s per unit width on a positive proportion of widths in [w₁, w₂].
  - Then min_{r′∈[r−ε, r]} (Möbius deficit) ≤ C·κ_s·r + o(1),
  - unless the row has ≥ c·log U zeros in {Re s ≥ a − C/log U, |Im s − γ| ≤ C} (Turán–Nazarov).
- **Value:** alone it only pushes the corner onto round 10's adversary (R2). With D4 (F1 rows) or B2 (F2 rows) it
  converts the p-corner at ≈ 4e-3 per unit of (1/2 − p₀).
- **First step:** a Turán–Nazarov lemma for the explicit-formula sums. This is pure complex analysis, and Mathlib has
  Jensen, Borel–Carathéodory and Hadamard. Then a numerical map of jointly attainable profiles over finite-zero models.

### D6 (rank 6). The long word through the theta side

- B2 needs P1's core estimate at η > 1/6 ("never combine"), which is twisted-Chowla strength.
- λ = 0.23 alone for −3e-4, or 0.20 combined with c = 1.95 everywhere.
- Listed for completeness. Lowest plausibility.

### D7. Function-field laboratory (support for D1 and D2)

- Over F_q[T] with q ≡ 1 mod 6, cubic Gauss sums and sextic symbols are explicit.
- The analogues of (F_Λ) and (X_fix) follow from Deligne in the large-q limit.
- Compute the large-degree regime to pin down the main and secondary terms exactly (Kubota poles, Patterson bias), so
  that the number-field statements are written with the right main terms.

## 4. Dead or capped (do not re-price)

- p-class refinement alone (R2): reduces to round 10.
- Sub-√ count theorems without J above √ (R1): at most −7.6e-5.
- Pointwise per-row bounds in higher Hölder orders: lose 0.026 in the exponent, since 1 − R − 2α − δz < 0 with
  α = δ(1 − m) ≈ 0.193 [derived].
- Decorrelating the bad rows from the physical packet: F1 rows carry |L(1/2)|² ≥ U^{δs₀} ≈ U^{0.17}, within U^{0.01} of
  the Hölder extremal U^{0.18}. The (4/3, 4) step is essentially sharp for the binding adversary [derived].
- Random slot sub-selection (matrix Chernoff) reproduces the trivial bound exactly [derived].
- Sextic slots, cubic rows, a different order or a different base field: the architecture is pinned (HD with a
  quadratic subcharacter, explicit cubic theta, quadratic leftover twist) [read].
