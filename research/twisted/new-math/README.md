# Twisted transfers: new-math targets (D1, task 156). Interim, stopped early

The lead stopped this early. No numerical experiment finished. No citation was checked online.
This note has three parts:
- derivations on the repo's ledger model (`../twisted_ode.py`, `../scan_split.py`);
- one structural observation, which reduces target (a) to the dual (child) form;
- the precise estimate that is still missing.

Tags:
- **[proved here]**: checked by hand, not machine-checked.
- **[known: …]**: from a source.
- **[numerical]**: computed.
- **[heuristic]**: an argument, not a proof.
- **[conjecture]**: a statement we do not know to be true.

## 1. Unit conversion and what must be shown (pricing)

- **The room-type twisted type is already in the model** [proved here]. The model's twisted margin
  is `0.75(1 − (2+κ)β) − kroom`. A D-decoupling that saves `W^e`, combined with a HIGH room charge
  `κ′`, is the setting `kroom = κ′ − e`, with negative values allowed. No code change is needed.
- **Scale and room charges are the same cost in two units** [proved here]. The conversion is
  `κ = κ′/(qβ)`. So `κ′ = ρ(3/4) = 2/7` corresponds to:
  - `κ = 0.98` at the start (β = 0.389);
  - `κ = 0.86` at the operating point (β = 0.444).

  This is the brief's "κ ≈ 0.8–1.0".
- **Threshold for the twisted type to pay at q = 3/4** [proved here]. With no LOW scale charge
  (κ = 0; `../README.md` says the LOW side is already uniform in the conductor), the type pays when
  `e > κ′ − 0.75(1 − 2β)`. At κ′ = 2/7 the threshold is:

  | β | e must exceed |
  |---|---|
  | 0.389 | 0.12 |
  | 0.444 | 0.20 |
  | 0.5 | 0.29 |

- **Weakest sufficient target for (a): `e ≥ κ′`** [heuristic].
  - That means `e ≥ 2/7` with today's per-D count, or `e ≥ 1/7` with a joint count.
  - Then `kroom ≤ 0` and the margin is at least that of the κ = 0 row, so the q = 3/4 region
    contains that row's region, which gives −6.2e-5.
  - This assumes θ is monotone in the q = 3/4 region. It has not been re-run.
  - In words: recover `W^{2/7}` of the `W` that Cauchy–Schwarz loses.
- **Full orthogonality makes the conductor irrelevant** [proved here]. Full orthogonality (e = 1)
  gives the type `(1, 2+κ, 1)`, with break-even `κ* = (1+q)/(qβ) − 2 ≈ 4.0` at the operating point.
  The resulting chain was not priced: q is capped at 3/4, the model stops at `Lend = 1.80`, and the
  return box was not checked.
- **Target (b) needs a nearly conductor-free count** [numerical: linear interpolation of the brief's
  table, not re-run]. With e = 0, the gain of 5e-5 needs `κ ≲ 0.05`, i.e. `κ′ ≲ 0.015`. That is a
  joint HIGH count whose conductor exponent is at most about 5 % of `ρ(3/4)`. I know of no
  zero-density estimate near this [heuristic].

## 2. Candidate theorem (a), the twisted-transfer sieve

**Setup.**
- `𝒟` is a slot of `W` primes D with `N(D) ≍ P = U^d`.
- `ℱ` is the residual columns: squarefree, coprime to `6∏D`.
- Coefficients `|γ_D| ≤ 1` and `a_n`.
- `H = U^μ`, with `Ω` smooth.

**TTS_e** [conjecture]:

    Σ_h Ω(Nh/H) |Σ_{D,n} γ_D a_n 𝔤(Dn,h)|²  ≤  U^{o(d)} W^{1−e} Σ_D Σ_h Ω(Nh/H) |Σ_n a_n ε(D,n)(n/D)₃ 𝔤(n,h)|².

- Cauchy–Schwarz gives e = 0. Section 1 needs `e ≥ κ′`.
- **Range:** d → 0 (the continuum chain), with `μ = 2α − σ`, where α is the full column norm. The
  dual length is `J = N(Dn)²/H = U^σ`.
- **TTS fails for arbitrary per-D functions** [proved here]. Take `T_D(h) = 𝔤̄(D,h)f(h)`. Then the
  left side is about `W²Σ|f|²` and the orthogonal size is `WΣ|f|²`. So a proof must use the fact that
  `T_D` is a Gauss polynomial with moduli coprime to D.

## 3. Structural observation: the twist disappears in the dual variable

**Fourier identity** [proved here; a standard computation]. For coprime squarefree supported u and v:

    F(u,v;j) := Σ_{h mod uv} 𝔤(u,h) 𝔤̄(v,h) ψ_{uv}(−jh) = χ̄_u(v) χ_v(u) χ̄_v(−1) √N(uv) · χ_u(j) χ̄_v(j).

The proof uses CRT with `h = v h₁ + u h₂`, then `𝔤(u,vh₁) = χ̄_u(v)𝔤(u,h₁)` and the finite Fourier
inversion of each Gauss sum. By primary reciprocity the prefactor is a sign that depends only on the
classes of u and v mod 4 [known: R1's verified identity L3, `../../newpowers/r1/results.txt`].
Poisson in h then gives:

    Σ_h Ω 𝔤(u,h)𝔤̄(v,h) = ±(H/√N(uv)) Σ_j χ_u(j)χ̄_v(j) Ω̂(·),   with N(j) ≲ N(uv)/H.

**Consequence** [proved here, up to routine bookkeeping].
- For the product coefficients `b(Dn) = γ_D a_n`, split D and n into classes mod 4. The coprime part
  of the full family's child is then a combination of `Σ_j |Γ(j)|² |A(j)|²`, where:
  - `Γ(j) = Σ_D γ_D χ_D(j)` is untwisted;
  - `A(j) = Σ_n a_n χ_n(j)`.
- **The cubic twist `(n/D)₃` is gone.** In the dual, the D-slot is evaluated at the row j itself,
  not at `jn²`, so there is no conductor growth.
- The fibre `D·ℱ` has child `|γ_D|² Σ_{D∤j} |A(j)|²`. Its energy agrees with `E_D` up to the
  1/P-proportion of rows h with D | h.
- Non-coprime pairs (`gcd(n₁,n₂) ≠ 1`) give Ramanujan-sum terms, as in paper69 (MF3.62) [heuristic: routine].

**Child form of TTS_e.** It is equivalent, up to the diagonal j = 0 terms, which are already
orthogonal, to:

    Σ_{N(j)≤J} w(j) |Γ(j)|² |A(j)|² ≤ U^{o(d)} W^{2−e} Σ_{N(j)≤J} w(j) |A(j)|².

**LOW rows give e = 1 − o(1)** [proved here, trivial]. Let `E_λ = {j : |Γ(j)|² > λW}` with
`λ = U^{o(d)}`. Outside `E_λ` the bound holds with `λW`.

**The exceptional set is small** [heuristic: standard Poisson completion]. For `P^{2r} U^ε ≤ J`:
- `Σ_j |Γ|^{2r} ≪_r J W^r`;
- hence `#E_λ ≪_r J λ^{−r}`.

**Missing estimate M_e** [conjecture]:

    Σ_{j ∈ E_λ} w(j) |Γ(j)|² |A(j)|² ≤ U^{o(d)} W^{2−e} Σ_j w(j) |A(j)|²,   with e ≥ 2/7 (or 1/7).

- This says the residual's child mass does not concentrate on the exceptional rows of an independent
  prime slot.
- Trivial bounds (`|A|² ≤ ‖a‖₁²`) lose `W^{α/σ}`, which is not enough.
- It is of the same type as the HIGH analysis the source theorem already does on live slots
  (paper69, §7.2.8, MF3.60–MF3.72). Unlike the earlier negative verdict, it has no conductor growth.

**Possible circularity: check this first** [heuristic].
- Proving TTS through the child treats D as a live slot of the child. The current chain already
  does that, with no transfer.
- Whether `(1, 2, 1)` is genuinely new, or only re-books the live slot's cost, depends on the child
  ledger. In MF3.71–3.72 a slot releases `6κd` of capacity at energy cost `κd`.

## 4. Literature

Nothing was checked online in this session. The pointers below come from
`../../literature/README.md` and from memory. **Check each one before citing it.**
- Heath-Brown, cubic large sieve: Israel J. Math. 120 (2000).
- Heath-Brown–Patterson, distribution of cubic Gauss sums at primes: J. reine angew. Math. 310 (1979).
- Dunn–Radziwiłł: arXiv:2109.07463.
- de Faveri, n-th order large sieve: arXiv:2610.04045 (repo note). Xu–Sang, its sharpness:
  arXiv:2610.17675 (repo note).
- Kowalski–Michel–Sawin, bilinear forms with Kloosterman sums.
- Fouvry–Kowalski–Michel, trace functions over the primes.

How these bear on the targets:
- **Heath-Brown's sieve in the parent does not help** [proved here]. Applying it pointwise in h to
  `Σ x_D y_n (n/D)₃` loses the n-orthogonality and gives `≈ N·H·‖γ‖²‖a‖²`, which is useless.
- **In the child form the cubic twist never appears** (section 3). The relevant tools are large-values
  and moment bounds for prime Dirichlet polynomials, together with the existing HIGH count [heuristic].

## 5. Not done (next steps)

1. **Numerics**, using the validated Gauss sums of `../../newpowers/r1/zw.py`:
   - compute `λ_max` of the pencil `(M_γ, Σ_D M_D)`;
   - for random a_n, and for adversarial a_n (the top generalized eigenvector);
   - for `γ_D = 1` and for `γ_D = conj 𝔤(D,1)`;
   - and record how it scales with W.
2. **Pricing**: run `scan_split.py 0 <κ′−e>` for (κ′, e) ∈ {(2/7, 2/7), (2/7, 0.2), (1/7, 1/7), (2/7, 1)}.
   A reproduction run of `scan_split.py 0 0` was started in `$SCRATCH/pricing`, with a copy of `ta/`.
   Its output was not inspected.
3. **Settle the circularity question** in section 3.

## 6. Lead's check (2026-10-29)

- **Fourier identity, structure confirmed [derived by the lead].**
  - For squarefree coprime u, v: 𝔤(u,h)𝔤̄(v,h) = 𝔤(u,1)𝔤̄(v,1)·χ̄_u(h)χ_v(h).
  - That is one character of h mod uv, so its transform at j is χ_u(−j)χ̄_v(−j) times a Gauss sum of
    modulus √N(uv).
  - With unnormalized sums, |F| = N(uv) on rows coprime to uv. The √N(uv) in §3 corresponds to a
    normalized convention; the conclusion is unaffected.
- **Circularity: probably real [derived].**
  - In the dual variable the product coefficients b(Dn) = γ_D a_n give Γ(j)A(j), a D-slot times the
    residual.
  - The face energies already bound such slot products.
  - So the twisted transfer is likely the h-side description of an existing live slot.
  - The only new ingredient would be M_e, a large-values / non-concentration estimate. That is the T6
    (Guth–Maynard) kind of estimate.
- **Next, if pursued:** compare ledgers, i.e. the cost (1, 2, 1) of the twisted type against MF3.71–3.72,
  before any numerics.
