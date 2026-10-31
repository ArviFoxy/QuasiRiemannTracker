# A spectral large sieve on the 6-fold cover: can it give the large sieve off V? (evaluation, 2026-10-30)

**Question.** The theta span V of the sextic large sieve looks like the residual spectrum of the 6-fold metaplectic
cover of GL(2) over K = Q(ω). Can a Deshouillers–Iwaniec (DI) type spectral large sieve on that cover, together with a
Kuznetsov / Bruggeman–Motohashi formula there, prove **(LS off V)** at the balanced point B = L?
- Background: journal entries "Replacing M", "Where the theta excess lives" and the outlier entries;
  `../rip/theta/README.md`; `README.md` ("Classification of the three walls").
- Evidence tags as in `../journal/JOURNAL.md`:
  - [read]: abstract and introduction read, or the cited section;
  - [derived]: my derivation, not refereed;
  - [heuristic]; [conjecture];
  - [Lean]: a declaration checked by reading it in the formal stack (not rebuilt).

## Verdict

- **The identification is right, and sharper than stated** [derived, §2].
  - Each twisted theta row vector is the residue at s = 1 + 1/6 of Kubota's Eisenstein series on the 6-fold cover,
    twisted by the character z ↦ χ_z(m). So it is the **residual spectrum at level m**, one direction per twist.
  - The residue functional is the Mellin transform of the radial profile at the pole (Xu–Sang's I(U)). It exists
    only in K-type 0.
  - The excess exponent at balance, B^{1/n}, is the residual spectral parameter 1/n. This matches the sharp bounds
    for n = 3, 4 and 6.
- **The proposed mechanism does not apply** [derived, §2.3].
  - The sieve matrix has **no cuspidal component**: no cusp form of the cover appears in its Poisson or Kubota
    expansion. One Poisson step produces Gauss sums, which are metaplectic Kloosterman sums with one frequency equal
    to 0. Those are Fourier coefficients of Eisenstein series.
  - Kuznetsov needs two non-zero frequencies.
  - Off V there is only the continuous spectrum. A large sieve for that continuous family is *equivalent* to
    (LS off V), by the classical large sieve in the modulus.
- **Size accounting** [heuristic, §3]. A DI-quality spectral large sieve on the cover pays for the whole cuspidal
  spectrum: about vol·T⁴ forms against about B rows. The best embedding gives Δ ≪ B^{3/2+ε} at B = L. That is weaker
  than the known B^{7/6}.
- **The self-duality survives.** At B = L the Poisson self-duality is Kubota's functional equation s ↔ 2 − s.
  Spectral theory inherits it.
- **Not a realistic route** to a power saving at the balanced point on any timescale I can name.
  - I found no spectral proof of *any* upper bound for an n-th order character large sieve; all are Poisson plus
    recursion.
  - I found no Kuznetsov formula written for the 6-fold Kubota character.
- **Worth doing:**
  - the sextic residual dictionary (Lemma S1, §6), as a theorem-level V;
  - five cheap numerical tests (T1–T5, §4);
  - partial results for restricted vector classes or unbalanced ranges (§6).

## 1. Literature map

### 1.1 Metaplectic covers: theta functions, Kloosterman sums, Kuznetsov

| work | setting | what is proved (relevant part) |
|---|---|---|
| Kubota (Kyoto lecture notes, 1969) | n-fold cover of SL₂ over K ⊃ μ_n | Eisenstein series with the n-th order Kubota character. Pole at 1 + 1/n (H³ normalization); its residue is the theta function. |
| Patterson, Crelle 296 (1977); Crelle 303/304 (1978) | cubic, Q(ω) | Coefficients of θ₃ determined: τ₃(c d³) = N(d)^{1/2} g̃₃(c). The 1978 paper conjectures the bias of Kummer sums. |
| Heath-Brown–Patterson, Crelle 310 (1979) | cubic | Σ_{N p ≤ X} g̃₃(p) ≪ X^{5/6+ε}, from Kubota series plus Vaughan's identity. |
| Flicker, Invent. 57 (1980) | n-fold covers of GL(2), all n | Correspondence with automorphic representations of GL(2). At complex places the spectral parameter scales by 1/n (used by Louvel for n = 3). |
| Goldfeld–Sarnak, Invent. 71 (1983) | cofinite Γ with multiplier | Kloosterman zeta Σ_c K(m,n,c)N(c)^{−s} (mn ≠ 0) has poles at the discrete spectrum, including the residual one. |
| Kazhdan–Patterson, IHES 59 (1984) | covers of GL_r | Periodicity τ(m p^n) = N(p)^{1/2}τ(m) and Hecke relations. For n ≥ 4 the theta coefficients are only partly determined. |
| Livné, Crelle 375/376 (1987); Livné–Patterson, Invent. 148 (2002) | cubic | First moment of cubic exponential sums: c_θX^{5/6} + O(X^{3/4+ε}) (theta term), via Goldfeld–Sarnak. |
| Eckhardt–Patterson, PLMS 64 (1992) | quartic | Biquadratic theta coefficients, partial. |
| Bump–Friedberg–Hoffstein, Duke 63 (1991); BAMS 33 (1996); Friedberg–Hoffstein–Lieman, Math. Ann. 327 (2003) | n-fold | Metaplectic Whittaker functions; double Dirichlet series built from Gauss sums and n-th order twists (Eisenstein-side objects). |
| Proskurin, Zap. LOMI 82 (1979); LNM 1677 (1998) | double cover; cubic on H³ | Kuznetsov formula for real weights (half-integral weight = double cover). The book covers cubic Eisenstein series, θ₃, Whittaker functions and Hecke operators T_{ν³}. |
| **Louvel, Forum Math. 26 (2014), arXiv 1107.0197** | cubic, Q(ω) | The one metaplectic Kuznetsov over Q(ω) I found, built on Bruggeman–Motohashi and Lokvenec-Guleska (details below). |
| Herman, arXiv 1208.1705 | cubic | Dirichlet series of a cubic metaplectic form, via Kuznetsov. |
| **Dunn, ANT 19 (2025), arXiv 2403.13151** | fixed cubic cusp form f on Γ₂ ⊂ SL₂(Z[ω]) | Σ ρ_f(ν)Λ(λ³ν) ≪ X^{1−1/578+ε}, plus a bilinear bound with kernel ρ_f(ab) (details below). |
| David–Dunn–Hamieh–Lin, arXiv 2306.11875 (ANT, to appear) | quartic | Quartic Gauss sums at primes, using Suzuki's coefficients at squares. |
| **Bröker–Hoffstein, arXiv 1312.0568** | sextic | Hecke relations; sextic theta coefficients partly proved, partly conjectured (details below). |
| Kaneko, arXiv 2502.18366 | metaplectic covers | The main term of the prime geodesic theorem is governed by the largest residual eigenvalue. |
| Karasiewicz (J. Number Theory 2020, arXiv 1809.04692); Chen, arXiv 2411.13143 | double cover of SL(3); general covers | Whittaker coefficients of metaplectic Eisenstein series. No Kuznetsov and no large sieve. |
| Iwaniec, Invent. 87 (1987); Duke, Invent. 92 (1988); Ahlgren–Andersen (arXiv 1510.05191); Dunn (arXiv 1708.03003); Dunn–Zaharescu (arXiv 1903.03416) | double cover | Kuznetsov for half-integral weight, with the theta function as residual spectrum. |

Details for the key rows:
- **Louvel** [read].
  - Bruggeman–Kuznetsov formula for the cubic cover over Q(ω), with all K-types (s, p, l, q) and the theta as an
    explicit residual term.
  - Eisenstein series of K-type p ≠ 0 have no theta pole (his (3.8)(ii)).
  - A Selberg-type theorem: exceptional parameters of cubic metaplectic forms lie in ]0, 1/6] ∪ {1/3}, from
    Gelbart–Jacquet and Flicker with s̃ = s/3.
  - Level-uniform first moment, and a theta-free averaged bound Σ(D) ≪ D√X + X^{5/6}D^{1/3}.
- **Dunn** [read].
  - The bilinear bound, ≪ ((AB)^{1/2} + A^{3/2}B^{1/4})‖α‖_∞‖β‖₂, is proved by the Browning–Vishe circle method
    plus Voronoi.
  - The linear sums use Voronoi plus Heath-Brown's cubic sieve.
  - No Kuznetsov. He notes that opening ρ_f into Kloosterman sums through Poincaré series, as Duke–Iwaniec do for
    holomorphic forms, is not available for Maass forms. No Deligne-type or Waldspurger-type bound for ρ_f is known.
  - At level Γ₂ the discrete spectrum is θ₃ plus tempered cusp forms (Patterson's cubic Shimura lift).
- **Bröker–Hoffstein** [read].
  - Hecke relations give τ₆(p⁵) = 0, τ₆(p⁴) = G₁(1,p) (a sextic Gauss sum) and τ₆(p) = G₂(1,p)τ₆(p³).
  - The coefficients at squarefree indices are undetermined.
  - Conjectured from numerics: τ₆(p²) = 2G₁⁽³⁾(1,p)/√3 up to a root of unity (a *cubic* Gauss sum), and
    τ₆(p)² ≈ unit·g₃/|p|^{1/2}·(factors of norm 3, 7, 13).

**Not found:**
- a Kuznetsov formula for the 6-fold Kubota character, or for any n ≥ 4;
- a DI-type spectral large sieve for metaplectic cusp forms of degree ≥ 3;
- a spectral proof of any upper bound for an n-th order character large sieve.

### 1.2 Spectral large sieves without a cover, and the critical point

- **Deshouillers–Iwaniec, Invent. 70 (1982).** For Γ₀(q): Σ_{|κ_j|≤K}|Σ_{n≤N} a_nρ_j(n)|² ≪ (K² + N/q)^{1+ε}‖a‖².
  The exceptional eigenvalues may be weighted by X^{2θ_j} for free only while X ≤ q/N. Also bilinear forms in
  Kloosterman sums.
- **Sum formulas for complex and number fields.**
  - Bruggeman–Motohashi, Funct. Approx. 31 (2003), arXiv math/0205066 (PSL₂(Z[i]));
  - Lokvenec-Guleska, thesis, Utrecht 2004 (Γ₀(I) over any imaginary quadratic field);
  - Bruggeman–Miatello, GAFA 8 (1998) and Mem. AMS 919 (2009);
  - Motohashi, Proc. Japan Acad. 72A (1996) (Picard group).
- **Watt, JNT 140 (2014), arXiv 1302.3112.** Spectral large sieve for Γ₀(q₀) ⊂ SL₂(Z[i]) at all cusps, "not quite a
  perfect analogy" of DI.
- **Qi, arXiv 2404.09085.** The true DI analogue for PGL₂(Z[i]) on square windows:
  Σ_{|ν|,|p|≤K} + Eis ≪ (K⁴ + X^{1+ε})‖a‖² with X ≍ N(n). It extends to Q(√−D) with class number 1.
- **Blomer–Brumley, Annals 174 (2011).** θ ≤ 7/64 over every number field.
- **Pascadi, Forum Math. Pi 14 (2026) e8, arXiv 2404.04239.** The *first* savings in the exceptional spectrum at the
  **critical point** N ≍ q (sequence length = level), for sequences with sparse Fourier transforms.

### 1.3 n-th order character large sieves (status, Oct 2026)

- **Earlier bounds.**
  - Heath-Brown: quadratic, Acta Arith. 72 (1995), perfectly orthogonal; cubic, Israel J. Math. 120 (2000).
  - Blomer–Goldmakher–Louvel, IMRN 2014: (AB)^{2/3} for all n ≥ 3.
  - All are elementary: Poisson plus recursion.
- **Dunn–Radziwiłł, arXiv 2109.07463 (Annals, accepted).** The cubic sieve is sharp under GRH. Also a level-aspect
  Voronoi formula for cubic Gauss sums and a corrected (dispersion) sieve.
- **de Faveri–Dunn–Hoffstein, arXiv 2607.07911** [read].
  - Unconditional sharp lower bound for cubic; A + B + A^{3/4}B^{1/2} + A^{1/2}B^{3/4} for quartic.
  - Conjecture (1.8) for all n.
  - Method: Rankin–Selberg (Zagier regularization) for metaplectic Eisenstein series and theta, plus Lindelöf on
    average for Kubota series in the twist aspect, their (2.9).
- **de Faveri, arXiv 2610.04045 (2 Oct 2026)** [read].
  - The upper bound of (1.8), for every n ≥ 3, for the n-th-power-free kernel.
  - Elementary: Poisson, recursion over n-th-power-free kernels, and coupling of root numbers.
  - The excess A^{1−1/n}B^{2/n} comes exactly from the n-th power part e of the dual modulus, E ≪ (B²/A)^{1/n}. That
    is the journal's dual multiplicity.
- **Xu–Sang, arXiv 2610.17675.** Matching lower bound for n = 6, with Gauss-sum extremal vectors.

**Reading.** The sharp bound is now a theorem for n = 6. No paper formulates the off-V refinement. Spectral theory of
covers enters the subject only through Kubota series (Eisenstein Fourier coefficients) and Rankin–Selberg, never
through Kuznetsov.

## 2. The target and the chain

### 2.1 The statement a spectral approach would have to prove

Notation (as in `../rip/theta/theta_core.py`):
- rows z: squarefree ideals coprime to 6 with N(z) ∈ [B, 2B];
- sources n: primary, with squarefree norm N(n) ≤ L, coprime to 6;
- M(z, n) = χ_z(n) = (n/z)₆;
- g(k, z) = Σ_{d mod z} (d/z)₆ e(Tr(kd/(√−3 z))), with g̃(k, z) = g(k, z)/√N(z) and g̃(z) = g̃(1, z);
- U a smooth radial profile.

Spike span:
- V_γ = span{θ_{m,u} : N(m) ≤ B^{1−6γ}, u a unit} ⊕ V_low;
- θ_{m,u}(z) = conj g̃(z)·χ_z(m)χ_z(u)·U(N z/B), in the |Eᵀc|² convention of the older scripts. The |E^H b|² convention
  of `../rip/theta/theta_offspan.py` conjugates it.
- V_low is the low-frequency block that carries the outlier.

**(LS off V)** ‖(I − P_{V_γ})M‖² ≤ B^{1+γ+o(1)} at L = B. The binding point is L ≈ B^{0.96} with γ ≈ 0.015.
- It comes with the detector condition ‖P_{V_γ}M a‖² ≤ L·B^γ‖a‖² for the leaf's vectors.
- The corrected form `CorrectedLargeSieve`, in progress under `../lean/arvi_kwall/`, packages both.
- The γ-loss is forced: every twist with N(m) ≤ B^{1−6γ} has excess ≥ B^γ.

### 2.2 The dictionary [derived]

1. **Factorization.** For squarefree z, g(n, z) = conj χ_z(n)·g(z) and |g(z)|² = N(z). Hence
   - M(z, n) = g̃(z)·conj g̃(n, z), i.e. **M = D·E**, with D = diag(g̃(z)) unitary and E(z, n) = conj g̃(n, z);
   - rows are the *moduli* of Gauss sums, and sources are their *frequencies*.
2. **Twists are frequency shifts.** For (z, mn) = 1, χ_z(m)·g(n, z) = g(n m⁵, z). A twisted theta is the same object
   at a shifted frequency, with a coprimality condition at m (level m).
3. **Eisenstein coefficients.** Fix a Hecke character ψ of conductor 𝔪 and infinity type (z/|z|)^p. Up to Γ and
   Bessel factors, Σ_z ψ(z)g(n, z)N(z)^{−s} is the n-th Fourier coefficient of Kubota's Eisenstein series on the
   6-fold cover twisted by ψ (Kubota; Bröker–Hoffstein (1.1); Louvel (3.8) with K-types for n = 3).
   - Its pole (normalized as Σ g̃ N^{−s}) is at s = 2/3, the theta point.
   - The pole occurs only for p = 0 and only for twists of sextic-residue type (ψ = χ_·(m)·(unit character)).
   - The residue is a theta Fourier coefficient at the shifted index.
   - There are **no cuspidal poles**. Those appear only in the Kloosterman zeta Σ_c K(m,n,c)N(c)^{−s} with
     mn ≠ 0 (Goldfeld–Sarnak; Louvel §1).
4. **Mellin–Hecke analysis of the rows.**
   - Take Hecke characters of conductor N(𝔪) ≤ Q and Mellin windows |p|, |t| ≤ T, with Q²T² ≍ B. The classical large
     sieve for them in the variable z is sharp.
   - So, up to B^ε, M is equivalent to the map a ↦ (Σ_n a_n K_ψ(n; p, t)), where
     K_ψ(n; p, t) = B^{−1/2}Σ_z U ψ(z)(z/|z|)^p N(z)^{−it} g̃(n, z).
   - These K_ψ are B-pieces of the Eisenstein coefficients in item 3.
5. **Contour shift.** K_ψ splits into a residual part and a continuous part.
   - Residual part: B^{1/6}·Û(2/3 − it)·δ_{p=0}·ρ_ψ(n). These are the theta spikes.
   - Continuous part: the coefficients on the unitary line, i.e. the tempered Eisenstein spectrum.

**What this explains** (all [derived], consistent with the logs):
- **V is the residual spectrum at all levels and twists.**
  - One direction per twist m, rank one in the profile. The functional is Û at the pole, Xu–Sang's
    I(U) = ∫U t^{−5/6}dt in their normalization. This matches `theta_profile.py`: I(U) = 0 kills the excess.
  - The weights are (B/N(m))^{1/6} = (B/N(m))^{θ_res} with θ_res = 1/6. They end near N(m) ≈ B²/L, where the dual
    length runs out.
  - So yes: the twisted thetas are "the residual spectrum at all levels". That is why V has dimension ≍ B^{1−6γ}.
- **Only one conjugation carries the pole.** In the |Eᵀc|² convention, each row vector pairs with column n through a
  Kubota sum at some index:

  | row vector | index | residue | numerics |
  |---|---|---|---|
  | conj g̃·χ(m) | mn (squarefree) | τ₆(mn): not fixed by Hecke theory, non-zero on average | excess |
  | g̃·χ(m) | (mn)⁵ | 0, since τ₆(m′p⁵) = 0 (Kazhdan–Patterson) | none |
  | conj g̃·conj χ(m) | n·m⁵ | 0, same relation at the primes of m | none |
  | plain χ(m) | none (no Gauss sum) | no pole | none |

  - The last column is from `theta_powers_B30000.log` and `theta_twists_B30000.log`.
  - `theta_offspan.py` uses the |E^H b|² convention, which reverses the conjugations.
  - Not computed: the coprimality correction at the primes of n (de Faveri–Dunn–Hoffstein §2.2).
- **Gauss-sum powers are neutral.**
  - Davenport–Hasse writes g̃₆² and g̃₆³ as lower-order Gauss sums times Jacobi-sum Grössencharacters.
  - Those characters have non-zero infinity type, so the twisted Eisenstein series has p ≠ 0 and no residue.
  - Hence conj G², G² and conj G³ carry no excess, and the plain rows (no Gauss sum, no pole) carry none either.
- **(LS off V) is equivalent to a large sieve for the polar-subtracted family:**
  sup_a Σ_{(ψ,p,t)} |Σ_n a_n (K_ψ − K_ψ^{res})(n; p, t)|² ≪ B^{γ+ε}(#window + L)‖a‖².
  This is an exact reformulation, not a reduction.

### 2.3 The proposed chain against the actual one

| step | proposal | what happens [derived] |
|---|---|---|
| 1 | Poisson / Voronoi | Poisson in z gives Gauss sums g(k; n, n′) of modulus nn′ and frequency k. The dual is the same sieve with rows k and a Gauss-twisted vector. |
| 2 | → metaplectic Kloosterman sums | Only degenerate ones: g(k, c) = K(0, k; c), the Eisenstein (Kubota) coefficients. Two-frequency sums never arise, because same-modulus products collapse: g(n,z)·conj g(n′,z) = N(z)·χ_z(n′n⁵). |
| 3 | Kuznetsov on the cover | Needs mn ≠ 0. What applies instead is Kubota's Fourier expansion with its functional equation s ↔ 2 − s, which maps window B to window L²/B. At B = L that is the journal's self-duality. |
| 4 | spectral LS: cusp + continuous + residual | The cuspidal part is absent and the residual part is V. The continuous part is the original problem. |

Spectral theory does enter legitimately in three places, all outside the generic core at the balanced point:
- **Voronoi for structured vectors** yields genuine Kloosterman sums of the cover (Dunn–Radziwiłł's level-aspect
  Voronoi; Dunn 2025).
- **Second moments of Kubota series in the twist aspect**, Σ_{N(n)≤X}|ψ(n, 1+it)|² ≪ X^{1+ε}, via Rankin–Selberg on
  the *trivial* cover (de Faveri–Dunn–Hoffstein §5). This is where GL(2)/Q(ω) tools fit (Bruggeman–Motohashi,
  Lokvenec-Guleska, Watt, Qi).
- **The fourth-moment route (M₄).** There g̃₆² = J̃·g̃₃ brings in the cubic cover at non-zero K-type.

## 3. Size accounting

- **Residual numerology** [read + derived].
  - In H³ normalization Kubota's E⁽ⁿ⁾ has its pole at 1 + 1/n, with eigenvalue 1 − 1/n². That is 8/9 for n = 3: the
    constant in the Lean stack, §5.
  - At balance the sharp bounds have excess B^{1/n}: B^{4/3} (n = 3), B^{5/4} (n = 4), B^{7/6} (n = 6).
  - In DI's language the theta is an exceptional eigenvalue with θ = 1/n, sitting at the critical point.
- **A DI-quality inequality on the cover** [heuristic].
  - Assume, for each level 𝔪, that cusp + Eisenstein + residual terms are ≪ (N(𝔪)²T⁴ + L)^{1+ε}‖a‖². Here
    vol Γ₁(𝔪) ≍ N(𝔪)², the Weyl law over all K-types gives ≍ vol·T⁴ forms, and Qi's square-window bound has this
    shape.
  - The rows of M are the Eisenstein points of all levels N(𝔪) ≤ Q in a window T, with Q²T² ≍ B.
  - Summing over levels gives Δ ≲ B²/Q + QL. The optimum is Q = B/√L with T ≍ 1, giving **Δ ≲ B^{3/2+ε}** at B = L.
  - With a single level and all characters mod 𝔪, Δ ≲ B².
  - Both are worse than B^{7/6}, and even than Blomer–Goldmakher–Louvel's B^{4/3}. The cost is the cuspidal spectrum,
    which does not occur in M. Subtracting the residual spectrum inside such an inequality changes nothing, so it
    reaches neither (B + L)B^ε nor any exponent below 7/6.
- **The GL(2) precedent at the critical point** [read].
  - DI's exceptional large sieve saves nothing at N ≍ q.
  - Pascadi (2026) broke this only for sequences with sparse Fourier transforms.
  - The balanced sextic point is that critical point, with the removable residual θ = 1/6 in place of exceptional
    eigenvalues. What remains after removal is the generic part, where no family has savings.
- **Dunn 2025** [read].
  - His bound is for one fixed cusp form. It saves A^{1/2} over Rankin–Selberg in its first term, and its second term
    beats Rankin–Selberg only for B ≥ X^{2/3}.
  - Its residual analogue (f = θ₆, kernel ρ_θ(mn)) has the shape of the detector condition, not of (LS off V).
- **The exceptional cusp spectrum, where Kuznetsov does enter** [derived].
  - Flicker (all n) plus Blomer–Brumley put the exceptional cusp parameters of the 6-fold cover at ≤ 7/384 ≈ 0.018,
    provided the archimedean scaling is s̃ = s/n as in Louvel's n = 3.
  - That is already above the K-wall budget γ ≈ 0.015, unless Selberg's conjecture is known at levels up to
    B^{1−6γ}.

## 4. Obstacles, and where the low-frequency outlier sits

1. **Structural, and decisive.** M has no cuspidal component; the off-V part is an Eisenstein-only family, and the
   self-duality is Kubota's functional equation (§2.3).
2. **Uniformity in level and twist.**
   - V has about B^{1−6γ} directions, which means residual spectrum at levels up to B^{1−6γ}.
   - Stating even the residual part with errors needs Lindelöf on average for twisted Kubota series, uniformly in the
     level. That is proved for n = 3, 4 (de Faveri–Dunn–Hoffstein), not for n = 6.
3. **The theta coefficients at squarefree indices are unknown for n = 6** (Kazhdan–Patterson; Bröker–Hoffstein).
   - V can be handled abstractly, as residues.
   - Explicit main terms, such as the outlier's, cannot be evaluated.
4. **The complex place.**
   - K-types (ν, p), with Bessel kernel J_{ν−p}(z)J_{ν+p}(z̄).
   - Separating the rows needs square windows in (t, p).
   - Watt and Qi settle this for the trivial cover. For a Kubota character only n = 3 is written down (Louvel).
5. **The low-frequency outlier** [derived + heuristic].
   - It is not first-order residual: it carries no Gauss-sum phase and is orthogonal to the twisted thetas.
   - It is not continuous spectrum, since tempered parts do not grow.
   - If its B^{1/6} rate is asymptotic, it is a **second-order residual (corner) term**. Two candidate mechanisms:
     - the double residue of Z(s, w) = Σ χ_z(n)N(z)^{−s}N(n)^{−w} where the row-theta and source-theta divisors meet
       (the journal's conjecture);
     - the conj source-theta channel. M maps conj g̃(j,·)U to z ↦ Σ_n conj g̃(jz, n)U ≈ L^{2/3}conj ρ_θ(jz). That is
       the sextic theta coefficient at the squarefree index jz, exactly what Hecke theory leaves undetermined.
       Bröker–Hoffstein's conjectural τ₆(p)² contains elements of norm 7 and 13, and the outlier loads on primes of
       norms 7, 13, 31 and 37. This is weak evidence, since 7 and 13 are the two smallest split primes.
   - Either way, spectral theory predicts K-type 0 and rank one in a radial profile.

**Tests** (existing scripts; days):
- **T1, angular.** Measure the excess of conj g̃·χ(m)·(z/|z|)^p·U as a function of p, using primary generators.
  Prediction: only p = 0 carries it. This tests the dictionary directly.
- **T2.** Angular spectrum of the outlier's left singular vector. A residual-type outlier is concentrated at p = 0.
- **T3.** Radial-profile rank of the outlier, as `theta_profile.py` measured it for theta.
- **T4.** The outlier per row class mod 4. The theta excess is per class; a cross-class effect is not.
- **T5, cubic proving ground.** Rerun the off-V experiment for the cubic family.
  - The excess there scales like B^{1/3}, about 31 at B = 3·10⁴, against B^{1/6} ≈ 5.6 for the sextic.
  - V is explicit there, since τ₃(c) = g̃₃(c).
  - If (LS off V) visibly fails there, the sextic version is not worth pursuing.

## 5. What the Lean stack already contains

Location: `../../submissions/openai-baseline/src/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/Eisenstein/`.
It is identical to the `lean-env` copy.
- 82 files, about 53k lines and 3.8k declarations; no `sorry` by grep. I did not rebuild it or check axioms.
- Namespace `CubicEisenstein`: the **cubic** cover only. The group is the Kubota kernel `globalKubotaKernel` inside
  the level-3 subgroups of SL₂(Z[ω]), acting on H³ = SL(2,ℂ)/SU(2).

| ingredient | files / declarations [Lean] |
|---|---|
| H³, invariant volume, fundamental domains, cusp cover | `HyperbolicSpace`, `HyperbolicVolume`, `FundamentalDomain`, `QuotientTopology`, `CuspIntegration` |
| L² of the quotient, level action by unitaries | `KernelQuotientL2 := Lp ℂ 2 (integralQuotientVolume globalKubotaKernel)`; `kernelLevelUnitary` |
| self-adjoint Laplacian (variational), Green identities | `kernelEnergyLaplacian_selfAdjoint`, `GreenIdentity`, `DirichletForm` |
| Fredholm property below the continuous spectrum; theta eigenspace finite-dimensional | `kernelSpectralFormOperator_isFredholm` (parameter in [0,1)), `kernel_theta_spectral_fredholm` (at 8/9), `kernelThetaNull` |
| meromorphic resolvent, with the theta projection as residue | `kernelSpectralResolvent_meromorphicAt`; `kernelSpectralResolvent_decomposition`: R(z) = (17/9)/(8/9 − z)·P_θ + regular |
| Eisenstein series (Re s > 2) and its L²-correction continuation near s = 4/3; residue vector in the 8/9 eigenspace | `Rows`, `SeedHeight`, `CutoffApproximation`, `kernelEisensteinResidueVector_graph` |
| Fourier–Whittaker coefficients (K-Bessel); scattering coefficients = cubic Gauss-sum Dirichlet series, continued, with residues | `ScatteringCoefficients`, `continuedNonzeroScattering_residue_limit`, `scatteringCoefficient_explicit_ramified`, `BesselMellinTransform` |
| Gauss sums: CRT, twisted multiplicativity, frequency twists | `arithmeticResidueSum_crt`, `cubicUnitGaussSum_frequency_twist`, `PrimePowerGaussSums` |
| Hecke theory for cubes and Patterson's determination of θ₃ | `CoverTrace`, `Correspondence*`, `cubicSource_cubeAverage` (eigenrelation), `sourceResidualFourierCoefficient_cube_sqrt` (τ(hp³) = √N(p)·τ(h)), `PrimeRecurrence`, `PrimeGaussFactors`, `ResidualOrthogonality` |
| sextic reciprocity with an explicit sign mod 4 | `sexticReciprocityPhase`, `idealRowHom_ideal_reciprocity` (`ConjugateLevelAction`) |
| Heath-Brown's cubic large sieve over Z[ω] | `CubicSieve/Sharp.lean`, `sieveNorm_sharp`: ≪ (MN)^ε(M + N + (MN)^{2/3}) |

Research Lean that also bears on this:
- `../lean/arvi_primeface/Duplication.lean`: sextic Gauss sums at primes equal conjugate cubic ones times a Hecke
  factor.
- `../lean/arvi_kwall/FlatDilution.lean`.

**Missing:**
- anything for the 6-fold Kubota character;
- cusp forms, Poincaré series, and two-frequency Kloosterman sums;
- Kuznetsov / Bruggeman–Motohashi;
- the Plancherel or Maass–Selberg expansion of the continuous spectrum, and the Weyl law;
- the complex Bessel kernels;
- spectral large sieves;
- the Shimura or Flicker correspondence;
- Rankin–Selberg unfolding.

**Reuse.**
- The stack formalizes, for n = 3, exactly the half that §2.2 shows is relevant: Eisenstein coefficients plus
  residual spectrum.
- A sextic port is needed:
  - the eigenvalue constant changes from 8/9 to 35/36, together with the group;
  - the arithmetic layer is n-specific, with p⁶ correspondences, and has only partial theta coefficients.
- The Kuznetsov half would be new formalization from scratch, and §2 says it is not needed.

## 6. Verdict, first lemma, cheaper results

- **Is this a realistic program for a power saving at B = L?** No, not through DI plus Kuznetsov on the cover.
  - There is a structural mismatch (no cuspidal component), and the self-duality is inherited.
  - The problem stays in the class of the three walls (`README.md`), and the spectral version adds no lever.
  - No timescale can be named, because no first step has been identified. Do **not** build a Kuznetsov formula for
    the 6-fold cover in order to attack (LS off V).
- **The first concrete lemma, if spectral work is done: Lemma S1, the sextic residual dictionary.**
  - Data: k coprime to 6; ψ a Hecke character of conductor 𝔪 coprime to 6k and infinity type (z/|z|)^p; U smooth on
    [1,2].
  - Claim:
    Σ_{z sqfree, (z,6𝔪k)=1} U(N z/B)ψ(z)g̃(k,z) = 1[p = 0, ψ ∈ Ψ_res]·Û(2/3)·c_ψ(k)·B^{2/3}
    + O_ε(B^{1/2+ε}(N(k𝔪)(1+|p|))^{A}),
    where Ψ_res is the finite set of sextic-residue twists and c_ψ(k) are residues (theta coefficients at level 𝔪,
    with the coprimality correction).
  - Mean square: Σ_{N(k)≤X}|c_1(k)|² ≍ X^{5/6}.
  - Proof route: Kubota / Bump–Friedberg–Hoffstein / Friedberg–Hoffstein–Lieman continuation, convexity, and
    Rankin–Selberg in the manner of de Faveri–Dunn–Hoffstein §5. Paper-level work of months; I did not attempt it.
  - It gives:
    - a theorem-level V, with its twist, profile and K-type structure;
    - the main terms of a sextic Dunn–Radziwiłł corrected sieve (target 0, `DR_PRIME_SIEVE.md`) and of the detector
      condition;
    - the predictions of T1–T3.
  - In Lean it would be a port of `WhittakerContinuation`, `ScatteringResidues` and `MeromorphicResolvent` to the
    sextic character: large, but on existing rails.
- **Cheaper partial results that still help:**
  1. T1–T5 (days). T1 checks the dictionary. T5 decides whether (LS off V) is plausible at all, in the family where the
     excess is largest and V is explicit.
  2. (LS off V) for smooth prime vectors at L ≤ B^{3/5}: the sextic form of the corrected Dunn–Radziwiłł sieve. Inputs
     are Lemma S1, the twisted Heath-Brown–Patterson bound H2, and Lindelöf on average.
  3. The detector condition for the leaf's vectors. It is unbalanced (dual length B^{1+6γ}) and is the residual
     analogue of Dunn's bilinear theorem.
  4. Structured vectors at the balanced point, the analogue of Pascadi's sparse-Fourier sequences: plain sums, prime
     pools and their products, whose Mellin–Hecke transforms are sparse. This is the (MC) program in `README.md`.
     Spectral theory supplies the residual bookkeeping there, not the saving.
