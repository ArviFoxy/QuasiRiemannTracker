# Round 11 — P1 (use (b)) fresh look: quadratic twists of slot-twisted cubic-theta vectors

Target: Σ_{N(k)≤K} |Σ_n c(n)χ_k(n)W(N(n)/N)|² ≪ K^{1+0.16δ'+o(1)} Σ|c|², c = g̃·A,
A(n) = Σ_{P~L} a(P)N(P)^{-1/2} conj((n/P)₃), N = K^{1+δ'}, δ' ≈ 1.1e-4, L ≈ K^{0.17}.

Labels: PROVED (argument complete up to routine bookkeeping noted), SKETCH (argument given,
one named input not yet checked against the literature), HEURISTIC, NUMERIC.

## 0. Context read
P1_PROBLEM.md, atom1/README.md, literature/README.md, round11/README.md, sextic_moment_notes.md,
LOG.md (slot-cost entries). Notes below are new unless marked.

## 1. Conventions checked against Dunn–Radziwiłł (arXiv 2109.07463, LaTeX source)
- DR (2.3): g̃(ab) = conj((a/b)₃) g̃(a)g̃(b) (the overline is lost in pdftotext; checked in source).
  So the slot twist conj((n/P)₃) is the SHIFT twist: g̃(n)conj((n/P)₃) = g̃(nP)/g̃(P). Matches P1_PROBLEM.
- DR (eq:bb): g̃(c)³ = μ(c)·c/|c| (c ≡ 1 mod 3). Note the μ(c): checked numerically (−1 at primes).
- DR Prop 5.2 (impfunc): R(s) = Σ_c g̃(c)conj((c/r)₃)(c/|c|)^ℓ N(c)^{-s} has functional equation with factor
  conj(g(r))/N(r)^{2s} and a dual series whose coefficients carry the Ramanujan weight
  b†_r(ν) = μ(r/(λν,r))φ(r)/φ(r/(λν,r)). Net effect: the shift twist has CONDUCTOR N(r), not N(r)².
- DR Lemma "functwisteq" (twisted theta under the Fricke map, any ψ periodic mod r with ψ̂ supported
  on units): the dual twist is ψ̃(u) = Σ_x ψ(x)S_{1/3}(x,u;r) with the cubic Kloosterman sum
  S_{1/3}. For primitive ψ this evaluates (two lines) to
      ψ̃(u) ∝ τ(ψ)·τ(ψ·(·/r)₃)·conj(ψ(u))·conj((u/r)₃),
  i.e. **dual twist = conj(ψ)·conj((·/r)₃)**, Ramanujan sum when ψ·(·/r)₃ is principal.

## 2. Two corrections to the framing (PROVED from DR's two statements above)
(C1) Critical length of S(k,P) = Σ_n g̃(n)χ_k(n)conj((n/P)₃)W(N(n)/N).
  ψ = χ_k·conj((·/P)₃) mod kP. Dual twist conj(ψ)conj((·/kP)₃) = (·/k)₆ × (principal mod P):
  the P-part is a Ramanujan sum, so the dual lives on m = Pm'. Conductor N(k)²N(P), dual length
  K²L/N, **critical length K·L^{1/2}**, not KL. (Dead zone for use (a)/(b): (K, KL^{1/2}) in the
  quadratic form, reflected to (KL^{1/2}, KL) in a sextic form; see C2.)
  Consequence for atom1 README §5 ("re-reflect: at T_d = H+z nothing to re-reflect"): at the
  binding of use (a) (N = KL) each S(k,P) is BEYOND critical and reflects to length exactly K
  (sextic twist). It does not help (below), but the stated reason is wrong.
(C2) Quadratic twists of θ₃ are dual to SEXTIC twists: ψ = χ_k ⇒ dual twist χ_k·conj((·/k)₃) = (·/k)₆
  [(·)₂ conj((·)₃) = (·)₆]. Equivalently g̃(m)(m/k)₆ = χ_k(m)g̃(mk)/g̃(k).
  So "without slots, Voronoi sends N > K to K²/N < K and Goldmakher–Louvel is diagonal"
  (atom1 README §8) is not right: after Voronoi one needs a SEXTIC large sieve (K rows, K²/N
  columns), whose general form (de Faveri) has Gauss-bias terms K^{5/6}M^{1/3}, K^{1/3}M^{5/6} ≫ K.

## 3. Hasse–Davenport lemma (PROVED; classical + numerically checked)
For squarefree m ≡ 1 mod 3 (DR conventions, ě(z) = e(Tr z)):
    g̃₃(m)·g̃₆(m) = μ(m)·conj((4/m)₆)·g̃₂(m)·(m/|m|),
with g̃_n(m) = |m|^{-1}Σ_{x mod m}(x/m)_n ě(x/m). Proof: HD duplication g(χ)g(χρ) = χ̄(4)g(χ²)g(ρ) at
primes with χ = (·/π)₆, plus g̃₃³ = μ·m/|m| (DR) at primes; the cubic cross-symbols of g̃₃ and g̃₆ cancel
and the quadratic reciprocity signs are exactly those of g̃₂. Script: scratchpad hd_check.py
(primes N(π) < 400: ratio −1 at every prime, +1 at every product of two primes); g̃₂(m) and (4/m)₆
depend only on m mod 4 (g2_comp.py). So ξ₀(m) := conj((4/m)₆)g̃₂(m)(m/|m|) is a finite combination of
Hecke characters of ∞-type z/|z| (CM characters of Q(ω): L(s, ξ₀ψ) = normalized L-functions of
Mordell curves y² = x³ + D with D | 432·(small)). **The Möbius function is intrinsic.**

## 4. The slot-free skeleton L = 1 is NOT easy (analysis; route-specific claims marked)
Q₀(K,N) := Σ_{k sqfree, N(k)≤K} |Σ_n g̃(n)χ_k(n)W(N(n)/N)|². Target K^{1+o(1)}N at N = K^{1+δ'}.
(a) Voronoi (C2): ≈ (N/M)Σ_k|Σ_{m~M} b(m)(m/k)₆|², M = K²/N, b ≈ g̃₃·(class fn mod 9).
(b) Poisson in k: off-diagonal ≈ (K/M)Σ_{h≲H}(signed) X(h)conj(Y(h)), H = M²/K, with
    X(h) = Σ_m b(m)g̃₆(m)conj((h/m)₆) = Σ_m μ(m)ξ₀(m)conj((h/m)₆)W̃   [by §3].
(c) Frequencies h = d²a⁶ (d from the squarefree sieve on k) make the character trivial:
    X = Σ_{(m,ad)=1} μ(m)ξ₀(m)W̃ — a Möbius sum of a FIXED CM Hecke character. Their total is
    ≈ (K/M)H^{1/6}·Q(Mob)/ζ_{Q(ω)}(2), Q(Mob) a fixed Hermitian form in the
    class-restricted Möbius sums Σ_{m≡α}μξ₀(m)W̃ (reciprocity signs; d-sum Σμ(d)N(d)^{-2} converges). With |Σμξ₀| replaced by M this is exactly de Faveri's bias
    term A^{5/6}B^{1/3}·B (A = K, B = M): the sixth-power frequencies ARE the Gauss bias, and for the
    theta vector the bias is multiplied by (|Σ_{m~M}μξ₀|/M)².
(d) PROVED (sketch): Q₀ ≪ K^{1+ε}N for N ≥ K^{3/2+ε} (then H < 1: only h = 0 survives), and trivially
    for N ≤ K. CONDITIONAL: under GRH for Hecke L-functions of Q(ω), Σ_{h≲H}|X(h)|² ≪ H M^{1+ε} ≤ M^{2+ε},
    so Q₀ ≪ K^{1+ε}N for all N.
(e) Route-specific obstruction for K < N < K^{3/2}: need |Σ_{N(m)~M}μ(m)ξ₀ψ(m)| ≤ M^{1−1/12+ε}
    (H ≈ M at N ≈ K), i.e. a zero-free strip Re s > 11/12 for L(s, ξ₀ψ). Unconditionally only
    M·exp(−c√log M). HEURISTIC: a zero of L(s,ξ₀ψ) with β > 11/12 would make Q₀ exceed K·N by
    K^{2β−11/6} near N ≈ K, unless the Hermitian form Q(Mob) degenerates on the zero's
    contribution (no reason seen) or the remaining frequencies cancel it (they are unrelated characters).

## 5. Slots: per-slot vs combined self-dual points; root numbers (PROVED from DR + reciprocity)
- Root number of ψ = χ_k·conj((·/P)₃) mod kP: from ψ̃ = τ(ψ)·(λ/kP)₃ψ(λ⁸)·G(ψ·(·/kP)₃, u) and CRT,
  the k–P cross factors are χ_k(P)²·conj((k/P)₃)(P/k)₃ = 1 (cubic reciprocity). So ε(k,P) = ε₁(k)ε₂(P).
- Dual of S(k,P): ∝ ε₁(k)ε₂(P)·Σ_{u'~K²L/N} g̃(Pu')(Pu'/k)₆ W̃ (+ a term smaller by L^{-1/6} in mean square,
  from the "−1" of the Ramanujan sum). Single slot: K²L/N columns ⇒ self-dual point N = K·L^{1/2}.
- Combination Σ_P α_P S(k,P): dual vector c'(n') on n' = Pu', i.e. K²L²/N columns ⇒ self-dual point
  N = K·L. So STRUCTURE.md's "slot raises the conductor by N(P)²" is wrong per slot but its consequence
  (combined dead zone (K, KL)) survives. At use (a) (N = KL) the combined problem is exactly self-dual
  (quadratic form ↔ sextic form, same column count KL); nothing gained by reflecting the combination.
- Consistency check of the premise: in the marked inverse moment the slot enters as ψ_u(P)ψ_u(n) = ψ_u(nP);
  Poisson in u gives sextic Gauss sums at nP and §3 turns μ(nP)g̃₆(nP) into ξ₀·conj(g̃₃(nP)): a DILATE.
  So the slot really is the shift twist (P1_PROBLEM is right; the N(P)² conductor statements are not).

## 6. Single-mark lemma at use (a) (SKETCH, unconditional; new)
At N = K·L (use (a): K = Z^{0.742}, L = Z^{0.129}), each S(k,P) is past its own critical length K·L^{1/2}.
Voronoi (DR functwisteq + Mellin separation of the K_{1/3}-transform) gives length-K sextic sums, and
de Faveri's sextic sieve at A = B = K (bias K^{7/6}) yields
    F_P := Σ_{k} |S(k,P)|² ≪ N·K^{7/6+ε}    (vs. N² = N·K·L from the quadratic sieve).
Saving L/K^{1/6} = Z^{0.0053}; in the (K + N^{1−η}K^η)Σ|c|² form this is η ≈ 0.041 (> 0.0076 needed).
It controls the slot-diagonal part Σ_P|α_P|²F_P only. The cross terms (Lemma MM) stay open:
trivially MM ≤ K^{13/3}L⁴, needed ≈ K⁴L⁴. So this proves P1(a) only for slot weights whose Gram
matrix is diagonal on average (e.g. random signs), which the count may not allow.
At use (b) (N = K^{1+δ'}) nothing similar: N < K·L^{1/2}, the reflected sums are longer (K^{1−δ'}L > K).

## 7. Tool-by-tool (where each one stops)
- DR Prop 9.1 (corrected cubic sieve). Works for CUBIC rows because the Poisson dual of a shift twist is
  again a shift twist (conductor N(h)): Voronoi makes the dual short and isolates Patterson's term,
  i.e. it removes the (AB)^{2/3} bias. It never beats max(A,B) (its errors contain X and B^{2+2η}).
  For QUADRATIC rows there is no bias to subtract; the obstruction is the N-term itself, and the Poisson
  dual of a quadratic row is a quadratic twist (conductor N(j)²), sub-critical for most j ≤ N²/K.
  The dispersion step does not close. Useful by-product: an n = 6 analogue of Prop 9.1 is exactly what
  §4 would need for the second de Faveri term (HEURISTIC: for the theta vector that term costs only
  H^{1/3}M^{3/2} ≤ M² because ⟨μξ₀, sextic-theta direction⟩ ≈ Σ g̃₃·(class) ≪ M^{5/6}, Heath-Brown).
- DR Prop 10.1 (Type II). Pointwise in the row; needs both variables in [X^{1/3+ξ}, X^{1/2−ξ}]; ours are
  P ~ X^{0.15}, n ~ X^{0.85}. A pointwise saving cannot touch the N-term of a mean square.
- dFDH (Rankin–Selberg, cubic-twist aspect) and DDDS (Σ_m|ψ(hm,s)|²): both are about shift twists =
  Fourier indices of θ₃ along rays, in the large-family regime (A ≫ critical length A^{1/2}).
  Quadratic twists are not Fourier indices of θ₃: by §3, S_k = Σ_n μ(n)ξ₀(n)conj(g̃₆(k³,n))W, a
  Möbius-weighted index-k³ coefficient of the SEXTIC Eisenstein series; the μ in the summed variable
  blocks unfolding. And the family is thin (K rows vs per-slot critical length K L^{1/2}).
- DIPP WMDS / mixed double series. First moment Σ_{k,n} g̃(n)(n/k)₂N(n)^{-s}N(k)^{-w}: Cartan integers
  (a_{kn}, a_{nk}) = (2, 1) ⇒ B₂/C₂, order 8; the s-equation turns χ_k into (·/k)₆ with sextic-Gauss root
  numbers, so it closes only inside a 6-fold-cover B₂-type WMDS (long root cubic, short root sextic).
  Plausible but only a FIRST moment. P1 is a second moment: nodes n₁ = k = n₂ with N(k)² conductors,
  Cartan determinant 0 ⇒ affine C̃₂, infinite group, continuation only to the Tits-cone tube. Affine
  WMDS give moments only over F_q(T) (Bucur–Diaconu, D̃₄); over Q such moments come from Li-type large
  sieves (Shen–Stucky), which keep the N-term past the critical point.

## 8. Verdict
- Not within reach of any one listed tool with modest work. Use (b) is a bare transition problem:
  N ≈ K is below both self-dual points (K L^{1/2} per slot, K L combined); every Poisson/Voronoi/HD move
  keeps an N-dominated configuration.
- Even L = 1 at N = K^{1+δ'} is open unconditionally. Its only non-routine input on the Voronoi route is
  the absence of sixth-power Gauss bias for the theta vector ⟺ Σ_{m~M}μ(m)ξ₀ψ(m) ≪ M^{11/12}, a
  zero-free strip for CM Hecke L-functions of Q(ω) (∞-type z/|z|). Open question for the owners: does
  the QRH machinery itself extend from Dirichlet characters to such Hecke characters? If yes, the L = 1
  skeleton (and slot-diagonal statements above K L^{1/2}) would follow by bootstrapping; P1 would not.

## 9. Statements usable as stated (labels as in the header)
1. PROVED (from DR Prop 5.2 + DR functwisteq): per slot, S(k,P) has conductor ≍ N(k)²N(P), critical
   length ≍ K·N(P)^{1/2}; the Voronoi dual is ε₁(k)ε₂(P)Σ_{u'} g̃(Pu')(Pu'/k)₆W̃ (+ smaller term).
2. PROVED: θ₃⊗χ_k is Voronoi-dual to θ₃⊗(·/k)₆ (three cusps F̄₁, F̄*₁₉, F̄*₁₀ on the dual side).
3. PROVED (classical, checked numerically): g̃₃g̃₆ = μ·conj((4/·)₆)·g̃₂·(·/|·|) on squarefree m ≡ 1 (3).
4. PROVED (sketch): L = 1, Q₀ ≪ K^{1+ε}N for N ≥ K^{3/2+ε} (Voronoi to M = K²/N ≤ K^{1/2−ε}; then the
   sextic family over ALL k ≤ K is exactly orthogonal on m ~ M by Poisson: dual range < 1).
5. CONDITIONAL (sketch): under GRH for Hecke L-functions of Q(ω), Q₀ ≪ K^{1+ε}N for every N.
6. SKETCH (unconditional): single-mark F_P ≪ N K^{7/6+ε} at N = K·N(P) (use (a)); η ≈ 0.041 there.
