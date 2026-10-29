# Radar sequences and waveform design: a sourced knowledge base

*Compiled 29 October 2026. Reader: analytic number theorist with a signal-processing background, working with sextic residue symbols on residue rings of ℤ[ω], Gauss sums, CRT/Good–Thomas factorisation and frequency dilations, and needing Bessel (large-sieve) bounds, coherence bounds and higher moments for dictionaries of Gauss-sum atoms.*

**Conventions.** e(x) = exp(2πix); g(χ) = Σ_x χ(x)e(x/p). Keys such as [HJ88] refer to `sources.md`. Evidence tags, each applying to the sentence it ends:

* **[T]** published theorem or established result (hypotheses as in the cited source);
* **[D]** derived here by an elementary argument and checked numerically (scratch computations, not shipped);
* **[F]** folklore, heuristic or conjecture;
* **[O]** open problem;
* **[U]** could not be confirmed in a source I could read.

## 0. Orientation: what is closest to your filter bank

1. **Same objects, different language.** For a split prime π of norm p, ℤ[ω]/(π) ≅ 𝔽_p and the sextic residue symbol is a sextic character of 𝔽_p^×; so the M-ary power-residue and Sidelnikov sequences with M = 3 or 6 [Si69; HY09; YG10; AM19] are exactly these objects, treated over finite fields. **No source found** uses the Eisenstein structure itself (reciprocity, composite or prime-power moduli, norm-form arithmetic) for sequence design. Searches (Crossref, arXiv, web) for Eisenstein, cubic/sextic residue and Gaussian-integer sequences returned only: Hall's binary sextic-residue difference sets [Hall56]; merit-factor theory for unions of sextic cyclotomic classes [GS17a, Cor. 2.6]; quartic-residue sequences whose asymptotics depend on a Gaussian-integer Jacobi-sum angle, with higher orders "not discussed" [BK17]; and non-quadratic character polynomials in e variables, which cover 𝔽_{p²} = ℤ[ω]/(p) (p ≡ 2 mod 3) as 2-D arrays [Ka13, Thm 1.4]. This is absence from searches, not proof of absence.
2. The nearest **Bessel/large-sieve** results are in number theory: the cubic large sieve over ℤ[ω] [HB00], its transfer to ℤ with a sextic extension [BY10, Thm 1.5], and its conditional sharpness [DR24, Thm 1.4] (§9).
3. The nearest **coherence** results: the Weil-representation (oscillator) system, whose atoms are products of multiplicative characters and quadratic chirps, with ambiguity ≤ 2/√p and cross-ambiguity ≤ 4/√p [GHS08; WG11] (§3.3, §7).
4. Two exact computations (derived here) frame everything: the Sidelnikov autocorrelation formula (§3.3) and the frame operator of the sextic Gauss-sum dictionary (§10).

**Suggested reading order.** [Sch16] (survey of aperiodic/periodic theory) → [JKS13a] and [Ka13] (merit factor and L⁴ via Gauss sums) → [GS17a] (sextic cyclotomy) and [BK17] (quartic residues) → [GHS08] with [WG11] (Weil-representation signals) → [HB00], [BY10], [DR24] (large sieve for cubic and sextic symbols) → [Mon78], [Kow08] (the Bessel-bound framework).

## 1. Basics

### 1.1 Matched filter, correlations, merit factor
For a known waveform in white noise the matched filter h(t) = s̄(T−t) maximises output SNR (peak value 2E/N₀) [T, classical; LM04]. Pulse compression compresses a long coded pulse (time–bandwidth product ≫ 1) to width ≈ 1/B; the cost is range sidelobes, the off-peak autocorrelation values [LM04].

For A = (A(0),…,A(n−1)) put C_u = Σ_k A(k+u)Ā(k) (aperiodic) and R_u = Σ_{k mod n} A(k+u)Ā(k) (periodic); R_u = C_u + conj(C_{n−u}) [D]. With A(z) = ΣA(k)z^k, |A(z)|² = Σ_{|u|<n} C_u z^u on |z| = 1, so (1/2π)∫|A|⁴ = Σ_u |C_u|² [D]. For unimodular entries, Golay's merit factor F = n²/(2Σ_{u≥1}|C_u|²) satisfies 1/F = ‖A‖₄⁴/n² − 1 [JKS13a (1.1)]: sidelobe energy is the L⁴ norm on the circle. Periodically, Σ_u |R_u|² = n⁻¹Σ_k |Â(k)|⁴ [D], so perfect periodic autocorrelation ⇔ constant |Â(k)| (the CAZAC property). The standard strategy is to take sequences with ideal periodic correlation and test the aperiodic sidelobes [Sch16 §1]; for shifted characteristic polynomials of difference sets, only near-Hadamard parameters can give a nonzero asymptotic merit factor [GS17a §1, quoting Jensen–Jensen–Høholdt].

### 1.2 Ambiguity function, Moyal identity, uncertainty
χ_u(τ,ν) = ∫u(t)ū(t−τ)e^{2πiνt}dt satisfies |χ_u| ≤ χ_u(0,0) = ‖u‖² and ∬|χ_u|² = ‖u‖⁴ (volume invariance, a Moyal-type orthogonality) [T: Moy49; AT85]. This is the radar uncertainty principle: sidelobe volume can be moved but not removed; [PH65] bounds its volume and height distributions. Sharp L^p form: for p ≥ 2, ∬|χ_u|^p ≤ (2/p)‖u‖^{2p}, equality iff u is a (chirped, shifted) Gaussian [T: Lieb90; the constant is the Gaussian value].

Finite version [D]: for u ∈ ℂ^N, A_u(a,b) = Σ_{x∈ℤ_N} u(x)ū(x+a)e(bx/N) has Σ_{a,b}|A_u|² = N‖u‖⁴ (Parseval in x, then in a). For ‖u‖ = 1 the mean of |A_u|² over the N²−1 non-origin points is 1/(N+1), so max|A_u| ≥ (N+1)^{−1/2}, with equality iff the N² time–frequency shifts of u form an equiangular tight frame (a SIC; existence in all dimensions is Zauner's conjecture [O]). For prime p, |supp f| + |supp f̂| ≥ p+1 [T: Tao05]: short support forces a spread-out DFT.

### 1.3 Doppler tolerance, LFM, hyperbolic FM
For u(t) = T^{−1/2}1_{[−T/2,T/2]}(t)e^{iπkt²}: |χ_u(τ,ν)| = (1−|τ|/T)·|sinc((ν+kτ)(T−|τ|))| for |τ| < T, with sinc x = sin(πx)/(πx) [D]. The ridge ν = −kτ means a Doppler shift moves the compressed peak in delay with almost no loss of height: Doppler tolerance bought with range–Doppler coupling [LM04]. Wideband Doppler is a dilation t ↦ st. The dilation eigenfunctions u(t) = t^{−1/2+iα} (hyperbolic FM, the "bat signal") are invariant up to a phase [D] and are the optimally Doppler-tolerant class [AT70; optimality as reported in secondary sources, U]. The finite analogue is exact: χ(tx) = χ(t)χ(x), so multiplicative-character sequences are dilation eigenvectors [T: GHS08 §I-B]. The finite chirp e(ux²/N) has |A| = N on the ridge b = 2ua and 0 elsewhere (N prime) [D]; cubic phases flatten the ridge (§3.2).

*Open:* a sharp finite-group analogue of Lieb's L^p inequality for A_u on ℤ_N or 𝔽_q² was not found [O/U]; existence of flat (SIC) orbits in every dimension [O].

## 2. Binary sequences

### 2.1 Barker codes
Barker sequences are ±1 sequences with |C_u| ≤ 1 for u ≠ 0; the known lengths are 2, 3, 4, 5, 7, 11, 13. None of odd length > 13 exists (Turyn–Storer 1961; shorter proofs by Schmidt–Willms 2015) [T: Sch16 Thm 3.1.2]. An even-length one (n > 2) is a perfect binary sequence, so n = 4u² with u odd and every odd prime divisor ≡ 3 mod 4 (Eliahou–Kervaire–Saffari), and none exists for 4 < n ≤ 4·10³³ [T: Sch16 §3.1, Prop. 3.1.5]. Turyn's conjecture (nothing beyond 13) is open [O]. The tools are cyclotomic integers, self-conjugacy and "field descent".

### 2.2 Merit factor: asymptotic values (n → ∞)

| Family | Asymptotic F | Source |
|---|---|---|
| Random ±1 | 1 | [GS17b] intro (Borwein–Lockhart) [T] |
| Rudin–Shapiro | 3 | Littlewood 1968, quoted in [JKS13a] [T] |
| Legendre, rotation R, length p | 1/F = 2/3 − 4R + 8R² (0 ≤ R ≤ ½): 3/2 at R = 0, **6 at R = ¼** | [HJ88]; [JKS13a Thm 2.1] [T] |
| Legendre, rotation R, length Tp | g(R,T); max **6.342061…** (largest root of 29x³−249x²+417x−27) at T = 1.057827…, R = ¾−T/2 | [JKS13a Thm 2.1, (2.2)] [T] |
| m-sequence | 3; length Tn with T ≈ 1.1157: 3.342065… (7x³−33x²+33x−3) | [JKS13a Thm 2.2] [T] |
| Jacobi, squarefree length n | as Legendre if max(4^{ω(n)}(log n)⁶, 5^{ω(n)})/κ(n) → 0 | [JKS13a Thm 2.3] [T] |
| Non-real character polynomials Σχ(j)zʲ, any rotation | 3 | [BC00] [T] |
| Non-quadratic χ, best length ratio (e = 1) | 3.342065… | [Ka13 Thm 1.4] [T] |
| Union of three of the six sextic classes mod p, p = x²+27y² with y²(log p)³/p → 0: Paley type / Hall type (Hall type needs (p−1)/6 odd) | T = 1, R = ¼: 6 / 54/17; optimised over R, T: 6.342061… / 3.518994… | [GS17a Cor. 2.6] [T] |
| Frank / Chu (unimodular) | (π²/4)√n / (π/2)√n, unbounded | [Sch16 Thms 4.2.6, 4.2.8] [T] |

Numerical spot checks agree with the Legendre rows (p up to 1.6·10⁵: F = 1.500, 2.884, 5.9995 at R = 0, 0.1, 0.25; 6.340 appended), m-sequence rows (period up to 2²⁰−1: 3.00, 3.343 appended), Rudin–Shapiro (N = 2¹⁹: 3.000) and the Hall-type rows (p = 280927: 3.168 at T = 1, 3.519 appended) [D]. Open: whether binary F can exceed 6.342061… or is bounded [O]; Golay conjectured that skew-symmetric sequences are asymptotically optimal, and skew-symmetric families attain 6.342061… [JKS13a Cor. 2.4]; Golay's ergodicity heuristic suggests ≈ 12.3 [F, secondary report, U]. For unimodular coefficients Erdős's flatness conjecture fails (Kahane), while for ±1 it remains open [Ka13 intro].

### 2.3 Legendre sequences and Fekete polynomials
Let f_p(z) = Σ_{j=1}^{p−1}(j|p)zʲ (for ±1 sequences the j = 0 coefficient is set to +1, as in [JKS13a (2.1)]). At p-th roots of unity f_p(e(k/p)) = (k|p)g with |g| = √p: flat [D]. The L⁴ norm is not determined by these p values but is exactly computable from the 2p-th roots of unity, since |f|⁴ = |f²|² has degree 2p−2 and (1/M)Σ_{k<M}|f(e(k/M))|⁴ is exact for M ≥ 2p−1 [D]. Between Gauss-sum points f is a Dirichlet-kernel combination of the character values; the fourth moment becomes a sum over a+b = c+d of products of four Gauss sums, with main terms from character orthogonality and errors from the Weil bound [Ka13 §§3–4; HJ88]. Result, for the shifted polynomial f_p^{(r)}(z) = Σ_{j=0}^{p−1}(j+r|p)zʲ with r/p → R: (‖f_p^{(r)}‖₄/√p)⁴ → 7/6 + ½(4|R|−1)² for |R| ≤ ½ [T: HJ88; GS17b (1)].

Higher moments: (‖f_p‖_{2q}/√p)^{2q} → 1, 5/3, 19/5, 3469/315, 21565/567, … (q = 1, 2, …), in closed form via tangent numbers and generalised Eulerian numbers; for m-sequences via Carlitz numbers [T: GS17b Thms 2.1, 2.3]. Sup norm: Pólya–Vinogradov gives ‖f_p‖_∞ ≪ √p log p; Montgomery (1980) gives ≫ √p log log p infinitely often [T, quoted in CGPS00 §1]; the truth is open [O].

### 2.4 m-sequences
With a primitive polynomial of degree n over 𝔽₂, s(t) = (−1)^{Tr(αᵗ)} has period N = 2ⁿ−1 and two-level periodic autocorrelation (−1 off peak) [GG05]. Its cross-correlation with the decimation s(dt) is C_d(τ) = Σ_{x∈𝔽_q^×}(−1)^{Tr(α^τ x + x^d)}, an exponential sum; Weil gives |C_d(τ)+1| ≤ (d−1)√q [D; Weil48]. d = 2^k+1 gives a quadratic form and a Gauss sum (Gold, §4); d = −1 (the sequence against its reversal) gives Kloosterman sums, |K| ≤ 2√q [D; HK11]. The aperiodic merit factor is only 3: ideal periodic correlation does not give ideal aperiodic correlation.

### 2.5 Rudin–Shapiro
P₀ = Q₀ = 1, P_{k+1} = P_k + z^{2^k}Q_k, Q_{k+1} = P_k − z^{2^k}Q_k [Ru59]. The parallelogram law gives |P_{k+1}|² + |Q_{k+1}|² = 2(|P_k|² + |Q_k|²), hence 2^{k+1} on |z| = 1 and sup|P_k| ≤ √2·2^{k/2} [D]: explicit ±1 polynomials of flat order √N.

### 2.6 Golay complementary pairs
(A,B) with C_u(A) + C_u(B) = 0 for all u ≠ 0 ⇔ |A(z)|² + |B(z)|² ≡ 2n on |z| = 1 [D]. Why it works: the two sidelobe spectra are complements that add to a constant, so energy conservation across the pair is exact (the Rudin–Shapiro recursion is its doubling). Binary pairs exist for lengths 2^a10^b26^c and for no other length ≤ 100; necessarily n is even with no prime factor ≡ 3 mod 4 [T: Sch16 §5.2 (Golay; Eliahou–Kervaire–Saffari; Borwein–Ferguson)]; other lengths are open [O]. Structure: Golay sequences are cosets of first-order inside second-order generalised Reed–Muller codes, with PMEPR ≤ 2 (3 dB) [T: DJ99, abstract level]. Doppler fragility: cancellation is exact only at ν = 0; ordering pairs along the Prouhet–Thue–Morse sequence annihilates low-order Taylor terms of the composite ambiguity function in ν [T: PCMH08].

## 3. Polyphase sequences

### 3.1 Frank, Chu, Zadoff–Chu (CAZAC)
Chu [Ch72]: gcd(r,N) = 1, c(k) = e(rk(k+1)/2N) for N odd (e(rk²/2N) for N even). Then c(k+u)c̄(k) = const·e(ruk/N), a geometric sum, so R_u = 0 for u ≢ 0 and |ĉ(k)| = √N for all k [D]. For roots r₁, r₂ with gcd(r₁−r₂, N) = 1 and N odd, every cross-correlation has modulus exactly √N (a quadratic Gauss sum); this fails when the gcd exceeds 1 (checked N = 9, 15) [D]. Such a family attains equality in Sarwate's inequality (§5) [D]. The DFT ĉ(k) = Σ_n c(n)e(−nk/N) is itself a quadratic Gauss sum, so Chu sequences are Fourier-invariant up to a chirp. Frank [Fr63]: N = m², c(im+j) = e(ij/m) for 0 ≤ i,j < m, i.e. the rows of the m × m DFT matrix concatenated [Sch16 Def. 4.1.3]; it is a perfect m-phase sequence [T: Sch16 Thm 4.1.4]. Since nk = (n² + k² − (k−n)²)/2, a length-N DFT is a chirp-sandwiched convolution [T: Blu70]. Aperiodically, Frank and Chu have merit factors ~ (π²/4)√n and (π/2)√n, so unimodular merit factors are unbounded; for ±1 sequences boundedness is open [T/O: Sch16 §4.2]. P1–P4 codes (Frank- and LFM-derived phase codes) and their Doppler behaviour are treated in [LM04] [U].

### 3.2 Alltop's cubic phases
For prime p ≥ 5, f_a(n) = e((n³+an)/p) [Al80]. Differencing kills the cubic: (n+u)³ − n³ = 3un² + 3u²n + u³, so each nontrivial correlation is a quadratic Gauss sum [D]. Hence every out-of-phase autocorrelation has modulus exactly √p, and cross-correlations of f_a, f_b vanish at u = 0 and have modulus √p for u ≠ 0 [D]. The Gabor system {M_bT_a f₀/√p} (f₀(n) = e(n³/p)) consists of p² unit vectors forming p orthonormal bases (one per time shift a), with cross-block inner products of modulus exactly p^{−1/2}: a tight frame with bound p and coherence 1/√p, against the equiangular value 1/√(p+1) [T: HS09 Props. 1–2; D]. Mechanism: Weyl–van der Corput differencing turns a chirp's ridge into a flat pedestal.

Application [HS09, arXiv v2 Thms 1–3]: with Alltop probing, K-sparse scenes on the N × N delay–Doppler grid (N = p) are recovered by basis pursuit or OMP if K < (√N+1)/2, and with high probability for K ≤ N/(16 log(N/ε)); K ≲ N/(2 log N) is observed but unproved for Alltop [O].

### 3.3 Power-residue, Sidelnikov and Weil-type sequences
Let q = p^m, χ: 𝔽_q^× → μ_M with M | q−1, χ(0) = 0.

* **Power-residue sequence** (q = p), s(x) = χ(x). R_u = Σ_x χ(x/(x+u)) = Σ_{y≠0,1}χ(y) = −1 for u ≠ 0, and ŝ(k) = χ̄(k)g(χ): DFT-self-dual up to conjugation [D]. Cross-correlations of constant multiples are ≲ √p + 2, with exact distributions via Jacobi sums and cyclotomic numbers [T: HY09].
* **Sidelnikov** [Si69], s(t) = χ(αᵗ+1), period q−1: R_u = −1 − χ(α^u), so |R_u| = 2|cos(πu/M)| ≤ 2 when the single zero entry is kept [D]; replacing it by a unimodular symbol gives ≤ 4, as in Sidelnikov's abstract. For M = 2 these are the Lempel–Cohn–Eastman binary sequences [LCE77]. Families: cross-correlation ≲ √q + 3 [HY09]; new families with maximum 2√q + 6, about √2 times Sidelnikov's lower bound at M = q−1 [YG10]; explicit cross-correlation distributions via Jacobi sums when p^x ≡ −1 (mod M) [AM19, abstract level].
* **Character × chirp products.** φ_{x,y}(i) = χ_x(i)e(yi²/p), x = 1,…,p−2, y ∈ 𝔽_p, form the split oscillator set Ω₀: p(p−2) sequences with |A| ≤ 2√p off the origin (unnormalised), cross-ambiguity ≤ 4√p, and |φ̂| < 2 [T: WG11 Thm 2, an elementary proof of [GHS08]]. When 6 | p−1, x = j(p−1)/6 (j = 1,…,5) gives exactly the nontrivial characters of order dividing 6. "Weil sequences" in the binary sense [RU06, abstract only, U]: from one Legendre sequence by shift-and-add, family size (p−1)/2, correlations ≤ 2√p + 5.
* **Hall sextic residues.** For primes p = 4x²+27 and a primitive root g with ind_g(3) ≡ 1 mod 6, D = C₀ ∪ C₁ ∪ C₃ (sextic cosets) is a (p, (p−1)/2, (p−3)/4) difference set [T: Hall56; checked here for every such p ≤ 5503], so ±1_D has ideal two-level autocorrelation. p = x²+27y² iff p ≡ 1 mod 6 and 2 is a cube mod p [GS17a §2]: Eisenstein arithmetic sits in the existence condition.
* **Aperiodic behaviour** is in §2.2. Cross-correlation: exact asymptotic formulas for the mean-square aperiodic crosscorrelation of pairs built from additive characters (m-sequences) and multiplicative characters (Legendre and relatives), including shifted, truncated or extended versions, are in [T: Ka16, abstract level]; a shifted Legendre sequence split roughly in half gives a lower value than m-sequence pairs. For the binary quartic-residue sequences of [BK17], real ±1 on cosets, the autocorrelation demerit factor tends to 1/2 − cos(2γ_p)/3 and the crosscorrelation demerit factor to 2/3 + cos(2γ_p)/3 at natural length, where p = a²+b² and cos 2γ_p = Re(g(θ)⁴/p²) = (a²−b²)/p; γ_p is equidistributed in (0, π/2) [T: BK17 Lemma 8.1]. A sextic analogue would plausibly be governed by the argument of g(χ₆)⁶/p³, a ℤ[ω] Jacobi-sum angle [F, my inference; BK17 leave higher orders undone].

**Where Eisenstein arithmetic enters, and where it does not** [D/F, reading of the cited theorems]. For the unimodular character polynomial itself, the limiting L⁴ ratio of a non-quadratic character is independent of the character and of the shift [Ka13 Thm 1.4; BC00], because only |g(χ)| = √q, orthogonality and the Weil bound are used. Arithmetic of the number field appears once characters are *combined* into ±1 sequences (cyclotomic classes, real parts, linear combinations): then cyclotomic numbers of order 6, equivalently the representations p = x²+27y² and 4p = L²+27M², decide the limit [GS17a Thm 2.3, Cor. 2.6], and for order 4 the Gaussian-integer angle does [BK17].

**L⁴ of sextic arrays over ℤ[ω]/(p), exact statement.** [Ka13 Thm 1.4]: let χ be a nontrivial non-quadratic multiplicative character of 𝔽_{p^e} (χ(0) = 0), α: ℤ^e → 𝔽_{p^e} a group epimorphism, f(z₁,…,z_e) = Σ_{j∈S}χ(α(j+t))z^j with S = ∏_k{0,…,s_k−1}, and suppose s_k/p → σ_k as p → ∞. Then ‖f‖₄⁴/‖f‖₂⁴ → −(2/3)^e∏σ_k + 2∏Ω(1/σ_k, 0), where Ω(x,y) = Σ_{n∈ℤ}max(0, 1−|xn−y|)²; the limit does not depend on χ or t [T]. For e = 2 and p ≡ 2 mod 3, taking α(j₁,j₂) = j₁ + j₂ω identifies 𝔽_{p²} with ℤ[ω]/(p), so this covers sextic characters on Eisenstein boxes. With merit factor F = ‖f‖₂⁴/(‖f‖₄⁴ − ‖f‖₂⁴): e = 1 gives 3 at σ = 1 and 3.342065 at σ = 1.115749; e = 2 gives 9/5 at σ₁ = σ₂ = 1 and ≈ 1.903 at the optimum σ₁ = σ₂ ≈ 1.0730 (root of x⁶ − 18(x−1)(3x²−4x+2), as in [Ka13 Thm 1.4(ii)]) [D from T].

## 4. Sequence families

Gold [Gold67, with companion 1968]: from a preferred pair of m-sequences (decimation d = 2^k+1 for suitable k; no preferred pairs exist when 4 | n [U]) one gets 2ⁿ+1 sequences of period N = 2ⁿ−1 with cross-correlation in {−1, −t, t−2}, t = 1 + 2^{⌊(n+2)/2⌋} [T; checked n = 5, 7: values {−9,−1,7} and {−17,−1,15}]. Proof idea: C_d is the Walsh spectrum of the quadratic form Tr(x^{2^k+1}), a binary Gauss sum whose modulus is 0 or 2^{(n+r)/2} with r the dimension of the radical [D, standard]. The small Kasami set has 2^{n/2} sequences with max|C| = 1 + 2^{n/2} (n even) [SP80; checked n = 6]; it is asymptotically Welch-optimal (max/Welch → 1), while Gold exceeds the Welch bound by a factor → √2 (n odd) or 2 (n even) [D]. The survey of correlation properties is [SP80]; [GG05] is the textbook.

Kloosterman link: d = −1 gives C(τ)+1 = K(α^τ) [HK11]; Weil gives |K| ≤ 2√q.

Kerdock and Delsarte–Goethals: nonlinear binary codes built from sets of alternating bilinear (quadratic) forms [Ker72; DG75], Z₄-linear [HKCSS94]. Mechanism [D for the Gauss-sum fact; the exact Kerdock/Delsarte–Goethals parameters are as I recall them from the literature, not re-verified, U]: a Kerdock set is a maximal family of alternating forms whose pairwise differences are nonsingular, so every pairwise correlation is a Gauss sum of a nondegenerate quadratic form, of constant modulus 2^{m/2}; Delsarte–Goethals sets relax the rank of differences and so allow larger families at a controlled loss. The sequence-side counterpart is a Galois-ring Weil–Carlitz–Uchiyama bound, used to build large PSK families with low correlation over alphabets of size p^e, e ≥ 2 [T: KHC95, abstract level]; the Kerdock link goes through [HKCSS94]. Open: I found no family of this type built from characters of order 6 over a Galois ring or over ℤ[ω]/(π^k) [O/U].

Zero-correlation zones. If M sequences of length N have vanishing auto- (u ≠ 0) and cross-correlations for |τ| ≤ Z, the M(Z+1) shifts Tᵗx_i (0 ≤ t ≤ Z) are pairwise orthogonal in ℂᴺ, so M(Z+1) ≤ N [D]. This is the form of the bound attributed to Tang–Fan–Matsufuji [TFM00] (their normalisation of Z not re-verified, U); binary ZCZ constructions start with [FSKD99]. ZCZ sets are partial orthogonal systems of shifted copies: zone width is traded against family size.

## 5. Bounds

* **Welch** [We74] [D]: for M unimodular sequences of length N, θ_max² ≥ N²(M−1)/(MN−1), because Σ_{i,j,τ}|C_ij(τ)|² = N⁻¹Σ_k(Σ_i|X_i(k)|²)² ≥ M²N² by Cauchy–Schwarz and Parseval. Moment form: unit vectors x₁…x_M ∈ ℂᴺ satisfy Σ_{i,j}|⟨x_i,x_j⟩|^{2k} ≥ M²/C(N+k−1,k), with equality iff {x_i^{⊗k}} is a tight frame for Sym^k, i.e. a projective k-design [T: We74, moment form as described in the literature; KR05]. For k = 1 this is the frame potential: max|⟨x_i,x_j⟩|² ≥ (M−N)/(N(M−1)), equality iff an equiangular tight frame (ETF) [T: SH03].
* **Sarwate** [Sa79] [D]: with θ_a the largest out-of-phase autocorrelation and θ_c the largest cross-correlation, θ_c²/N + (N−1)θ_a²/((M−1)N²) ≥ 1. Equality holds for perfect autocorrelation with flat cross-correlation √N, e.g. Chu families (checked N = 31).
* **Aperiodic.** The same argument over 2N−1 lags gives θ_max² ≥ N²(M−1)/(M(2N−1)−1) [D]; Levenshtein improves this for binary codes (M ≥ 4, N ≥ 2), asymptotically by a factor 2 in the squared bound according to the abstract records [Lev99; exact form U]. **Sidelnikov** [Si71] gives bounds for sequences with symbols in roots of unity that improve on Welch's for such alphabets [T: as characterised in secondary sources, U].
* **ETFs from difference sets** [D; XZG05]: if D ⊂ ℤ_N is an (N,K,λ) difference set, the N columns of the K × N matrix of DFT rows indexed by D are unit vectors forming an ETF with μ² = (N−K)/(K(N−1)) (checked on Paley (31,15,7)). Paley, Singer and Hall (sextic) difference sets therefore all give Welch-equality codebooks.
* **MUBs from Gauss sums.** For prime p, the bases {p^{−1/2}e((an²+bn)/p)}_b (a ∈ 𝔽_p) with the standard basis give p+1 bases whose cross inner products all have modulus p^{−1/2} (quadratic Gauss sums); prime powers use Galois-field Gauss sums [T: WF89]. The complete set is a projective 2-design [KR05]; checked p = 5, 7, 11: equality in the k = 1 and k = 2 Welch bounds [D].

*Open:* full classification of (N,K) for which ETFs exist, and of the sequence families that meet Sidelnikov's bound, is incomplete [O, general knowledge, not tied to a source read]. For the sextic Gauss-sum dictionary of §10 the coherence misses the Welch value only by the factor ≈ √(6/5) [D].

## 6. Frequency hopping: Costas arrays
A Costas array is an n × n permutation matrix whose difference vectors are all distinct; as a hopping pattern its ambiguity sidelobes are ≤ 1 (thumbtack) [Co84; Dr11]. **Welch:** p prime, g a primitive root, f(i) = g^{i+c} mod p (0 ≤ i ≤ p−2) is Costas of order p−1 for every c, since g^{i+k} − g^i = g^i(g^k−1) is injective in i [D; GT84]; deleting the corner dot gives order p−2. **Lempel–Golomb:** q a prime power, α, β primitive, α^{f(i)} + β^i = 1 gives order q−2, symmetric for α = β [T: Dr11 Thm 3; GT84]; both checked for all primes ≤ 37. Status [Dr11]: all orders ≤ 29 enumerated (204, 712, 164 arrays at n = 27, 28, 29); no array is known at n = 32 or 33; existence for all n, the complexity of deciding it, and the growth of C(n) are open, the best upper bound being C(n) = O((n−1)!) [O]. No L-function input appears in these constructions [U].

## 7. Group-theoretic designs
The finite Heisenberg–Weyl group is generated by time shifts T_a and modulations M_b with T_aM_b = e(ab/N)M_bT_a; the ambiguity function is a matrix coefficient ⟨u, M_bT_a u⟩ [T: HCM06; GHS08]. For prime p the Schrödinger representation is irreducible, so by Schur's lemma every orbit {M_bT_a u} is a tight frame: Σ_{a,b}|⟨f, M_bT_a u⟩|² = p‖f‖²‖u‖² [D]. Energy bounds for full orbits are therefore exact; all the difficulty is coherence, the supremum of one off-origin ambiguity function, with lower bound (p+1)^{−1/2} from §1.2.

[GHS08]: the Heisenberg system is p+1 orthonormal bases (MUBs) with |A_φ| the indicator of a line; the oscillator system, eigenvectors of tori of Sp₂(𝔽_p) in the Weil representation, has ~p³ unit signals with |A| ≤ 2/√p off the origin, cross-ambiguity ≤ 4/√p, sup|φ| ≤ 2/√p, and is closed under the DFT [T]. Its split-torus model is {χ(t)/√(p−1)}, the eigenfunctions of the dilation representation ρ_aφ(t) = φ(at), i.e. exactly the power-residue sequences [T: GHS08 §I-B]. The non-split torus gives characters of the norm-one group of 𝔽_{p²}^× (cyclic of order p+1), which carry sextic characters when p ≡ 5 mod 6, i.e. p inert in ℤ[ω] [D/F, my reading]. [WG11] makes the split part elementary (§3.3).

Rader [Rad68]: the DFT restricted to 𝔽_p^× is a convolution on the cyclic group 𝔽_p^×, diagonalised by multiplicative characters with Gauss sums as eigenvalues [D]. Good–Thomas: DFT_{mn} ≅ DFT_m ⊗ DFT_n for coprime m, n. [AT85] describe the range of u ↦ χ_u in terms of special functions and show it is closed [abstract level].

*Open:* the best constant in the oscillator bound (2 in |A| ≤ 2/√p): my numerics for sextic characters give max|A|/√p ≈ 1.86–1.92 for p ≤ 127 (the sum Σχ(x)χ̄(x+a)e(bx/p) is a rank-2 mixed sum, so Weil–Deligne gives 2√p [D]), but whether 2 is asymptotically sharp was not found in the sources read [O/U]. Also open: signals from characters of ℤ[ω]/(π^k), k ≥ 2 (Galois-ring/local-ring Weil representation) [O/U].

## 8. Beyond the matched filter

**Mismatched filters** [AG73]: with S the convolution matrix of s and R = Σ_{k≠0} s_k s_kᴴ + σ²I (shifted copies as "interferers"), the least-squares filter w = R⁻¹s₀/(s₀ᴴR⁻¹s₀) is the Capon/MVDR beamformer [D]. Frame view: if the shifts s_k are independent with Gram matrix G, the zero-sidelobe filter is the dual vector s̃₀ = Σ_l (G⁻¹)_{0l}s_l with noise gain (G⁻¹)₀₀ [D]; the loss is controlled by the lower frame bound of the shift system. For Barker-13 complete range-sidelobe suppression costs ≈ 0.2 dB [T: AG73 abstract].

**Compressed-sensing radar.** Coherence μ gives RIP constant δ_k ≤ (k−1)μ (Gershgorin) [D], so pairwise coherence reaches only k ≈ 1/μ ≈ √N for Alltop/Gabor dictionaries (the square-root barrier), whereas random partial-Fourier and random-window Gabor matrices are RIP at sparsity of order N/polylog N [F, standard compressed-sensing results, not tied to a source read]. Beyond the barrier, [BDFKK11] construct explicit n × N RIP matrices of order k ≥ n^{1/2+ε} (N^{1−ε} ≤ n ≤ N, δ = n^{−ε}) using sumset and exponential-sum estimates with additive structure [T]. [BFMW13] survey deterministic RIP techniques and conjecture that ETFs from Paley graphs are RIP like random matrices [F]. For Gauss-sum atoms, exceeding the barrier means controlling k-fold (moment) interactions, not only pairwise coherence. *Open:* whether partial Gabor or character × chirp dictionaries are RIP beyond √N (Alltop: K ≲ N/(2 log N) unproved) [O].

## 9. L-functions, Fekete polynomials and the large sieve

**9.1 Fekete.** Γ(s)L(s,(·|p)) = ∫₀¹ f_p(t)(log 1/t)^{s−1}/(1−t^p) dt/t [D; CGPS00 (1.1)]. Fekete observed that if f_p has no zero in (0,1) then L(s,(·|p)) has no real zero s > 0, hence no Siegel zero [T: CGPS00 §1; the reference given there is FP12, which I did not read]. Only 23 primes < 1000 have a zero in (0,1); Baker–Montgomery (1990) showed that for almost all p the number of such zeros → ∞ (probably ≍ log log p), so the sufficient condition fails generically [T, quoted in CGPS00]. CGPS Thm 1: the number of zeros on |z| = 1 is ~κ₀p with 0.500668 < κ₀ < 0.500813 [T]. That at least half lie on the circle is a Gauss-sum argument: |f_p(e(k/p))| = √p exactly, and the values at consecutive roots of unity have opposite sign when the Legendre symbols agree, so the intermediate value theorem applies [CGPS00 §1].

**9.2 Gauss-sum bias.** For Kummer's cubic sums S_p = Σ_n e(n³/p), S_p/(2√p) = cos 2πθ_p and θ_p is equidistributed [T: HBP79]. Yet, conditionally on GRH for Hecke L-functions over ℚ(ω), Σ_{p≤X, p≡1 (3)} S_p/(2√p) ~ (2(2π)^{2/3}/(5Γ(2/3)))·X^{5/6}/log X (Patterson's conjecture) [T: DR24 Thm 1.1]. The model "Gauss-sum atoms are random phases" fails by a power-saving bias, and that bias makes the cubic large sieve sharp.

**9.3 The large sieve is a Bessel bound.** Additively, for S(x) = Σ_{M<n≤M+N}a_n e(nx), Σ_{q≤Q}Σ*_{a mod q}|S(a/q)|² ≤ (N+Q²)‖a‖² [T: MV73]; the sharp constant N−1+Q² is due to Selberg and independently Cohen [secondary report, U]. Duality: ‖Φ‖ = ‖Φ*‖, so Bessel bounds for atoms and for their dual transform coincide [Mon78; Kow08; used in DR24 §9]. Gauss sums transfer multiplicative to additive [D]: for primitive χ mod q, χ(n) = τ(χ̄)⁻¹Σ_a χ̄(a)e(an/q) and |τ|² = q, so Σ*_χ|Σ a_nχ(n)|² ≤ (φ(q)/q)Σ_{(a,q)=1}|S(a/q)|², whence Σ_{q≤Q}(q/φ(q))Σ*_χ|Σ a_nχ(n)|² ≤ (N−1+Q²)‖a‖².

Power-residue families are much sparser than all characters, so beating N+Q² is the point. Quadratic: ≪ (Q+M)(QM)^ε [Heath-Brown 1995, quoted in BY10 (8)]. Cubic over ℤ[ω] [T: HB00 Thm 2]: Σ_{N(a)≤A}μ²(a)|Σ_{N(b)≤B}β_b(b/a)₃|² ≪ (A+B+(AB)^{2/3})(AB)^ε‖β‖², with squarefree a, b ≡ 1 mod 3. Over ℤ [T: BY10 Thm 1.4], with χ primitive and m squarefree, (m,3) = 1: Σ_{Q<q≤2Q}Σ*_{χ mod q, χ³=χ₀}|Σ_{M<m≤2M}a_mχ(m)|² ≪ Δ(Q,M)‖a‖² with Δ = (QM)^ε·min{Q^{5/3}+M, Q^{4/3}+Q^{1/2}M, Q^{11/9}+Q^{2/3}M, Q+Q^{1/3}M^{5/3}+M^{12/5}}; **Thm 1.5 states that the same holds under the weaker hypothesis χ⁶ = χ₀ (sextic)**. Sharpness [T: DR24 Thm 1.4]: under GRH for Hecke L-functions over ℚ(ω), the operator norm B(A,B) of the cubic-symbol dictionary satisfies (AB)^{2/3} ≪ B(A,B) ≪ (AB)^{2/3+ε} in the stated ranges, so the (AB)^{2/3} term cannot be removed. A sextic large sieve over ℤ[ω] with an optimal exponent does not appear in the sources read [O].

**9.4 Higher moments.** L⁴ for every nontrivial character, in e variables: [Ka13]. L^{2q}, all q: Fekete and Galois polynomials only [GS17b]. L^{2q} with q ≥ 3 for non-quadratic characters, and for ℤ[ω]-arrays, was not found [O/U]. Welch's moment bounds (§5) give lower-bound benchmarks.

## 10. Dictionary: radar concept ↔ number theory / harmonic analysis

| Radar or coding concept | Counterpart |
|---|---|
| Matched-filter sidelobes | off-diagonal Gram entries ⟨φ_i,φ_j⟩ of the shift dictionary |
| Aperiodic ISL Σ_{u≠0}\|C_u\|² | ‖A‖₄⁴ − n² on the unit circle (Littlewood, Erdős flatness) |
| Periodic ISL | n⁻¹Σ_k\|Â(k)\|⁴ − n² (fourth moment of the DFT) |
| Perfect periodic autocorrelation (CAZAC) | flat DFT; Zadoff–Chu ↔ quadratic Gauss sum |
| Power-residue sequence | multiplicative character; flatness ↔ \|g(χ)\| = √p; ŝ(k) = χ̄(k)g(χ) |
| Two-level autocorrelation | cyclic difference sets (Singer, Paley, Hall) |
| m-sequence cross-correlation | exponential sums over 𝔽_q: Gauss (Gold), Kloosterman (d = −1), Weil bound |
| Welch bound | frame potential; equality ⇔ ETF; k-th moments ⇔ projective k-designs |
| Sarwate trade-off | Cauchy–Schwarz on the Gram matrix of all shifts |
| Ambiguity function | matrix coefficient of the Heisenberg/Weil representation; Moyal ⇔ Plancherel |
| Narrowband / wideband Doppler | modulation / dilation (Mellin); Doppler tolerance ⇔ dilation eigenfunction |
| Chirp ridge vs thumbtack | quadratic vs cubic phase (Weyl differencing); SIC ⇔ flat orbit |
| Golay pair, Rudin–Shapiro | \|A\|² + \|B\|² = const on the circle; Reed–Muller cosets |
| Merit factor | ‖A‖₄/‖A‖₂ of a polynomial on the circle |
| Fekete polynomial | Dirichlet L-series integral; Fekete hypothesis ⇒ no Siegel zero |
| ZCZ set | M(Z+1) orthogonal shifted copies (dimension count) |
| Costas array | distinct-difference permutation: gⁱ (Welch), αⁱ + βʲ = 1 (Lempel–Golomb) |
| Mismatched filter | dual-frame vector; Capon/MVDR with Gram inverse |
| Sparse delay–Doppler recovery | RIP of partial Gabor/Alltop dictionary; coherence ~N^{−1/2}; additive combinatorics beyond |
| Welch bound ↔ large sieve | frame bound N−1+Q²; duality ‖Φ‖ = ‖Φ*‖; Gauss sums convert χ to e(a/q) |

**Worked example [D, checked q = 31].** Let q ≡ 1 (mod 6) be prime and take atoms φ_{j,a}(x) = χʲ(x)e(ax/q) on 𝔽_q^×, j ∈ ℤ/6, a ∈ 𝔽_q^×. Then ⟨φ_{j,a},φ_{k,b}⟩ = q−1 if (j,a) = (k,b); 0 if a = b, j ≠ k; −1 if a ≠ b, j = k; and has modulus √q if a ≠ b, j ≠ k (a Gauss sum of χ^{j−k}). The normalised coherence √q/(q−1) is within a factor ≈ √(6/5) of the Welch value (5/(6q−7))^{1/2}. The frame operator is S = 6qI − 6P, where P is |H| times the projection onto the six sextic characters (H = sextic residues): eigenvalue 5q+1 on span{χʲ}, 6q elsewhere; including a = 0 makes S = 6qI exactly. The cause is dilation invariance, D_tφ_{j,a} = χʲ(t)φ_{j,at}: S commutes with dilations and is diagonal in the multiplicative characters. For coprime moduli m₁m₂ the atoms and Gauss sums factor, so frame operators tensor and exact bounds multiply (Good–Thomas). This exactness is lost when the signal is confined to a box or ball, which is where Poisson summation and the large sieve are needed [HB00].

## 11. Mechanisms worth stealing
Stated neutrally; each with its source.

1. **Dilation-orbit diagonalisation.** A dictionary invariant under 𝔽_q^× has a frame operator that commutes with dilations, so the Bessel bound is the largest isotypic energy, a Gauss-sum modulus [Rad68; GHS08 §I-B; D].
2. **Weil-representation orbits with proven coherence.** Orbits of the oscillator group give atoms χ(i)e(yi²/p) with ambiguity ≤ 2√p and cross-ambiguity ≤ 4√p; Schur's lemma makes full orbits tight [GHS08; WG11; HCM06].
3. **Trace identities and designs.** Welch/Sarwate identities come from Cauchy–Schwarz on the Gram matrix; k-th moment versions have equality exactly at projective k-designs, which complete MUB systems saturate for k = 1, 2 [We74; Sa79; KR05; SH03].
4. **Fourier interpolation.** L^{2q} norms of a polynomial are exact quadratures on roots of unity; at Gauss-sum nodes the integrand is flat, between nodes it is a Dirichlet-kernel combination, and the moment reduces to Gauss/Jacobi-sum counts plus Weil errors [Ka13; GS17b; JKS13a].
5. **Duality, positivity and Gauss-sum transfer.** Bound the dual operator, extend sums to full groups using positivity, and trade χ for e(a/q) at the cost of weights q/φ(q) [Mon78; MV73; Kow08; DR24 §9].
6. **Complementary pairing.** Combine two systems whose sidelobe spectra add to a constant (Golay, Rudin–Shapiro); in dictionary language, adjoin partner atoms until the frame operator is scalar [Go61; Ru59; DJ99].
7. **Weyl differencing.** A cubic phase differenced once gives a quadratic Gauss sum of exactly known modulus, turning a ridge into a pedestal [Al80; HS09].
8. **Group-theoretic Doppler tolerance.** Dilation eigenfunctions (hyperbolic FM; finite characters) are exactly Doppler-invariant, while chirps are tolerant only along a ridge [AT70; GHS08; LM04].
9. **Mismatched filtering as dual frames.** Remove sidelobes with the inverse Gram matrix, at a cost set by the lower frame bound [AG73; D].
10. **Zero-correlation zones as orthogonality counts.** M(Z+1) ≤ N, equality ⇔ an orthogonal system of shifted copies [TFM00; D].
11. **Periodic-to-aperiodic transfer.** Rotations, truncation and appending, plus an approximate difference-set condition (Σ_u(|(D+u)∩D| − p/4)²(log p)³/p² → 0) computable from cyclotomic numbers, decide the limit; order-6 cyclotomy separates Paley type (6.34) from Hall type (3.52) [GS17a Thm 2.3, Cor. 2.6].
12. **CRT-stable asymptotics.** Jacobi sequences keep the Legendre limit when all prime factors of the squarefree length are large [JKS13a Thm 2.3]; exact frame bounds multiply under tensor structure [D].
13. **Beating pairwise coherence.** Additive-combinatorial estimates on sumsets give RIP of order n^{1/2+ε} where Gershgorin stops at √n [BDFKK11; BFMW13].
14. **Bias warning.** Gauss-sum phases are equidistributed but biased at power-saving level; this bias is what the cubic large sieve's (AB)^{2/3} term records [HBP79; DR24].

**Ranking for bounding energies of Gauss-sum families.** Most likely to transfer: 1 (exact frame operators), 2 (proved coherence for character × chirp atoms), 3 (moment benchmarks and designs), 4 (higher moments via interpolation), 5 (large-sieve duality). Runners-up: 7, 13.

**How the sources bear on your two open questions.**

*Coherence.* Same modulus: exact. The Gram matrix of {χʲ(x)e(ax/q)} has entries −1, 0, q−1 or Gauss sums of modulus √q, so no estimate is needed (§10). Adding chirps and time shifts: the Weil bound gives 2√p and 4√p [GHS08; WG11], and about 1.9√p is attained numerically for p ≤ 127 [D]. For aperiodic (truncated) versions, mean-square crosscorrelations of character sequences have exact asymptotics [Ka16; BK17]. Across different moduli (the large-sieve regime) atoms live on different residue rings and coherence is an incomplete sum; Gershgorin loses, the Bessel bound must come from duality plus Poisson summation [HB00; BY10], and Gauss-sum bias gives a provable obstruction [DR24].

*Higher moments.* Lower-bound benchmarks: Welch's 2k-th moments, with equality at designs [We74; KR05]. Computation: Fourier interpolation gives L⁴ for every nontrivial character [Ka13] and all L^{2q} for Fekete and Galois polynomials [GS17b]. The missing case is L^{2q}, q ≥ 3, for non-quadratic characters, where, as in [Ka13] Thm 1.4 versus 1.5, only character/conjugate pairings should survive [F]. Moments of cross-correlations over Sidelnikov-type families are expressed through Jacobi sums and cyclotomic numbers [HY09; AM19].

## 12. Consolidated open items
* Sequence or array designs that use the Eisenstein structure of sextic residue symbols (reciprocity, composite or prime-power moduli π^k, norm-form arithmetic), with their L⁴, L^{2q}, ambiguity and Bessel properties; none located [O].
* L^{2q} limits for q ≥ 3 for non-quadratic characters and 𝔽_{p²}-arrays [O/U].
* A sextic large sieve over ℤ[ω] with sharp exponent; sharpness beyond the cubic case [O].
* Coherence or RIP beyond √N for character × chirp dictionaries via additive combinatorics [O].
* Flat ambiguity/SIC existence, Costas orders 32 and 33, binary merit-factor bound, even Barker lengths, Golay lengths, sup norm of Fekete polynomials [O].
