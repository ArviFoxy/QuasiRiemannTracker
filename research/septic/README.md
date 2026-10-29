# Identities of Gauss sums of order ℓ: septic sums, classification, and what it means for the chain

Question (Arvi, 2026-10-29): classify the identities satisfied by septic (order 7) Gauss sums, or prove that there are
none; find more identities like the sextic ones (unit scale, Collet's sixth-power pool, Sil's fourth-power transfer),
possibly coming from cohomology / traces of Frobenius on geometric objects.

Status tags: **[L]** Lean theorem in the library; **[T]** published theorem (reference given), not formalised;
**[C]** exact computation in this folder (script named); **[D]** own derivation, checkable by hand, not formalised.

## 0. Answer in five lines

1. Every identity the chain uses is a formal consequence of three facts, for any order ℓ: the dilation eigen-relation
   `g(n, E h) = χ_n(E)⁻¹ g(n, h)`, CRT twisted multiplicativity `g(ab, h) = χ_a(b) χ_b(a) g(a, h) g(b, h)`, and ℓ-th power
   reciprocity `χ_a(b) = ε(a, b) χ_b(a)` [L for ℓ = 6]. For order ℓ they give the pool `g(u, p^ℓ h) = 1_{p∤u} g(u, h)` and the
   transfer `g(B n, h) = ε g(B, h) g(n, B^{ℓ−2} h)` (ℓ = 6: Sil's `D⁴`; ℓ = 7: `D⁵`) [D].
2. **Rigidity:** a twist-free transfer has scale cost `c ≡ 0 (mod ℓ)`, so `c = ℓ` at best (R2 §2.4 for ℓ = 6, same proof for
   any ℓ) [D]. Septic sums cost 7 instead of 6: **strictly worse for the chain.** The order of the characters is the lever:
   a cubic amplifier would cost 3.
3. **Local identities (one prime):** by Stickelberger + Kronecker, the multiplicative relations among `g(χ^a)`,
   `a = 1..ℓ−1`, modulo roots of unity, are the integer kernel of the Stickelberger vectors [T]. For ℓ = 7 (any prime ℓ)
   the only ones are `g(χ^a) g(χ^{−a}) = p`; ℓ = 6 has exactly one more, Hasse–Davenport `g(χ) g(χ⁴) ~ g(χ²) g(χ³)` [C:
   `stickelberger_rank.py`]. So septic sums have *fewer* identities than sextic ones, not more.
4. **Global identities (across primes):** the monomials in Gauss sums whose Stickelberger vector is integral (Jacobi
   sums, `g^ℓ`) are Hecke characters of `Q(ζ_ℓ)` — Weil, via the CM of the Fermat curve `x^ℓ + y^ℓ = 1` [T]. This is the
   geometric source Arvi suspected: Gauss sums are traces of Frobenius on `H¹_c(G_m, L_χ ⊗ L_ψ)`, Jacobi sums on `H¹` of
   Fermat curves (§3).
5. None of the identities in 3–4 lowers the transfer cost (the Hasse–Davenport factorisation of `g₆` through `g₃, g₂`
   reproduces the same exponent `4 mod 6`, §4). What could: a lower-order amplifier, a twisted transfer with a
   conductor-uniform source theorem (R2 lemma T), or the squared-block source (R2 §3).

(Sections 1–5 below: definitions, proofs or references, computations.)

## 1. Rigidity of twist-free transfers (sextic case; the proof works verbatim for any order ℓ)

Notation of the library: `O = ℤ[ω]`, `χ_n(x) = idealRowHom x (span n)`, `g(n, h) = sexticGauss n h`,
`ε(a, b) = sexticReciprocityPhase a b`.

**Theorem R (no cheaper transfer).** Let `D` be a supported primary prime, `m ≥ 1`, `s ≥ 0`, `c ∈ ℂ`. Suppose
`g(Dᵐ n, h) = c · g(Dᵐ, h) · g(n, Dˢ h)` for every supported primary `n` coprime to `D` and every `h`.
Then `6 ∣ 2m + s`. In particular the scale cost `2m + s` of a twist-free transfer is a positive multiple of 6;
Sil's `D⁴` (`m = 1, s = 4`) and the squared block `D²` (`m = 2, s = 2`) are optimal, and no identity of this shape
with smaller cost exists.

*Proof.* For `n` as above:
* CRT [L `sexticGauss_coprime_product`]: `g(Dᵐn, h) = χ_{Dᵐ}(n) χ_n(Dᵐ) g(Dᵐ, h) g(n, h)`;
* reciprocity [L `idealRowHom_primary_reciprocity`]: `χ_{Dᵐ}(n) = ε(Dᵐ, n) χ_n(Dᵐ)`;
* dilation [L `sexticGauss_unit_scale`]: `g(n, Dˢh) = χ_n(D)^{−s} g(n, h)`.
So the hypothesis reads `(ε(Dᵐ, n) χ_n(D)^{2m+s} − c) · g(Dᵐ, h) g(n, h) = 0` for all `h`. At `h = D^{m−1}`,
`g(Dᵐ, D^{m−1}) ≠ 0` (prime-power table) and `g(n, D^{m−1}) = χ_n(D)^{1−m} g(n, 1)`.
(i) `n = 1`: `χ_1 = 1`, `ε = 1`, `g(1, ·) = 1`, so `c = 1`.
(ii) By Dirichlet's theorem take a rational prime `q ≡ 1 (mod 12)` that is a primitive root modulo `p = N(D)`
(`D` split; for `D` inert the residue field is `F_{p²}` and one takes `q` generating `F_{p²}^×/F_p^×`-part of the
sextic character — for inert `D` the sextic symbol is trivial on `F_p^×`, so this case needs `n` non-rational and is
excluded from the formal statement). Then `n = q` is supported, primary, coprime to `D`, squarefree (`q = π π̄`), so
`g(q, 1) ≠ 0`; `q ≡ 1 (mod 4)` gives `ε(·, q) = 1`; and `χ_q(D) = ε(q, D) χ_D(q) = q^{(p−1)/6} mod D`, a primitive
sixth root of unity. Hence `ζ₆^{2m+s} = 1`, i.e. `6 ∣ 2m + s`. ∎

For order ℓ the same proof gives `ℓ ∣ 2m + s` (septic: cost ≥ 7).

**Formalised (m = 1) [L]:** `QRH.ArviNewpowers.Rigidity.no_cheaper_transfer` in
`research/lean/arvi_newpowers/Rigidity.lean` (dev tree `Submissions/arvi_newpowers/Rigidity.lean`), axioms
`propext, Classical.choice, Quot.sound`. Statement: for a supported primary prime `D` of prime norm `p`, if
`sexticGauss (D n) 1 = c · sexticGauss D 1 · sexticGauss n (D^s)` for every supported primary `n` coprime to `D`,
then `6 ∣ 2 + s`. The test modulus in the proof is `n = −q` with `q` a rational prime, `q ≡ 11 (mod 12)`, `−q` a
primitive root mod `p` (Mathlib's Dirichlet theorem `Nat.forall_exists_prime_gt_and_modEq`); along the way:
`prime_natCast_of_mod_three` (rational primes `≡ 2 mod 3` stay prime in `ℤ[ω]`), `absNorm_natCast`
(`N((m)) = m²`), `orderOf_mk_natCast`, `six_dvd_sub_one`. The general-`m` and general-`E` versions (R, R′ below)
follow the same proof; their formalisation needs the prime-power Gauss sum at `h = D^{m−1}` and is not done.

**Theorem R′ (no cheaper dilation of any kind).** Let `D` be a split supported primary prime, `m ≥ 1`, and `E` a
supported primary element (any element, not only a power of `D`), `c ∈ ℂ`. If
`g(Dᵐ n, h) = c · g(Dᵐ, h) · g(n, E h)` for every supported primary `n` coprime to `D E` and every `h`, then
`6 ∣ v_D(E) + 2m`; hence `N(E) ≥ N(D)^{(−2m) mod 6}` and the cost `2m + v_D(E)` is again a positive multiple of 6.

*Proof.* As in R, the identity is `ε(Dᵐ, n) χ_n(E Dᵐ Dᵐ) = c` whenever `g(Dᵐ, ·) g(n, ·) ≢ 0` (now
`χ_n(E)^{-1}` from the dilation). `n = 1` gives `c = 1`. By Dirichlet's theorem pick a rational prime `q` with
`q ≡ 1 (mod 12)`, `q` a primitive root mod `p = N(D)`, and `q ≡ 1 (mod N(P))` for every prime `P ≠ D, D̄` dividing `E`
(and `q ≡ 1 (mod p)` would be replaced by the primitive-root condition only at `D`; if `D̄ | E`, use `q ≡ 1` on the
`D̄` side by working with `n = π` a prime factor of `q` instead of `q` — the formal statement assumes `D̄ ∤ E`).
Reciprocity turns `χ_q(x)` into `∏_{P | x} (q / P)₆^{v_P(x)}`, all factors are 1 except the one at `D`, which is a
primitive sixth root `ζ` raised to `v_D(E) + 2m`. So `ζ^{v_D(E)+2m} = 1`. ∎

(The same argument with `n ↦ n^j` dilations on the block side reproduces R1's bi-dilation table `BD`, again with
cost a multiple of 6: dilating by the residual modulus only moves the twist to the block, where it is a twist of the
amplifier coefficients, i.e. R2's twisted types.)

## 2. Identities at one prime: complete list (Stickelberger)

For a prime `π` of `ℤ[ω]` of norm `p ≡ 1 (mod 6)` let `χ = χ_π` (order 6) and `G_a = g(χ^a)`, `a = 1..5`.
By Stickelberger's theorem [T: Stickelberger 1890; e.g. Washington, *Cyclotomic Fields*, Prop. 6.13] the ideal of
`G_a` in `ℚ(ζ_6, ζ_p)` has exponent vector `(⟨a t / 6⟩)_{t ∈ (ℤ/6)^×}`, `p` has `(1, 1)`, and a monomial with zero
exponent vector is a root of unity (Kronecker: all its conjugates have absolute value 1). So the multiplicative
relations among `G_1..G_5, p` modulo roots of unity form the integer kernel of a 2 × 6 matrix of rank 2
[C: `stickelberger_rank.py`]: a lattice of rank 4, generated by the three conjugate pairs
`G_a G_{6−a} = χ^a(−1) p` and **one** more relation, Hasse–Davenport `G_1 G_4 = χ(4)^{-1} G_2 G_3` (exact form
R1 §3.5.5, checked on 231 primes). Every other identity at one prime (Kummer `G_2³ = −p π`, `G_3² = χ(−1) p`, the
sixth-power law `G_1⁶ = ±p π⁴`, the Jacobi link) is a consequence of these plus Stickelberger's evaluation of
the root of unity. For prime order ℓ (septic) the matrix has rank `(ℓ+1)/2` and the kernel is only the conjugate
pairs: there is no Hasse–Davenport relation because ℓ has no proper divisor.

## 3. Where the identities come from geometrically (the "cohomology" question)

* **Gauss sums are traces of Frobenius.** On `G_m` over `F_p` there are rank-one lisse sheaves `L_χ` (Kummer: from
  the covering `t ↦ t^6`) and `L_ψ` (Artin–Schreier: from `t ↦ t^p − t`). `H^i_c(G_m, L_χ ⊗ L_ψ)` vanishes for
  `i ≠ 1` and is one-dimensional for `i = 1`, and the Lefschetz trace formula gives
  `g(χ, ψ) = −Tr(Frob | H¹_c(G_m, L_χ ⊗ L_ψ))` [T: Deligne, SGA 4½, *Sommes trig.*].
* **Dilation** (`g(n, E h) = χ̄_n(E) g(n, h)`) is the translation `t ↦ E t` on `G_m`: it fixes `L_χ` up to the
  constant `χ(E)` and moves `L_ψ` to `L_{ψ(E·)}`.
* **CRT twisted multiplicativity** is the product decomposition `Spec O/(ab) = Spec O/a ⊔ Spec O/b`, the twist being
  the restriction of `χ_{ab}` to the two factors; **reciprocity** is the product formula for Hilbert symbols
  (global class field theory).
* **Hasse–Davenport** comes from the Kummer isogeny `[2] : G_m → G_m`: `[2]_* Q̄_ℓ = Q̄_ℓ ⊕ L_{χ³}`, so
  `[2]^*`-pullback and the projection formula split `H¹_c(L_χ ⊗ [2]^* L_ψ)` into two pieces; it exists for sextic
  sums because `6 = 2 · 3`.
* **Jacobi sums** `J(χ^a, χ^b) = G_a G_b / G_{a+b}` are Frobenius eigenvalues on the `(a, b)`-eigenspace of `H¹` of the
  Fermat curve `x⁶ + y⁶ = 1`, whose Jacobian has complex multiplication; therefore `π ↦ J(χ_π^a, χ_π^b)` is an
  algebraic Hecke character of `ℚ(ω)` [T: Weil 1952, *Jacobi sums as Grössencharaktere*]. The sixth-power law
  `G_1⁶ = χ(−1) p · J(χ,χ) J(χ,χ²) J(χ,χ³) J(χ,χ⁴)` is a product of such characters: this is the *only* way Gauss
  sums at different primes are linked multiplicatively. A monomial that is not of Jacobi type (non-integral
  Stickelberger vector, e.g. `G_1` itself) has no such link: its argument is equidistributed over primes
  [T: D. R. Heath-Brown, S. J. Patterson, *The distribution of Kummer sums at prime arguments*, J. reine angew. Math. 310 (1979) 111–130, for cubic sums; S. J. Patterson, *The distribution of general Gauss sums and similar arithmetic functions at prime arguments* (1987), for order n ≥ 3 over fields containing μ_n (as summarised in David–Dunn–Hamieh–Lin, arXiv:2306.11875)].
* **Stickelberger's exponents** are the slopes of Frobenius (Newton polygon) on the crystalline side
  (Gross–Koblitz: `G_a = −π_p^{s(a)} Γ_p(·)`), and the complete set of relations among such monomials corresponds to
  (absolute) Hodge cycles on Fermat varieties [T: Deligne 1979–82; Koblitz–Ogus]. That is the precise version of
  "identities come from cohomology": every identity is an isomorphism of these rank-one motives.

## 4. What this means for the chain

The chain's amplifiers are *pointwise-in-`h` transfer identities*; §1 (Theorems R, R′) shows that none of them is
cheaper than cost 6, whatever the dilation. The identities of §2–3 are of a different kind (values at one prime, or
Hecke characters across primes); feeding them into an amplifier does not change the transfer exponent (the
Hasse–Davenport factorisation `G_1 = χ(4)^{-1} G_2 G_3 / G_4` has cubic and quadratic factors whose own transfers
`D¹` and `D⁰` recombine to the sextic `D⁴`). Cheaper amplification therefore needs one of: (a) a twisted transfer
with a source theorem (R2 lemma T), (b) the squared-block source (R2 §3), or (c) amplifier coefficients of lower
order (cubic would cost 3) — whether the baseline's sextic order can be lowered is under investigation (§5).
