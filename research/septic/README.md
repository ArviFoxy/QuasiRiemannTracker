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

For order ℓ the same proof gives `ℓ ∣ 2m + s` (septic: cost ≥ 7). Formalisation: planned (`Rigidity.lean`), from the
three library lemmas, Mathlib's Dirichlet theorem (`Nat.setOf_prime_and_eq_mod_infinite`) and the prime-power
non-vanishing lemmas.
