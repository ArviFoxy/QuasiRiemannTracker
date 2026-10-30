# A cubic large sieve past the √-barrier for prime vectors (sharpened Dunn–Radziwiłł)

Status: paper-level derivation from the published proofs, checked step by step against the text of
Dunn–Radziwiłł (arXiv 2109.07463v3, "DR") but **not refereed and not in Lean**. Evidence tag: [derived].
Purpose: record the one mechanism found so far that beats the √-barrier for the kind of vectors our slots are (see
`README.md`, target 0, and `../journal/JOURNAL.md`, 2026-10-30).

## Statement

Notation as in DR §9. A = size of the moduli a (squarefree, a ≡ 1 mod 3, N(a) ≍ A), B = length.

**Claim.**
- Hypotheses:
  - H1: one of the following holds:
    - (a) GRH for Hecke L-functions over Q(ω), as in DR;
    - (b) only the half-plane hypothesis that no such L-function vanishes for Re s > β₀, for some fixed
      β₀ ≤ 7/8. This is available inside our continuation argument.
  - H2: a twisted Heath-Brown–Patterson bound,
    Σ_{N(P)≍B, P prime} W(N(P)/B) g̃(P)‾ (P/|P|)^ℓ (k/P)₃ N(P)^{it} ≪ B^{5/6+ε}(1 + |ℓ| + |t| + N(k))^{O(1)}
    whenever ℓ ≠ 0 or k is not a cube.
- Conclusion: for every smooth W supported in [1, 2], every ε > 0 and every A^{1/2+ε} ≤ B ≤ A^{3/5−ε},

  Σ_{N(a)≍A} μ²(a) |Σ_{N(P)≍B} W(N(P)/B) (P/a)₃|² ≪_ε A^{1+ε}·B,

  i.e. the cubic large sieve is **diagonal for smooth prime vectors up to B = A^{3/5}**.
- Under H1(a) with η → 0 in place of H2 (square-root cancellation for the twisted prime sums), the range extends to
  B ≤ A^{5/7}.

Compare: Heath-Brown's bound A + B + (AB)^{2/3} is diagonal only up to B = A^{1/2}, and that is sharp for general
vectors (DR Theorem 1.4; de Faveri–Dunn–Hoffstein, unconditionally).

## Derivation

1. **Vector.** Write c_P = W(N(P)/B) = β_P g̃(P) with β_P = W(N(P)/B) g̃(P)‾. β is supported on primes, so it is
   squarefree and w-rough with w ≍ B. For prime support, the divisibility "u | a" in DR's axiom (3.2) leaves only
   u = 1 and u = a. So β ∈ C_η(B, w) with η = 1/3 by H2, and only for the small twists k that DR §9 actually uses:
   N(k) ≤ X^ε(1 + B²/A).
2. **η ≤ 1/4 is not needed.** DR use η ≤ 1/4 once, to get AB^{2η} ≤ X (line "Since η ≤ 1/4 we have
   AB^{2η} ≤ X"). That holds for every η ≤ 1/2. η also appears in D₂'s B^{2+2η}, which is ≤ AB iff
   B ≤ A^{1/(1+2η)} = A^{3/5} at η = 1/3.
3. **Prop 8.1 (Type I) is sharper than stated.**
   - The large-C range gives (8.6), ≪ U^{1+ε}/C₀³ with C₀ = (UN(r))^{1/12+ε/2}, i.e. U^{3/4}N(r)^{−1/4} up to
     X^{O(ε)}.
   - The main-term tail (8.9) is O(U^{3/4}N(r)^{−1/4}).
   - The small-C error is (8.10), U^{1/12+ε}N(r)^{7/12+ε}(1 + ℓ⁶).
   - DR state the weaker U^{5/6−ρ}N(r)^{−1/6−ρ}, ρ < 1/10000. The proof gives ρ = 1/12.
4. **Under H1(b).**
   - RH enters Prop 8.1 only through Möbius sums over c, twisted by (c/|c|)^{3ℓ}, at real part 1/2. Under the
     half-plane hypothesis these lose C^{β₀−1/2} ≤ C^{3/8}.
   - Large-C error: U^{1+(β₀−7/2)/12}N(r)^{(β₀−7/2)/12} = U^{0.781}N(r)^{−0.219}.
   - Small-C error: U^{0.115}N(r)^{0.615}.
   - Both stay below the Prop 8.1 main term U^{5/6}N(r)^{−7/6} once U ≥ N(r)^{2.47}.
   - DR's GRH in Theorem 1.4 (the lower bound, via a contour shift past zeros of ζ_K(3s − 2)) is not used in this
     upper-bound chain.
5. **Cross term C (DR (9.42)–(9.46)), π = γ = 1.**
   - The a-sum is Prop 8.1 at level r = b₁ (N(r) ≍ B), U ≍ A, weighted by N(a)^{−1/6} ≈ A^{−1/6}.
   - Summed over b₁ (B terms) and b₂ (weight Σ|β_{b₂}|N(b₂)^{−1/6} ≍ B^{5/6}), the errors are:
     - under H1(a): (AB)^{7/12}·B and B^{29/12}A^{−1/12};
     - under H1(b): (AB)^{0.615}·B and A^{−0.052}B^{2.448}.
6. **Diagonal D and trivial term T.**
   - D₁ (9.37): the main term + O(A^{2/3}B^{5/3}/w^{9/10}) + O(X^{1+ε}(1 + (B²/A)^{−1000})). The second is the
     diagonal AB as soon as B² ≥ A^{1+ε}.
   - D₂ (9.40): ≪ X^ε(AB^{2η} + B^{2+2η}).
   - T (9.18): the main term + O(A^{1/6+ε}B^{5/3}).
7. **Main terms.**
   - They are all proportional to A^{2/3}|Σ_b β_b N(b)^{−1/6}|².
   - For our β, Σ_P W g̃(P)‾ N(P)^{−1/6} ≪ B^{2/3+ε} by H2 at ℓ = 0, k = 1. That is Patterson's bias for primes,
     ~B^{5/6}/log B before the N^{−1/6} weight.
   - So they contribute ≪ A^{2/3}B^{4/3}, which is ≤ AB for B ≤ A.
8. **Collect, against the diagonal AB.** Each term is diagonal on the range shown:

   | term | diagonal for |
   |---|---|
   | B^{8/3} | B ≤ A^{3/5} |
   | (AB)^{7/12}B, or (AB)^{0.615}B under H1(b) | B ≤ A^{5/7}, or A^{0.627} |
   | B^{29/12}A^{−1/12}, or A^{−0.052}B^{2.448} | B ≤ A^{13/17}, or A^{0.727} |
   | A^{1/6}B^{5/3} | B ≤ A^{5/4} |
   | w-terms (w ≍ B) | always |
   | X²(B²/A)^{−1000} | B ≥ A^{1/2+ε} |

   So the binding constraint is B ≤ A^{3/5}, from D₂ at η = 1/3.

## What is still to check

- **H2 with the stated uniformity.** Heath-Brown (Israel J. Math 2000) proves the untwisted X^{5/6+ε}. The twisted
  version with polynomial dependence on (ℓ, t, k) should follow from the same Vaughan-identity proof, using the
  theta function at level k. If the dependence is N(k)^c with c > 0, the threshold becomes (1 + 2c)/(5/3 + 4c):
  0.571 at c = 1/6, still past 1/2.
- **Prop 9.1 vs 9.2.** Prop 9.2 sums over all moduli a with πγ²|a. Restricting to squarefree a (Prop 9.1, Lemma 9.2
  sieve weights) adds only w-type terms.
- **ε-bookkeeping.** DR fix ε < 1/10000 throughout. The ρ = 1/12 reading needs every other ε-dependent step to
  survive, which looks routine.

## Why it does not yet move θ

- Our faces use the **sextic** family, through Sil's √A reference (the sextic sieve's M^{5/6}N^{1/3} term). A
  sextic version needs a level-aspect Voronoi formula for sextic Gauss sums, and the sextic theta coefficients are
  only partly known (Brøker–Hoffstein, arXiv 1312.0568).
- The face's vectors are smooth × prime, not w-rough.
- Even with the reference relaxed, the faces stop at 6KB/(1 + K) → 2B, because K ≥ 1/2 (the selected norm's
  √-barrier). So this route is worth ≈ 0 alone.
- The inverse word's slot cost (P1) is a joint quadratic-row × cubic-slot norm with vectors longer than the family
  (B > A), where this sieve gives nothing.

It is nonetheless the first concrete evidence that the √-barrier is not intrinsic for prime vectors.
