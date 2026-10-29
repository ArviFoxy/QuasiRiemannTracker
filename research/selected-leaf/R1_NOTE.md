# R1: the dualized selected energy (plan and proof chain)

Status: proof sketch [derived] plus an inventory of the Lean pieces [Lean, read]. Nothing here is proven yet
beyond the cited library theorems. Purpose: restore the selected-norm leaf (E5) after the sixth-root dilution
found in E5b (`../journal/JOURNAL.md`).

## 0. What is needed

Leaf rows w = V·z (|z|² ≤ bΦ K, M = log_Z(N(V)K)), polynomial

  positiveSlotRow(w) = (X₁X₂∏P_k)^{-1/2} · S₁(w) S₂(w) ∏_k T_k(w),

where S_j are the smooth plain sums `rowTwistedSum η m V z W_j t X_j` and T_k the prime slots. Selected rows:
some slot subset D with Σ_D w ≥ s_min has ∏_D ‖normalizedSlot‖² ≥ Z^{δ w(D)} (PR 93's `slotMass`).

**Target.** With X₁ ≥ X₂, x_j = log_Z X_j, P = x₁ + x₂, s = Σ w_k:

  Σ_{w selected} |positiveSlotRow(w)|² Φ(|z|²/K) ≤ C Z^{ε} (1+|t|+height)^n · Z^{max(M, P + s + (M − 2x₁)₊/6)}.

Price (selected branch): (P + s + (M − 2x₁)₊/6 − M)₊. The ledger scan (`root_ledger.py`, variant 'dual')
shows the K = 1/2 + η native line then holds to L ≈ 2.005.

## 0b. The library already has the I-side functional equation (found 2026-10-29)

`Moments/TwistedReflection.actual_original_twisted_reflection` (any `Character` χ with χ.residue ≠ 1):

  polynomial χ X ω = G · Σ_{D ⊆ S} Σ'_{H S-smooth} μ(∏D) ψ(∏D) ψ̄(H)/√(N(∏D)N(H)) ·
                      polynomial χ.inverse (paperRadialFourier (normTwistedSource W (ω/2π))) (N(ψ.mod)N(∏D)/(X N(H)))

ψ is primitive, ‖G‖ = 1, S = `redundantSet χ.modulus ψ.modulus`. Further pieces:
- `plain_polynomial_eq_row` (`Moments/DetectorDictionary.lean:33`) identifies the leaf's `rowTwistedSum` with
  `HeckeDyadic.polynomial`.
- `exists_row_character_with_conductor` / `exists_row_character_radical` give the row's `Character`.
- `actual_row_nonprincipal` (`Moments/NonprincipalGate.lean:49`) shows the row character is non-principal.
- A quantitative truncation is `actual_original_retained_approximation`.

So steps 1–6 below collapse into one library theorem. Divisors D cost nothing: the d-term has dual length
L₁N(d) but coefficient 1/N(d), so its large-sieve bound is ≤ the d = 1 term. Per root r, S is the fixed bad
primes plus the primes of r, and Σ_{D,H} 1/√(N(D)N(H)) ≤ Z^{ε}.

## 1. Proof chain (original sketch; steps 1–6 are now one library call)

1. **Row factorization.** For a source n coprime to 6 and primary (λ² | n − 1), with the row's supported
   numerator r (f⁴z = u λ^a 2^b r): `idealRowHom_factor_numerator` gives idealRowHom(row)(n) =
   numeratorBadTwist·(n/r)₆. The twist is periodic mod 72 and depends on (u, a, b, r mod 4). The moving part
   is `movingNumeratorRow r n = idealRowHom n (span r)`.
   `RowCompletion/PeriodicRows.exists_actual_periodic_row` packages the whole row as a periodic function
   mod Q·m·72·r.
2. **Primitive part.** Write r = ∏ p^{e_p}. Then (n/r)₆ = ∏_{e_p ≢ 0 (6)} (n/p)₆^{e_p mod 6} ·
   [n coprime to the p with 6 | e_p] = finiteSexticRow(P_w, j_w)(n)·[coprime E_w].
   Conductor c_w = ∏_{P_w} p: squarefree, good, with exponents j ∈ {1..5}.
3. **Möbius** on [coprime E_w] (and on the mask primes): Σ_{d | rad E_w} μ(d)[d | n] costs 2^{ω} ≤ Z^{ε}
   terms. Write n = d n', so the length becomes X/N(d).
4. **Bounded part.** B_w (primary indicator, unit, λ- and 2-supplements, reciprocity phase, η) is periodic
   mod N₀ = 72·Q·m and takes finitely many shapes. Split n' by class mod N₀. Choose the coset representative
   ≡ 0 mod c_w (CRT, since c_w is coprime to N₀). This turns the class sum into a radial-weight sum twisted by
   a phase that depends only on h mod N₀ and on c_w mod N₀ (finitely many row classes).
5. **Poisson + Gauss.** `GaussSum/SexticRadialPoisson.canonical_compact_radial_poisson_normalized`:
     Σ_z finiteSexticRow(P,j)(z)·W(|z|²/X) = (X·G/|c|)·Σ_h conj(finiteSexticRow(P,j)(h))·Ŵ(X|h|²/|c|²),
   with |G| = 1 (`norm_canonicalNormalizedGauss`). The summation variable is an arbitrary element of O,
   so this is the I-side dual verbatim (the library uses it for the z-side). The twist N(I)^{it} is radial:
   use W_t(x) = (xX)^{it} W(x) (support [1/4, 9/4], smooth).
6. **Family match.** conj(finiteSexticRow(P_w, j_w)(h)) = conj(idealRowHom(u_w)(h))·(bounded twist), with u_w
   the sixth-free core: the same factorization as step 1, read backwards. So, up to conjugation, the dual is
   a polynomial in PR 93's selected matrix entries idealRowHom(u)(J).
7. **Separation.** Ŵ(X|h|²/|c_w|²) depends on the row through N(c_w). Dyadic in N(c_w), then a partition of
   unity on the dual side; Mellin on Re s = 0 turns N(c_w)^{iτ} into a unimodular row factor.
   Ŵ decays rapidly beyond Z^{ε}(1+|t|)², which truncates the dual length to Z^{ε}(1+|t|)²·N(c_w)/X.
8. **Norm.** |S₁S₂T|² = (X₁/N(c))·|conj(dual)·S₂·T|²: a polynomial in idealRowHom(u)(·) with sources
   J·I₂·I_T. PR 93's `ActualSelectedSlotNorm` (proved: `NaturalUniformNear.natural_selected_cell_norm`) holds
   per root with any sources. The coefficient ℓ² mass costs a divisor bound τ₃ ≤ Z^{ε}.
9. **Root sum.** Rows w = u·g(r)⁶ (`sixthFrequencyEquiv`, `sixthFreeFiber` in PR 93). Per root ρ = log_Z N(r)
   the bound is max(X_eff, (1−δ)y + δX_eff), y = M − 6ρ, X_eff = min(x₁, y − x₁) + x₂ + s. Roots with
   y < x₁ contribute O(Z^{−A}) (rapid decay of Ŵ: the dual has no terms). Summing over ≈ Z^ρ roots gives
   the target exponent; the sum is uniform_sixth_root_sum-like.

## 2. Lean inventory (read)

| need | library theorem |
|---|---|
| row as periodic function | `CanonicalRowCompletion.exists_actual_periodic_row`, `rowTwist_eq_actualPeriodicRow_primary` |
| reciprocity factorization | `CanonicalRowCompletion.idealRowHom_factor_numerator` |
| Poisson, squarefree sextic, radial | `ActualEisensteinCubic.canonical_compact_radial_poisson_normalized` |
| unimodular Gauss factor | `norm_canonicalNormalizedGauss` (used in `Moments/Primitive.lean`) |
| general periodic Poisson | `Poisson/EisensteinLattice.actual_eisenstein_periodic_poisson` |
| per-root selected norm | PR 93 `FineNaturalCount.ActualSelectedSlotNorm` (proved) |
| sixth-root bookkeeping | PR 93 `FineDetectorCount.uniform_sixth_root_sum`, `natural_root_count_of_uniform_free_counts` |
| primal bound from norm | `FiniteSieveOperator.operator_conjTranspose_norm` |
| slot sixth-root mask | PR 93 `normalizedSlot_sixth_root` |
| Möbius mask + primitive Poisson, collected | `PrimeRows/IdealGenerators.canonical_masked_compact_radial_poisson_collected` |
| dual-weight separation (unit log-phases, L¹ kernel ≪ (1+R)^{-A}) | PR 93 `RadialSeparation.radial_pair_log_separation`, `paperRadialFourier_log_separation_envelope` |
| z-side analogue with bad classes mod 36 | PR 93 `MaskedPairPoisson.admissible_masked_pair_poisson`, `primitivePair_frozen_frequency` |

## 3. Risks (updated after the inventory)

- Step 7 is covered by PR 93's separation envelope; what must be checked is that its constant is uniform in
  the height twist (the weight is x^{it}W(x); the baseline has `normPowerProfile ... t` with polynomial
  seminorm growth, `volumeControl_polynomial_height`).

- Step 4 (bounded twist inside Poisson) has no library lemma yet; the CRT-coset trick needs care.
- Step 7 needs t-uniform decay of the radial Fourier transform of W_t with polynomial (1+|t|) loss
  (cf. `normPowerProfile_uniform_degree`).
- The E5 leaf must also run the unselected branch: row-dependent lowest-amplitude deletion sets, union over
  2^{#slots} choices (fixed before Z), parent contract.
