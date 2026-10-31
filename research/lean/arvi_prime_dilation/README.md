# arvi_prime_dilation: the bilinear core of the prime-dilated short reference

Lean for Step 2 of the journal entry "The reference wall needs no metaplectic input" (2026-10-31). No `sorry`; every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (`#print axioms` at the end of each file).

| file | content |
|---|---|
| `PhaseMul.lean` | multiplicativity of Sil's Gauss phase over coprime supported sixth-power-free ideals: `phase_mul_unit`, `phase_mul`, `phase_mul_of_modulus_eq`, `phase_mul_of_norm_mod_thirty_six`, `phase_mul_root_of_unity`; `literal_identity_at_one_iff` (the identity without the unit factor is not provable) |
| `Bilinear.lean` | `bilinear_cs` (Cauchy–Schwarz) and `bilinear_sieve`, `bilinear_sieve_squarefree`: ‖Σ_{s,q} u_s v_q conj(rowValue(q², s))‖² ≤ C(P₂X)^ε·majorant(P₂, X)·Σ‖v‖²·Σ‖u‖², from Sil's `OptimalBound` with rows {q²} |
| `Correlation.lean` | the canonical phase `phaseCan` of a squarefree supported ideal (`unitOf`, `norm_phaseCan`); its exact multiplicativity `phaseCan_mul`; `slot_term_eq` (a slot coupling is a sign times conj rowValue(q², s)); `class_split_bound`; **`correlation_bound`**: ‖Σ_{s,q} α_s a_q·conj(phaseCan(sq))·idealRowHom k (sq)‖² ≤ C(P₂X)^ε·majorant(P₂, X)·Σ‖α‖²·Σ‖a‖², with C depending on ε only; `correlation_bound_of_eq` |

## The unit factor

- Sil's `modulus I` is a `Classical.choose` generator of the radical. So `modulus (I*J)` and `modulus I * modulus J`
  differ by a unit u. The exact identity carries `idealRowHom u (I*J)`, a sixth root of unity, which equals
  `u^((N(IJ) − 1)/6)` (`idealRowHom_unit_eq`).
- This is harmless for the bilinear bound. Write each modulus as a unit times the primary generator of the radical.
  The unit factors then split into two kinds:
  - **per-source factors**, depending on the product ideal only, which are absorbed into the source vector;
  - **factors constant on finitely many classes** (units of O × norms mod 36), handled by splitting the sums along
    those classes.

## The correlation bound (T3, done)

- **Canonical phase.** For a squarefree supported I the radical is I, so `modulus I = unitOf I · primaryGenerator I`
  for a unit `unitOf I` (`exists_unit_modulus_eq`). Removing that unit gives
  `phaseCan I = conj(idealRowHom (unitOf I) I)·phase I`, of modulus one, and exactly multiplicative:
  `phaseCan (IJ) = idealRowHom (pg J) I · idealRowHom (pg I) J · phaseCan I · phaseCan J` (`phaseCan_mul`).
- **Reciprocity** comes from Sil's `SieveOperator.row_reciprocity` (the baseline's `idealRowHom_ideal_reciprocity`).
  Its sign depends only on the residue classes of the primary generators mod 4, so the file does not need
  `ReciprocityBridge`.
- **Classes.** Only the q-sum is split, by the class of q (16 classes of `ZMod 4 × ZMod 4`); the sign for the class of
  s is absorbed into the s-coefficients. So C = 16·C₀, with C₀ from `bilinear_sieve_squarefree`.
- **Scope.** Sources s and slots q are squarefree (`PowerFree 2`). The long factor's non-squarefree part needs either
  the general phase or a separate argument.

## Next

The reference fork itself: the Poisson step of Sil's `coherent_weighted_bound`, with the sixth-power-repeated dual
rows kept as correlations and bounded by `correlation_bound`.
