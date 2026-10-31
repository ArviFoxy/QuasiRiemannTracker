# arvi_prime_dilation: the bilinear core of the prime-dilated short reference

Lean for Step 2 of the journal entry "The reference wall needs no metaplectic input" (2026-10-31). No `sorry`; every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (`#print axioms` at the end of each file).

| file | content |
|---|---|
| `PhaseMul.lean` | multiplicativity of Sil's Gauss phase over coprime supported sixth-power-free ideals: `phase_mul_unit`, `phase_mul`, `phase_mul_of_modulus_eq`, `phase_mul_of_norm_mod_thirty_six`, `phase_mul_root_of_unity`; `literal_identity_at_one_iff` (the identity without the unit factor is not provable) |
| `Bilinear.lean` | `bilinear_cs` (Cauchy–Schwarz) and `bilinear_sieve`, `bilinear_sieve_squarefree`: ‖Σ_{s,q} u_s v_q conj(rowValue(q², s))‖² ≤ C(P₂X)^ε·majorant(P₂, X)·Σ‖v‖²·Σ‖u‖², from Sil's `OptimalBound` with rows {q²} |

## The unit factor

- Sil's `modulus I` is a `Classical.choose` generator of the radical. So `modulus (I*J)` and `modulus I * modulus J`
  differ by a unit u. The exact identity carries `idealRowHom u (I*J)`, a sixth root of unity, which equals
  `u^((N(IJ) − 1)/6)` (`idealRowHom_unit_eq`).
- This is harmless for the bilinear bound. Write each modulus as a unit times the primary generator of the radical.
  The unit factors then split into two kinds:
  - **per-source factors**, depending on the product ideal only, which are absorbed into the source vector;
  - **factors constant on finitely many classes** (units of O × norms mod 36), handled by splitting the sums along
    those classes.

## Next (T3)

The correlation bound for slot convolutions is
‖Σ_{s,q} α_s a_q·conj(phase(sq))·idealRowHom k (sq)‖² ≪ (P²X)^ε·majorant(P², X)·‖α‖²‖a‖², with the constant
depending on ε only.
- Inputs: `phase_mul_unit`, reciprocity (`QRH.ArviKWall.ReciprocityBridge.reciprocity_composite`, which turns the
  coupling into rowValue(q², s) times a sign by classes mod 4), and `bilinear_sieve`.
- After that comes the reference fork itself: the Poisson step of Sil's `coherent_weighted_bound`, with the
  sixth-power-repeated dual rows kept as correlations and bounded by T3.
