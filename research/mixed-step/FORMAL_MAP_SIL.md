# FORMAL_MAP_SIL: Sil's fourth-power transfer at Collet's first MAIN (2026-10-25)

Read-only: nothing was edited or built. "(inf.)" marks my own inference; every other claim is cited.

Path prefixes:
- `F/` = `lean-env/qrh/Submissions/arvi_repeated_marks_on_sil_face_20261025/FourthPower/`
- `B/` = `…/openai_baseline/OAI/NumberTheory/DirichletL/Moments/`
- `H/` = `…/hailey_collet_1252270103/`, and `C/` = `H/Record1252270103Source/`

## Summary

1. **Everything in (T) is proved in Sil's tree.** This covers (T) itself, Cauchy–Schwarz and the pushforward, with no `sorry` or `axiom` in the files below (grep).
   - The algebra is stated over baseline types and applies to Collet verbatim: CRT, ray table, fourth power, pushforward.
   - The column bookkeeping that feeds it is tied to Sil's restricted source: `Data`, `tupleWeight`, `originalKernel`.
2. **Correction to ADVERSARIAL_REVIEW §1.1 and MIXED_STEP_LEMMA §2.1.**
   - The claim "non-coprime n, D vanish on both sides" holds only on the residual side (`GaussTransfer.fourth_power`, F/GaussTransfer.lean:81).
   - On the left side it fails. Take a column with p | D and p | v₀v₁ (the ordinary pair). Then p² ∥ u, and the sextic Gauss sum mod p² is N(p)·1_{p|h}·g_p(h/p). This is nonzero for p ∥ h (inf., standard).
   - Sil never meets such columns. His restriction makes the marked product coprime to the ordinary pair (`restriction`, F/MixedCommonRestriction.lean:38; `Restricted`, F/KernelRestrictedState.lean:54).
   - Accordingly, `fixed_product_rays` (F/MixedSupplierKernel.lean:141) carries the mask `IsCoprime (f*D) n` on its left side.
   - Collet's projectors give only a squarefree marked product and a squarefree ordinary pair, i.e. valuation ≤ 2 (C/Collision/Projector.lean:40). So these "collision" columns do occur.
   - Their density per selected slot is ≍ Σ_{p∈pool} 1/N(p). That is not a power of U (inf.), so they cannot be dropped.
   - **This is the main formal gap.**
3. **The "f" in u = f·D·n is Sil's supplier block.**
   - It consists of the child slots whose primes divide the child seed L (`supplierCharacters`, F/MixedSupplierPartition.lean:25, called with u := seed at F/MixedSupplierReconstruction.lean:245).
   - It is not the paper's first frozen width. That width is already outside Collet's child modulus, in `K*markedProduct B` and the puncture `R*C` (C/High/GlobalPhysicalAllocationMain.lean:56–60).
4. **The residual is a literal Collet source, under two hypotheses.** These are (S), no selected slot supplies L, and (Col), no selected/ordinary collision. Then the residual is literally Collet's child MAIN on `{i // i ∉ J}`. Only two things change: τ ↦ `childCharacter τ ξ` and T ↦ T/∏_J P.
5. **Size.** About 1.0–1.6k lines under (S) and (Col). Discharging (Col) is open, and it is the dominant risk.

## 1. Inventory, step by step (all F/)

| step | Sil theorem (file:line) | stated over |
|---|---|---|
| columns → tuples | `finite_column_sum` (MixedRestrictedDictionary:69), `split_tuple_sum` (MixedTupleRows:31), `source_gauss_sum` (MixedSupplierReconstruction:186) | baseline `Tuple`/`finiteColumnCoefficient`, any β and multiplier |
| supplier partition | `profile_full_partition` (MixedSupplierPartition:37) | baseline `profileCoefficient` |
| freeze, then select | `split_two_levels` (MixedSupplierSplit:188); `selected_holes` (MixedSupplierReconstruction:404) → `crossGate` (MixedSupplierKernel:58) | generic `weightedSum` |
| expanded MAIN | `tuple_supplier_expansion` (:127), `original_gauss_supplier_expansion` (:195), `masked_tuple_supplier_expansion` (:245) | Sil's `tupleWeight H v * profileCoefficient …` |
| u = f·seed, seed ⊥ D | `actual_suppliers_seed` (:436), `surviving_seed_iff` (MixedSelectedCommon:27) | generic ideals |
| kernel split | `full_gate_split` (Kernel:77), `original_kernel_split` (:99), `literal_row_eq` (:262) | Sil's `restriction` |
| CRT and rays | `normalized_coprime_product` (MixedSelectedCommon:46), `masked_product_rays` (:74), `fixed_product_rays` (Kernel:141) | generic |
| fourth power | `GaussUnits.fourth_power` (:36); `GaussTransfer.fourth_power`, `normalized_fourth_power`, `whole_column` (:81, :98, :106); `sparse_fourth_power` (MixedPhysicalTransfer:50); `restricted_gauss_transfer` (KernelWholeColumns:85) | generic; FifthFree needed only where the coefficient ≠ 0 |
| (T) assembled | `fixed_supplier_row_fourth` (Kernel:174); `ideal_seeded_selected_row_fourth` (MixedSelectedCommon:190), with f only in the seed mask | generic |
| family form | `selected_fourth` (MixedSupplierFourthRow:288), `actual_family_fourth` (:358), `partition_branch_fourth` (:430) | Sil `Data` (:27) |
| residual is a source | `common_height_character` (MixedSupplierSource:59, generic); `common_polynomial_source` (:238); `common_polynomial_original` (MixedSupplierCanonical:179) | Data → Sil `originalColumn` |
| Cauchy over (χ, ξ, D) | `first_ray_sq` (MixedSupplierPositive:323, generic); `fourth_family_sq` (:340), `ray_budget_grouped` (:418), `weighted_original_sum` (:598), `normalized_selected_card` (:251) | Data |
| pushforward | `fiber_card`, `weighted_pushforward`, `frequency_norm_bound` (PositiveFamily:27, :49, :92); `sparse_weighted_average` (MixedPhysicalTransfer:66) | generic |
| grouped average | `selected_fiber_subpower` (:479), `actual_grouped_average` (:525) | Data |
| choice of the block | `upward_subset` (GlobalSlotSelection:17); `Specification` (:33) hard-codes 43/100 | generic |

The assembled identity `fixed_supplier_row_fourth` reads:

Σ_v A·B_v·heightCoeff(fD·n_v)·[fD ⊥ n_v]·idealGauss(fD·n_v)(k)
= Σ_{χ,ξ} π_{χξ}·(A·heightCoeff(fD)·χ(fD)·idealGauss(fD)(k))·gaussPolynomial(n)(fixedCommonCoefficient n B f τ t ξ)(D⁴k).

**Which Cauchy path Sil actually uses.** Sil's chain applies Cauchy at the original frequency: `original_family_sq` (MixedSupplierOuterFamily:53), reached through `uniform_weighted_original_sum` (:77) from OuterFreshConsumer:490. The fourth-power path (`fourth_family_sq` … `actual_grouped_average`) is proved but has no consumer (grep). (T) needs exactly this unused path.

## 2. What applies verbatim, and what each adapter must prove

**Verbatim.** All rows marked "generic" above. Each takes arbitrary ideals and coefficient vectors. The same holds for `prime_product_gauss_norm` (MixedSupplierPositive:118).

**Γ is not an obstacle.**
- Collet's actual Γ is `(√T)⁻¹·rowWeight τ fixedBadMask 1 1 t` (C/High/GlobalPhysicalAllocationMain.lean:93).
- `rowWeight` is a `→*₀` hom (B/HeckeExpansion.lean:13), so Γ(D·n) splits with no twist.
- `rowWeight_split` (B/SourceRow.lean:14) only moves the row variable z, and here z = 1.
- On supported I, `heightCoeff_eq_fixed_rowWeight` (B/SecondHeightFamily.lean:29) turns Γ into Sil's `heightCoeff`.

The twists in (T) come from elsewhere:
- **CRT reciprocity phase.** It is expanded by `firstPhaseTable_expansion` (B/FirstColumns.lean:50), with mass ≤ 256 (:57).
- **χ_n(D)².** It is consumed by `fourth_power`.
- **The ray label ξ.** It enters the residual character through `child_ideal_primary` (B/SecondChildProfile.lean:16).
- **χ_n(f)², when there are suppliers.** Sil's `common_height_character` absorbs it into a Hecke character ψ with modulus ≤ N(τ)·C·N(f)·N(12). The alternative is Collet's row parameter A = f², but that changes Γ's shape.

**Fifth-freeness** (about 20 lines). Combine three lemmas:
- `tuple_valuation_of_projectors` (C/Collision/Projector.lean:40), or `valuation_bound_of_dvd` (H/Record1252270103CommonGeometry/ColumnTypes.lean:37);
- `powerFree_iff_valuations` (F/KernelIdeal.lean:23);
- `element_fifth_free` (F/KernelWholeColumns.lean:72).

**Coprimality.**
- `squarefreeIndicator_mul` (H/Record1252270103TwoIdeal/Projector.lean:24) splits sq(K·D·M) into three parts:
  - sq(D)·[D ⊥ K], which depends on D only (Sil's `selectedGate`);
  - sq(K·M), the residual's own projector;
  - [D ⊥ M], Sil's crossGate.
- [D ⊥ R] comes from the puncture in `profileCoefficient`.
- A₁ and A₂ divide C, so the child puncture R·C keeps D off them.
- **[D ⊥ v₀v₁] is missing. That is (Col).**

**Seed and suppliers.**
- Under (S), set f = 1. Then L | D·n ⟺ L | n (`surviving_seed_iff` at f = 1), and no partition is needed.
- Otherwise, port Sil's full partition (`profile_full_partition`, `split_two_levels`, `partition_branch_fourth`).
  - Cauchy over frozen assignments costs at most τ(L)^{|ι|} = Z^{o(1)} (inf.).
  - But f then enters the Gauss modulus, so (Col) must also cover f.
- Collet's seed is L = `(column l).2.1.val` (C/Core/InitialRegularToTruncatedMain.lean:29). It is squarefree (`actual_first_live_squarefree`, H/Cycle61/Physical/InitialMass/ActiveColumns.lean:59). Its primes may be marked primes.

**F.** At the first MAIN layer the chain uses F = `fun _ => 1` (same file). A general F needs F(Dc·D·X) = F(Dc·X) for every selected D. Pool corrections satisfy this, because pool primes avoid the slots (`hmarked`).

**Bound to Sil's records.** The proofs below can serve as templates of ≤ 100 lines each:
- the `Data`-indexed lemmas in MixedSupplierFourthRow, Positive, OuterFamily, Source and Canonical;
- the `tupleWeight` expansions: `packed_coefficient` (MixedSupplierSplit:72), `productKernel` and `supplierExpansion` (Reconstruction:33, :110);
- `MixedSelectedVolume.actual_selected_volume_average` (:67), which is stated over Sil's `Source`.

## 3. The residual's shape

Sil's "common residual vector" (`fixedCommonCoefficient`, Kernel:133; `commonVector`, FourthRow:84) is already a literal source. `common_polynomial_original` (Canonical:179) rewrites it as Sil's `originalColumn` on RestIndex, with:
- puncture R·f;
- seed L/f;
- slot characters `avoid u ν`;
- the new character ψ.

So Sil's residual and Collet's source differ in the tuple projector, not in how the residual is built:
- Sil uses `tupleWeight` (restriction ∧ injective);
- Collet uses `markedSourceModifier`.

**For Collet, assume (S), (Col) and F = 1.** Then the residual coefficient is exactly
`CoupledFirst.coefficient s' (markedSourceModifier A₁ A₂ Dc K 1) R L I · (√(T/∏_J P))⁻¹ · rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I`,
where s' is s restricted to `{i // i ∉ J}` (inf.). The coefficient form, `Input` and `profileCoefficient` (B/SourceProfileMass.lean:27) are all unchanged.

With suppliers, the residual instead carries R·f, L/f, K·f, ν·[P ∤ L] and ψ. All of these are still in Collet's vocabulary.

**What the downstream needs.**
- `Input.restrict`, about 40 lines, modelled on `commonData` (B/CommonRadialData.lean:60).
- A transport `child (s.restrict J) C R B' ψ t ≃ (child s C R B τ t).restrict J`. It is needed because `correctedChildGaussEnergy` (C/High/GlobalPhysicalAllocationMain.lean:50) is phrased through the parent and the allocation. About 100–200 lines (inf.).
- The change τ ↦ `childCharacter τ ξ` is harmless if the conductor bounds are uniform in τ. Every first-MAIN lemma takes τ as a parameter (inf.).

## 4. Minimal lemma

```lean
theorem collet_main_selected_transfer (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
  ∃ C > 0, ∀ {ι} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ N →
  ∀ (s : Input ι) (J : Finset ι) (A₁ A₂ Dc K R L : Ideal O) (τ : Character)
    (t T : ℝ) (n : ℤ) (Z M W : ℝ), 1 < Z → 0 < T → dyadicScale n ≤ Z^M →
    ∏ j ∈ J, s.hi j * s.P j ≤ W →
    (∀ j ∈ J, ∀ p ∈ s.slots j, ¬ p ∣ L) →                                    -- (S)
    (∀ v ∈ Fintype.piFinset s.pools,
      CoupledFirst.tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L v ≠ 0 →
      IsCoprime (∏ j ∈ J, v (.inl j)) (v (.inr 0) * v (.inr 1))) →          -- (Col)
    let S₀ := finiteColumns (Fintype.piFinset s.pools)
    let c := fun I : supportedColumns S₀ =>
      CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L I *
        ((Real.sqrt T : ℂ)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)
    let s' := s.restrict J                                   -- new: Input {i // i ∉ J}
    let S₁ := finiteColumns (Fintype.piFinset s'.pools)
    let c' := fun (ξ : RayCharacter) (I : supportedColumns S₁) =>
      CoupledFirst.coefficient s' (markedSourceModifier A₁ A₂ Dc K (fun _ => 1)) R L I *
        ((Real.sqrt (T / ∏ j ∈ J, s.P j) : ℂ)⁻¹ *
          rowWeight (childCharacter τ ξ) fixedBadMask 1 1 t I)
    ∃ rows : Finset O, (∀ r ∈ rows, r ≠ 0 ∧ normValue r ≤ 16 * Z^M * W^4) ∧
      (∑' h, dyadicWeight n (normValue h) *
          ‖gaussPolynomial .univ (sourceGenerator S₀) (sourceGenerator_supported S₀) c h‖^2)
        ≤ C * (∏ j ∈ J, s.hi j * s.M j ^ 2) * (Z^M * W^4)^ε *
          ∑ ξ, ∑ r ∈ rows,
            ‖gaussPolynomial .univ (sourceGenerator S₁) (sourceGenerator_supported S₁) (c' ξ) r‖^2
```

**Chaining into Collet's pool.** The output is a sum over a finite set of rows. Collet's `corrected_gauss_energy_ball` (C/Coefficient/CorrectedDensity.lean:53) consumes exactly that form, at M′ = M + log_Z(16W⁴). Its premises `hsq` and `hsmall` hold for c′_ξ by `source_column_no_prime_square` (C/Coefficient/AmplifierSupport.lean:20). The result is 𝓜 ≤ C·Z^ε·Σ_ξ (corrected residual energy at M′ + 6L).

**Proof steps and the lemmas each uses.**
1. Reduce to finitely many rows: `dyadic_energy_le_sum` and `dyadRows_ne_zero` (B/FirstAmplificationChoice.lean:207, :181).
2. Columns to tuples: `source_gauss_sum`, `finite_column_sum`, `split_tuple_sum`, plus a new box split J ⊔ Jᶜ.
3. Factorize the coefficient: `squarefreeIndicator_mul`, `surviving_seed_iff`, `map_mul` for `rowWeight`, and `heightCoeff_eq_fixed_rowWeight`. (Col) inserts the coprimality mask. New, about 250 lines.
4. The identity (T): `ideal_seeded_selected_row_fourth`, or `fixed_supplier_row_fourth` at f = 1. Then `child_ideal_primary`. Fifth-freeness as in §2.
5. Cauchy–Schwarz:
   - `first_ray_sq` and `norm_sum_sq_le_card`;
   - the selected scalar is at most |selectedWeight| by `prime_product_gauss_norm` and `rowWeight_norm_le_one` (B/FirstTailAggregate.lean:15);
   - templates: `fourth_family_sq`, `ray_budget_grouped`.
6. Group by D and bound the fibres (template `selected_fiber_subpower`). Normalize the count by ∏_J P (template `normalized_selected_card`).
7. Push forward: `weighted_pushforward` and `frequency_norm_bound` (template `actual_grouped_average`).
8. Choose J with `upward_subset`, over the slots allowed by (S).

## 5. Size (inf.)

| piece | lines |
|---|---|
| `Input.restrict`, box split, factorization, residual identity | 350–500 |
| identity steps 3–4 | 150–250 |
| positive chain, steps 5–7 | 300–450 |
| pool chaining and child/restrict transport | 150–300 |
| block selection under (S) | 50–100 |
| **subtotal: the lemma under (S) and (Col)** | **≈1.0–1.6k** |
| Sil-style suppliers in place of (S) | +0.6–1.0k (adds f-collisions) |
| **discharging (Col)** | **open** |

There are two routes to (Col):
- **Exact reduction mod p².** Since g(p²m, h) = 0 unless p | h (baseline `primePowerGauss_nonprincipal_extra_divisibility`), reduce and then transfer again at radius M − w_j. This is new mathematics, about 0.5–1.5k lines.
- **Sil's precedent.** Restrict marked ⊥ ordinary at the source and restore afterwards: F/Kernel*, Restoration*, Restored*, about 7.9k lines.

For comparison, Sil's (T)-relevant files total about 4.5k lines: MixedSupplier* 3.7k plus the transfer core 0.8k.
