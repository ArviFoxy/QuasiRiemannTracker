# E_mixed3: last third of the Mixed* group (Sil, fourth-power submission)

Scope. The 47 files in `lists/E_mixed3.txt` (MixedLiveNormalization through MixedUniformSource), under `Candidate/FourthPower/` of `sil-fourth-power-20261025`. Read: module docstring, imports and every declaration header of all 47 files. Full proofs read for six central declarations: `selected_fourth`, `fixed_supplier_row_fourth`, `actual_grouped_average`, `actual_selected_volume_average`, `uniform_small_width_native`, `uniform_source`. Read outside the group, for section 4 only: `GlobalSlotSelection`, `MixedLedger`, `IncumbentInput`, `Parameters`, `OuterFreshSelection` (excerpt), `RepairedRestrictedSource` (heads), `FinalFromRawSides`, `RepairedActualSideProvider` (wrapper), `RepairedContributionContract` (def), `RepairedSourceSideSupply` (def), and `Record1252270103Source/Core/Contract.lean` in `submissions/hailey-collet-1252270103`. Nothing was built or run. The 47 files contain no `sorry`, `admit` or `axiom`. Anything not read directly is marked (inferred).

## 1. Files

Notation: `N(I)` is `Ideal.absNorm`. `d` is the prefix pair. `G` is the genuine common ideal. `D` is the artificial divisor. `Σw` is total slot width. `κ` is the exponent per unit slot width.

- **MixedLiveNormalization.lean**. Scale transfer between frozen and live normalizations (imports MixedLiveRows).
  - `normalization T P = (√T)⁻¹·∏(√P i)⁻¹`; `normalization_sq`: `‖normalization‖² = 1/(T·∏P)`.
  - `frozen_live_identity`: frozen-normalized energy = `(‖c‖²/∏frozenScale)` × live-normalized energy.
  - `frozen_source_energy`: frozen coefficient energy ≤ `((∏M)²·max(1,b)^card ι / N(G))·E/pairNorm d`, reusing the baseline frozen estimate.

- **MixedLiveRows.lean**. Identifies the inherited live profile with the centered natural row.
  - `radical_character_mask`: `1_{IsCoprime I R}·χ(I)` equals χ with the primes of R excluded (a nonzero puncture acts through its radical).
  - `punctured_pool_profile`, `source_live_profile`: exact equalities between the punctured live profile and the centered coefficient on finite pools; no child energy assumed.
  - `source_live_box`, `residual_pool_twice`: prefix multiplication `d·B` on the live box, with pools unchanged.

- **MixedLocalizedDictionary.lean**. Exact localization of the second-Poisson density at scale `K4 = 16·K·W⁴`, with outer factor `1/W`.
  - `fourth_prefactor`: `16KW³ = 16KW⁴/W`.
  - `source_retained`, `source_discarded`: localized retained and discarded densities equal `secondRetained/DiscardedEnergy` at K4, divided by W.
  - `source_retained_split`: retained density splits into exceptional and nonexceptional `partEnergy` terms under a cap H on `N(I)`.
  - `source_discarded_bound`: uniform rapid-decay bound on the discarded density, with `(Σ‖β‖)²·16KW⁴·(e^H X)²` in the numerator and `/W`.

- **MixedNativeFloor.lean**. Non-fixed-inducing physical row at the total-width floor, via the native punctured chain. The only place in the group where the exponent 3/4 is an analytic output.
  - `height_energy_exact`: normalized sector energy = restricted residual energy / source volume.
  - `source_height_units`: frequency conversion `t/(2π)`.
  - `uniform_small_width_native`: if `Σw ≤ rho`, the row energy is ≤ `C·…·Z^{(3/4)·rho+ε}/(N(G)·pairNorm d·N(D))·(1+‖v‖)^{2·deg}`. Hypotheses `51/100 ≤ β`; κ = 3/4 from `IncumbentInput.native_kappa_bound`.

- **MixedOriginalCoprimality.lean**. Exact masks of the original structured column (tuple restriction, old seed, punctures).
  - `original_nonzero_masks`: nonzero weighted column ⇒ `IsCoprime I R` and `seed ∣ I`.
  - `original_seed_eq_one`: the seed can be removed on a whole column divisible by it.
  - `extracted_puncture_redundant`, `residual_puncture_redundant`: inserting the puncture changes no coefficient.
  - `original_divisor_column`: adapter to the FixedPair height dictionary.

- **MixedOriginalNormCap.lean**. Full-norm caps for the actual source support.
  - `sourceNormCap P b T d = b²·(T/pairNorm d)·∏(2P i)` (def).
  - `original_column_norm`: a nonzero original column has `N(I) ≤ sourceNormCap`.
  - `residual_norm_gates`: a nonzero residual coefficient forces `N(G), N(D), N(I)` below H and `N(G)·N(D) ≤ H`.
  - `sourceNormCap_power_bound`, `eventually_sourceNormCap_power`: the cap is ≤ `Z^{1+L+M}` once Z is large.

- **MixedOriginalSecondZero.lean**. Second-diagonal (zero-frequency) bounds for the original residual.
  - `original_column_bound`: `‖sourceCoefficient‖ ≤ C·profileCap·Y^ε`.
  - `original_residual_second_zero`: second-zero energy ≤ `C·profileCap²·Y^{1+ε}/(N(G)·N(D))`.
  - `original_residual_zero_density`: zero density on the first physical residual pool, with prefactor `16KW³`.

- **MixedOriginalSource.lean**. Uniform estimate for the actual original restricted column source.
  - `originalMaskedRow`, `original_masked_row_eq`: equals `commonMaskedRow` once the seed (dividing G) is removed.
  - `uniform_original_source`: radial energy ≤ `(C·G^δ·D^δ/G/pairNorm d/D)·…·Z^{s.width+κ·Σw+ε}`, with `2β−1 ≤ κ`.

- **MixedOriginalTail.lean**. L1 mass and support of the discarded Fourier density of the original column.
  - `profileCap = 2·supControl W₁·supControl W₂·∏M`, `poolCap`, `massCap = profileCap·poolCap` (defs).
  - `original_coefficient_mass`: `Σ|coeff| ≤ massCap`.
  - `original_coefficient_cap`: nonzero coefficient ⇒ `N(I) ≤ sourceNormCap`.
  - `original_discarded_bound`: discarded density ≤ `massCap²·16KW⁴·(e^H X)²·C·control/(…)/W`.

- **MixedOriginalTailCaps.lean**. Explicit scale caps with the prefix denominator kept.
  - `source_caps_with_prefix`: `poolCap ≤ 4(128b)²256^N·Z^{2L+Pexp}/pairNorm d`; `sourceNormCap ≤ b²2^N·Z^{2L+Pexp}/pairNorm d`.
  - `eventually_source_caps`: both are ≤ `Z^{2L+Pexp+ε}` for large Z.

- **MixedOriginalTailPower.lean**. Arbitrary polynomial saving for the discarded original tail.
  - `choose_fourth_tail_order`: a fixed Adec with tail prefactor ≤ `64·Z^{−saving}`. Docstring: exponent `12B = 2B+5B+2B+2B+B`.
  - `original_tail_arbitrary_saving`: discarded density ≤ `C·profileCap²·control·Z^{−saving}`.

- **MixedPhysicalEnvelopes.lean**. Coefficient-agnostic adapter from canonical envelopes to the physical second block. Its envelope premises are explicit.
  - `actual_canonical_source_envelopes`: dyadic-scale envelope for the physical source, eventually in Z.
  - `paired_normalized_windows`: common raw volume cancels; output is `A/√(cd)·√(E₁E₂)·heightEnvelope^{J₁+J₂}·profileMoment J₁·profileMoment J₂`.

- **MixedPhysicalTransfer.lean**. The fourth-power transfer on the first-Poisson residual columns.
  - `physical_coefficient_fifth_free`: fifth-freeness (`PowerFree 5`) is inherited wherever the coefficient is nonzero.
  - `sparse_fourth_power`: `gaussPolynomial(D⁴·k) = Σᵢ bᵢ·(idealRowHom D (span aᵢ))²·gaussRow(aᵢ)(k)`. This is the core `^4` identity.
  - `sparse_weighted_average`: `Σ_D w_D·Σ_k ρ‖…‖²/W ≤ (L·C·(16KW⁴)^ε/W)·Σ_r‖gaussPolynomial(r)‖²`.
  - `actual_first_physical_average`: the same bound on the literal first physical column pool.

- **MixedPoissonCompletion.lean**. Completes the positive fourth-power image by a smooth ball, then applies second Poisson.
  - `image_energy_le_smooth`: frequency energy ≤ `gaussEnergy(ballProfile, 16KW⁴)`.
  - `density_normalized_poisson`: `gaussEnergy(16KW⁴)/W = secondPoissonDensity K W`.
  - `weighted_second_poisson`: weighted D-average ≤ `L·C·(16KW⁴)^ε·(secondPoissonDensity).re`.

- **MixedPoissonLocalization.lean**. Localization of the completed family.
  - `density_split`: `secondPoissonDensity = zeroDensity + localized(retainedWeight R) + localized(discardedWeight R)`.
  - `zero_density_norm_le`: `‖zeroDensity‖ ≤ 16KW³·‖paperRadialFourier ballProfile 0‖·Σ‖bᵢ‖²`.
  - `density_re_le`: the real part is bounded by the zero term plus the two localized norms.

- **MixedPrincipalAllocations.lean**. Genuine allocation pairs for the original principal source.
  - `allocation_admissible`: allocated sources stay admissible in `(N, Bcap, Z)`.
  - `original_row_allocated`: `originalRow = Σ over allocations of shifted allocated rows` (exact).
  - `pairBudget`: sum over allocation pairs of `budget·budget·min(saving)`.
  - `uniform_original_height_pair`: pair bound with `α < 4/5` and `α+2δ < 1`.

- **MixedPrincipalBudget.lean**. Finite allocation budget with the positive-part principal saving.
  - `fullMarkedCost_eq`: `fullMarkedCost = 1024^{card ι}·(∏M)³`.
  - `allocated_budget_le`: allocated budget ≤ `baseBudget/N(G)`; `allocated_saving_le`: saving ≤ `commonSaving`.
  - `uniform_pair_budget`: `pairBudget ≤ C·G₁^δ·G₂^δ·baseBudget²/(G₁G₂)·min(commonSaving)`.
  - `common_pair_saving_power`: saving ≤ `Z^{−α·max(l−v,0)}`.

- **MixedPrincipalCentered.lean**. Exact principal normalization at multiplied prefixes.
  - `prefixNormMax e = max(N(e₁), N(e₂))` (def).
  - `centered_physical_identity`: centered row = `(√pairNorm e)⁻¹·(row at X/N(eᵢ) − row at Y/N(eᵢ))`, with no estimate.
  - `shortened_lower_left`, `shortened_lower_right`: `L/prefixNormMax e ≤ X/N(eᵢ)`.
  - `uniform_centered`: uniform bound for the fixed-inducing centered row, `α < 4/5`.

- **MixedPrincipalFrozen.lean**. Frozen source amplitude for the fixed-inducing branch.
  - `frozen_linear_cost`: `‖frozenCoefficient‖/rawReduction ≤ (∏M·max(1,b)^card)/N(G)`.
  - `uniform_frozen_principal`: uniform frozen principal row bound, `α < 4/5`.

- **MixedPrincipalHeights.lean**. Profile conversion and independent-height control.
  - `shiftSource`, `shifted_row`: a height shift `v` moves frozen and live coefficients together.
  - `original_height_row`: exact identity `residualPhase·originalMaskedRow`.
  - `shifted_budget`: `budget(shifted) ≤ 2^J·budget·(1+|v|)^J`.
  - `uniform_shifted_pair_rows`: pair rows at two independent heights, `α < 4/5`, `α+2δ < 1`.

- **MixedPrincipalMasked.lean** (440 lines). Artificial divisor mask and its paired summation.
  - `masked_row_allocated`, `masked_row_frozen`: allocation sum; exact indicator per frozen tuple.
  - `bounded_labels_uniform`: `#labels ≤ K·N(D)^δ`.
  - `shortened_saving`: `(max(1,x/q))^{−α}/n ≤ (max(1,x/p))^{−α}·n^{−(1−α)}`.
  - `uniform_masked_principal`: row bound uniform in the live type, with constants fixed before it (the `N(D)^{δ−(1−α)}` form is inferred from `uniform_frozen_masked`).
  - `paired_mask_norm_mass`: `Σ‖μ‖·N(D)^{δ−(1−α)}·N(D)^{δ−1} ≤ C` when `α+2δ < 1`. Docstring: α = 7/10 needs δ < 3/20.

- **MixedPrincipalPair.lean**. The principal `Source` record and its paired rows.
  - `structure Source`: original data only (S, H, pool, d, B, G, R, Fhole, ν, Wslot, P, M, W₁, W₂, t₁, t₂, X, Y, U, T, L). It has no analytic fields.
  - `Admissible N Bcap Z`: numerical caps only.
  - `saving α = (max 1 (L/prefixNormMax prefixPair))^{−α}` (def).
  - `uniform_frozen_masked`: row ≤ `C·budget·N(D)^{δ−(1−α)}·saving α`, plus a second bound.
  - `uniform_frozen_masked_pair_rows`: paired rows, with the right-hand row evaluated at `−z`.

- **MixedPrincipalPoolCaps.lean**. Full finite-pool norm bounds for principal admissibility.
  - `residual_plain_norm`: `N(I) ≤ 128b(X+Y)/N(d)`.
  - `eventually_full_pool_norm`: `poolNorm ≤ Z^{2(2L+Pexp+ε)}`.
  - `eventually_conductor_budget`: `conductorBudget ≤ Z^{Bη+BR+BC+BE+4L+2Pexp+M+3ε}`.

- **MixedPrincipalPositivePart.lean**. Positive-part saving for principal rows.
  - `max_power_saving`: `(max(1,Z^{l−v}))^{−α} = Z^{−α·max(l−v,0)}`.
  - `uniform_centered_positive`: positive-part form of `uniform_centered`, `α < 4/5`.

- **MixedPrincipalWindow.lean**. Fourier windows for original columns in the inner exceptional branch.
  - `height_row_neg`, `window_row_neg`: reflection at `−z` uses the reflected character.
  - `moving_window_eq`, `conjugate_window_eq`: the moving and conjugate windows equal the window row for the twisted character.
  - `uniform_original_window_pair`: whole-source window-pair bound, `α < 4/5`, `α+2δ < 1`.

- **MixedRawEnvelope.lean**. Raw physical-source envelope.
  - `divisorSlack B ε = ε/(4(B+1))`; `capped_divisor_subpowers`: `N(G)^s·N(D)^s ≤ Z^{ε/2}`.
  - `uniform_raw_source_envelope`: restricted energy ≤ `rawBudget(…)/N(D)·(1+‖v‖)^{2·deg}`, with `2β−1 ≤ κ` and `51/100 ≤ β`.

- **MixedRestrictedDictionary.lean**. Exact dictionary from restricted common columns to masked live tuples.
  - `height_source_natural_character`: row polynomial = `Σ β·natural character·N(I)^{it}`.
  - `restricted_energy_natural_character`: an equality of energies; the height phase is kept.
  - `finite_column_sum`, `restricted_live_column_sum`, `common_masked_column_sum`: finite regroupings with no norms.
  - `normalized_common_masked_identity`: the normalized original source equals a sum of frozen-weighted masked common rows. Mentions `fixedBadMask^6` (the sixth-power physical mask).

- **MixedSecondProfile.lean**. Zero-frequency diagonal for bounded, unnormalized profile coefficients.
  - `bounded_second_zero`: energy ≤ `C·B²·N^{1+ε}/N(seed)`.
  - `normalized_profile_second_zero`: energy vanishes when `L·V < 1`; otherwise ≤ `C‖κ‖B²L^{1+ε}V^ε/N(seed)`.

- **MixedSecondZero.lean**. Literal second-Poisson zero frequency on grouped ideals.
  - `energy_zero_subunit`: energy vanishes when all `N(I) < 1`.
  - `grouped_second_zero`: energy ≤ `C·N^ε·B²/N(seed)`.
  - `normalized_grouped_second_zero`: `(κ/V)·energy ≤ C‖κ‖N^εB²/(V·N(seed))`.

- **MixedSelectedCommon.lean**. Finite selected-block Gauss separation.
  - `surviving_seed_iff`: `f·seed ∣ f·D·n ↔ seed ∣ n`.
  - `normalized_coprime_product`: `gaussRow(d·a) = sexticReciprocityPhase·(idealRowHom d (span a))²·gaussRow d·gaussRow a`.
  - `moving_square_zero`: non-coprime pair ⇒ `(idealRowHom d)^2 = 0`. The proof goes through `h6 : (idealRowHom d)^6 = 0` and then `eq_zero_of_pow_eq_zero`.
  - `selected_row_fourth`: `selectedRow = Σ_{χ,ξ} pairCoeff·(A·χ(d)·gauss d)·gaussPolynomial(commonCoefficient)(d⁴·k)`.
  - `selected_family_fourth`: a family of selected products shares one residual vector for each ξ.

- **MixedSelectedVolume.lean**. Average over the selected-prime volume.
  - `volume q = ∏_{j∈J} P_j`, `padding q = 2^{#J}`, `scale q = padding·volume` (defs).
  - `selected_products_norm`: `N(F) ≤ scale q` for selected products.
  - `average_exact`: `A/volume = padding·(A/scale)`.
  - `actual_selected_volume_average` (proof read): the averaged selected energy ≤ `padding·L·C0·(16K·scale⁴)^ε·outputEnergy`.
  - `fourth_scale_exact`: `16K·scale⁴ = padding⁴·16K·volume⁴`; `eventually_padding_cost`: `padding·padding^{4ε} ≤ Z^{loss}`.

- **MixedSourceAssembly.lean**. Assembly tools: radical caps, Cauchy sums, counts.
  - `radical_union_cap`: `N(rad(R·F) ∪ H) ≤ Z^{BR+BF+BH}`.
  - `radial_family`: `radialEnergy(Σf_i) ≤ (Σmass_i)²·E`; `radial_phase_sum`: `≤ (#ι)²·E` for phases of norm ≤ 1.
  - `genuine_count_squared`, `fixed_count_squared`: `#allocations² ≤ C·N(D)^ε`.

- **MixedStateEnvelope.lean**. All-height envelope for the restricted physical source in a `NaturalState`.
  - `uniform_source_height_envelope`: the energy divided by the source volume `X₁X₂∏Z^{w}` is ≤ `C·(G^δ·D^δ/G/pairNorm d/D)·diagonal·control²·sourceHeight^{deg}·(1+‖v‖)^{2deg}·Z^{s.width+κΣw+ε}`, with `2β−1 ≤ κ`.

- **MixedSupplierCanonical.lean**. Canonical zero-extension of the supplier residual coefficient.
  - `finite_column_zeroextend`: zero-extension to the full marked alphabet, with no norm taken.
  - `common_column_original`: `commonColumn = originalColumn` on canonical `sourcePools`, with supplier holes kept.
  - `common_polynomial_original`: `∃ψ`, conductor ≤ `τ·C·N(frozen)·N(12)`, equal to a Gauss polynomial with the common column.
  - `original_avoiding_energy`: energy ≤ `#allocations·Σ commonRow energies`.

- **MixedSupplierFourthRow.lean** (453 lines). Supplier data record and the fourth-power selected expansion. The central file of the fourth-power transfer.
  - `structure Data`: pool, A, B, H, R, u, ν, Wslot, P, W's, X's, Y's, d, `L` (live indices), `J ⊆ L` (selected). No analytic fields.
  - `frozen_divides`: `frozenProduct ∣ u`. `selected_seed_coprime`: `IsCoprime seed (selectedProduct)`.
  - `selected_fourth` (proof read): `selectedRow = Σ_{χ,ξ} pairCoeff·selectedScalar·gaussPolynomial(commonVector)((primaryGenerator selectedProduct)⁴·k)`.
  - `actual_family_fourth`: for injective frozen x there is one seed and one residual vector common to all selected y.
  - `partition_branch_fourth`: summed over frozen x, `originalFamily` is replaced by `fourthFamily`, with seeds depending on x.

- **MixedSupplierKernel.lean**. Masks and Gauss separation for fixed suppliers.
  - `crossGate f D M := IsCoprime f D ∧ IsCoprime f M ∧ IsCoprime D M`; `selectedGate R f D := IsCoprime f D ∧ IsCoprime D R`; `commonGate H R f seed M A B := IsCoprime f M ∧ restriction H (f·M) A B ∧ IsCoprime (f·(A·B·M)) R ∧ seed ∣ A·B·M`.
  - `original_kernel_split`: `originalKernel = [selectedGate]·commonKernel·[IsCoprime D (A·B·M)]`.
  - `fixed_supplier_row_fourth` (proof read): `Σ_v A·B_v·heightCoeff·(f·D·n_v)-Gauss = Σ_{χ,ξ} pairCoeff·(…)·gaussPolynomial(fixedCommonCoefficient)((primaryGenerator D)⁴·k)`.
  - `literal_row_eq`: the literal residual row equals the row consumed by `fixed_supplier_row_fourth`.

- **MixedSupplierOriginalFrequency.lean**. Supplier dictionary at the ORIGINAL physical frequency. No K4 and no D⁴ step.
  - `fixed_supplier_row_original`: the same CRT identity, with `gaussPolynomial` at `n_v` (no fourth power).
  - `outer_column_active_tuple`: a nonzero grouped outer column yields an active original tuple.
  - `original_energy_common_sectors`: outer energy decomposes into common-sector pairs at the original K.
  - `original_normalization`: `‖normalized‖² = ‖·‖²/(X₁X₂·∏P_j)`.

- **MixedSupplierOuterActive.lean**. Gates for the outer original-frequency branch.
  - `structure SelectedActive`: necessary scalar gates for a selected assignment.
  - `scalar_zero_off_active`: `selectedScalar = 0` off the gate, at every frequency and height.
  - `selected_positive_nonneg`, `scalar_sq_le_positive`: a k-independent majorant `selectedPositiveWeight` that keeps the natural zeros.
  - `original_common_divisor_active`, `actual_outer_common_divisor`: common divisors are coprime to `f·D` and to the fixed character. This is the input to "old+fresh" forcing.

- **MixedSupplierOuterFamily.lean**. Positive reduction of the whole original supplier family, before K4.
  - `selected_row_sq`: `‖selectedRow‖² ≤ 256·Σ‖pairCoeff‖·selectedPositiveWeight·‖originalPolynomial‖²`.
  - `original_family_sq`: same, with a factor `#activeSelected`.
  - `uniform_weighted_original_sum`: one residual seed for every character, height and weight ρ.

- **MixedSupplierPartition.lean**. Full marked-supplier partition of the original column.
  - `supplierCharacters u L ν := KernelHoleCompletion.mixed ν (P ∣ u) L` (def).
  - `supplier_character_nonzero`: nonzero iff `(i ∈ L ↔ ¬P ∣ u)`.
  - `profile_full_partition`, `originalColumn_full_partition`: exact sums over all L, with no estimate.
  - `selected_product_coprime`: `IsCoprime u (∏_{i∈J} v_i)` on a nonzero branch.

- **MixedSupplierPositive.lean** (648 lines). Positive reduction of the frozen supplier family and the D-average.
  - `prime_product_gauss_norm`: `‖primaryGaussRow(∏_S P_i)‖ ≤ 1` for distinct primes.
  - `active_selected_annular_card`: `#active ≤ 256^{#J}·∏P_j`; `normalized_selected_card`: `#active/∏P ≤ 256^{#J}`.
  - `first_ray_sq`: `‖Σ_{χ,ξ} pair·F‖² ≤ 256·Σ‖pair‖·‖F‖²`.
  - `selected_fiber_subpower`: `#{selected with product D} ≤ C·N(D)^δ`.
  - `actual_grouped_average` (proof read): `Σ_D groupedWeight(D)·Σ_k‖commonPolynomial(D⁴k)‖²/W ≤ ((∏M)²·C·(2W)^δ·(16KW⁴)^ε/W)·Σ_r‖commonPolynomial(r)‖²`.
  - `weighted_original_sum`: final positive reduction, with `256·#active`, `groupedWeight`, and `D⁴k`.

- **MixedSupplierReconstruction.lean**. Regroups the supplier partition into the exact reconstructed kernel.
  - `tuple_supplier_expansion`, `original_column_supplier_expansion`: exact equalities with `supplierExpansion`.
  - `original_gauss_supplier_expansion`: Gauss specialization at frequency `t + 2π(w−θ)`.
  - `profile_seed_mask`: `(if seed ∣ ∏v then tupleWeight·profile with seed := 1 else 0)` equals `tupleWeight·profile with seed`; the mask is not dropped.
  - `first_gauss_common_tuples`: the first-child Gauss polynomial regrouped over genuine common allocations.
  - `selected_holes`: collapses all cross-holes into `crossGate`.
  - `actual_suppliers_seed`: `u = (∏ frozen)·seed` with `seed` coprime to the selected product.

- **MixedSupplierSource.lean**. Common-vector and source interfaces with the fixed-supplier cubic character.
  - `common_gate_original`, `common_kernel_original`: the common gate and kernel in original form.
  - `common_height_character`: `∃ψ`, conductor ≤ `τ·C·N(f)·N(12)`, with `heightCoeff ψ = heightCoeff τ·(idealRowHom f I)²·ray ξ`. The fixed-f twist has linear conductor in N(f).
  - `common_polynomial_source`: `commonPolynomial` = Gauss polynomial over `commonColumns` with `heightCoeff ψ`.
  - `frozen_avoid_norm`: `‖frozenAvoid‖ ≤ 1`. `supplier_dvd_puncture`: `u ∣ (R·f)·G`.

- **MixedSupplierSplit.lean**. Fixes all supplier values, then splits the selected slots.
  - `packed_coefficient`: packed coefficient = `ordinaryKernel·∏ν·Wslot(N(p)/P)`.
  - `originalColumn_weighted`: `originalColumn = weightedSum(slotAmplitude)(columnKernel)`.
  - `split_two_levels`: `weightedSum = Σ_t(frozen amplitudes)·Σ_s(selected amplitudes)·remainingSum`.
  - `packed_two_level_product`: the tuple product is `(∏t)(∏s)(n₁n₂∏r)`.
  - `originalColumn_supplier_selected_split`: the concrete branch split, with no separability premise.

- **MixedTupleRows.lean**. Identifies the restricted Sum-indexed coefficient with the marked row.
  - `pack_product`: `finiteTupleProduct(pack p n) = n₁n₂·∏p`.
  - `normalized_character_sum`: equality before norms, between the punctured tuple sum and a weighted natural-character sum.
  - `centered_extraction`: `centeredCoefficient = (√pairNorm d)⁻¹·(rect(X/N(d₁),…) − rect(Y/…))`.
  - `punctured_profile_character_sum`: the excluded-prime character equals the centered coefficient.

- **MixedUniformAllocated.lean**. Uniform constants over every live marked subset.
  - `uniform_allocated_subsets`: allocated radial energy ≤ `(C·N(F)^δ/pairNorm d/N(∏selectedDivisor))·…·Z^{s.width+κ·Σ_{i∈selectedLive} w_i+ε}`, with `2β−1 ≤ κ`. Note: the κ-weight runs only over selected-live slots.

- **MixedUniformSource.lean**. Uniformizes the canonical source over every remaining marked subset, before any allocation.
  - `uniform_source` (proof read): radial energy ≤ `(C/pairNorm d)·diagonalControl·control²·(1+|t|+V)^{deg}·Z^{s.width+κ·Σw+ε}`. `degree` and `control` are chosen once over all `T : Finset α`, using `hβ : 51/100 ≤ β` and `hκ : 2β−1 ≤ κ`.

## 2. Group overview

The group implements the step where the mixed moment is turned into uniform, data-independent source bounds. Three strands run in parallel.

(1) Principal and original strand (MixedPrincipal*, MixedOriginal*). Fixed-inducing rows and the original restricted column get explicit caps (`sourceNormCap`, `poolCap`, `profileCap`) and a positive-part saving `(max 1 (L/prefixNormMax))^{−α}`, with `α < 4/5` and `α+2δ < 1`. The artificial divisor D is summed with weight `N(D)^{δ−(1−α)}·N(D)^{δ−1}`.

(2) Supplier and fourth-power strand (MixedSupplier*, MixedSelected*, MixedPhysicalTransfer, MixedPoisson*, MixedLocalizedDictionary). Frozen suppliers are fixed, the selected slots J give a product D, and the Gauss polynomial at `D⁴·k` replaces the sixth power (`sparse_fourth_power`, `selected_fourth`). One residual vector is shared by all selected assignments for a given frozen x (`actual_family_fourth`). Losses are the fiber count `(2W)^δ`, the scale `(16KW⁴)^ε/W`, and the padding `2^{#J}`.

(3) Native and uniform strand (MixedNativeFloor, MixedRawEnvelope, MixedStateEnvelope, MixedOriginalSource, MixedUniformSource, MixedUniformAllocated). A non-fixed-inducing row at total width `Σw ≤ rho` costs `Z^{(3/4)rho+ε}`. The uniform envelopes cost `Z^{s.width+κΣw+ε}` with `2β−1 ≤ κ`. All constants are chosen before the data and before Z.

Inputs: OpenAI baseline modules (CommonRawCost, SecondLocalization, SecondEnergySplit, SecondDiagonal, Moments.*), `HeckeZeroSupremum.beta`, and earlier Mixed* files (MixedCanonicalSource, MixedCenteredEnergy, MixedCommonEnergy, MixedHeightEnergy, MixedCommonRestriction, MixedArtificialRestriction).

Outputs: `uniform_source`, `uniform_original_source`, `uniform_allocated_subsets`, `uniform_raw_source_envelope`, `uniform_source_height_envelope`, `uniform_small_width_native`, `actual_grouped_average`, `actual_selected_volume_average`, `original_discarded_bound`, `density_re_le`, `weighted_original_sum`. Consumers (from imports): MixedFrozenSource, MixedCommonAllocated, MixedCanonicalEnvelope, MixedHeightEnergy, RepairedSmallNativeRaw, OuterFreshSelection, OuterFreshConsumer, MixedSourceAssembly's users.

## 3. Constants and vocabulary

| Term | Where in the group | Meaning (read unless marked) |
|---|---|---|
| `^4` (fourth) | `sparse_fourth_power`, `fixed_supplier_row_fourth`, `selected_fourth`, `selected_row_fourth`, `actual_grouped_average`, `actual_family_fourth` | Frequency dilation `D⁴·k`. The factor `(idealRowHom D)²` multiplies each term. Its norm is at most 1 by `idealRowHom_norm`, which `MixedSupplierPositive` uses in its positive majorant (call site read). Exact unimodularity was not read. |
| `16·K·W⁴` (K4) | `fourth_prefactor`, `source_retained`, `density_normalized_poisson`, `sparse_weighted_average`, `actual_selected_volume_average` | Fourth-power physical scale. `fourth_prefactor` gives `16KW³ = 16KW⁴/W`, the zero-mode prefactor. |
| `scale⁴` vs `volume⁴` | `fourth_scale_exact` | `16K·scale⁴ = padding⁴·16K·volume⁴`. The padding is the only extra factor. |
| `^6` (sixth) | `moving_square_zero` (proof uses `^6`, `h6`), `normalized_common_masked_identity` (`fixedBadMask^6`) | The classical sixth-power route. In this group it appears only as a vanishing statement for non-coprime pairs and as a physical mask. It is not an amplifier here. |
| 93/25 | 0 hits in the group | Slope of the source face (`sourceSlope`, Parameters.lean). Outside the group it is the coefficient of Σw in the root inequality and of `s` in `globalFace`. See section 4. |
| 43/100 | 0 hits in the group (the group's `MixedLedger` is not assigned) | Lower selection fraction `φ` for the selected width `w(R)/S`. Appears in `GlobalSlotSelection.Specification` and `large_branch`, `OuterFreshSelection`. |
| 3/4 | `uniform_small_width_native` (the native exponent and the κ argument) | Native exponent per unit of total width, and the value κ = 3/4 supplied by `IncumbentInput.native_kappa_bound` (2β−1 ≤ 3/4 when β ≤ 7/8). |
| 3/7 | 0 hits | (inferred) threshold where `(3/4)(1−φ) = φ`. Since 43/100 − 3/7 = 1/700, the selection clears it with margin 1/700. |
| 1/400 | 0 hits | (read in `MixedLedger.slot_reserve`, outside the group) `(43/100)S − (3/4)(57/100)S = S/400`, the reserve left by the native gate. `GlobalSlotSelection.large_branch` has `rho/400` and `(Σw)/400`. |
| 2, 4, 6 (per unit width) | No explicit `2S+4d` or `6d` in the group. Numeric 2 appears in `2·P_i` (doubling of the dyadic endpoint) and `2^{#J}` (padding). 256 appears in `256^{#J}`. No literal 4 or 6 cost occurs | (inferred) The cost of unselected width is 2 and of selected width 6, giving `2 + 4φ`. The 6 = 2 + 4 split is not read in these files. Outside the group, `MixedFirstChosenEnergy.reference_exponent_choice` and `MixedLedger.second_diagonal_gate` use `P + 2S + 4d < R`, which is a different accounting. |
| native | `MixedNativeFloor` (title and docstring: "checked native punctured chain", "unconditional 3/4") | The non-fixed-inducing side, at the total-width floor. The chain itself lives in the `Native*.lean` files (imported by many group files), which I did not read (inferred). |
| selected | `Selected q := q.J → Alphabet q`; `selectedProduct`, `selectedScalar`, `selectedRow`, `selectedGate`, `selectedProducts`, `SelectedActive`, `volume`, `padding`, `scale` | The slots J ⊆ live indices carrying the fourth power. Their product is D. |
| unselected | 0 literal hits | (inferred) The complement `J \ R` in `GlobalSlotSelection`, which is `Rest q` in `MixedSupplierFourthRow` (`restWeight`, `restProduct`). It pays the native 3/4. |
| supplier | `Data.L` (live indices), `Frozen q := Lᶜ → Alphabet q`, `frozenProduct`, `frozenWeight`, `supplierCharacters`, `supplierExpansion`, `avoid`, `frozenAvoid` | Marked primes dividing `u`. Each branch fixes their values, and their holes are kept in the coefficient, never removed inside a norm. |
| twisted | 0 literal hits; "twist" means a cubic character multiplier | Fixed-f twist (`fixedCommonCoefficient`); moving D character (`originalMovingCoefficient`). `common_height_character` builds a cubic twist with conductor linear in N(f). |
| outer | `MixedSupplierOriginalFrequency`, `MixedSupplierOuterActive`, `MixedSupplierOuterFamily`, `MixedLocalizedDictionary` (outer 1/W); NativeFloor docstring ("d=0 outer ledger") | The original-frequency branch, with no K4 and no D⁴ step. Contrast "inner exceptional branch" in `MixedPrincipalWindow`. |
| fresh | `MixedSupplierOuterActive` ("old+fresh forcing"), `MixedSupplierOuterFamily` ("fresh-D forcing") | The new artificial divisor D, against the old common divisors. |
| κ, β, θ | `uniform_*` hypotheses `51/100 ≤ β`, `2β−1 ≤ κ` | `IncumbentInput.baseline_beta`: β ≤ 7/8. `Parameters.theta = 1749387/2000000` (≈ 0.8747) is the target; `Parameters.kappa = 2θ−1` (≈ 0.7494, below 3/4). |
| 256 | `first_ray_sq`, `selected_row_sq`, `active_selected_annular_card` | Cauchy–Schwarz constant over ray pairs (χ, ξ) (inferred that |RayCharacter| = 16). |
| 72, 12 | `Q ≤ span {72}` in every uniform theorem; `span {12}` in `common_height_character` | Level of the characters, and the cubic conductor normalization. |

## 4. Final assembly: best reading

Notation: S = total live slot width, R (= J in the group) = the selected set, d = w(R), s = S − d = unselected width. Read items cite declarations. (inferred) marks inferences.

1. Source bounds. Each uniform theorem in the group has the form `energy ≤ C·(prefactor)·Z^{s.width+κΣw+ε}` with `2β−1 ≤ κ` (`uniform_source`, `uniform_original_source`, `uniform_allocated_subsets`, `uniform_source_height_envelope`, `uniform_raw_source_envelope`). The native variant has `Z^{(3/4)rho+ε}` on the floor (`uniform_small_width_native`).

2. Fourth-power transfer. For each frozen x, the selected rows are Gauss polynomials at `D⁴·k` with one common residual vector (`selected_fourth`, `actual_family_fourth`, `partition_branch_fourth`). The D-average is `actual_grouped_average`, with fiber loss `(2W)^δ` and scale loss `(16KW⁴)^ε/W`. The padded volume (`actual_selected_volume_average`, `fourth_scale_exact`) costs `2^{#J}`, absorbed by `eventually_padding_cost`.

3. Floor and large branches (read in GlobalSlotSelection, MixedLedger). If S ≤ rho, `exists_selection` gives R = ∅ and `small_branch` gives native cost `(3/4)·S ≤ 3rho/4`. If rho < S, `large_branch` gives `43/100·S ≤ w(R) ≤ 43/100·S + mesh` and the native gate `(3/4)·w(J∖R) < w(R)`, with reserve `S/400` (`MixedLedger.slot_gate`, `slot_reserve`).

4. Slope (inferred arithmetic). Unselected width costs 2 and selected costs 6 per unit, so the mean cost per unit total width is `2 + 4φ`. The gate forces `φ > 3/7`, the selector gives `φ ≥ 43/100`, and `2 + 4·43/100 = 93/25`. At the threshold the slope would be 26/7, so 93/25 is 1/175 above it. The "extra 4 on selected" is inferred to come from the fourth-power scale.

5. Root and face (read in OuterFreshMixedCapacity, OuterFreshSelection, RestoredRootSource ~L408). The slope appears in `log_Z(T/pairNorm d) + (93/25)·Σw ≤ Q − Δ`. The face is `globalFace B lam cap` with `(B, lam, cap) = (99999/100000, 93/25, 3/50)` (`sourceB`, `sourceSlope`, `sourceCap` in Parameters.lean). Its `Admissible m₁ m₂ s M` is `s ≤ cap·M ∧ m₁+m₂+lam·s ≤ B·M` (hailey-collet `Record1252270103Source/Core/Contract.lean`). `SourceContract.admissible_exact` restates it.

6. Contrary branch (θ < β; read as wrappers). `RepairedRestrictedSource.restricted_unit_source_of_raw_sides`, with input `ContraryRawSideProvider`, yields the restricted unit source for `targetFace`. `actual_required_source` restores the full source. `FinalFromRawSides.full_source_of_raw_sides` converts it to `fullSourceFace`. `ReturnCommonProbe.common_probe_from_full_source` and then `TerminalTransfer.beta_of_common_probe` give β ≤ θ in `FinalFromRawSides.beta_of_raw_sides`. The sibling `ReturnCommonProbe.common_probe_of_contrary_source` feeds `common_probe_of_raw_sides` and is not on this path.

7. Raw-side input. `actual_contrary_raw_side_provider` is `contrary_provider_of_pending_small actual_small_contribution`. The `PendingSmallContribution` Prop is declared in `RepairedContributionContract`, and `actual_small_contribution` proves it. I read only the wrapper. The group's native bound enters via `RepairedSmallNativeRaw.uniform_native_raw`, whose call site I read.

Caveats. (a) The 2/6 unit costs and the attribution of 93/25 to the selected/unselected split are inferred. (b) The gate `P+2S+4d<R` outside the group does not reconcile with 2/6 without reading `MixedFirst*` and `Transport*`. (c) `uniform_masked_principal` was read at its header only; its `N(D)` exponent is inferred from `uniform_frozen_masked`.

## 5. Dependency notes

- `MixedUniformSource` is imported by `MixedFrozenSource`, which is imported by `MixedSourceAssembly`.
- `MixedRawEnvelope` is imported by `MixedCanonicalEnvelope`, which is imported by `MixedNativeFloor` and `MixedActualFamily`.
- `MixedSupplierPositive` is imported by `MixedSelectedVolume`, `MixedSupplierOuterActive` and `MixedSupplierSource`.
- `MixedPoissonCompletion` and `MixedSupplierOuterFamily` are imported by `OuterFreshConsumer`.
- `MixedPrincipalWindow` is imported by `MixedInnerExceptionalPair` and `MixedOriginalTail`.
