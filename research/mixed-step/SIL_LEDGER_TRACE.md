# Sil mixed step: exponent ledger, cited

Lean files are under `/home/user/lean-env/qrh/Submissions/arvi_repeated_marks_on_sil_face_20261025/FourthPower/` and are cited as `File:line`. "Baseline" means `…/openai_baseline/OAI/NumberTheory/DirichletL/Moments/`. Nothing was edited or built. "(derived)" marks my algebra on cited statements. "(inferred)" marks a claim not stated in the code.

## Summary

Units are log_Z. W = `MixedSelectedVolume.scale` = 2^#J·∏_{j∈J}P_j, with Z^d ≤ W ≤ Z^{d+ω}. d = log_Z ∏_{j∈J}P_j.

| per unit of | inner gate `P+2S+4d ≤ R−ρ` | outer `Rdecl` | total vs root width Q | energy |
|---|---|---|---|---|
| P | 1 | 0 | 1 | none |
| live S | 2 = 3/2 (exceptional) + 1/2 (short reference) | 0 | 2 | cost κ = 3/4 (native) |
| selected d | 4 = 7/2 (exceptional, W^{7/3}) + 1/2 (reference conductor R+d) | 2 (Cauchy count W × regrouping W) | **6** | saving 1, native component only |
| frozen | 0 | 1 | 1 | none |

- **Net W factor: none.** The bound #active·scale ≤ 512^N·(∏_J P)² is cancelled exactly by the selectedVolume² = (∏_J P)² in `firstReference`, which is the −2d of Rdecl. The resulting `rawSupplierCost` contains no W.
- **The saving d is used once:** in the native component, Z^{κS}/W ≤ Z^{κS−d} (the only consumer of `Gates.Wlower`). The zero component costs W³ (+3d) and the exceptional one W^{7/3} (+7d/3), both through `Wupper`.
- At d = (43/100)(S+d), 2S+6d equals (93/25)(S+d). The native margin is then d − (3/4)S = (S+d)/400.

## Q1. From the original energy to the grouped average

Unused code: `MixedSupplierPositive`'s fourth-power path (`fourth_family_sq`:340, `weighted_original_sum`:598, `normalized_selected_card`:251, `actual_grouped_average`:525), `MixedSupplierOriginalFrequency.original_normalization`:285 and `MixedSelectedVolume.actual_selected_volume_average`:67. No other file names them (grep). The chain the proof actually uses (large branch):

1. **Cauchy over selected assignments y.** This is at the original K, with D still in the coefficient (`outerColumn`, MixedSupplierOriginalFrequency:128). `MixedSupplierOuterFamily.original_family_sq`:53: `‖originalFamily‖² ≤ 256*#activeSelected*∑y∑χ∑ξ ‖pairCoeff‖*(selectedPositiveWeight*‖originalPolynomial‖²)`.
   - The factor 256 is the ray-table mass (`first_ray_sq`:323).
   - `#activeSelected ≤ 256^#J*∏_{j∈J}P_j` (`active_selected_annular_card`:235) counts assignments, not products. **One factor of W.**
2. **Energies, grouping by D, four components.** `OuterFreshConsumer.uniform_supplier_energies`:478 passes to energies. `selected_energy_grouping`:387 groups by D, with weight `outerGroupedWeight ≤ groupedWeight` (:369). `RepairedGroupedConsumer.uniform_supplier_grouped_four`:137 splits into four Poisson components before taking norms.
3. **Regrouping.** `scale*physicalAverage = ∑y selectedPositiveWeight*physicalBlock` (RepairedGroupedConsumer:164). `RepairedRawRetained.selected_sum_le_blocks`:106 then multiplies by `scale`. **Second factor of W.**
4. **The average at width Rdecl.** `OuterFreshNonexceptionalBlock.uniform_actual_nonexceptional_block`:67 applies under the gates `log(live.T/pn)+2Σ_live w+4d ≤ Rdecl−ρ` and `(3/4)Σ_live w<d` (:111–115). Inside it, `OuterFreshAllocatedWindow.uniform_actual_allocated_window`:127 bounds with rows `normValue z ≤ paddedRadius η Z Rdecl` and bound ∝ `Z^Rdecl/fixedPres*Z^ε`. The call path continues through `uniform_seeded_rest_window` (MixedFirstOuterUniformity:770) and `MixedFirstSourceWindow.uniform_seeded_selected_column_window`:498 to `MixedFirstCenteredSourceMoment.uniform_centered_source_moment`:274, the grouped moment at R = Rdecl.
5. **Conversion to the first reference.** `raw_block_of_normalized` (RepairedRawRetained:42) with `first_declared_exact` (RepairedRawReference:124) gives `nominalChildScale*normalizer*Z^Rdecl/fixedPres = firstReference*Z^{4θ}`, where `firstReference = N(τ)(V_root/N C₁)²/(fixedPres*frozenVolume*selectedVolume²)` (:56). The result is `RetainedBound` (RepairedActualLargeRetained:44): `‖selectedSum‖ ≤ C*scale*firstReference*…/N(seed)`.
6. **Cancellation.** `raw_supplier_reference_identity` (RepairedRawSupplier:277) states `(‖fW‖²*256*#active)*(scale*firstReference/N seed) = referenceBase*rawSupplierCost`. Then `selected_card_scale`:94 gives `#active*scale ≤ 512^N*selectedVolume²`, and `actual_raw_supplier_cost`:142 gives `rawSupplierCost ≤ 256*512^N*2^N*Kslot^{2N}/N(u)`. `retained_raw_cost` (RepairedLargeSupplierBudget:158) assembles these. **Net factor W⁰** against `referenceBase(τ,C₁,V_root)` (RepairedRawReference:31).

**Normalization.** `original_normalization` divides by `X₁X₂*∏_{RestIndex}P`. Here RestIndex is the live-unselected set (`MixedSupplierSource`:89; `rest_type_eq`, MixedFirstOuterUniformity:43), so the product includes neither the selected nor the frozen primes. By `residual_volume_partition` (RepairedRawExceptional:37), V_orig = V_res·frozenVolume·selectedVolume.

Dividing steps 1–3 by V_orig gives (derived):
`E_orig/V_orig ≤ 256·512^N·(‖fW‖²/frozenVol)·W·[Σ_D (gW/W)E_D/V_res]`.
- Measured against the D-sum Σ_D gW·E_D/V_res, there is no W factor.
- Measured against the 1/W-average (`groupedMoment`), there is a factor W^{+1}.

The Lean never forms this ratio. It works with raw energies against references that are quadratic in the volume (step 6).

**The 1/W of `actual_grouped_average`.** It sits on both sides, so the step is a pure pushforward with no saving. The analogue actually used, `MixedFirstAveragedWindow.actual_selected_window_average`:109, also keeps the 1/W attached to the K4 energy: `outputEnergy = Re gaussEnergy(16KW⁴)/W` (:98). Its inputs are `PositiveFamily.weighted_pushforward`:49 and `GaussTransfer.normalized_fourth_power`:98. After Poisson the prefactor becomes 16KW³ (`MixedPoissonCompletion.secondPoissonDensity`:38).

**Where the saving d is used.** Only in `MixedFirstPaidCosts.native_paid`:329, through `native_cost_power … h.Wlower` (MixedFirstNonexceptionalNormalization:96; hypothesis `hWlower : Z^d≤W`; output `Z^((3/4)Σw−d+2ε+(BG+1)δ)`), together with `Gates.native : (3/4)S<d` (:128).
- In this step W := `scale` (MixedFirstUniformEnergy:125).
- `Wlower` comes from `actual_padding_gates`:63 (MixedFirstUniformLossBudget:66).

## Q2. Bounding the dilated moment

**The bound.** `MixedFirstUniformEnergy.uniform_grouped_first_energy`:90 feeds `MixedFirstChosenEnergy.uniform_chosen_first_energy`:107:
`(N(Dseed)^step Z^step)*‖Σ_F (gW/scale)*finiteHeckeEnergy(selectedCoefficient F)‖/sourceVolume ≤ C*Kslot^{2N}A²H^J*(N(η)K)*Z^{εfinal}`.
- Hypotheses: `0≤R`, `P+2S+4d≤R−ρ`, `(3/4)S<d` and `cstar*Z^{referenceExponent R P S d} ≤ s.L`.
- `uniform_source_moment`:246 then adds the short-rectangle reference branch. `uniform_centered_source_moment`:274 follows.
- The exponent is R+ε.

**The four components.** They come from `actual_energy_four_parts` (MixedFirstFourParts:112) and are paid by `actual_costs_paid` (MixedFirstPaidCosts:481). Each is normalized by `reference = N(τ)(V/N C)²Z^allowance` (MixedFirstExceptionalNormalization:195):

| component | W enters as | exponent that must be ≤ 0 | cite |
|---|---|---|---|
| zero | 16·Kchild·W³ (MixedFirstFullBudget:80) | P+S−R+3d | `zero_paid`:271; `second_diagonal_gate` MixedLedger:58 |
| nonexceptional | fullCost/Wblock (MixedFirstNonexceptionalAllocation:85,117) | κS−d | `native_paid`:329 |
| exceptional | (16KW⁴)^{5/6}/W ∝ W^{7/3} (MixedInnerExceptionalBlock:437) | P+S−5R/6+7d/3−2l/3 | `referenceExponent` MixedFirstExceptionalWindow:185; `exceptional_paid`:355 |
| short reference | χ_F conductor ≤ Z^{R+d+ω} (MixedFirstReferenceActualCaps:91) | R+d+2l−P+S−R/2 | `reference_gate` MixedLedger:27; `centered_reference_gates` MixedFirstReferenceActualCaps:161 |
| tail | none | BG(1+δ)−saving | `tail_paid`:425 |

**Origin of 2S and 4d.** The exceptional row gives `lower = (3/2)(P+S+7d/3−5R/6)`. The reference row gives `upper = (P−S−R/2−d)/2` (MixedLedger:12–14). `upper−lower = R−P−2S−4d` (:16).
- Hence 2S = 3/2 + 1/2 and 4d = 7/2 + 1/2.
- At the midpoint l = P+S/2+3d/2−3R/4 (MixedFirstChosenEnergy:32), both margins are multiples of P+2S+4d−R (derived).
- The zero row's 3d is implied by the gate (`diagonalSlack` MixedFirstGeometricCaps:225).

## Q3. The native cost

**Where κ·S is paid.** In the non-fixed-inducing retained part of the second Poisson of the K4 first-side energy. The chain:
1. `nonexceptionalPart` (MixedFirstActualNonexceptional:83).
2. `uniform_actual_allocated_part`:112.
3. `MixedActualNonexceptionalBound.uniform_actual_nonexceptional_bound`:54. Here `closedBudget`:39 carries `Z^{κΣw+ε+δ+εg}` and `/Wblock`, with no K4.
4. The source envelope chain (`MixedActualEnvelopePhysical` → … → `MixedFrozenSource.uniform_live_source`:97) reaches `MixedUniformSource.uniform_source`:30, which gives `Z^{s.width+κΣ_{i∈T}w_i+ε}` under `hκ: 2β−1≤κ`.
5. Through `NativeNonfixedEnergy.canonical_energy` to `NativeSlotDeletion.canonical_delete`:72, then `energy_delete`:26 together with baseline `RayMaskedFloorSlots.natural_slot_product`:33.

κ = 3/4 comes from `IncumbentInput.native_kappa_bound`:24.

**Rows.** The dual frequencies are `partRows false η χ Q m C D U R`: the `sourceRows` filtered by ¬`FixedInducingRow (childCharacter η χ)` (baseline SecondEnergySplit.lean:37). Each row's character is the natural child character at z (`NaturalRow η z`), where η is the first-side τ.
- Slots deleted: the residual's live-unselected T, with Σw ≤ S (MixedFirstPaidCosts:144).
- Fixed-inducing rows go to the exceptional component instead.

**Paid by d** in `native_paid` (Q1).

**Pointwise: yes.**
- `energy_delete`'s hypothesis is per row: `∀z, keep z → profile≠0 → ‖∏_{i∈F} normalizedSlot … z …‖² ≤ E`. The proof compares the row sum term by term.
- `natural_slot_product` is likewise per row (η, z, `NaturalRow`, ¬FixedInducingRow), with per-slot exponent κ·w_i.
- E and κ are uniform. κ is constrained only by 2β−1 ≤ κ, where β is global.

A smaller rate on a sub-family of rows would need two things (inferred):
- a split of the rows, which is exact for these positive sums (cf. `physicalBlock_filter_split`, SecondEnergySplit.lean:20);
- a per-row slot bound with the smaller exponent. No such bound exists in the tree.

## Q4. The −2d in hdeclared

**Definition.** `Rdecl = declaredWidth` (OuterFreshRootAdmission:87):
`(inputWidth−log frozenVolume)+(D0−c)−max(D0−c,0)−2·log selectedVolume−log normValue(commonFreqGen C₂ D₂)+log N(∏U)−θ+4θ`.
Here Q = inputWidth η K Z is the root width (hroot, :147).

**What it encodes.** `normalizer*Z^Rdecl/fixedPres = (N(η)K/(frozenVolume*selectedVolume²))*Z^{D0−c−max(D0−c,0)+3θ}` (OuterFreshDeclaredMass:39). Combined with the first child scale this is exactly `firstReference*Z^{4θ}` (RepairedRawReference:124).

**Why it loses 2d.** The original energy carries #active (≤ 256^#J·∏_J P) from step 1 and scale (= 2^#J·∏_J P) from step 3. Together these are at most 512^N·(∏_J P)² = 512^N·Z^{2d}. The selected average must therefore be bounded at width Q − 2d (− log frozenVolume) for `rawSupplierCost` to be free of W. Equivalently, the reference is quadratic in the volume: ref(V_root) = ref(V_res)·frozenVol²·(∏_J P)² (derived).

**Gate arithmetic.** `actual_allocated_large_gate` (OuterFreshMixedCapacity:183) combines four inputs:
- `actual_common_capacity` at κ = 2 (:91);
- hroot with (93/25)(S+d) (:196);
- hdeclared with −2d (:197–199);
- d ≤ (43/100)(S+d)+mesh.

The conclusion needs (57/25)d ≤ (43/25)S + 4·mesh (derived), which is tight at 43/100. The frozen part is paid by `residual_root_capacity` (OuterFreshSelection:185) via `frozen_root_capacity`:148.
