# F_repaired: map of the 90 "Repaired*" modules

Source (read-only): `scratchpad/pr74/submissions/sil-fourth-power-20261025/src/Candidate/FourthPower/`
List: `research/combined/fourthpower_map/lists/F_repaired.txt` (90 files, 12,799 lines, 488 top-level declarations).

Method: statement-level extraction (module header, every declaration's signature and docstring). Five central files were read in full: RepairedRootParameters, RepairedRestrictedSource, RepairedSourceSetupBound, RepairedLargeBlock, RepairedSmallContribution. Short files outside the list were read where the top layer needs them (FinalFromRawSides, IncumbentInput, Parameters, RestoredInitialSource, GaussUnits, MixedFirstCutoffs, MixedFirstUniformLossBudget), and definitions were looked up in the openai-baseline and hailey-collet submissions. Nothing was compiled: lake and lean were not run.

Items marked **(inferred)** were not read directly.

---

## 0. Checked facts

- **Top theorem.** `actual_global_source` (RepairedRestrictedSource.lean, line 96). Its only explicit argument is `hcontra : theta < HeckeZeroSupremum.beta`. Its conclusion is `QRH.Record1252270103Source.GlobalSource (99999/100000) (93/25) (3/50)`.
- **Escape hatches in the 90 files.** None: no `sorry`, `axiom`, `admit`, `native_decide`, `unsafe` or `opaque` declaration. The two grep hits are English words in comments.
- **Closure of `actual_global_source`.** Transitive imports reach 421 Candidate modules, 2,923 openai-baseline modules, 26 hailey-collet modules, 15 RellichKondrachov modules and 4 PrimeNumberTheoremAnd modules. None of them contains `sorry`, `axiom`, `unsafe`, `opaque`, `native_decide`, `initialize` or `implemented_by`. Mathlib and Lean core were not followed.
- **Closure of the endpoint.** `RepairedUnconditionalEndpoint` also reaches 1,780 hailey-collet modules (the PR67 bootstrap). Four of them, `Certificate/{Argmin,Bracket,MonoTactic,Tactic}`, define evaluators as `unsafe def` plus `opaque` MetaM code. This closure is not the one of `actual_global_source`.
- **Import closure within the list.** 89 of the 90 files lie in the closure of RepairedRestrictedSource. The exception is RepairedUnconditionalEndpoint, which reaches it through FinalFromRawSides.
- **Name-based reachability (approximate, over-inclusive).** From `actual_global_source` and `actual_required_source`, 462 of 488 declarations are reached. Excluding the four endpoint declarations, 22 are not named from the chain: `RepairedBlockUniformity.{ThreeStage, ThreeStageSlot, three_stage_card}`, `RepairedRawExceptional.{seed_scalar, raw_selected_geometry_seed, raw_selected_cauchy_geometry, moving_root_reference}`, `RepairedRawSupplier.residual_profileCore`, `RepairedRawTail.uniform_raw_tail_original_seed`, `RepairedRemainderGeometry.{linear_seed_scalar, raw_zero_geometry}`, `RepairedRootParameters.reference_gates`, `RepairedSmallCharacter.empty_outer_rows`, `RepairedSmallCostControl.simple_cost_mono`, `RepairedSmallMass.empty_raw_cost`, `RepairedSmallRawBudget.small_modulus_volume_cancel`, `RepairedSmallRootFamily.supplier_rest_type`, `RepairedSmallSideAlgebra.{first_frozen_native_geometry, simple_cost_independent_height}`, `RepairedSmallWholeGauss.original_scale_energy_of_bounds`, `RepairedSupplierProfiles.profileEnvelope_nonneg`, `RepairedSupplierSplit.supplierBranch_nonneg`. Of the 22, 17 are named by no other declaration in the list. These may be alternative routes or dead code. Automation-only use (simp, linarith, positivity) would not be detected.

---

## 1. Per-file map

### 1a. Parameters, root data and caps (10 files)

- **RepairedRootParameters.lean**: numeric root parameters, the root face and centering. Main: `rootReserve` = 1/100000; `mesh ε` = min(rootReserve/1024, ε/1024); `mixedReserve` = rootReserve/8; `omegaLoss ε` = min(rootReserve/100000, ε/100000); `windowCap N ε` = 8 + N·mesh; `seedCap N ε` = 7 + N·mesh; `internalScale`, `cutoffLoss`, `commonPower` (defs). `mesh_spec`, `omega_spec`, `cap_spec`: positivity and bounds. `internal_losses_paid`: the four losses plus the seed term fit under min(stepN/4, omegaLoss/4, widthFloor/1600). `original_reserve_paid`: mixedReserve + 4·mesh + 4·cutoffLoss ≤ rootReserve. `Face P S`: 0 ≤ S ≤ 3/50 and P + (93/25)S ≤ 1 − rootReserve. `centered_spec`: the centered exponent lies strictly inside the admissible interval, with margins 20ω. `reference_gates`: the reference-provider inequalities. `contrary_inputs`: θ < β implies 51/100 ≤ β and 2β − 1 ≤ 3/4.
- **RepairedRawContext.lean**: structural root record and branch quantity. Main: `RootInput` (structure, lines 36–72): a Source with d = (1,1), R = 1, H = ∅, Fhole = 1, X and Y ≤ Z³, pool ≤ Z⁸, the face, (2/9)Z^ℓ ≤ L, and Z ≤ Kroot ≤ Z²; it states "NO source/energy/moment bound". `root_capacity`: logb Z(T/pairNorm) + (93/25)Σw ≤ inputWidth − rootReserve. `large G B L`: widthFloor < liveWidth(L). `contribution`: the shared branch quantity for `large` or its complement.
- **RepairedRootCaps.lean**: fixed-exponent arithmetic caps from the root face. Main: `root_product` (∏P = Z^{Σw}), `root_volume_cap` (volume ≤ Z), `root_volume_inverse` (≤ Z²), `root_norm_cap_two` (norm cap ≤ Z²), `common_norm_caps` (both common norms ≤ Z²), `first_modulus_cap`, `child_inverse_cap`.
- **RepairedCapEvent.lean**: one eventual arithmetic event, fixed before moving data. Main: `Event N ε Z` (structure): (9/4)²·2^N ≤ Z, fixedPresentationCost ≤ Z, sigmaFixed, outerFixed, innerFixed ≤ Z, a uniform cutoff admission, and `PoolBound`. `eventually_event`: it holds for all large Z.
- **RepairedChildCaps.lean**: caps on the retained child. Main: `second_cutoff_caps` (second cutoff ≤ Z¹⁴ when K⁻¹ ≤ Z¹⁰), `child_upper_cap`, `cutoff_le_one`.
- **RepairedDescendantBounds.lean**: abstract-source cap conjunctions. Main: `SupportBounds`, `FrozenBounds` (named conjunctions over an abstract first Source), `support_of_first_caps`, `frozen_of_first_caps`.
- **RepairedDescendantCaps.lean**: caps for the actual first source of an allocation. Main: `firstSource`, `firstCover`; `first_product_caps` (live count ≤ N, ∏P ≤ Z, ∏2P ≤ Z²); `residual_support_caps`, `residual_frozen_caps`.
- **RepairedConductorCaps.lean**: conductor caps under the same event. Main: `pool_norm_cap` (poolNorm ≤ Z¹⁶), `linear_sigma_cap` (σ-conductor ≤ Z⁹), `outer_family_cap`, `plain_family_cap`.
- **RepairedPointCaps.lean**: admissibility gates for one actual point. Main: `Bounds` (structure), `actual_bounds` (every gate, arithmetic only).
- **RepairedFirstPoint.lean**: dependent first-common data. Main: `Point d` (structure: label, inactive set, allocation B, nonvanishing frozen coefficient, τ, modulus, index, retained band), with projections `source`, `cover`, `selection`, `large`, `data`, `residual`, `unavoided`, `scale`, `cutoff`, `radius`.

### 1b. Frames, contributions and assembly (8 files)

- **RepairedFirstFrame.lean**: the frame record. Main: `Frame d` (structure): an active label (C, D), inactive E, τ with modulus η·fixedBadMask·72·(prime subset of E)·activeConductor, dyadic index, and membership in the retained band. `Frame.scale` (nominal child scale), `Frame.reference`, `Frame.point`.
- **RepairedContributionContract.lean**: the contribution contract. Main: `contributionBound` (amplitude · reference · Z^{ε/4}/|u| · (1+|tp|)^{2J}); `ContributionFor d hε branch J S C` (every frame's branch quantity ≤ that bound); `PendingSmallContribution` (the small-branch proposition, later proved).
- **RepairedCombinedFinite.lean**: union and max of the two branch bounds. Main: `FrameRawFor J S C` (every frame's raw energy ≤ contributionBound); `frame_raw_of_contributions` (large and small give FrameRawFor with max degree, union of controls, summed constant); `contributionBound_add`, `contributionBound_mono`.
- **RepairedActualFrameSides.lean**: both orientations of each retained block. Main: `retained_of_frame_raw` (FrameRawFor ⇒ SupplyFor); `actual_artificial_gates` (artificial divisor squarefree with norm ≤ Z⁸); `common_label_swap`, `swapped_label`.
- **RepairedCombinedSideFromSmall.lean**: assembly of the two branches. Main: `contrary_provider_of_pending_small` (the small statement plus the internal large estimate give ContraryRawSideProvider).
- **RepairedActualSideProvider.lean**: the closed proof of the side provider. Main: `actual_small_contribution` (proves PendingSmallContribution); `actual_contrary_raw_side_provider` (ContraryRawSideProvider, with no added premise).
- **RepairedSourceSideSupply.lean**: the side-provider interface. Main: `RootShape α` (pairs T0 ⊆ α with S ⊆ T0), `amplitude`, `SupplyFor d J control Cside` (RetainedRawSides with loss ε/4 and profile amplitude), `ContraryRawSideProvider` (for θ < β, eventually in Z and for every root input with Kroot = bΦ·Z, SupplyFor holds), `outer_loss_budget`.
- **RepairedSupplierSplit.lean**: the shared finite supplier boundary. Main: `supplierBranch` (the large or small predicate with the full supplier Cauchy count in both branches), `finite_source_split`, `firstBranch` (the first boundary used by both branches), `finite_common_split`, `raw_energy_of_branch_bounds`.

### 1c. Large branch (8 files)

- **RepairedBlockUniformity.lean**: uniform blocks over a finite indexed family. Main: `uniform_actual_block_family` (one degree, control and constant for every block in the family), `blockBudget_single_constant`, `blockBudget_mono`, `angleEnvelope_mono`, `ThreeStage` (three-level index shape).
- **RepairedLargeBlock.lean**: the large nonexceptional block for a generic root. Main: `uniform_generic_first_large_block`: one constant and event before all root-family members and first live subtypes; it yields `RepairedLargeTail.Result` for a generic root Source. Also `coarse_gates`, `cutoff_le_one`.
- **RepairedActualLargeRetained.lean**: the large retained supplier. Main: `RetainedBound` (predicate); `uniform_actual_large_retained` (large nonexceptional retained bound, no energy premise).
- **RepairedLargeTail.lean**: the physical tail as a named conclusion. Main: `Result` (definition: tail bound for an abstract first source).
- **RepairedLargeSupplierBudget.lean**: the four-part large supplier budget. Main: `Controls`, `Constants` (structures); `budget` (zero, nonexceptional, exceptional, tail); `uniform_large_supplier_cost`.
- **RepairedLargeProfile.lean**: one profile per root. Main: `degree`, `control`, `uniform_root_profile` (the paid large root budget becomes one homogeneous profile product with one degree).
- **RepairedLargeFirstCost.lean**: the large contribution through both Cauchy counts. Main: `total_loss_paid` (firstLoss + 10·cutoffLoss ≤ ε/4); `uniform_large_first_cost`.
- **RepairedLargeContribution.lean**: the large branch in the shared Frame format. Main: `uniform_large_contribution` (eventually in Z, for every root and frame, the large contribution ≤ Cside·S-control·height·reference·Z^{ε/4}/|u|·(1+|tp|)^{2J}).

### 1d. Small branch (28 files)

- **RepairedSmallAdmission.lean**: the small residual data. Main: `ResidualFacts` (seven residual facts over an abstract source); `actual_small_residual`; `actual_global_avoidance` (u divides the residual R times the seed).
- **RepairedSmallCharacter.lean**: empty-selection characters. Main: `empty_selected_product` (J = ∅ ⇒ product = 1); `child_ideal_cubic`; `exists_supplier_character` (a new σ with linear conductor bound and matching heights); `empty_outer_rows`.
- **RepairedSmallEmptyGauss.lean**: empty selection in the Gauss energy. Main: `empty_selected_energy_le` (at most one term, weight ≤ 1); `empty_gauss_eq_on_gate`; `empty_gauss_re_le`.
- **RepairedSmallWholeGauss.lean**: whole-σ Gauss energy at original K. Main: `original_scale_four_parts` (four-piece positive bound); `original_scale_energy_of_bounds`.
- **RepairedSmallNativeRaw.lean**: native ordinary energy with G = seed = 1. Main: `rawEnergy`, `unit_sector_energy`, `unit_height_energy`, `uniform_native_raw`.
- **RepairedSmallNativeFamily.lean**: one native envelope for all finite subtypes. Main: `uniform_native_raw_subsets`.
- **RepairedSmallAvoidedNative.lean**: native row for the avoided source. Main: `uniform_avoided_native` (unconditional; no third Gauss generation).
- **RepairedSmallRowAllocation.lean**: allocation of the ordinary restricted row. Main: `frozenScalar`, `sectorEnergy`, `liveEnergy`, `sector_energy_le_allocations` (Cauchy on the row), `avoided_sector_energy_le`.
- **RepairedSmallActivePhysical.lean**: admissibility of active avoided labels. Main: `factor_caps`; `uniform_active_avoided_physical`.
- **RepairedSmallPhysical.lean**: second physical block on the avoided coefficients. Main: `uniform_avoided_physical`.
- **RepairedSmallRetained.lean**: native nonexceptional retained aggregation. Main: `uniform_avoided_retained`.
- **RepairedSmallClosed.lean**: avoided native remainder with the harmonic-seed payment. Main: `uniform_avoided_nonexceptional`.
- **RepairedSmallOriginalScale.lean**: native remainder at the original Gauss scale. Main: `uniform_original_scale_nonexceptional` (localization with K/16 and W = 1).
- **RepairedSmallRawBudget.lean**: linear ordinary-row volume budget. Main: `slotCost`; `frozen_linear_cost`; `uniform_allocation_count` (allocation count squared ≤ C·G^δ); `avoided_energy_of_live_bounds`; `small_modulus_volume_cancel` (conductor and volume cancel against the raw residual).
- **RepairedSmallCommonProfile.lean**: one shared profile factor for the four small providers. Main: `commonProfile`, `profile_powers_le`, `profile_cap_le`, `exceptional_profile_le`.
- **RepairedSmallCostControl.lean**: homogeneous native raw cost. Main: `simpleCost`, `simple_cost_mono` (monotone in degree and control, for finite uniformity), `closed_budget_eq_simple`.
- **RepairedSmallSideAlgebra.lean**: exact algebra of the native cost. Main: `native_cost_to_frozen_budget`; `first_frozen_native_geometry` (the first frozen coefficient pays both powers of the first common norm); `simple_cost_independent_height`.
- **RepairedSmallShapeRawCost.lean**: empty-selected shapes paid by rawSupplierCost. Main: `native_shape_raw_cost`, `exceptional_shape_raw_cost`, `zero_shape_raw_cost`, `tail_shape_raw_cost`.
- **RepairedSmallFourShapes.lean**: the four raw scalar shapes. Main: `nativeShape`, `exceptionalShape`, `zeroShape`, `tailShape` (all nonnegative); `native_cost_le_common`, `exceptional_cost_le_common`.
- **RepairedSmallMass.lean**: exact shared supplier mass for the empty branch. Main: `empty_raw_cost`; `uniform_branch_of_raw_cost` (the full supplier Cauchy count, with no second Cauchy).
- **RepairedSmallSupplier.lean**: finite small supplier with sigma energy. Main: `empty_supplier_sigma` (σ with linear conductor, original seed); `ray_energy_bound` (finite ray sum ≤ 256·A).
- **RepairedSmallSupplierCost.lean**: small supplier paid by rawSupplierCost. Main: `uniform_small_supplier_cost` (includes the finite-ray mass).
- **RepairedSmallFirstBudget.lean**: four empty-selected shapes paid at the first common reference. Main: `zeroBudget`, `nativeBudget`, `exceptionalBudget`, `tailBudget`, `geometryBudget`; `paid_geometry`; `firstLoss` = (3/4)·widthFloor + 19·cutoffLoss.
- **RepairedSmallPoint.lean**: the four small providers at the actual residual source and radius. Main: `nativeLoss` = (3/4)·widthFloor + 11·cutoffLoss, `exceptionalLoss` = 19·cutoffLoss, `zeroLoss` = 8·cutoffLoss; `GaussBound` (definition, no estimate); `Result`; `uniform_small_point`.
- **RepairedSmallRootFamily.lean**: all four providers for a finite root-type family. Main: `uniform_root_full_gauss`; `supplier_rest_type` (definitional equality of residual types, no transport).
- **RepairedSmallUniformFour.lean**: one application of all four providers. Main: `uniform_full_gauss` (one degree, control and constant before moving data).
- **RepairedSmallFirstCost.lean**: the small contribution through both Cauchy counts. Main: `uniform_small_first_cost`.
- **RepairedSmallContribution.lean**: the small branch in the shared Frame format. Main: `uniform_small_contribution` (all four providers and both counts internal; the centre of this layer).

### 1e. First-band raw mechanism (10 files)

- **RepairedFirstRawSides.lean**: the raw-side contract. Main: `rawEnergy`, `windowEnergy`, `sideBudget`; `RawSideBounds` (definition: both original raw side energies bounded by sideBudget·(1+|v|)^{2J} for every artificial divisor and character pair); `window_from_raw_heights`.
- **RepairedFirstRawWindows.lean**: unamplified first-column windows. Main: `windowPolynomial`, `finite_window_le_energy`, `left_column_bound`, `right_column_bound` (at independent KL and KR).
- **RepairedFirstRawScalar.lean**: exact unit dictionary and paired reference. Main: `retained_selected_one`, `unit_prefactor`, `window_pair_reference`.
- **RepairedFirstRawKernel.lean**: whole kernel from raw sides. Main: `matrix`, `paired_column_bound`, `kernel_from_raw`.
- **RepairedFirstRawProjector.lean**: finite Möbius and ray projection. Main: `ray_projector` (constant 256), `mobius_ray_projector` (keeps the Nu⁻¹ weight).
- **RepairedFirstRawBlock.lean**: the first physical block. Main: `artificialMass`, `actual_block_expansion`, `block_of_raw_sides`.
- **RepairedFirstRawRetained.lean**: the retained band. Main: `RetainedRawSides` (definition: RawSideBounds for every first label, inactive subset and block); `actual_retained_blocks`; `uniform_retained_of_raw_sides`.
- **RepairedFirstRawGeometry.lean**: numerical first-band geometry for unit roots. Main: `frequencyCap`; `uniform_unit_retained_of_raw_sides`.
- **RepairedFirstFullBall.lean**: full-ball cost from raw sides. Main: `full_mask_identity`; `fullBallCost_of_raw_sides` (given RetainedRawSides, a full-ball bound with a fixed constant, eventually in Z).
- **RepairedFirstFullBallFamily.lean**: the full-ball bound uniform over finite root types. Main: `fullBallCost_of_raw_sides_family`.

### 1f. Shared raw, supplier, budget and remainder machinery (18 files)

- **RepairedRawReference.lean**: generic raw reference. Main: `referenceBase`, `firstReference`, `profileCore`; `nominal_equality`, `child_deficit_exact`, `first_declared_exact` (exact cancellation of the first scale).
- **RepairedRawReferenceScale.lean**: one reference bound for two root cases. Main: `raw_reference_of_lower_minimum` (c = 1 for the centered reference; c = 2/9, ℓ = 0 for the low branch).
- **RepairedRawExceptional.lean**: raw exceptional geometry. Main: `residual_volume_partition`, `raw_selected_geometry`, `raw_allocation_reference_seed`, `moving_root_reference`.
- **RepairedRawSupplier.lean**: frozen-supplier count and raw supplier cost. Main: `activeFrozen`, `residualSeed`, `uniform_frozen_count`, `rawSupplierCost`, `uniform_raw_supplier_mass`, `uniform_raw_supplier_cauchy_mass`.
- **RepairedRawColumnBudget.lean**: sharp lower column support. Main: `common_factor`, `sharp_pair_denominator`, `root_factor_sharp`, `actual_block_sharp_budget_le`.
- **RepairedRawRetained.lean**: generic raw nonexceptional block and finite assembly. Main: `raw_block_of_normalized`, `selected_sum_le_blocks`, `uniform_raw_retained_from_blocks`, `cancel_gain`.
- **RepairedGroupedConsumer.lean**: four components aggregated before norms. Main: `original_four_identity`, `actual_grouped_four_components`, `selected_norm_le` (triangle only for individual companions), `uniform_supplier_grouped_four`.
- **RepairedGroupedExceptional.lean**: exceptional grouped contribution at original K. Main: `active_selected_norm_lower` (lower edge for active amplitudes only), `active_fresh_gain`, `uniform_grouped_exceptional`.
- **RepairedExceptionalRawCost.lean**: exceptional component ready for raw mass. Main: `uniform_exceptional_raw_cost` (saving in [2/3, 4/5)).
- **RepairedComponentRawCost.lean**: exact component ratios before supplier mass. Main: `supplierFront`, `raw_cost_exact`, `exceptional_le_raw_cost`, `zero_le_raw_cost`, `tail_le_raw_cost`.
- **RepairedSupplierFourCost.lean**: integration of the four grouped components. Main: `finite_supplier_of_four`.
- **RepairedSupplierProfiles.lean**: residual profile factors. Main: `selectedCap`, `markedCap`, `profileEnvelope`, `selectedMass_le`, `residual_sourceProfile_le`.
- **RepairedRawTail.lean**: the second tail at original Kchild. Main: `spend_tail`, `uniform_raw_tail_original_seed`.
- **RepairedRemainderGeometry.lean**: exact zero and tail normalization. Main: `raw_zero_geometry`, `coefficient_zero_of_cap_lt_one`, `sharp_support_factored` (sharp support = b²·2^card·(volume/pairNorm)), `residual_profileCap_le`.
- **RepairedRemainderRawCost.lean**: second zero and tail in rawSupplierCost. Main: `uniform_zero_raw_cost`, `uniform_tail_raw_cost`.
- **RepairedPlainRemainders.lean**: generic second zero and tail at original K. Main: `uniform_plain_second_zero`, `uniform_plain_zero`, `uniform_plain_tail_seed`.
- **RepairedPaidFirstBudget.lean**: the finite supplier budget paid at the first reference. Main: `firstLoss`, `rootBudget`, `paid_budget`.
- **RepairedFirstScalarBudget.lean**: first-allocation scalar gates. Main: `frozen_scalar_cap`, `first_volume_cap`, `exceptional_shape_reference`, `zero_geometry_reference`, `inverse_reference_cap` (ref⁻¹ ≤ Z⁸), `tail_power_reference` (Z⁻⁴⁰ ≤ ref).

### 1g. Source-level restoration (7 files)

- **RepairedSourceRootInput.lean**: constructors of RootInput for the restored setup. Main: `lowInput` (ℓ = 0, not centered), `highInput` (ℓ = rootExponent, centered); `actual_sharp_seed_cap`, `actual_radial_caps`, `actual_holes_card`.
- **RepairedSourceRootGeometry.lean**: volume and caps for the restored root. Main: `root_volume_exact` (volume = Z^{ordinary + marked width}), `root_norm_sharp`, `minimum_cap` ((2/9)Z^ℓ ≤ L ⇒ Z⁻⁸ ≤ L), `eventual_root_caps`.
- **RepairedSourceProfiles.lean**: homogeneous profile bounds for the restored source. Main: `control_mono`, `root_height`, `actual_amplitude_bound`, `profile_budget_mono`.
- **RepairedSourceBallSupply.lean**: full ball from the side provider. Main: `uniform_ball_of_side_provider`.
- **RepairedSourceActualBall.lean**: full ball for the actual source root. Main: `uniform_actual_ball_of_side_provider`.
- **RepairedSourceSetupBound.lean** (central, read in full): the retained setup energy bound. Main: `uniform_setup_of_side_provider` (given the side provider and the contrary branch, an eventual bound ∑ initialWeight·‖literalRow‖² ≤ C·diagonalControl·control²·(1+|t|+V)^J·Z^{1+ε} for every setup).
- **RepairedRestrictedSource.lean** (central, read in full): the top layer. Main: `restricted_unit_source_of_raw_sides`; `uniform_restricted_unit_source_of_raw_sides` (mesh chosen before N); `actual_uniform_restricted_unit_source`; `actual_global_source` (the top theorem); `targetFace`; `actual_required_source`.

### 1h. Endpoint (1 file)

- **RepairedUnconditionalEndpoint.lean**: the endpoint. Main: `actual_beta_bound` (β ≤ θ, through FinalFromRawSides); `actual_canonical_bound`; `dirichlet_nonvanishing` (L(χ,s) ≠ 0 for Re s > 1749387/2000000, excluding the trivial character at s = 1). It uses `OlderIncumbentSupplier.actual` (PR67, outside the list).

---

## 2. Architecture overview

The top theorem `actual_global_source` has one explicit hypothesis, θ < β. It is the contrary branch of the split β ≤ θ or θ < β. The chain has five stages.

1. **Parameters and root data** (section 1a). `rootReserve`, `mesh`, `widthFloor`, and the N-dependent `windowCap` and `seedCap` depend only on ε and N. A `RootInput` is a structural root with face `Face P S` (0 ≤ S ≤ 3/50, P + (93/25)S ≤ 1 − 10⁻⁵). Its caps are proved, not assumed.
2. **Frames and assembly** (1b). A *frame* is one retained first band: an active common pair, an inactive subset, a second character τ, and a dyadic index. `FrameRawFor` bounds every frame's raw energy by one `contributionBound`. `frame_raw_of_contributions` combines the two branches, and `retained_of_frame_raw` gives `SupplyFor`.
3. **Two width branches** (1c, 1d). Both branches share one finite supplier partition. The *large* branch is liveWidth > widthFloor, and the *small* branch is its complement. Large uses a generic block and a four-part supplier budget (zero, nonexceptional, exceptional, tail). Small uses the native and exceptional providers for empty selections (J = ∅; **inferred** from the shape lemmas). Each branch yields a uniform bound in the shared Frame format.
4. **Raw sides** (1b, 1e). The *raw sides* are `RawSideBounds`: the two original window energies at independent KL and KR, bounded by sideBudget·(1+|v|)^{2J} for each artificial divisor and character pair. `RetainedRawSides` collects them over all first labels and blocks. `ContraryRawSideProvider` is proved from the two branches, which discharges the raw-side input.
5. **First-band mechanism and restoration** (1e, 1g). Kernel, projector, block, retained, geometry and full ball turn raw sides into a full-ball bound that is uniform over the root family. `uniform_setup_of_side_provider` and `actual_uniform_restricted_unit_source` follow. The external `global_source_of_restricted` gives the full `GlobalSource`.

The endpoint takes `beta ≤ theta` by cases. The contrary case uses this source. It also needs the inherited PR67 bound.

**What "repaired" means.** The docstrings name the replaced forms. A sum-of-norms triangle inequality is replaced by a grouped four-component bound. The canonical pool gets a lower edge only for active amplitudes. Column support is kept sharp rather than merged. The restored-root constructor and normalized supplier cost are dropped. The small proposition is changed from pending to proved. Sources are made abstract to avoid expansion. The earlier versions are not in this directory, so this list is inferred from the docstrings.

---

## 3. Assumptions and numeric parameters

### 3.1 Hypotheses of the top theorem

- **Explicit:** `hcontra : theta < HeckeZeroSupremum.beta`, the only argument of `actual_global_source`.
- **Named external definitions:**
  - `theta` = 1749387/2000000 (Candidate/FourthPower/Parameters.lean:13).
  - `OAI.SevenEighths.HeckeZeroSupremum.beta` (written `HeckeZeroSupremum.beta` in the files) = `sSup zeroSetWithSentinel`, with `zeroSetWithSentinel = insert (1/2) zeroRealParts` (openai-baseline, `OAI/NumberTheory/DirichletL/Hecke/ZeroSupremum.lean`, lines 7–16).
  - `GlobalSource B lam cap` = `UniformUnitFaceSource (globalFace B lam cap)`, with `globalFace B lam cap` = ⟨B, lam, 0, B, 0, cap⟩ (hailey-collet, `Record1252270103Source/Core/Contract.lean`, lines 15–20). The face means: plain masses in [0, B·M], slot mass in [0, cap·M], and m₁ + m₂ + lam·s ≤ B·M.
- **Discharged inside the chain:**
  - `hsupply : ContraryRawSideProvider` is discharged by `actual_contrary_raw_side_provider` (ActualSideProvider.lean:36), a closed proof.
  - `PendingSmallContribution` is discharged by `actual_small_contribution` (ActualSideProvider.lean:23).
- **Used from outside the list:** `RestoredInitialSource.global_source_of_restricted` and `uniform_source_of_restricted`. The latter needs `face.plainHi ≤ 1`, which is 99999/100000 ≤ 1 (checked by norm_num).
- **Hidden hypotheses:** none in the closed term. The checked closure has no `sorry`, `axiom`, `opaque` or `unsafe`. Whether the tree compiles was not checked.

### 3.2 Hypotheses carried mid-chain

| Hypothesis | Enters at | Status |
|---|---|---|
| `hβ : 51/100 ≤ β` | uniform_small/large_contribution, uniform_generic_first_large_block | Discharged: first conjunct of `contrary_inputs hcontra` (since θ ≥ 0.51). |
| `2β − 1 ≤ 3/4` (κ) | second conjunct of `contrary_inputs` | Discharged: `IncumbentInput.native_kappa_bound`, from the baseline's β ≤ 7/8 (external). Only the first conjunct is consumed at the provider level. |
| `hKslot : 1 ≤ Kslot` | providers | Discharged by `RestoredRootSource.slotBound_spec` (external). |
| `hcard`, ε > 0, `Wslot` smooth with support in [1,2], `bΦ ≥ 2`, Q ≠ ⊤, Q ≤ (72), Q ≤ M, Q ≤ η₀.modulus | universal binders of `ContraryRawSideProvider` and `RestrictedUnitSource` | Not discharged: these are the statement's own domain. |
| RootInput fields (hcanonical, hM, hunit, hR, hH, hF, hX/hY, hnorm, hpool, hface, hminimum, hmargin, hKlow/hKcap, hη, hZ ≥ 5) | built by `lowInput`/`highInput` | Structural data from a Setup, proved from the caps. Not energy hypotheses. |
| `Event N ε Z` | caps | Produced by `eventually_event`. |
| `RawSideBounds` and `RetainedRawSides` | premise of the FirstRaw implications; conclusion of the provider | Internal: the provider proves them, and the implications are instantiated with that result (**inferred** from the call graph). |
| Canonical with σ ≡ 33/50 and Cap 16 | RootInput.hcanonical, LargeBlock | Structural data. The argument order is read from `Canonical`'s use in RepairedSmallAdmission (inferred). |
| `OlderIncumbentSupplier.actual` (β ≤ 174963413/200000000 via `pr67_exact`) | endpoint only, `beta_of_raw_sides` | External PR67 input. Not used by `actual_global_source`. Its closure includes the `unsafe`/`opaque` certificate evaluators listed in section 0. |

### 3.3 Numeric parameters

Line numbers refer to the files as read. "Role" entries marked (inferred) are read from call sites or names.

| Name | Value / definition | Where | Role |
|---|---|---|---|
| rootReserve | 1/100000 | RootParameters:13 | Global reserve. The face intercept is 1 − rootReserve. |
| mesh ε | min(rootReserve/1024, ε/1024) ≈ 10⁻⁸ | :14 | Slot-width ceiling w_i ≤ mesh ε. Depends on ε only, so it is chosen before N and the root family. |
| widthFloor ε | = mesh ε | :15 | Large/small threshold (large iff widthFloor < liveWidth). Also divided by 400 in internalScale. |
| mixedReserve | rootReserve/8 = 1.25·10⁻⁶ | :16 | Reserve in stepN; passed as rho to the block family (inferred). |
| omegaLoss ε | min(rootReserve/100000, ε/100000) ≤ 10⁻¹⁰ | :17 | Margin unit: centering margins 10ω and 20ω, reference gates. |
| windowLoss ε | min(1,ε)/100 | :18 | εfinal in budgetStep. |
| windowCap N ε | 8 + N·mesh ε | :19 | Lcap of the setup; ≥ 8. |
| seedCap N ε | 7 + N·mesh ε | :20 | Seed exponent: sourceNormCap ≤ Z^seedCap (RootInput.hnorm). |
| stepN N ε | budgetStep(windowCap, seedCap, windowLoss, mixedReserve) | :21–22 | = min(mixedReserve/100, min(1,windowLoss)/(100·budgetDenominator)). budgetDenominator = 1 + tailCap + sourceExponent + seedCap, with sourceExponent B = 3B+1 and tailCap = 25·sourceExponent + 5 (MixedFirstUniformLossBudget.lean:75–78; MixedFirstCutoffs.lean:35). |
| internalScale | min(stepN, omegaLoss, widthFloor/400) | :23–24 | Master scale of every loss. |
| cutoffLoss, artificialLoss, massLoss | internalScale/1000 each | :25–27 | The three losses paid in the first and retained estimates. |
| commonPower | internalScale/(1000(seedCap+1)) | :28 | Loss on the common allowance; multiplied by 2·seedCap in internal_losses_paid. |
| Face | 0 ≤ S ≤ 3/50 and P + (93/25)S ≤ 1 − rootReserve | :90 | Root admissibility; P = logb Z T, S = Σw. |
| 93/25 (= 3.72) | slope lam | Face:90; RawContext:85; LargeBlock:105; RestrictedSource:28, 97 | Cost per unit slot width. Compare the classical 6κ = 4.5 with κ = 3/4 (from the task statement). |
| 3/50 | slot cap | Face:90; RestrictedSource:28, 97 | Upper bound S ≤ 3/50 on total slot width; the cap of globalFace. The exact string 3/50 occurs only in these lines; other grep hits are 33/50. |
| 99999/100000 | intercept B = 1 − rootReserve | RestrictedSource:28, 97; Parameters:28 | Plain-mass cap of globalFace; the restoration needs plainHi ≤ 1. |
| 51/100 | lower bound on β | RootParameters:199; hβ | From θ < β with θ ≈ 0.8747 > 0.51. |
| θ | 1749387/2000000 | Parameters:13; UnconditionalEndpoint:24 | Contrary-branch threshold; the Dirichlet nonvanishing region. |
| 3/4 (κ) | — | SmallPhysical:89 (base exponent (3/4)·rho + ε + Bnorm·δ); SmallFirstBudget:43; SmallPoint:44 | Native and small exponents. firstLoss = (3/4)·widthFloor + 19·cutoff; nativeLoss = (3/4)·widthFloor + 11·cutoff. |
| 5/6 | exceptional threshold | RootParameters:94, 164–173; RawContext hmargin | P + S − 5/6 ≤ −10ω in the low case; centered margin with (2/3)·centeredExponent. |
| 3/2, 1/2, 3/10 | centering edges | RootParameters:91–93 | lower = (3/2)(P+S−5/6); upperOne = (P−S−1/2)/2; upperTwo = 3/10 − S. |
| 43/25, 77/25, 1/20 | interval gaps | RootParameters:110–111 | Non-degeneracy of the centering interval. Depends on the face. |
| 2/9 | low minimum | RawContext hminimum; SourceRootGeometry:89; RawReferenceScale | L ≥ (2/9)·Z^ℓ. |
| [2/3, 4/5) | exceptional saving window | ExceptionalRawCost:35; GroupedExceptional:103 | Admissible saving exponents. |
| 33/50 | σ value in Canonical; lo = hi in the block family | RawContext:54; LargeBlock:99, 121, 151, 189; PointCaps:94; SmallAdmission:92, 110, 116; SmallPoint:108, 130, 164 | Fixed canonical σ-level (**inferred**). |
| 16 | Cap in Canonical | RawContext:54; LargeBlock:99 | (**inferred**); pool norm bound Z¹⁶ in ConductorCaps. |
| 7 | declared-width bound | LargeBlock:121, 175–177 | Bdecl; declaredWidth ≤ 7 (**inferred**). |
| Z⁸, Z³, Z² | caps on |u|, pool and Kroot; on X, Y; on norms | CapEvent; RawContext:36–72 | Fixed-exponent caps. |
| Z⁻⁸, Z⁻⁴⁰ | lower bounds on L and on ref | SourceRootGeometry:89; FirstScalarBudget:213, 242 | Minimum-cap exponents. |
| 5 | Z ≥ 5 | RawContext hZ; SourceSideSupply:70 | Eventual threshold. |
| 72, 12 | conductor levels | CapEvent (sigmaFixed, outerFixed, innerFixed); Q ≤ span{72} | Fixed arithmetic constants. |
| 2 ≤ bΦ | ContraryRawSideProvider | SourceSideSupply:65 | Radial constant with Kroot = bΦ·Z. |

---

## 4. Reuse for a different face (slope L, cap, intercept)

**Generic, reusable as is or with light edits:**

- **Uniformity machinery with no face constants.** `BlockUniformity` (uniform_actual_block_family), `RawRetained` (uniform_raw_retained_from_blocks), `RawSupplier` (uniform_frozen_count, uniform_raw_supplier_mass and cauchy_mass), `SmallRootFamily` (uniform_root_full_gauss), `LargeProfile` (uniform_root_profile). A grep finds none of 93/25, 3/50 or 99999/100000 in these files.
- **Exact algebra and bookkeeping.** RawReference, ComponentRawCost, GroupedConsumer, SupplierSplit, RemainderGeometry, RawColumnBudget, SmallSideAlgebra, SmallCostControl, SmallCommonProfile, SourceProfiles, DescendantBounds, FirstFrame, FirstPoint.
- **Scaffolding.** The frame, FrameRawFor and SupplyFor chain (ContributionContract, CombinedFinite, ActualFrameSides, CombinedSideFromSmall). The mesh-before-N restriction pattern (RestrictedSource). The restoration `uniform_source_of_restricted`, which is parametric in the face and needs only plainHi ≤ 1. The by-cases endpoint in FinalFromRawSides, with θ as a parameter.
- **Loss template.** Each loss is a fixed fraction of min(stepN, omegaLoss, widthFloor/400) (RootParameters:21–28, 51–57). The template is reusable, but the denominators 1000, 400, 1024 and 100000 are choices.

**Specific to (99999/100000, 93/25, 3/50):**

- RootParameters: rootReserve, `Face` (line 90), the edges lower/upperOne/upperTwo (lines 91–93, with constants 3/2, 1/2, 3/10, 5/6), interval gaps 43/25, 77/25, 1/20 (lines 109–111), the margin lemmas (164–171) and `reference_gates` (180–197).
- RawContext.root_capacity (lines 84–95, slope 93/25).
- LargeBlock's hypothesis (line 105) with 93/25 and rootReserve.
- RestrictedSource: `targetFace` (line 28) and the statement of `actual_global_source` (lines 96–99).
- Parameters.lean: sourceB, sourceSlope, sourceCap, countFace (lines 28–30, 71).
- UnconditionalEndpoint: θ = 1749387/2000000 (line 24).
- Exponent regime: 2/9 (lower minimum), the window [2/3, 4/5), 3/4 (native and small losses), and the 33/50, 16, 7 constants (**inferred** as exponents of this regime).

**Effect of changing each face parameter** (**inferred** from the dependency pattern):

- **Cap (3/50).** The cap enters Face and the globalFace triple. The algebra uses S symbolically, so this change is cheap.
- **Intercept (1 − 10⁻⁵).** It enters Face, globalFace B, and rootReserve. rootReserve feeds mesh, mixedReserve, omegaLoss and every loss, so the whole loss budget moves. Keep rootReserve = 1 − B consistent.
- **Slope (93/25).** It enters Face, root_capacity, the LargeBlock hypothesis and the globalFace triple. The centering edges, the interval gaps 43/25, 77/25 and 1/20, and the reference gates depend on this algebra and must be re-derived. The exceptional saving window and the native exponents may also move.

---

## 5. Limits

- Five central files were read in full. The other 85 were read at statement level. The extractor truncated signatures at about 330 characters, so long statements were not read completely.
- Reachability and in-degree are name-based. They over-count where names collide (for example `scale`, `reference`, `cover`). They under-count where a lemma is used only by automation or through dot notation on structure fields.
- Nothing was compiled, so the tree's buildability is unverified. The absence of `sorry` and `axiom` was established by grep only.
- Mathlib and Lean core were not followed.
- The endpoint's closure includes the `unsafe`/`opaque` certificate evaluators of the PR67 bootstrap (section 0). Whether their outputs are kernel-checked was not determined.
- The fourth-power identity is `GaussUnits.fourth_power` (GaussUnits.lean, line 36): for χ⁶ = 1, `row χ ψ (k·u⁴) = (χ u)²·row χ ψ k`. None of the 90 files names it or the GaussTransfer lemmas. Its consequences reach this layer through upstream modules (**inferred**). The only sixth-named item in the 90 files is the lemma `rowTwist_extract_sixth_mask`, used at RepairedSmallCharacter.lean line 57.
- The meaning of "repaired" is inferred from docstrings, since the earlier versions are not in this directory.
