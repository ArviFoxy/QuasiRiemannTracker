# I_return: map of Sil's return (57 files)

## 0. Scope and checks

- Files: the 57 names in `/home/user/QuasiRiemannTracker/research/combined/fourthpower_map/lists/I_return.txt`, read from `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/pr74/submissions/sil-fourth-power-20261025/src/Candidate/FourthPower/` (read-only). No Lean file was edited. Lean and lake were not run, so compile status is unverified.
- Grep over the 57 files: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `implemented_by` or `extern`.
- Import graph: all 57 files lie in the import closure of `FinalFromRawSides` (477 FourthPower modules reachable). The source input is `RepairedRestrictedSource.actual_required_source`, which is outside this list.
- PR69 comparisons use the read-only tree `/home/user/QuasiRiemannTracker/submissions/hailey-collet-1252270103/src/Submissions/hailey_collet_1252270103/`.
- Numbers in sections 3 and 4 come from my own scripts. Scalar guards use exact Fractions; the finite certificate uses a float sweep with local refinement. These are not Lean results. Scripts: `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/margins.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/scan.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/cand.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/sweep.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/refine.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/thetacert.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/physswap.py`, `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/bern.py`.

Constants (from `Parameters.lean`): θ = 1749387/2000000, h = 39823/50000, ℓ = 11/3 − 4θ, κ = 2θ − 1, η = 10⁻⁷, reserve = 10⁻⁹, incumbent = 8747759/10⁷.

## 1. Per-file map

### 1a. Parameters, target, source interface, final assembly

- **Parameters.lean**: exact constants and the four Face records. `parameters_exact` (κ, ℓ, x, y as rationals); `joins_exact` (ds, dk, dplus); `conductor_order` (d0 < y < ds < dk < dplus < 2y); `feedback_domain`; `structure Face` and `Face.Included` (a face's budget implies the GlobalSource budget); `Face.source_domain` (a point in a face's budget lies in the source budget); `countFace`, `physicalFace`, `xFace`, `yFace` with their `_included` lemmas.
- **TargetCompatibility.lean**: arithmetic interfaces for the target. `target_exact` (θ = 8746935/10⁷); `target_half` and `target_seven_eighths` (θ ∈ [1/2, 7/8]); `native_feedback_gap` (3/4 − κ = 613/10⁶); `probeShift` (= −(4 + y − x)/6); `boundary_signal_exact` (θ + probeShift = 1158919/6000000).
- **TerminalTransfer.lean**: generic endpoint adapters. `CanonicalGoal` (Dirichlet L-function nonvanishing for Re s > 1749387/2000000, excluding the trivial pole); `beta_of_common_probe` (UniformCommonProbe θ c ⇒ β ≤ θ, via Collet's Cycle25); `canonical_of_return_probe` (the probe at probeShift gives CanonicalGoal).
- **IncumbentInput.lean**: split on β. `baseline_beta` (β ≤ 7/8 from OpenAI's original theorem); `native_kappa_bound` (2β − 1 ≤ 3/4); `small_branch` (β < 0.51 ⇒ β ≤ θ); `contrary_inputs` (θ < β ⇒ 0.51 ≤ β and 2β − 1 ≤ 3/4); `target_cases` (exhaustive split).
- **SourceContract.lean**: ordinary-source interface. `face` := globalFace(99999/100000, 93/25, 3/50); `RequiredSource` := UniformUnitFaceSource face; `required_source_exact` (ε-mesh form); `admissible_exact` (the six admissibility inequalities).
- **FinalFromRawSides.lean**: final assembly. `full_source_of_raw_sides` (θ < β ⇒ full source, from the outside module); `common_probe_of_raw_sides` (⇒ UniformCommonProbe θ probeShift); `beta_of_raw_sides` (β ≤ θ, by case split, with the source used only when θ < β); `canonical_of_raw_sides` (CanonicalGoal).

### 1b. Scalar certificate, count algebra, finite 86-box certificate

- **ReturnCertificate.lean**: exact scalar receipt. `structure ComplementaryGuards` (33 strict inequalities); `complementary_guards` (all hold); `last_conductor_margin` (dplus − dk = 10087380243/138202430000000000); `shifted_global_source_domain` (small reflected shifts lie in the source budget); `large_shift_saving`; `capacity_joins` (old and new capacities agree at ds and dk); `returnValue` (linear in the count envelope R); `return_from_cleared` (clearing a positive denominator gives returnValue ≤ θ − reserve).
- **ReturnCountData.lean**: count algebra for "improved" branches. `roleFace` (count, physical, x, y); `ImprovedBranch` (role, capped, shift ∈ Fin 9); `ImprovedBranch.face` (intercept lowered by shift/4000); `improved_face_included`; N and J formulas, with `admissionGuard` (15 guards); `admitted_tail` (count > 1 − 2δ·mHigh − 2δp·sMinus); `cleared_return_sound` (cleared inequality ⇒ return ≤ θ − reserve).
- **ReturnBernstein.lean**: positivity certificates for degree-(2,3) polynomials. `positive_on_box` (Bernstein coefficients ≥ m > 0 ⇒ polynomial > 0 on the box); `positive_on_box_from_tensor`; `certificate_sound`; `split_delta`, `split_p`. Only upstream import: Collet's Bernstein basis.
- **ReturnFinite.lean** (8,664 lines, generated): exact certificate for the 86-box return. 94 polynomials `poly000`–`093`; 216 Bernstein blocks `bern/tensor/cert000`–`215`, all with witness m = 10⁻¹⁵; 17 window admissions; `row00`–`row85` (each `Certified e δ p` for one of six conductor edges); `cover_*` per edge; `envelope` (minimum of the old ratio and the containing-window ratios); `edge_return_bound` (returnValue ≤ θ − 10⁻⁹ for all six edges on [0,3/4] × [0,1/2]).
- **ReturnCountParameters.lean**: one theorem, `exists_count_parameters`. Gives PR69 `CountParameters` from the fixed-amplitude selected envelope count (imported from Collet).
- **ReturnWindows.lean**: the 17 windows as PR69 `AdmittedWindow`s. `admittedWindow` (i : Fin 17); `countScheme` (17 windows); `countScheme_window_count` (= 17); `admittedWindow_face` (window face is the broadFace of its improved face). Header says "not imported … not Lean checked" (see §5).
- **ReturnEnvelopeBridge.lean**: reindexes PR69's count envelope to the Option(Fin 17) certificate. `variableEnvelope` (κ-dependent); `variableEnvelope_le_old`; `upstreamEnvelope_eq_variable` (k ≥ 7/10); `variableEnvelope_gap_from_target` (variable − envelope ≤ (5/12)(k − κ)/18).
- **ReturnMonotone.lean**: monotonicity in p. Derivatives of the branch quantities; `count_hasDerivAt`; `admitted_count_antitone` (count non-increasing in p on the admitted region); `old_count_antitone`; `envelope_antitone` (envelope non-increasing on [0,1/2]).
- **ReturnFeedback.lean**: scalar variable-κ feedback (not an analytic theorem). `variableCapacity` (old for d ≤ ds, new after); `old_capacity_cost` (≤ 25/784·(k − κ)); `count_cost` (≤ 5/288·(k − κ)); `energy_return` (energy ≤ θ − reserve + (1/8)(k − κ)); `contrary_return` (θ < β ⇒ energy(2β − 1, …) − β ≤ −reserve − (3/4)(β − θ)).
- **ReturnContinuous.lean**: continuous scalar return. `selectedCapacity`; `complete_return` (returnValue ≤ θ − reserve on all of [d0, dplus]); `old_return` and `new_return` (the two halves); `interval_return` (interpolation between endpoints).
- **ReturnPhysicalSchedule.lean**: scalar physical schedule at cutoff 1/250. `scheduledCapacity`; `scheduled_capacity_le_supply` (≤ ℓ/d); `scheduled_capacity_damping`; `large_capacity_reserve`.
- **ReturnAnalyticFinish.lean**: scalar layer of the physical numerator; explicitly no endpoint. `signalShift` (= −(4 + y − x)/6); `numerator_kernel_identity` (exponent identity); `physical_packet_certificate` (exponent < signal β − reserve/2 − (β − θ)/2 − height, under a (β − θ)/4 budget); `physical_full_face_downward` (downward physical domain lies in the full source budget).

### 1c. Source faces, carriers, incumbent step, common probe

- **ReturnSourceFaces.lean**: face transport. `fullSourceFace` (= GlobalSource; the file calls it the sole new analytic input); `branchSourceFace`; `branch_admissible` (sub-face admissibility ⇒ full-source admissibility); `intermediateCountFace`, `intermediatePhysicalFace` (C30 faces, Included); `intermediate_sources_of_full_source`.
- **ReturnSourceInputs.lean**: joint detector and source data. `parameters` (Geometry instance); `exists_joint_data`; `actual_count_moments` (moments from the full source); `actual_physical_input`; `actual_active_fourth`.
- **ReturnCarrierInterfaces.lean**: carriers for data and heights. `commonMesh`, `rowPadding`, `withSmallerE`; `exists_compatible_data_with_mesh` (data for κ ∈ [7/10, 3/4]); `normalizer` and `source_normalizer_bound` (|normalizer⁻¹| ≤ C·Z^{t/8}); `HeightAdmissible`.
- **ReturnIntermediateBound.lean**: intermediate bound. `incumbent_from_full_source` (source + prior ⇒ β ≤ 8747759/10⁷); `initial_source_from_full_source`; `intermediate_suppliers_from_full_source`; `older_natural_cap`.
- **ReturnOldCount.lean**: old count at the contrary κ = 2β − 1. `baseline_beta` (β ≤ 7/8, OpenAI); `contraryKappa`; `contrary_gates` (7/10 ≤ κ ≤ 3/4 and 51/100 ≤ β); `weighted_old_actual_moments` (moments from one source, mesh and amplifier pair); `weighted_old_actual_count`.
- **ReturnCommonProbe.lean**: common probe. `common_probe_from_full_source` (full source + prior ⇒ UniformCommonProbe θ probeShift, with loss (β − θ)/2); `common_probe_of_contrary_source`; `beta_of_contrary_source` (⇒ β ≤ θ); `canonical_of_contrary_source`.

### 1d. Counts, moments, physical pieces

- **ReturnActualCount.lean**: actual selected-envelope count for the 17 windows. `selected_count_from_full_source` (source + β ≤ incumbent + θ < β ⇒ count bound at any ε, via a mesh); `SelectedCountBound` (def); `common_moments_of_affine`; `exists_saved_parameters`.
- **ReturnMaskedCount.lean**: masked amplitude-class count for the common detector and source. `choose_count_height` (height chosen after the degree); `actual_moments_at_count_height`; `ActualMaskedCount` (def); `actual_masked_count`.
- **ReturnCountBridge.lean**: PR69 count bodies re-instantiated with the 17-window envelope. `selected_source_count`; `canonical_source_count_with_error`; `source_masked_count_with_error`; `envelope_count_antitone`; `masked_amplitude_class_count`.
- **ReturnMomentBridge.lean**: source moments from initial fields. `source_moment_mono_constant`; `source_moments_from_initial_fields`; `actual_source_moments` (PR69 SourceMoments at the new geometry).
- **ReturnPhysicalInput.lean**: full-source finite physical pair. `FullPhysicalAt` (def); `finite_physical_pair_full`; `full_input_of_unit`.
- **ReturnPhysicalFourier.lean**: physical Fourier estimates on the full downward domain. `full_fourier`; `full_hybrid_fourier`.
- **ReturnPhysicalRetained.lean**: reflected restoration with the full source. `full_actual_retained_fourth`; `full_retained_fixed_profile`.
- **ReturnPhysicalActive.lean**: original numerator and active coefficient-bin fourth moment. `full_original_numerator_fourth`; `coefficient_box_geometry`; `full_active_box_fourth`.
- **ReturnPhysicalHelpers.lean**: pinned helper estimates for the physical packet. `source_prime_bins`; `source_scalar_on_rows`; `eventually_uniform_source_conductor`; `weighted_source_height_le`; `source_pools_nonempty` (eventual statements as Z → ∞).

### 1e. Packets and numerators

- **ReturnPacket.lean**: physical return packet with the full SourceFace, cutoff 1/250 and scheduled-capacity damping. `weighted_dilation_bin`; `packet_weighted_bins`; `actual_label_packet_bin_bound`; `source_packet_amplitude_class`.
- **ReturnLowPacket.lean**: natural old-band physical packet on d0 ≤ d ≤ ds. `old_active_box_fourth`; `old_packet_weighted_bins`; `old_actual_label_packet_bin_bound`; `old_source_packet_amplitude_class`.
- **ReturnPacketSummation.lean**: packet summation. `returnLoss`; `masked_class_mean_bounds`; `source_integrated_amplitude_classes`; `actual_raw_source` (raw packet bound for GapData, feeding the numerator).
- **ReturnCombinedPackets.lean**: both physical conductor ranges on one source. `physicalCapacity`; `combined_source_packet_amplitude_class` (lower branch used at d = ds).
- **ReturnClassApplication.lean**: H-class application with a numerical compatible source. `actual_class_packets`; `physical_loss_bound`; `actual_loss_budget`; `actual_numeric_return` (mesh (β − θ)/10⁴).
- **ReturnNumeratorCarrier.lean**: literal finite cells and partitions. `fullW_bin_partition`; `fullW_dyadic_partition`; `fullW_cells_norm_bound`; `selectedRows`; `selected_rows_facts`.
- **ReturnFiniteError.lean**: cube-to-FullW finite error at the new geometry. `actual_row_cap`; `uniform_cube_fullW_error`; `finite_cube_fullW_arbitrary_saving`; `actual_normalized_cube_fullW_arbitrary_saving`.
- **ReturnFiniteNumerator.lean**: actual finite numerator. `FullWCellsAt` (def); `fullW_sum_bound`; `actual_finite_numerator`; `exists_finite_numerator` (finite numerator bound for β > θ, from source + prior).
- **ReturnFullNumerator.lean**: Mellin integration and normalizer division. `source_height_absorption`; `actual_fullW_cells`; `transportHeightLoss`; `transport_height_loss_bounds`; `count_height_transport_gate`.
- **ReturnScalarBridge.lean**: scalar bridge for the packets. `numerator_packet_exponent`; `source_packet_exponent`; `physical_loss_bound` (lemma); `capacity_damping` (reflected capacity inequality).

### 1f. Transport chain (Collet/OpenAI adaptation)

- **TransportGeometry.lean**: guards for the new parameters. `TransportBounds` (class); `of_exact_values`; `theta_bounds` (874/1000 < θ < 7/8); `signal_at_boundary`.
- **TransportContours.lean**: measurability and Fubini for arithmetic profiles. `source_joint_fubini`; `source_ordered_ae`; `arithmetic_onLines_bound`.
- **TransportErrors.lean**: cube-row error savings. `original_row_cube_arbitrary_saving`; `finite_cube_arbitrary_saving`; `principal_shift_is_common` (principal shift equals Assembly.signalShift).
- **TransportEuler.lean**: Euler-product remainder bounds. `remainder_unramified_bound`; `remainder_globalClosedCorrection_bound`; `actual_source_analytic` (Euler-factor version).
- **TransportFinal.lean**: finite numerator to source probe. `baseline_beta`; `FixedFiniteNumeratorInput` (def); `sourceProbe_high_of_finite_numerator_at`.
- **TransportFiniteProduct.lean**: slot products for the correction. `correction_lower_bound`; `combined_slot_bound`; `global_norm_bound`.
- **TransportFloor.lean**: floor-cube arithmetic and savings. `floor_loss_bound`; `actual_floor_cube_arithmetic`; `actual_floor_cube_saving`; `actual_floor_rows_saving`.
- **TransportNonfloor.lean**: nonfloor probe transport. `actual_nonfloor_probe_transport`; `normalizedProbe_high_of_finite_nonfloor_numerator_at`.
- **TransportPrincipalBounds.lean**: principal bounds. `full_scale_bound`; `residue_scale_bound`; `source_remainders_strict_saving`.
- **TransportPrincipalCompare.lean**: principal vs ray comparison. `actual_window_residue`; `actual_ray_principal_comparison`.
- **TransportPrincipalPhysical.lean**: Gaussian shift and principal pool. `gaussianMoment_tendsto`; `principal_box_majorant`; `principal_physical_pool_ordered`.
- **TransportReduction.lean**: canonical probe reduction. `canonical_probe_exists_ray_cube`; `actual_normalized_probe_transport_saving`.
- **TransportSignal.lean**: source probe. `sourceProbe` (def); `sourceProbe_low` (sourceProbe = O(Z^(signal θ + loss))); `fixed_source_contract`; `exists_normalized_actual_source_bound`.
- **TransportTails.lean**: dyadic tails. `large_physical_tail_arbitrary_saving`; `large_original_physical_tail`; `small_original_physical_tail`; `canonical_large_original_tail`.

## 2. Overview: Sil's return against PR69

The return is PR69's machinery re-instantiated at a new geometry. 49 of the 57 files cite Collet or PR69. Verified differences:

- **Constants.** Sil's θ = 0.8746935. PR69's final is 8747729897/10¹⁰ (`Record1252270103Finite/ReturnConstants.lean`). PR69's intermediate is 8747759/10⁷ (`C30/ReturnConstants.lean`), which Sil calls `incumbent`. h moves from 0.8001009617 to 0.79646.
- **Faces.** Sil's `xFace` and `yFace` equal PR69's (countCB, countCL) and (physicalB, physicalLambda) exactly. Sil adds `countFace` (the global budget with cap 0.05499) and a new `physicalFace` (slope 12567/4000, intercept 4ℓ/(h+η) + slope/25, cap 0.043).
- **Windows.** PR69's `CountWindows.returnWindows` lists 38 windows (27 in its IntermediateCount copy). Sil uses 17 admitted windows plus the old branch, and certifies the return on 86 rectangles for six conductor edges. This generated certificate is the largest new object.
- **Feedback.** `ReturnFeedback` is a scalar variable-κ feedback with the capacity switch at ds (PR69 uses dm). Its contrary margin is (3/4)(β − θ). Collet's `GenericFeedback.new_supremum_deficit` gives (24/25)(β − θ) for the new-branch exponent. The two quantities are not identical (inferred), so this comparison is indicative only.
- **Common probe and old count.** `ReturnCommonProbe` and `TerminalTransfer` reuse PR69's `UniformCommonProbe` with the new shift −(4 + y − x)/6. `ReturnOldCount` evaluates the old supplier at κ = 2β − 1 and uses only OpenAI's β ≤ 7/8.
- **Actual count, packets, Mellin.** `ReturnActualCount`, `ReturnPacketSummation` and `ReturnFullNumerator` instantiate PR69's count, packet and Mellin bodies. I found no new Mellin argument. "Same-source" occurs once (`ReturnOldCount`: moments from one source, mesh and amplifier pair), which is bookkeeping.

Faces used. `fullSourceFace` = GlobalSource(0.99999, 3.72, 0.06) is the one analytic input (`ReturnSourceFaces`). Roles: count (`countFace`), physical (`physicalFace`), x and y (PR69 faces). `ImprovedBranch` lowers each intercept by shift/4000 (shift ≤ 8); each lowered face is included in the source.

Where θ enters. κ = 2θ − 1 sets the count envelope and old capacity. ℓ = 11/3 − 4θ fixes x, y, ds, dk, dplus and `physicalIntercept`. The return target is θ − 10⁻⁹. `probeShift` depends on θ. The contrary branch compares k = 2β − 1 with κ = 2θ − 1. `CanonicalGoal` is stated for Re s > 1749387/2000000.

## 3. Receipts and tight margins at θ = 0.8746935

Scalar guards (exact). All hold. Smallest margins, with what they depend on:

| Guard | Margin | Note |
|---|---|---|
| conductor_last, dplus − dk | 7.30e−8 | Identity: 10⁻¹⁰ + η·2ℓ/(y + η). Structural, not binding on θ |
| target θ < 874699/10⁶ | 5.5e−6 | Decimal-target check only |
| count_cap, 0.0549989 − 0.05499 | 8.9e−6 | Independent of θ |
| principal_conductor, h/600 − 1/1000 − 1/4000 | 7.7e−5 | Depends on h only |
| incumbent − θ | 8.2e−5 | Binding from above at θ = 8747759/10⁷ |
| large_shift, largeShiftReserve − η | 2.6e−4 | |
| native_feedback_gap, 3/4 − κ | 6.1e−4 | |
| width_upper, width_lower, floor_guard, source_cap | 3.0e−3 to 6.3e−3 | |

Scan of the scalar guards: upward, the first failure is `incumbent` at θ ≈ 8747759/10⁷. Downward from θ to 0.8700, no scalar guard fails.

Finite certificate (numeric, my sweep on the 6 edges over [0,3/4] × [0,1/2], refined locally):

- Tightest edges are `newtop` (5.6e−7) and `newkink` (5.8e−7), at δ ≈ 0.46374, p = 1/2. That point lies in row22's range [237/512, 477/1024], certified with window 9 (branchC, shift 0) and Bernstein block `bern152`.
- `oldswitch` and `newswitch` have margin 5.0e−3 at δ ≈ 0.50652, p = 1/2. There only the old branch applies, since δ lies just above 33195/65536 ≈ 0.5065155, the top of the window table. `oldpeak` is 7.6e−2 and `oldsmall` 0.11.
- Threshold for the fixed window table and faces: `newtop` changes sign at θ ≈ 0.8746935 − 1.4e−7 (≈ 0.87469336). The window admission guards were not re-checked at other θ (inferred that this is the binding structure).
- Reserve is 10⁻⁹, which is about 560× smaller than the `newtop` margin.

Bernstein witnesses (exact, all 216 blocks parsed). Smallest coefficients: `bern152` 2.53e−7, `bern190` 2.84e−7, `bern171` 3.15e−7, `bern209` 3.44e−7, `bern113` 3.64e−7. None is ≤ 0 or < 10⁻¹⁵. 69 blocks have minimum < 10⁻³; the median minimum is 1.3e−2.

Sensitivity to the physical face (numeric, window table held fixed). Replacing `physicalFace` by Collet's y-face (0.96739, 3.27308) in the physical roles and in dk and newCapacity leaves the scalar guards passing (dplus − dk = +4.6e−3). The `newtop` margin then becomes −2.4e−4 at δ ≈ 0.4925, p = 1/2. So the 5.6e−7 margin depends on the physical face at the 10⁻⁴ scale.

## 4. Alternative faces

Verified (exact arithmetic):

- **Count candidate (0.96775, 2.91120, 0.0549989).** `Face.Included` fails: 0.96775 + (3.72 − 2.9112)·0.0549989 = 1.012231 > 0.99999 (excess 0.01224). Largest admissible intercept for this slope and cap is 0.95551. With Sil's cap 0.05499 the excess is 0.01224 (essentially unchanged).
- **Physical candidate (0.97187, 3.0, 0.0549989).** `Face.Included` fails: lhs = 1.011479 (excess 0.01148). With Sil's cap 0.043 the excess is 0.00284. Largest admissible intercept is 0.96039.
- **Physical candidate at Sil's h and θ.** dk = 0.8024782 > dplus = 0.7964600. The guards `conductor_last`, `large_shift`, `slope_lower` (Sp − 3 = 0 is not > 0) and `source_cap` fail.
- **Count candidate.** Among the scalar guards, the count intercept and slope do not appear; only the cap enters, through `count_cap`. With the candidate cap 0.0549989 that strict guard becomes 0 and fails. The count face also enters the 86-box certificate through the count role, which I could not test without regenerating it.

Assessment.

- Neither candidate face is a sub-face of GlobalSource, so the current `Face.source_domain` argument cannot use them. They would need a new source estimate that the present code does not contain.
- With the physical candidate, the conductor order fails at Sil's h and θ. Using it would require re-solving h and the physical formula together (inferred).
- The count candidate can only be tested by regenerating the 17 windows and the 86-box certificate, which the code does not do (inferred).
- From this code I cannot establish a better θ than PR69's 8747729897/10¹⁰. Sil's θ is about 1.4e−7 above the threshold of its own certificate for the present faces, so any gain needs new faces and a regenerated certificate.

Pieces that are face-generic: `Face.Included` and `Face.source_domain`; the `ImprovedBranch` algebra and `cleared_return_sound`; the Bernstein positivity lemmas; `ReturnFeedback` (depends only on κ, ds and the cost constants); and `ReturnCommonProbe`, which depends on the source only through `UniformUnitFaceSource fullSourceFace`. Face-specific pieces: the Parameters constants, `physicalIntercept` and `dk`, the 17 windows and `ReturnFinite`.

## 5. Stale or unresolved items

- `ReturnEnvelopeBridge.lean` and `ReturnWindows.lean` say "Not imported into src and not Lean checked". Both are imported by live modules (for example `ReturnFeedback`, `ReturnActualCount`, `ReturnMaskedCount`, `ReturnOldCount`), so the comment looks stale (inferred). Compile status is unverified by me.
- `ReturnActualCount.lean` lists β ≤ incumbent as an outstanding input. `ReturnIntermediateBound.incumbent_from_full_source` derives it from the same full source and the prior, so the header probably predates that lemma (inferred).
- `ReturnAnalyticFinish.lean` cites `return-analytic-finish-findings.txt`. I searched the repository and the scratchpad and did not find it.
- `ReturnSourceFaces.lean` calls the global source "still-to-be-proved". That matches `FinalFromRawSides` importing `RepairedRestrictedSource`, which sits outside this list.
