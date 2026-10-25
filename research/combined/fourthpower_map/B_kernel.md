# B_kernel: the Kernel* group (38 files)

Source (read-only): `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/pr74/submissions/sil-fourth-power-20261025/src/Candidate/FourthPower/`

Method: module headers, imports, and declaration headers with docstrings for all 38 files. Full proofs were read for five central results: `KernelIdeal` global identities, `KernelAllocationIdentity` allocation identities, `KernelWholeColumns.restricted_gauss_transfer`, `KernelCollisionEnergy.collision_block_mass`, and `KernelSelectedMass.selected_ideal_mass`. Line numbers refer to the source file. Anything not read directly is marked "(inferred)". No Lean file was edited and nothing was built.

Notation: `K` = `kernelSeries` = `LocalKernels.ordinary` = (1-x)(1-y)·T. `T` = `truncatedSeries` = Σ_{i+j≤4} x^i y^j (15 monomials, the 5-power-free truncation). `B` = `base` = (1-x)(1-y). `R` = `reciprocalSeries` = 1/K. `O` = `ordinarySeries`, defined in an imported baseline namespace (not read); the proved identity `ordinary_geometric_identity` gives (1-x)(1-y)·O = 1, so O = 1/B. `rootMass σ` = Σ' over supported ideals I of N(I)^(-σ) (`SieveDescent.lean:47-48`).

Expanded form of K (inferred: derived by hand from the definitions and checked against `ordinaryCoefficient`): K = 1 - Σ_{i+j=5} x^i y^j + xy·Σ_{i+j=4} x^i y^j, which has 12 monomials. The marked series B-K has 14 monomials.

---

## 1. Per-file map

Grouped by stage: A = formal series, ideal identities and masses; B = allocations, labelled slots, holes and collisions; C = physical rows, scalars, energies and punctures.

### A. Formal series, ideal identities and absolute masses

- **KernelFormal.lean**: fifth-free formal series T, K, R, O and their exact local identities. No analysis.
  - `forward_divisor_identity` (L63): K·O = T.
  - `inverse_divisor_identity` (L81): R·T = O.
  - `forward_marked_series` (L104) and `inverse_marked_series` (L120): `markedMul` of (K, B-K) with (O,O) gives (T,1); `markedMul` of (R, (K-B)R²) with (T,1) gives (O,O).
  - `forward_rectangular_convolution` (L84) and `inverse_rectangular_convolution` (L93): coefficient-level rectangle sums of K and R equal the indicator of i+j<5, resp. 1.
  - The degree-4 monomials x⁴, y⁴ of T are at L27-29.

- **KernelCoefficients.lean**: coefficient tables tying the formal series to finite monomial lists.
  - `ordinary_series_expansion` (L15): K = Σ_{i<12} c_i x^{a_i} y^{b_i}.
  - `marked_series_expansion` (L22): B-K = Σ_{i<14} (same form).
  - `ordinary_coefficient_table` (L30), `marked_coefficient_table` (L41): coefficient of x^j y^k.
  - `ordinary_coefficient_nonzero` (L72): nonzero coefficients occur only at the 12 listed exponents.

- **KernelInverseCoefficients.lean**: coefficients of R = 1/K.
  - `reciprocal_recurrence` (L23): R_n + Σ_{i<11} c_{i+1} R_{n-e_{i+1}} = δ_{n,0}.
  - `shift_small` (L50), `reciprocalCoeff_small_degree` (L59): R_n = 0 for 0 < deg n < 5.
  - `reciprocalCoeff_abs_bound` (L82): |R_n| ≤ 2^{deg n}.

- **KernelSeriesMass.lean**: generic absolute-mass calculus with weight z^{deg}.
  - `weight` (L21): |coeff_n|·z^{deg n}.
  - `mass_mul` (L48): mass(AB) ≤ mass(A)·mass(B) (Cauchy product).
  - `finite_polynomial_mass` (L59): mass of Σ c_i x^{e_i} ≤ Σ|c_i| z^{deg e_i}.
  - `reciprocal_summable` (L91), `reciprocal_mass` (L100): Σ_n |R_n| z^{deg n} ≤ 1+400z³ for 0 ≤ z ≤ 2/5.

- **KernelIdeal.lean**: ideal-level divisor identities for the 5-power-free indicator.
  - `powerFree_iff_valuations` (L23): PowerFree 5 I ⇔ every valuation < 5.
  - `restricted_kernel_eq_indicator` (L63): ideal kernel of T equals the indicator of PowerFree 5 (IJ).
  - `forward_global_identity` (L93): 1[PowerFree 5 (IJ)] = Σ_{d|I, d'|J} forwardIdeal(d,d'), where forwardIdeal = idealKernel K.
  - `inverse_global_identity` (L119): 1 = Σ_{d|I, d'|J} inverseIdeal(d,d') · 1[PowerFree 5 (cofactor product)].

- **KernelIdealMass.lean**: absolute mass of the actual ideal kernel at critical exponents (2/3, 1/3).
  - `idealMass` (L17): |forwardIdeal d| · N(d1)^(-2/3) · N(d2)^(-1/3).
  - `ideal_mass_product` (L32): Euler-product form.
  - `local_coefficient_mass` (L46): the local term equals `ordinaryWeight p i`.
  - `forward_ideal_mass` (L62): Σ_{d∈D} idealMass d ≤ exp(11·rootMass(5/3)) for any finite D of supported pairs.

- **KernelInverseMass.lean**: central absolute mass of the reciprocal series.
  - `localMass z ij` (L17): |R_ij|·z^{i+j}.
  - `localMass_geometric` (L23): localMass ≤ (2z)^{i+j}.
  - `localMass_total` (L39): Σ ≤ 1+400z³ for z ≤ 2/5.
  - `localMass_finite` (L99): finite-sum version.

- **KernelInverseIdealMass.lean**: central absolute mass of the inverse ideal kernel at N(P)^(-1/2).
  - `supported_prime_norm` (L18): Supported P ⇒ 7 ≤ N(P).
  - `central_radius` (L26): N(P)^(-1/2) ≤ 2/5 for N(P) ≥ 7.
  - `local_central_mass` (L35): local sum ≤ 1+400·N(P)^(-3/2).
  - `inverse_ideal_mass` (L96): Σ_{d∈D} idealMass d ≤ exp(400·rootMass(3/2)), uniform in D and in S.

- **KernelInverseMarkedMass.lean**: the marked inverse series M_inv = (K-B)·R² = (H-B)/H², where H = K.
  - `markedSeries` (L18).
  - `marked_polynomial_mass` (L31): mass(B-K) ≤ 14z.
  - `reciprocal_mass_le_27` (L54): mass(R) ≤ 27 for z ≤ 2/5.
  - `marked_inverse_mass` (L62): mass(M_inv) ≤ 10206·z for z ≤ 2/5. The proof uses (14z)·729, and 729 = 27².
  - `local_marked_mass_finite` (L96): finite local sum ≤ 10206·z².
  - `prime_marked_mass` (L112): local mass at N(P)^(-1/2) ≤ 10206/N(P).

- **KernelReflectedMass.lean**: central forward mass and the reflection cost.
  - `ordinary_central_mass` (L27): mass(K) ≤ 1+11z⁵ for z ≤ 1.
  - `centralMass d` (L78) = idealPairWeight K (1/2) d.
  - `central_ratio` (L104): x^(-1/2) y^(-1/2) (y/x)^(1/6) = x^(-2/3) y^(-1/3).
  - `reflected_mass_split` (L116): reflectedMass d = 2·centralMass d + idealMass d.
  - `reflected_ideal_mass` (L127): Σ_d reflectedMass ≤ 2·exp(11·rootMass(5/2)) + exp(11·rootMass(5/3)).

- **KernelForwardMass.lean**: the forward kernel K as 12 monomials with anisotropic weights.
  - `ordinaryCoefficient` (L19) = ![1, -1 ×6, 1 ×5].
  - `critical_ordinary_weight` (L21): p^(-(j+k)/2)·p^((k-j)/6) = p^(-(2j+k)/3). This is the origin of the exponents 2/3 and 1/3.
  - `ordinaryWeight_nonconstant` (L61): for every nonconstant monomial (i ≠ 0), the critical weight is ≤ p^(-5/3).
  - `ordinary_local_mass` (L69): Σ_i ordinaryWeight p i ≤ 1+11·p^(-5/3) for p ≥ 1.
  - `finite_euler_mass` (L80): ∏_{P∈S} (1+C·N(P)^(-σ)) ≤ exp(C·rootMass σ). Generic.
  - `ordinary_global_mass` (L96).

- **KernelSelectedLocal.lean**: single-prime bounds for the actual kernels, feeding the selected and marked masses.
  - `finite_table_mass` (L16): mass of a finite monomial table ≤ Σ_k |c_k| x^{e_k} y^{e_k}.
  - `ordinary_local` (L55): Σ_{ij∈T} localWeight(K) ≤ 1+11·N(P)^(-5u) for u ≤ min(s,t).
  - `marked_local` (L96): ≤ 14·N(P)^(-u).
  - `inverse_ordinary_local` (L134): ≤ 1+400·N(P)^(-3/2) at (1/2,1/2).
  - `inverse_marked_local` (L142): ≤ 10206·N(P)^(-1/2).

- **KernelMarkedMass.lean**: forward marked correction B-K as 14 monomials.
  - `markedCoefficient` (L18) = ![-1, -1, 1 ×7, -1 ×5].
  - `markedWeight_le` (L61): ≤ p^(-1).
  - `marked_local_mass` (L68): Σ ≤ 14·p^(-1).
  - `marked_pool_mass` (L74): Σ over (prime, monomial) pairs ≤ 14·X^δ·rootMass(1+δ).
  - `marked_assignments_subpower` (L90): Σ over assignments α → S×Fin 14 of Π markedWeight ≤ C·X^ε.

- **KernelPunctureMass.lean**: the correction B/H and its masses.
  - `correction` (L19) := B·R, which equals 1/T.
  - `reciprocal_coeff_sharp` (L22): |R_n| ≤ (5/3)^{deg n}.
  - `reciprocal_mass_wide` (L72): mass(R) ≤ 144 for z ≤ 11/20.
  - `base_mass` (L114): mass(B) ≤ 4.
  - `correction_mass` (L129): mass(correction) ≤ 576 = 4·144 for z ≤ 11/20.
  - `reflected_radius` (L139): p^(-1/3) ≤ 11/20 for p ≥ 7.
  - `correction_local` (L153): ≤ 576 at s, t ≥ 1/3.
  - `fixed_support_ideal_mass` (L193): Σ_d idealWeight(atPrime H)(s,t) ≤ C·Z^ε, for a fixed finite puncture set H dividing F with N(F) ≤ Z^B, and s, t ≥ 1/3.
  - `fixed_support_reflected_mass` (L252): same, with the factor (1+ratio^(1/6)) inserted, ≤ C·Z^ε.
  - `atPrime H P` (L175) := correction if P ∈ H, else 1. It is used by KernelPunctureRows and KernelPunctureFamily.

- **KernelFixedSupportMass.lean**: Euler mass over a fixed finite prime support. Imports one baseline lemma unchanged.
  - `prime_divisors_in_support` (L15).
  - `support_product_subpower` (L25): ∏_{P∈S} (1+C·N(P)^(-a)) ≤ K·N(F)^ε for S ⊆ primeSupport(F), with K chosen before F.
  - `polynomial_support_mass` (L54): the same with N(F) ≤ Z^B, bound K·Z^ε.

- **KernelSelectedMass.lean**: absolute mass of the prime-dependent `kernelOn`. A selected (supplying) prime uses the marked factor; the others use the ordinary factor.
  - `localWeight` (L20) := |coeff_{ij}(A)| · N(P)^(-s·i-t·j). `idealWeight` (L27) := |kernelOn(A)| · N(d1)^(-s) · N(d2)^(-t).
  - `idealWeight_product` (L35): Euler factorisation for supported pairs.
  - `finite_ideal_product` (L48): Σ_{d∈D} idealWeight ≤ ∏_P Σ_{ij} localWeight.
  - `selected_product` (L77): ∏_P (marked ? w : 1) = ∏_{labels i} w(slot i), for injective slot.
  - `selected_ideal_mass` (L91), full proof read: Σ_{d∈D} idealWeight(marked ↦ B, else A)·∏_i z(slot i) ≤ (∏_P ordinary_P)·∏_i markedMass(slot i)·z(slot i).
  - `prime_assignments_subpower` (L126): Σ over slot maps α → S of ∏_i K/N(slot i) ≤ C·X^ε. The docstring calls this a harmonic family.

- **KernelInverseSlotMass.lean**: optional inverse marked slots.
  - `Choice S T` (L16) := Option (Σ P : S, T P). `none` = unselected; `some` = selected at a prime with a monomial index.
  - `choiceWeight` (L18): 1 for unselected, localMarkedMass(N^(-1/2)) for selected.
  - `marked_pool_mass` (L28): Σ ≤ 10206·X^δ·rootMass(1+δ).
  - `optional_assignments_subpower` (L60): Σ_{a: α → Choice} Π_i choiceWeight ≤ C·X^ε.
  - `inverse_allocations_subpower` (L105): Σ over a finite set A of pairs (d, allocation) of idealMass(d) · Π_i choiceWeight ≤ C·X^ε.

### B. Allocations, labelled slots, holes and collisions

- **KernelRestrictedState.lean**: the literal restricted state.
  - `Restricted S live I J` (L54) := PowerFree 5 (IJ) ∧ no live supplying prime divides IJ.
  - `restricted_coefficient` (L35): local coefficient of 1 (marked) or T.
  - `restricted_kernel` (L57): kernelOn(live ↦ 1, else T)(I,J) = 1[Restricted].
  - `forward_restricted_identity` (L85): the sum over frozen allocations of the convolution equals 1[Restricted S marked I J].
  - `inverse_residual_restricted` (L96).

- **KernelAllocationIdentity.lean**: core local-to-ideal identities.
  - `kernelOn` (L18) := ∏_{P∈S} coeff_{localExponent(I,J,P)}(A P).
  - `divisor_convolution` (L31): Σ_{d|I, d'|J} kernelOn(A)(d)·kernelOn(B)(cofactor) = kernelOn(A·B)(I,J).
  - `allocation_expansion` (L67): a sum over per-prime choices of kernelOn equals kernelOn of the summed local factor.
  - `forwardFactor` (L78) = K (live) or B-K (frozen). `inverseFactor` (L81) = R or M_inv. `inverseResidual` (L84) = 1 for live marked primes, else T.
  - `forward_local` (L87), `inverse_local` (L96): per-prime sums. At a marked prime, Σ_b forwardFactor(b)·O = 1, since K·O + (B-K)·O = B·O = 1. At an unmarked prime it equals T.
  - `forward_allocated_identity` (L107): Σ over frozen allocations of the divisor convolution = kernelOn(marked ↦ 1, else T).
  - `inverse_allocated_identity` (L121): the same inverse sum equals 1. Full proof read.

- **KernelLabelledSlots.lean**: labelled slot families.
  - `frozen S slot T P` (L20): P is occupied by a label in T. `marked` (L23) = frozen over all labels.
  - `allocationEquiv` (L75): admissible 0/1 allocations ≃ Finset of labels, for injective slot.
  - `labelled_reindex` (L82): Σ over admissible allocations f(a) = Σ_{T⊆labels} f(frozen T).
  - `restricted_frozen_labels` (L108), `actual_freezing_restriction` (L125): restriction under freezing.
  - `forward_labelled_identity` (L142), `inverse_labelled_identity` (L155).

- **KernelHoleCompletion.lean**: forbidden-hole completion for injective tuples.
  - `good`, `bad`, `mixed L` (L17-23): split entries by a forbidden predicate and a label set L.
  - `product_partition` (L32) and `full_partition` (L43): Π_i a_i(x_i) = Σ_L Π_i mixed.
  - `complete_holes` (L62): injective(good) = injective(a) - Σ_{L≠univ} injective(mixed L).
  - `freeze_forbidden` (L74), `frozen_support` (L106): nonzero frozen coefficients occur only at forbidden values.
  - `fewer_live_labels` (L115).

- **KernelAssignmentReindex.lean**: weighted sums over injective tuples and their frozen/live split.
  - `weightedSum a f` (L17) := Σ_{x injective} f(x)·Π_i a_i(x_i).
  - `remainingSum T a t f` (L20): sum over the complement, with cross-distinctness holes.
  - `split_weighted` (L27): weightedSum splits as Σ_{t on T} Π a · remainingSum.
  - `split_convolution` (L98), `remainingSum_constant` (L115).

- **KernelCollisionEnergy.lean**: generic finite collision-energy lemmas, adapted from PR69 DeletionCollision files. Imports one baseline algebra module.
  - `collision_block_mass` (L20), full proof read: for |J| ≥ 2, Σ_p Π_{i∈J} v_i(p) ≤ L·B^{|J|}. Two ℓ² energies are used, and the other factors use the sup bound.
  - `weighted_family_energy` (L62): weighted Cauchy-Schwarz over a finite family. The count of assignments does not enter.
  - `sum_family_energy` (L88).
  - `setoid_card_le` (L132): #Setoid(I) ≤ 2^{K²} for |I| ≤ K.
  - `collision_assignments_mass` (L143): Σ over collision assignments ≤ (L·B^K)^K, uniform in the equality pattern.
  - `product_energy_of_singletons` (L170), `weighted_physical_energy` (L254), `weighted_product_energy_of_singletons` (L280).

- **KernelCollisionInverse.lean**: exact reverse collision completion.
  - `patternPolynomial r a` (L16) := sum over tuples with kernel r of Π a_i.
  - `complete_collisions` (L45): injectiveTuplePolynomial a = Π_i Σ_p a_i(p) - Σ_{r≠⊥} patternPolynomial r a. This is Möbius inversion on set partitions (inferred characterisation).
  - `fewer_quotient_labels` (L58), `fewer_singleton_labels` (L69): nontrivial patterns have strictly fewer live labels.
  - `freeze_collision_blocks` (L74).

- **KernelCollisionMass.lean**: central mass of genuine repeated-prime blocks, with at least two slots on one prime.
  - `centralWeight B P` (L18) := B·N(P)^(-1/2).
  - `central_pool_energy` (L29): Σ_{P∈S} centralWeight² ≤ B²·X^δ·rootMass(1+δ).
  - `central_collision_mass` (L48): Σ over collision assignments of Π centralWeight ≤ C·X^ε, uniform in the equality pattern r.
  - `actual_collision_mass` (L91): the same for complex coefficients with |a| ≤ centralWeight.

- **KernelNaturalSlots.lean**: baseline ("native") annular prime slots.
  - `slotTerm χ pool β P I` (L21) := (√P)^(-1)·χ(I)·β(I)·1[I∈pool].
  - `annular_half_weight` (L36): (√P)^(-1) ≤ 2·N^(-1/2) for N ≤ 2P.
  - `slotTerm_bound` (L50): |slotTerm| ≤ centralWeight(2B).
  - `slotTerm_deleted` (L70).
  - `natural_product_completion` (L81): injective family = Π naturalSlot - collisions.
  - `natural_hole_completion` (L92).
  - `natural_collision_mass` (L110): uniform C·X^ε.

### C. Physical rows, scalars, energies and punctures

- **KernelRowPools.lean**: ideal-pair rectangles and divisor pools.
  - `rectangle b X₁ X₂` (L21) := idealBall(bX₁) × idealBall(bX₂). `supportedRectangle S b X₁ X₂` (L61) restricts the primes to S.
  - `residual_rectangle` (L117): the residual pool of a divisor d is the rectangle at scales X_i/N(d_i).
  - `natural_polynomial_finite` (L142): for W supported in (-∞, b], the one-variable Hecke-dyadic polynomial equals a finite sum over the ideal ball of radius bX.
  - `natural_pair_row` (L167): with r ≡ 1, the rectangle row is a product of two one-variable polynomials.
  - `inverse_full_rectangle` (L188), `forward_full_rectangle` (L207): row = Σ_T Σ_{d∈divisorPool} extractedScalar × shorter child row.

- **KernelRowProfiles.lean**: row profiles and normalisation.
  - `pairProfile` (L19) := W₁(N(n1)/X₁)·W₂(N(n2)/X₂).
  - `normalizedRow χ D r W₁ W₂ X₁ X₂` (L53) := (√(X₁X₂))^(-1) Σ_{n∈D} r(n)·χ(n)·pairProfile(n).
  - `extractedScalar χ k d` (L58) := k(d)·χ(d)/√(pairNorm d).
  - `extractedScalar_bound` (L77): |extractedScalar| ≤ |k(d)|/√(pairNorm d).
  - `ordinary_extracted_mass` (L87): ≤ idealPairWeight(f, 1/2)(d).
  - `normalized_extraction` (L61), `forward_profile_row` (L112), `inverse_profile_row` (L136).

- **KernelRowExpansion.lean**: finite divisor reindexing of physical rows.
  - `pairCharacter χ n` (L21) := χ(n1·n2).
  - `finite_row_reindex` (L29): Σ_{n∈D} Σ_{d|n} k(d) r(cofactor) χ(n) f(n) = Σ over divisorPool D of the reindexed sum.
  - `restrictedValue S live n` (L52) := 1[Restricted].
  - `forward_row_expansion` (L57), `inverse_row_expansion` (L126): an unrestricted row equals a sum of rows restricted at live labels.
  - `inverse_restricted_row` (L169), `residualPool_supported` (L105).

- **KernelMarkedRows.lean**: exact restoration of the whole injective marked family.
  - `sourceValue` (L34), `childValue` (L37), `extraction inv S t χ d` (L40).
  - `fixed_profile` (L48): normalizedRow(source) = Σ_{T⊆labels} Σ_{d} extraction(T) × normalizedRow(residualPool d, childValue of the complement).
  - `family_expansion` (L70): weighted sum over injective frozen tuples of Σ_d extraction × remainingSum of child rows.
  - `naturalCoefficients` (L105), `natural_family_expansion` (L111), `natural_rectangle_expansion` (L128).

- **KernelPhysicalScalars.lean**: physical scalars.
  - `extracted_central_bound` (L20): |extracted scalar| ≤ idealWeight(1/2, 1/2).
  - `scalar` (L37), `scalar_bound` (L43): phases excluded, uniform majorant M.
  - `frozenNorm S slot` (L66) := ∏_i N(slot i).
  - `criticalRatio S slot d` (L72) := (N(d2)/(N(d1)·frozenNorm))^(1/6). This is the sixth-root reflection ratio.
  - `reflected_weight` (L80): ForwardCentralMass × criticalRatio = ForwardCriticalMass.
  - `natural_scalar_mass` (L126): uniform in character, zeros, annuli and profiles, ≤ C·X^ε.

- **KernelCommonScalarMass.lean**: one common positive majorant for all physical characters.
  - `weight inv B S slot d` (L18) := (2B)^{|α|} · frozenMass(ordinary/marked series for inv; exponents 1/2, 1/2, 1/2).
  - `scalar_le_weight` (L27): ‖scalar‖ ≤ weight.
  - `weight_subpower` (L37): Σ ≤ C·X^ε.
  - `reflected_weight_subpower` (L71): the same with the extra sixth-root ratio.

- **KernelFamilyEnergy.lean**: physical energy of a family in one positive norm.
  - `Index F D` (L19) := Σ_{t∈F} D(t). `sum_index` (L25).
  - `actual_envelope_energy` (L35): row-independent envelope for the frozen coefficients.
  - `actual_subpower_energy` (L73): for inv in {false, true}, Σ_u ρ_u|Σ_{t,d} scalar·G|² ≤ C·X^ε·E. The per-child energy E is an explicit hypothesis, and the docstring says this is not the final source theorem.

- **KernelReflectedEnergy.lean**: reflected physical aggregation.
  - `variable_physical_energy` (L20): (Σ_u ρ_u|Σ_j F_j(u)|²) ≤ (Σ_j w_j·γ_j)²·E, given ‖F_j‖ ≤ w_j‖G_j‖ and Σ_u ρ_u‖G_j‖² ≤ γ_j²·E.
  - `criticalRatio_sq` (L45): ratio² = (N(d2)/(N(d1)·frozenNorm))^(1/3).
  - `reflected_cost` (L55): 3+q² ≤ (2(1+q))².
  - `actual_reflected_subpower` (L117): with per-child budget E·(3 + ratio^(1/3)), the energy is ≤ C·X^ε·E. The child energy is an explicit input (`actual_reflected_envelope`, L58).

- **KernelActualMass.lean**: top-level absolute masses of the frozen families.
  - `frozenMass S A B s t v slot d` (L20) := idealWeight(B on frozen primes, A otherwise; exponents s, t) · ∏_i N(slot i)^(-v).
  - `ForwardCentralMass` (L108) = frozenMass(K, B-K; 1/2, 1/2; 1/2). `ForwardCriticalMass` (L111) = (K, B-K; 2/3, 1/3; 2/3). `InverseCentralMass` (L114) = (R, M_inv; 1/2, 1/2; 1/2).
  - `fixed_labels_bound` (L32): Σ_d frozenMass ≤ exp(C·rootMass σ)·∏_i K·N(slot i)^(-1).
  - `selected_subpower` (L76): general statement with hypotheses hA (unselected local ≤ 1+C N^(-σ)), hB (marked local ≤ K N^(-u)), and huv: u+v = 1.
  - `forward_central_subpower` (L118): instance (C,K,σ) = (11, 14, 5/2), bound M·X^ε.
  - `forward_critical_subpower` (L135): instance (11, 14, 5/3), exponents (2/3, 1/3, 1/3, 2/3).
  - `inverse_central_subpower` (L153): instance (400, 10206, 3/2).

- **KernelPunctureRows.lean**: exact removal of common ordinary primes (punctures).
  - `augmented S H live P` (L31) := live(P) ∨ (P ∈ H).
  - `correction_truncated` (L23): correction · T = 1.
  - `local_identity` (L34), `augmented_restriction` (L43), `divisor_identity` (L53), `complex_divisor_identity` (L65).
  - `row_expansion` (L90), `normalized_row_expansion` (L125), `actual_scalar_bound` (L146), `full_rectangle` (L152).
  - The docstring says the common puncture is literal avoidance in both ordinary factors.

- **KernelPunctureFamily.lean** (terminal in the group): the whole marked family with punctures.
  - `frozenPrimes S slot T` (L21).
  - `actual_frozen_restriction` (L26), `actual_frozen_disjoint` (L42).
  - `family_expansion` (L53): weighted sum over labels of normalised rows with punctured restricted values.
  - `energy` (L98): Σ_u ρ_u|Σ_d extractedScalar·G|² ≤ C·Z^ε·E, with per-child budget E·(3 + ratio^(1/3)), for fixed F and H dividing F.

- **KernelWholeColumns.lean** (terminal in the group): the fourth-power bridge. This is the only module in the group that contains D⁴.
  - `markedProduct slot` (L22) := ∏_i slot i.
  - `marked_valuation` (L27): the valuation of markedProduct at Q is 1 if Q is a supplying prime and 0 otherwise.
  - `restricted_whole_fifth_free` (L47): if IJ is 5-power-free and no slot prime divides IJ, then IJ·markedProduct is 5-power-free.
  - `labelled_restriction_whole` (L62): the same, starting from Restricted(marked).
  - `element_fifth_free` (L72): an ideal that is 5-power-free gives an element that is FifthFree (in the sense of GaussTransfer).
  - `restricted_gauss_transfer` (L85), full proof read: if span(a) = IJ·markedProduct, then gaussRow a (D⁴·k) = (idealRowHom D (span a))²·gaussRow a k. The proof applies the external `GaussTransfer.normalized_fourth_power`.

---

## 2. Group overview

The group builds exact finite identities for the fifth-power-free restriction and bounds their absolute masses uniformly in the prime pool. The local kernel is K = (1-x)(1-y)·T, with T = Σ_{i+j≤4} x^i y^j, and R = 1/K is its inverse. "Kernel" means this divisor kernel, not a fourth-moment kernel. `KernelIdeal` shows that PowerFree 5 (IJ) = Σ K over divisor pairs, and that 1 = Σ R·indicator.

A supplying ("marked") prime is split into a frozen factor (B-K, or (K-B)R² for the inverse, with B = (1-x)(1-y)) and a live factor (K or R). Since K·O + (B-K)·O = 1 with O = 1/B, sums over allocations collapse exactly to the restricted indicator. Collisions and forbidden holes are removed by exact inclusion-exclusion over set partitions and forbidden sets.

An unselected prime contributes 1 + C·N^(-σ) with σ > 1 (C = 11 at σ = 5/2 or 5/3; C = 400 at σ = 3/2 for the inverse). A selected prime contributes K/N(P), because u+v = 1, so selected primes form a harmonic family costing X^ε. The physical-row files restore each Dirichlet row as Σ_T Σ_d (extracted scalar) × (shorter child row), with reflection ratio (N(d2)/(N(d1)·frozenNorm))^(1/6).

The only fourth-power step is `KernelWholeColumns.restricted_gauss_transfer`: if IJ·Π p_i is 5-power-free, then G(D⁴k) = (idealRowHom D)²·G(k). The three aggregated energy theorems (`KernelFamilyEnergy.actual_subpower_energy`, `KernelReflectedEnergy.actual_reflected_subpower`, `KernelPunctureFamily.energy`) take the per-child energy bound as a hypothesis, so this group does not close the source estimate.

Inputs: `LocalKernels`, `SieveDescent` (rootMass), `SieveCentralReference`, `SexticSieve`, `GaussTransfer`, and unchanged baseline modules.

Outputs: 15 outside modules import group files: Mixed (3), Native (3), Principal (2), Reference (5), Restoration (2). The prefix-to-group reading is inferred from the names. In-group import roots are KernelCollisionEnergy and KernelHoleCompletion; terminal modules are KernelPunctureFamily and KernelWholeColumns. One direct-import chain: KernelFormal → KernelIdeal → KernelIdealMass → KernelReflectedMass → KernelRowProfiles → KernelSelectedMass → KernelSelectedLocal → KernelActualMass → KernelPhysicalScalars → KernelPunctureRows → KernelPunctureFamily.

---

## 3. Where the key constants appear

**Fourth powers (^4, u⁴, "fourth")**
- `KernelWholeColumns.lean:90-92`: `gaussRow a ha (D^4*k) = (idealRowHom D (span a))^2 * gaussRow a ha k`, under the 5-freeness of the whole column. This is the only fourth-power identity in the group. It is a transfer of the form G(D⁴k) = χ-analogue² · G(k), with idealRowHom read as the character analogue (inferred).
- `KernelWholeColumns.lean:4`: the docstring says "actual Gauss fourth-power identity".
- `KernelFormal.lean:27-29`: x⁴ and y⁴ monomials of T. These are degree-4 coefficients, not a power transfer.
- The 5 in PowerFree 5 and the degree-4 truncation are the fifth-free condition that makes the fourth-power identity applicable (`GaussTransfer.FifthFree`, external).

**Sixth powers (^6)**
- No `^6` and no "sixth power" appear in the group.
- Sixth-root exponent 1/6 only: `KernelPhysicalScalars.lean:72-73, 88-89, 96, 106, 115-117` (criticalRatio, reflected_weight); `KernelReflectedMass.lean:104-110, 114` (central_ratio; reflectedMass = centralMass·(2+ratio^(1/6))); `KernelPunctureMass.lean:236-260`, docstring at L251 ("sixth-root length-ratio cost"); `KernelPunctureFamily.lean:115`; `KernelCommonScalarMass.lean:69` (docstring "sixth-root reflected ratio").

**93/25, 43/100, 3/4, the greedy fraction φ**
- Not present. A grep over all 38 files for "93", "43/100", "3/4" and "φ" returned no matches.

**"2 vs 6" slot costs**
- No slot cost of 6 appears. The nearest analogues are:
  - `KernelReflectedMass.lean:116`: reflectedMass = 2·centralMass + idealMass. The 2 counts the two central terms (inferred).
  - `KernelReflectedMass.lean:127`: Σ reflectedMass ≤ 2·exp(11·rootMass(5/2)) + exp(11·rootMass(5/3)).
  - `KernelReflectedEnergy.lean:55, 117` and `KernelPunctureFamily.lean:98`: energy budget 3 + ratio^(1/3), and 3+q² ≤ (2(1+q))².
  - `KernelCommonScalarMass.lean:18-19`: (2B)^{|α|}.
  - `KernelNaturalSlots.lean:50`: |slotTerm| ≤ centralWeight(2B).
- Per-prime costs in this group are K/N(P) for selected primes and 1+C·N^(-σ) for unselected primes. These are not the 2-vs-6 slot widths of the global source.

**"native"**
- `KernelNaturalSlots.lean` (the whole file, docstring L1-4: "Actual baseline natural prime slots"), `KernelPhysicalScalars.lean:126` (natural_scalar_mass), `KernelRowPools.lean:142, 167`, `KernelMarkedRows.lean:105-128`, `KernelCollisionMass`/`KernelNaturalSlots` natural_collision_mass.

**"selected"**
- `KernelSelectedMass.lean:77, 91, 126` (selected_product, selected_ideal_mass, prime_assignments_subpower).
- `KernelSelectedLocal.lean`, `KernelActualMass.lean:76` (selected_subpower).
- `KernelInverseSlotMass.lean:16-18` (Choice: `some` = selected).

**"marked"**
- Pervasive. Key sites: `KernelLabelledSlots.lean:23` (marked = frozen over all labels); `KernelMarkedMass.lean:18` (14 monomials of B-K); `KernelInverseMarkedMass.lean:18` (markedSeries); `KernelAllocationIdentity.lean:78, 107` (forwardFactor with freeze, forward_allocated_identity); `KernelRestrictedState.lean:54` (Restricted with live primes); `KernelMarkedRows.lean:48` (fixed_profile).

**"inverse"**
- R = reciprocalSeries: `KernelFormal.lean:17`. Files: `KernelInverseCoefficients`, `KernelInverseMass`, `KernelInverseIdealMass`, `KernelInverseMarkedMass`, `KernelInverseSlotMass`. Identities: `KernelIdeal.lean:119`, `KernelAllocationIdentity.lean:96, 121`, `KernelLabelledSlots.lean:155`, `KernelActualMass.lean:153`, `KernelRowExpansion.lean:126`, `KernelRowPools.lean:188`.

**"collision"**
- `KernelCollisionEnergy.lean:20, 132, 143`; `KernelCollisionInverse.lean:45`; `KernelCollisionMass.lean:48, 91`; `KernelNaturalSlots.lean:81, 110`.

**Exponent and numeric constants**
- **1/2**: central exponent. `centralWeight` (`KernelCollisionMass.lean:18`); `ForwardCentralMass` (`KernelActualMass.lean:108`); `centralMass` (`KernelReflectedMass.lean:78`).
- **2/3 and 1/3**: critical reflected exponents. `critical_ordinary_weight` (`KernelForwardMass.lean:21`); `idealMass` (`KernelIdealMass.lean:17-46`); `ForwardCriticalMass` (`KernelActualMass.lean:111`).
- **1/6 and 1/3**: the sixth-root ratio and its square. `KernelReflectedEnergy.lean:45` (criticalRatio_sq: ratio² has exponent 1/3).
- **5**: fifth-power freeness. `PowerFree 5` at `KernelIdeal.lean:23`, `KernelWholeColumns.lean:47`. Tails: 1+11z⁵ (`KernelReflectedMass.lean:27-28`); 1+11N^(-5u) (`KernelSelectedLocal.lean:55`); 5/2 (`KernelReflectedMass.lean:63`); 5/3 (`KernelForwardMass.lean:69-70`).
- **11**: nonconstant monomials of K. `KernelForwardMass.lean:19`, with constant 11 at `:69`, `KernelActualMass.lean:127`.
- **14**: monomials of B-K. `KernelMarkedMass.lean:18`; `KernelActualMass.lean:127, 144, 162` (constant K = 14).
- **400 and 3/2**: inverse central constant. `KernelInverseMass.lean:39-40`; `KernelInverseIdealMass.lean:35-37`; `KernelSeriesMass.lean:100-101`.
- **10206 = 14·27²**: `KernelInverseMarkedMass.lean:62-64, 87` (the proof uses `(14*z)*729`). 27: `KernelInverseMarkedMass.lean:54-55`.
- **2/5**: radius for the reciprocal series. `KernelSeriesMass.lean:91-100`; `KernelInverseMass.lean:32-39`; `KernelInverseIdealMass.lean:26`.
- **7**: minimal supported prime norm. `KernelInverseIdealMass.lean:18-19`; `KernelPunctureMass.lean:139`.
- **11/20, 144, 576**: correction radius and constants. `KernelPunctureMass.lean:72-73, 129-137` (576 = 4·144, with 4 = mass(B)).
- **u+v = 1**: hypothesis `huv` in `selected_subpower` (`KernelActualMass.lean:76`). This is what makes each selected prime cost K/N(P).
- **2 in 2^{deg}**: `KernelInverseCoefficients.lean:82` (|R_n| ≤ 2^{deg n}), `KernelInverseMass.lean:23` ((2z)^{i+j}).

---

## 4. Reusable outside this development

Generic lemmas that do not depend on the Gauss or kernel content:
- **Collision and partition counting.** `KernelCollisionInverse.complete_collisions` (L45) is Möbius inversion of injective tuple polynomials over set partitions (inferred characterisation). `KernelNaturalSlots.natural_product_completion` (L81) is the same identity for slot-indexed families. `KernelCollisionEnergy.setoid_card_le` (L132) bounds #Setoid(I) ≤ 2^{K²}. `collision_assignments_mass` (L143) gives a cost depending only on the slot count.
- **Collision moments.** `KernelCollisionEnergy.collision_block_mass` (L20): for |J| ≥ 2, Σ_p Π_{i∈J} v_i(p) ≤ L·B^{|J|}, using two ℓ² energies and sup bounds elsewhere. `weighted_family_energy` (L62) and `sum_family_energy` (L88) are weighted Cauchy-Schwarz bounds for finite families that do not count assignments.
- **Hole completion.** `KernelHoleCompletion.complete_holes` (L62) and `product_partition` (L32) give inclusion-exclusion for forbidden entries, and `KernelAssignmentReindex.split_weighted` (L27) splits injective tuples into frozen and live parts.
- **Labelled reindexing.** `KernelLabelledSlots.labelled_reindex` (L82) identifies admissible 0/1 allocations with subsets of labels.
- **Absolute-mass calculus.** `KernelSeriesMass.mass_mul` (L48) (submultiplicativity of mass under the Cauchy product) and `finite_polynomial_mass` (L59).
- **Euler-product masses over prime sets.** `KernelForwardMass.finite_euler_mass` (L80): ∏(1+C N^(-σ)) ≤ exp(C·rootMass σ). `KernelFixedSupportMass.support_product_subpower` (L25) and `polynomial_support_mass` (L54): ∏ over primes dividing F is ≤ K·N(F)^ε.
- **Harmonic families.** `KernelSelectedMass.prime_assignments_subpower` (L126): Σ over slot maps of ∏ K/N(slot i) ≤ C·X^ε.
- **Recurrence majorants.** `KernelInverseCoefficients.reciprocalCoeff_abs_bound` (L82): |R_n| ≤ 2^{deg n} from a bounded-coefficient recurrence whose nonconstant shifts have degree ≥ 5. The same technique plausibly applies to inverses of other polynomial series with high-degree nonconstant part (inferred).
- **Divisor reindexing.** `KernelAllocationIdentity.divisor_convolution` (L31) and `allocation_expansion` (L67). `KernelRowExpansion.finite_row_reindex` (L29). `KernelRowPools.residual_rectangle` (L117).
- **Weighted Cauchy-Schwarz with variable scale.** `KernelReflectedEnergy.variable_physical_energy` (L20).

Observations for the parent:
- `KernelInverseMass` (docstring) says an O(z³) tail suffices. `KernelInverseCoefficients.reciprocalCoeff_small_degree` (L59) shows R_n = 0 for 0 < deg n < 5, so the tail could be sharpened (inferred from the code; the docstring says a sharper tail is unnecessary).
- Some declaration names repeat across files, which matters if the files are imported together. `idealMass` appears in `KernelIdealMass` (forward, critical) and `KernelInverseIdealMass` (inverse, central). `marked_pool_mass` appears in `KernelMarkedMass` and `KernelInverseSlotMass`. `family_expansion` appears in `KernelMarkedRows` and `KernelPunctureFamily`.
- The energy statements that close the group (`KernelFamilyEnergy.actual_subpower_energy`, `KernelReflectedEnergy.actual_reflected_subpower`, `KernelPunctureFamily.energy`) all take the child-energy bound as an input.
