# H group: Sieve* and Principal* (statement-level map)

Source (read-only): `/tmp/claude-0/-home-user-QuasiRiemannTracker/b22b8f38-5565-550f-b1b7-0bec29e2d6ba/scratchpad/pr74/submissions/sil-fourth-power-20261025/src/Candidate/FourthPower/`

Scope: the 45 files in `lists/H_sieve_principal.txt` (12 Principal*, 33 Sieve*), about 440 declarations. Line numbers "L" are declaration lines in those files.

Method: module headers, and each statement's name, hypotheses and conclusion, extracted from the source. Read in full: `SieveImprovement.lean`, `SieveOptimal.lean`, `SieveExponent.lean` (`completed_of_exponent`), `SievePoissonRecurrence.lean` (`lambda_recurrence`), `PrincipalCubic.lean` (`forced_fourth_power`, `fresh_count`), plus the definitions of `SexticSieve.OptimalBound` and `majorant`, which sit outside H. Import edges come from the `import` lines. Lean and lake were not run.

Checks: no `sorry`, `admit`, `native_decide` or `axiom` declaration in the 45 files. The one textual hit for "axiom" is a word in a comment in `SieveGrowthAlgebra.lean` L4.

Notation:
- theta(A,B) = squaredNorm(freeRange A, freeRange B): rows and columns both sixth-power-free (`SieveRanges.theta`).
- lambda(A,B) = squaredNorm(fullRange A, freeRange B): rows unrestricted, columns sixth-free (`SieveRanges.lambda`).
- "sixth-free" means `PowerFree 6`. N(.) is the absolute norm.
- exponentShape(alpha,M,N) = M + N^alpha + M^(5/6) N^(1/3).
- majorant(A,B) = A + B + A^(5/6) B^(1/3) + A^(1/3) B^(5/6) (`SexticSieve`, outside H).
- referenceMajorant(M,N) = M + M^(1/6) N + M^(5/6) N^(1/3) + M^(1/3) N^(5/6) (`SieveReference` L14).

## 0. Import structure (from `import` lines)

- **Algebra branch:** SieveOperator, then SieveCoupling, SieveGaussPairs, SieveRayCoupling, SievePairPoisson, SieveGcd, SieveInitial, SieveInitialEnergy, SieveRanges, SieveDescent.
- **Poisson branch:** SieveSmoothed (bridge: imports SieveGcd, SieveInitial, SieveRanges), SieveGcdNorm, SievePoissonBound, SieveDualGeometry, SieveColumnGeometry and SieveFrequencyGeometry, SieveBoxFamily, SieveColumnPartition, SieveBandBound, SieveGrowthAlgebra, SievePoissonSeries, SievePoissonRecurrence.
- **Side branch:** SieveWindow, SieveBilinear, SieveUncoupling.
- **Merge and output:** the two branches meet at SieveExponent, then SieveImprovement, SieveOptimal, SieveReference, SieveElementReference, SieveCentralReference, SieveReferenceScales.

## 1. Per-file map

### Principal* (12 files): cancellation between equal-area rectangles, and fixed-inducing rows

- **PrincipalCubic.lean** (93 lines). Fresh squarefree cubic parameter d in a fixed-inducing row A*d^2. It forces a fourth-power divisor. Imports PrincipalExceptional. Used by OuterFreshCount (outside H).
  - `coefficient_cubic` (L17): coefficient(A d^2) = coefficient(A) * idealRowHom(d)^2. Identity.
  - `fresh_element_valuation` (L40): v_P(A d^2) mod 6 = 2, for P | d squarefree and P not dividing A.
  - `forced_fourth_power` (L47): FixedInducingRow(A d^2, z) implies d^4 | sixthRemainder(z) and N(d)^4 <= N(sixthRemainder(z)). It uses the baseline `CenteredExceptionalProfile.actual_forced_fourth_power`, whose source is not in the src tree.
  - `fresh_count` (L68): #rows <= 768 * 6^{omega(Q)} * C^(1/6) * Z^(M/6 - (2/3) delta), when N(d) >= Z^delta and N(z) <= C Z^M.

- **PrincipalExceptional.lean** (90 lines). Actual fixed-inducing family. Combines restricted cancellation with the forced-fourth-power count. Imports PrincipalPhysical.
  - `uniform_energy` (L25), alpha < 4/5: the sum over fixed-inducing rows z of the squared difference of two equal-product rectangle rows is at most 768 * 6^{omega(Q)} * Cr^(1/6) * Z^((R-2g)/6) * (C Z^eps (1+|t1|+|t2|)^J prod_i 256 M_i sqrt(T prod_i P_i) L^(-alpha))^2.

- **PrincipalExtraction.lean** (102 lines). Fractional cost after shortening both ordinary factors. Imports PrincipalKernel.
  - `fractional_cost` (L33): (sqrt n)^(-1) sqrt(T/n) (L/n)^(-alpha) = n^(-(1-alpha)) sqrt(T) L^(-alpha). The saving is 1 - alpha, not 1/2 - alpha.
  - `sum_bound` (L73): |sum_d extractedScalar * G(d)| <= C M sqrt(T) L^(-alpha), given the child inequality. The header says alpha = 7/10 gives a summable mass.
  - `shorter_lower_bound` (L18), `central_shortened_volume` (L26), `pair_weight` (L46), `actual_scalar_cost` (L55): elementary steps.

- **PrincipalKernel.lean** (129 lines). Forward kernel for marked primes: local series B at avoided primes, H5 elsewhere. Imports KernelPunctureRows.
  - `local_identity` (L23): localSeries(avoid) * ordinarySeries = 1 if avoid, else truncatedSeries. Exact.
  - `divisor_identity` (L29): sum over divisors of I and J of kernelOn = 1 if Restricted S live I J, else 0. Exact.
  - `base_local` (L39): sum of localWeight(base) over a finite set T of pairs is at most 4.
  - `ideal_mass` (L57): for sigma > 1/5, sum over d in D of idealWeight(sigma,sigma)(d) <= C Z^eps.

- **PrincipalRows.lean** (140 lines). Exact fixed-puncture centred rows. A common finite outer rectangle makes the divisor sets identical. Imports PrincipalKernel, ReferencePrimeEnclosure.
  - `row_expansion` (L20) and `normalized_expansion` (L46): row = sum_d kernelOn(d) chi(d) (residual sum over the residual pool). Identities.
  - `cutoff_invariance` (L67): enlarging the outer cutoff leaves the normalized row unchanged.
  - `centered_expansion` (L100): the difference over equal-product rectangles expands with identical divisor sets.

- **PrincipalRectangle.lean** (113 lines). All-positive-scale cancellation for equal-product rectangles. Imports baseline HeckeTwist.
  - `fractional_of_two_bounds` (L19): if r <= B T and r <= A (T/L), then r <= (A+B) T L^(-alpha) for 0 <= alpha <= 1. This is a generic interpolation, and it also holds for L < 1.
  - `normalized_fractional_rectangle` (L43): for equal products X1 X2 = Y1 Y2 = T, |(sqrt T)^(-1) (twisted X-rectangle - Y-rectangle)| <= K sqrt(T) L^(-alpha), with K = 4E * 128(b1 M1 + b2 M2) + 2 * 128 b1 M1 * 128 b2 M2 and E the sum of two volumeControl terms.

- **PrincipalRestricted.lean** (164 lines). Literal fifth-free principal cancellation with a common finite puncture. Imports PrincipalRows, PrincipalRectangle, PrincipalExtraction.
  - `polynomial_zero` (L23): the HeckeDyadic polynomial at 0 equals (sqrt X)^(-1) twistedIdealSum(W, 0, X). Identity.
  - `plain_pair` (L41): the normalized pair equals (sqrt(X1 X2))^(-1) times the product of two twisted ideal sums.
  - `restricted_rectangle` (L59), alpha < 4/5: same type of bound, with volumeControl terms and the L^(-alpha) saving. The header says there is no residual analytic-energy hypothesis. The full conclusion was not read.

- **PrincipalUniform.lean** (135 lines). Uniform principal cancellation for fifth-free rows, with two ordinary heights. Imports PrincipalRestricted, baseline NaturalFixedRaySourceDegree.
  - `profile_zero` (L21): normPowerProfile(W) at 0 equals W. Identity.
  - `uniform_rectangle` (L29), alpha < 4/5: |normalizedRow(S,b,X) - normalizedRow(S,b,Y)| <= C Z^eps (1+|t1|+|t2|)^J sqrt(T) L^(-alpha), uniformly over eta, chi, psi with N(chi.modulus) <= Z^B, Q | psi.modulus, InducedBy chi psi.

- **PrincipalMarked.lean** (115 lines). Principal cancellation for the whole injective marked family ("slots"). Imports PrincipalMarkedMass. Used by MixedActualColumns (outside H).
  - `row` (L21): the row sum over injective slot tuples iota -> S.
  - `row_difference` (L27): row(X) - row(Y) = weightedSum over slots of normalized-row differences. Identity.
  - `uniform_marked` (L41), alpha < 4/5: |row(X1,X2) - row(Y1,Y2)| <= C Z^eps (1+|t1|+|t2|)^J (prod_i 256 M_i) sqrt(T prod_i P_i) L^(-alpha).

- **PrincipalMarkedMass.lean** (134 lines). Absolute aggregation of annularly normalized marked coefficients ("slot mass"). Imports PrincipalUniform, KernelMarkedRows.
  - `slot_mass` (L19): sum over atoms of |slotTerm| <= 256 B sqrt(P), when |beta| <= B and pool norms are at most 2P.
  - `prime_slot_mass` (L58): the same, summed over prime slots in S.
  - `weighted_norm_le` (L71): |sum over injective slots of G(slot) prod_i a_i(slot_i)| <= C prod_i sum_p |a_i(p)|.
  - `active_pool` (L93): a nonzero slot product lies in the pools.
  - `support_norm_bound` (L119): N(supportIdeal) <= Z^(2B) when prod_i 2P_i <= Z^B.

- **PrincipalPhysical.lean** (116 lines). Principal cancellation for the literal physical row, with no character-existence hypothesis. Imports PrincipalMarked. Used by MixedExceptionalDictionary (outside H).
  - `character_coefficient` (L35) and `character_off_supported` (L42): idealCoeff chi = coefficient(eta,m,A,z), and it vanishes off supported ideals. Identities under the row hypothesis.
  - `row_eq_character` (L56): the physical row equals PrincipalMarked.row for chi.
  - `uniform_physical` (L67), alpha < 4/5: same bound as uniform_marked, for FixedInducingRow(eta, Q, m, A, z).

- **PrincipalQuantitative.lean** (264 lines). Finite-seminorm version, with constants chosen before the profiles. Imports PrincipalUniform, PrincipalPhysical, baseline FiniteProfileExceptionalNormalize. Used by MixedPrincipalCentered (outside H).
  - `normalized_row_scalars` (L27): normalizedRow(c1 W1, c2 W2) = c1 c2 normalizedRow(W1, W2).
  - `norm_power_reconstruct` (L37): reconstruction of power profiles.
  - `uniform_rectangle_unit` (L54), alpha < 4/5: as uniform_rectangle, with sourceControl(W_i) <= 1 (a source seminorm).
  - `uniform_physical` (L162), alpha < 4/5: bound C (sourceControl W1 * sourceControl W2) Z^eps (1+|t1|+|t2|)^J (prod_i 256 M_i) sqrt(T prod_i P_i) L^(-alpha).

### Sieve* (33 files): a sextic large sieve and its exponent iteration

- **SieveBandBound.lean** (334 lines). Aggregates the dual Poisson family over all columns and one frequency band. Imports SieveColumnPartition.
  - `density` (L17) and `weight` (L21): explicit dyadic weights. density = C L^eps lambda(L,2P) (2P)^eps / P, so a band weight is a product of two lambda-densities.
  - `actual_band_bound` (L221): (sum_x |sum_{i,j coprime} dualTerm|)^2 <= ((#BadLabel)(#Label)^2)^2 * T * (sum |a|^2)(sum |b|^2), for T at least the weight.
  - `fixed_column_band` (L281): the same, with the column scales fixed before the frequency sum.

- **SieveBilinear.lean** (251 lines). Repeated-prime parameters kept in column blocks; bilinear coprime bounds by block operator norms. Imports SieveUncoupling, SieveRanges.
  - `leftBlock_norm` (L37) and `rightBlock_norm` (L49): block embeddings do not increase operator norm.
  - `coherent_coprime` (L65): (sum over u,v,k of |coprime-masked bilinear form|)^2 <= ||A||^2 C N1^eps ||a||^2 * ||B||^2 C N2^eps ||b||^2.
  - `frequency_lambda_bound` (L150): ||frequencyMatrix||^2 <= C L^eps lambda(L,N).
  - `coherent_frequency_bound` (L168): the bilinear bound with lambda(L1,N1) and lambda(L2,N2).

- **SieveBoxFamily.lean** (270 lines). Dyadic-box form of the cross family. Imports SieveColumnGeometry, SieveFrequencyGeometry.
  - `ColumnBox` (L19) and `cost` (L35): repeated and radical parts with scale bounds, and cost(eps,C,B,L).
  - `log_ratio_bound` (L47): |log(X/P)| <= log 2 for P <= X <= 2P.
  - `actual_family_le_box` (L120): the dual cross family on fixed labels is at most boxFamily of the located coefficients.
  - `actual_box_bound` (L228): (sum_k |dual cross|)^2 <= (D/(1+M ||c||^2 K0/(s1 s2))^d)^2 (cost1 sum|a|^2 / s1)(cost2 sum|b|^2 / s2).

- **SieveCentralReference.lean** (242 lines). Sixth-power extraction for centrally normalized coefficients. Imports SieveElementReference.
  - `reducedCoefficient` (L18): a'(J) = a(J D^6).
  - `column_mask` (L23): row_x(J D^6) = row_x(J) 1[(D,x) = 1]. Identity.
  - `reduced_mass` (L91): the reduced mass is at most (A/N(D)^6) N^delta rootMass(1+delta).
  - `root_cauchy` (L123): weighted Cauchy-Schwarz with weights N(D)^(-2).
  - `summed_root_energy` (L139): sum_x |sum_D f_D(x)|^2 <= rootMass(2) rootMass(4) B, when sum_x |f_D(x)|^2 <= B / N(D)^6.
  - `central_reference` (L175): if |a_I|^2 <= A / N(I), then elementEnergy(rows, columns, a) <= C (MN)^eps referenceMajorant(M,N) A.

- **SieveColumnGeometry.lean** (131 lines). Lossless embedding of columns into (repeated part, radical) blocks. Imports SieveDualGeometry.
  - `radical_geometry` (L28): rad(I) is supported and sixth-free, with N(rad I) <= N.
  - `coefficients_mass` (L58): zero-extension preserves sum |a|^2.
  - `pair_extend` (L78) and `blocks_triangle` (L113): reindexing identities for pairs and blocks.

- **SieveColumnPartition.lean** (129 lines). Places each sixth-free column in a dyadic box. Imports SieveBoxFamily.
  - `Label` (L15) = ray label x Fin(columnDyadicLength N + 1). `labels_card` (L99): #Label = 576 (columnDyadicLength N + 1).
  - `fiber_radical_bounds` (L28): scale <= N(rad I) <= 2 scale.
  - `fiber_sharp_bound` (L44): N(sharp I) <= N / scale.
  - `labels_small_power` (L103): #Label <= C N^eps. `fiber_masses` (L115): the fibers partition sum |a|^2.

- **SieveCoupling.lean** (117 lines). Repeated-prime split I = rad(I) sharp(I), with the cross factors of the sextic root-number calculation (header: the character-algebra part of de Faveri Lemma 3.3). Imports SieveOperator, SievePrimitive.
  - `sharp` (L17): sharp(I) = prod_P P^(e_P - 1).
  - `normal_form` (L23): rad(I) sharp(I) = I. `norm_normal_form` (L43): N(rad I) N(sharp I) = N(I).
  - `row_norm_one` (L51): |rowValue(R,I)| = 1 for coprime R and I.
  - `cross_coupling` (L68) and `column_coupling` (L92): rowValue(I, rad J) conj(rowValue(J, rad I)) = phase(ray J.rad, ray I.rad) rowValue(sharp I, rad J) conj(rowValue(sharp J, rad I)). Exact.

- **SieveDescent.lean** (129 lines). Sixth roots in the completed-norm descent. Imports SieveRanges.
  - `roots A` (L14) is the image of fullRange A under sixthQuotient. `root_norm_le` (L28): N(D) <= A^(1/6). `roots_card` (L40): #roots <= 128 A^(1/6).
  - `finite_root_mass` (L53): sum_{D in F} N(D)^(-sigma) <= rootMass(sigma) for sigma > 1.
  - `lambda_scale_descent` (L76): there is R in [1, A^(1/6)] with lambda(A,B) <= rootMass(1+eps) A^eps R theta(A/R^6, B).

- **SieveDualGeometry.lean** (196 lines). Identifies the literal dual Poisson term with the cross kernel. Imports SievePoissonBound, baseline CubicSieve.FrequencyDyads.
  - `dualCoefficient_mass` (L29): ||dualCoefficient||^2 <= ||a||^2 / N(rad I).
  - `dualTerm_cross` (L51): dualTerm(I,J,K) = eta conj(dualCoef I) dualCoef J crossKernel(sharp I, sharp J, rad I, rad J, K) Wtilde(M ||c||^2 N(K) / (N(rad I) N(rad J))). Exact formula.
  - `dualFamily_zero_bound` (L132): |dualFamily(0)|^2 <= ||Wtilde(0)||^2 (sum |a|^2)(sum |b|^2).
  - `poisson_frequency_shells` (L185): pairing(gramMatrix) = M (dualFamily(0) + sum_j sum_{k in dyad j} dualFamily(k)).

- **SieveElementReference.lean** (155 lines). Reference bound on literal Eisenstein elements, including the factors over 2 and 3 and the zero frequency. Imports SieveReference.
  - `elementEnergy` (L17): sum over x in rows of |sum_I a_I rowValue(x,I)|^2.
  - `nonzero_energy_partition` (L38): elementEnergy = sum over labels l in BadLabel(M) of energy(frequencies_l, twisted(factor_l) a). Exact.
  - `nonzero_reference` (L48) and `element_reference` (L117): energy <= C (MN)^eps referenceMajorant(M,N) coefficientMass. The second includes the zero frequency.
  - `zero_energy_le` (L99): the zero-frequency term is at most coefficientMass.

- **SieveExponent.lean** (155 lines). Exponent invariant and its completed-row consequence. Imports SievePoissonRecurrence, SieveDescent.
  - `exponentShape` (L15), `HasExponent alpha` (L17): theta(M,N) <= C (MN)^eps exponentShape(alpha,M,N) for all eps > 0.
  - `HasCompletedExponent alpha` (L21): lambda(M,N) <= C (MN)^eps (M^alpha + M^(1/6) N) for M > 0, N >= 1.
  - `exponent_initial` (L25): HasExponent 2.
  - `mixed_le` (L60): M^(1/3) N^(5/6) <= M^alpha + M^(1/6) N for alpha >= 7/6 and M >= 1. This is weighted AM-GM with weight 1/6, and 7/6 is exactly the threshold (checked by hand).
  - `root_shape` (L95): R exponentShape(alpha, N, M/R^6) <= 2 (M^alpha + M^(1/6) N) for 1 <= R <= M^(1/6).
  - `completed_of_exponent` (L107): HasExponent alpha with alpha >= 7/6 implies HasCompletedExponent alpha. The proof uses sixth-root descent, theta reversal with constant 256, and root_shape. The constant is 512 C (D+1).

- **SieveFrequencyGeometry.lean** (194 lines). Finite bookkeeping for all nonzero frequencies, including 2 and 3. Imports SieveDualGeometry.
  - `badFactor u a b` (L20) = u lambda^a 2^b, with N = 3^a 4^b (lambda is the prime above 3, inferred).
  - `labels_card` (L90): #BadLabel = 6 (columnDyadicLength X + 1)^2. `labels_small_power` (L95): <= C X^eps.
  - `frequency_sum` (L165): sum_{x in R} F(x) = sum_l sum_{K in frequencies_l} F(factor_l K). Exact reindexing.
  - `frequency_geometry` (L174): K in frequencies_l implies Y/||factor||^2 <= N(K) <= X/||factor||^2.

- **SieveGaussPairs.lean** (64 lines). Exact normalized Gauss coupling for two coprime sixth-free ideals. Imports SieveCoupling.
  - `pair_coupling` (L38): pairGauss(I,J) = chi_J^(-1)(-1) phase(I) conj(phase(J)) row_J(I) conj(row_I(J)). Exact.
  - `pair_modulus_norm` (L52): N(modulus I * modulus J) N(sharp I) N(sharp J) = N(I) N(J).

- **SieveGcd.lean** (264 lines). GCD and Mobius descent, adapted from the baseline CubicSieve. Imports SievePairPoisson, baseline CubicSieve.Mobius.
  - `common_mobius` (L43): conj(row_D z) row_D z = sum_{E | D} mu(E) 1[E | z] = 1[(D,z) = 1].
  - `row_divisor_factor` (L50): row_I z = row_D z row_{I/D} z for D | I.
  - `gcd_mobius_descent` (L150): Mobius expansion of the weighted GCD-block sum with descended coefficients. Identity.
  - `nested_divisor_count` (L209): sum over D in S with D | I of tau(D) <= tau(I)^2.
  - `descended_mass` (L225): sum of |descended|^2 <= C B^eps sum |a|^2. The loss is an arbitrary small power.

- **SieveGcdNorm.lean** (125 lines). GCD sorting into concrete coprime norms with an explicit finite maximum. Imports SieveSmoothed.
  - `pairs B` (L17) = {(1,1)} union {(D,E): D in fullRange B, E | D}. `envelope M B` (L20) = max over these pairs of coprimeNorm(M/N(E), B/N(D)).
  - `envelope_attained` (L51): the envelope equals coprimeNorm(M/Delta1, B/Delta2) for some 1 <= Delta1 <= Delta2 <= B.
  - `finite_energy_bound` (L59): sum_z |sum_j row(cols j, z) a_j|^2 <= C B^eps envelope(M,B) sum |a|^2.
  - `lambda_gcd_descent` (L79): lambda(M,B) <= C B^eps envelope(M,B).

- **SieveGrowthAlgebra.lean** (187 lines). Explicit numerical growth algebra for the completed Poisson bound. Imports SieveBandBound, baseline CubicDyadicDecay.
  - `mainCoefficient` (L16) = (2N/M)^alpha N^(alpha-1). `secondaryCoefficient` (L17) = 2 (2N/M)^(1/6) N^(1/6).
  - `coefficients_exact` (L171): M main = 2^alpha M^(1-alpha) N^(2 alpha - 1), and M secondary = 2 * 2^(1/6) M^(5/6) N^(1/3). Identities.
  - `dyadicGrowth` (L114) and `dyadic_growth_sum` (L128): for 1 <= alpha <= 2 and eps < 1/6, sum_j dyadicGrowth(eps,alpha,t,U,V,j) <= K t^(-3 eps) (U+V). The decay is (1+tX)^(-3).

- **SieveImprovement.lean** (192 lines). The sextic exponent iteration, in the pattern of the baseline HeathBrownIteration. Imports SieveExponent. Read in full.
  - `step alpha` (L13) = (12 alpha - 7)/(6 alpha - 1). `enlargement alpha` (L14) = (12 alpha - 8)/(6 alpha - 1).
  - `step_error_le` (L31): step(alpha) - 7/6 <= (5/6)(alpha - 7/6). The fixed point is 7/6 with contraction factor 5/6.
  - `enlarged_shape` (L69): T + shape(alpha,T,N) <= 3 exponentShape(step alpha, M, N), for T = max(M, N^(enlargement alpha)).
  - `improve` (L117): HasExponent alpha with 7/6 < alpha <= 2 implies HasExponent(step alpha). The proof chains completed_of_exponent, lambda_recurrence, estimate_le and enlarged_shape, with eps = min(delta/13, 1/12) and constant 3C(A+1).
  - `exponent n` (L158) and `exponent_error_le` (L167): exponent(n) - 7/6 <= (5/6)^(n+1). `exponent_proved` (L176): HasExponent(exponent n) for all n.
  - `arbitrary_close` (L181): for every delta > 0 there is alpha in (7/6, 2] with alpha < 7/6 + delta and HasExponent alpha.

- **SieveInitial.lean** (192 lines). Initial Polya-Vinogradov control for repeated-prime sextic columns. Imports SieveGcd, baseline QuadraticSieve.InitialBound.
  - `coprime_polya_vinogradov` (L40): |sum_z row_I(z) conj(row_J(z)) W(|z|^2/A)| <= pvControl(W) N(modulus I * modulus J).
  - `masked_coprime_polya_vinogradov` (L82): the same with a factor 2^{omega(D)}. `mask_cost_le_norm` (L104): 2^{omega(D)} <= N(D).
  - `gram_offdiagonal` (L153): for distinct sixth-free I, J with N <= B, |Gram_IJ| <= pvControl(W) B.

- **SieveInitialEnergy.lean** (244 lines). Initial energy bound, adapted from the baseline QuadraticSieve.InitialBound. Imports SieveInitial.
  - `gram_diagonal` (L31): the diagonal Gram term is at most diagonalControl(W) M.
  - `initial_element_bound` (L191): sum_{z in R} |sum_I a_I row_I(z)|^2 <= c (M + N^2) coefficientMass.
  - `initial_ideal_bound` (L220): energy(rows, columns) <= c (M + N^2) coefficientMass. This is exponent 2.

- **SieveOperator.lean** (110 lines). Literal finite operator for the sextic sieve, with reciprocity at a fixed loss. Imports SexticSieve (outside H).
  - `energy_bound` (L36): energy <= squaredNorm * coefficientMass. `bound_iff` (L44): squaredNorm <= K iff for all a, energy <= K coefficientMass.
  - `row_reciprocity` (L75): rowValue(R,I) = phase(ray I, ray R) rowValue(I,R), with |phase| <= 1.
  - `operator_reverse_le` (L79): ||M(rows,cols)|| <= 16 ||M(cols,rows)||. `squaredNorm_reverse_le` (L103): squaredNorm(rows,cols) <= 256 squaredNorm(cols,rows).

- **SieveOptimal.lean** (96 lines). Closes the sextic sieve from the iteration. Read in full. Imports SieveImprovement.
  - `ordered_shape` (L16): for N <= M and alpha <= 7/6 + delta, exponentShape(alpha,M,N) <= 2 (MN)^delta majorant(M,N).
  - `theta_optimal` (L50): theta(M,N) <= 512 C (MN)^eps majorant(M,N) for all M, N >= 1. The case N > M uses theta reversal with factor 256.
  - `optimal_bound` (L87): `OptimalBound` (SexticSieve): for all eps there is C with energy(rows,cols,a) <= C (AB)^eps majorant(A,B) coefficientMass, for sixth-free rows of norm at most A and columns of norm at most B.

- **SievePairPoisson.lean** (268 lines). Poisson summation for coprime sixth-free pairs. The cubic multiplicities 4 and 2 are replaced by e and 6 - e. Imports SieveRayCoupling.
  - `exponents_range` (L54): 0 < e(P) < 6. `inverse_local` (L65): actualSextic^(6-e) = (actualSextic^e)^(-1).
  - `row_identity` (L72): finiteSexticRow(exponents, z) = rowValue_I(z) conj(rowValue_J(z)).
  - `pair_poisson` (L141): sum_z row_I conj(row_J) W(|z|^2/A) = (A pairGauss / ||eis(modulus I modulus J)||) sum_k conj(row(k)) Wtilde(A |k|^2 / ||eis(mod)||^2).
  - `family_poisson` (L238): the finite version, over coprime pairs of columns, with dualTerm.
  - "Principal" here means the row and Gauss sum on the full product modulus (`principalRow` L99, `principalGauss_eq` L112). This is inferred from the definitions.

- **SievePoissonBound.lean** (218 lines). Bilinear interface for the smoothed Poisson family. Imports SieveGcdNorm, SieveWindow.
  - `operator_norm_le_of_pairing` (L31): if |pairing(G,a,b)|^2 <= K^2 sum|a|^2 sum|b|^2 for all a, b, then ||G|| <= K. No Hermitian or positivity hypothesis is needed.
  - `gram_pairing_poisson` (L66): the Gram pairing in Poisson form, with dualTerm.
  - `coherent_weighted_bound` (L148): there are C, D with: the dyadic-box cross kernel with Fourier weight is at most (D/(1+H)^m)^2 (C L1^eps lambda(L1,N1) sum|a|^2)(C L2^eps lambda(L2,N2) sum|b|^2).

- **SievePoissonRecurrence.lean** (208 lines). Returns the full Poisson estimate to the coprime operator norm, and sets up the recursion. Imports SievePoissonSeries. Read `lambda_recurrence` in full.
  - `shape(alpha,M,N)` (L103) = M^(1-alpha) N^(2 alpha - 1) + M^(5/6) N^(1/3). `estimate(eps,alpha,A,M,N)` (L106) = M + A N^(12 eps) M^(-3 eps) shape(alpha,M,N).
  - `matrix_growth` (L43): ||gramMatrix|| <= profile(...), under the completed-growth hypothesis lambda(L,B) <= A (LB)^eps (L^alpha + L^(1/6) B).
  - `coefficients_four` (L108): M (main + secondary) <= 4 shape.
  - `coprime_simple` (L126): coprimeNorm(M,N) <= C estimate(eps,alpha,A,M,N).
  - `lambda_recurrence` (L179): under the same growth hypothesis with constant A, lambda(M,N) <= C N^eps estimate(eps,alpha,A,M,N), for all M, N >= 1.

- **SievePoissonSeries.lean** (326 lines). Attaches the explicit dyadic growth majorant to the Poisson family. Imports SieveGrowthAlgebra.
  - `fixed_dyadic_bound` (L34): fiberBand <= C0 A N^(4 eps) dyadicGrowth(...) sqrt(mass_a mass_b), under the completed-growth hypothesis.
  - `scale_loss` (L156): N^(4 eps) (M/(2PQ))^(-3 eps) <= 2^(3 eps) N^(10 eps) M^(-3 eps).
  - `uniform_fiber_series` (L182): sum_j fiberBand <= C A N^(10 eps) M^(-3 eps) (main + secondary) sqrt(sum|a|^2 sum|b|^2).
  - `all_series_bound` (L269): sum_j wholeBand <= C A N^(12 eps) M^(-3 eps) (main + secondary) sqrt(sum|a|^2 sum|b|^2).

- **SievePrimitive.lean** (113 lines). Primitive Fourier analysis of the sextic row for sixth-free I. Imports SixthDecomposition, baseline GaussSum.ReflectionPool and Moments.Primitive.
  - `exponent` (L23) and `exponent_lt` (L28): multiplicities 1 through 5.
  - `modulus` (L45) = product of the distinct prime factors. `finite_row` (L57): finiteSexticRow = idealRowHom.
  - `phase` (L78): |phase| = 1 (L82). `gauss_transform` (L86): normalizedResidueGauss(k) = conj(row_I(k)) phase(I).
  - `radial_poisson` (L101): the Poisson formula for the sextic row.

- **SieveRanges.lean** (124 lines). Concrete norm functions theta and lambda on the finite families. Imports SieveInitialEnergy.
  - `theta` (L37) and `lambda` (L38): the squared-norm definitions given in the notation above.
  - `theta_le_lambda` (L70). `theta_reverse` (L73): theta(A,B) <= 256 theta(B,A).
  - `lambda_initial` (L86): lambda(A,B) <= c (A + B^2).
  - `lambda_sixth_extraction` (L102): lambda(A,B) <= sum_{D in roots A} theta(A/N(D)^6, B).
  - Header says "the optimal sieve is still open". See section 5.

- **SieveRayCoupling.lean** (101 lines). Finite ray and unit labels for the repeated-prime Gauss coupling. Imports SieveGaussPairs.
  - `unitExponent` (L31) = ((N(I) - 1)/6) mod 6 in Fin 6. `unitPhase e u` (L33) = u^e.
  - `unit_value` (L35): idealRowHom(u, I) = unitPhase(unitExponent I, u).
  - `eta` (L50): a finite-label phase built from unitPhase and SieveOperator.phase, with |eta| <= 1.
  - `labels_finite` (L61): #Label = 576, where Label = Oˣ x Fin 6 x Coord.
  - `gauss_coupling` (L84): pairGauss(I,J) = eta(label I, label J) phase(I) conj(phase(J)) rowValue(J.rad, sharp I) conj(rowValue(I.rad, sharp J)). Exact, with no squarefree hypothesis.

- **SieveReference.lean** (104 lines). Completed-row reference majorant, with sixth powers and natural masks. Imports SieveOptimal.
  - `referenceMajorant` (L14): see notation.
  - `root_reference` (L29): R majorant(M/R^6, N) <= referenceMajorant(M,N) for 1 <= R <= M^(1/6).
  - `lambda_reference` (L44): lambda(M,N) <= C (MN)^eps referenceMajorant(M,N).
  - `ideal_reference` (L91): rows supported with norm <= M (not required sixth-free), columns sixth-free with norm <= N. Then energy <= C (MN)^eps referenceMajorant coefficientMass.

- **SieveReferenceScales.lean** (110 lines). The two length caps after natural reflection. Imports SieveCentralReference.
  - `two_scale_majorant` (L21): referenceMajorant(Z^R, N) <= Z^R (3 + T^(1/3)) if v <= (4/5) R, y <= R/2, N <= Z^v and N <= Z^y T.
  - `two_scale_reference` (L53): elementEnergy <= C Z^(R+eps) (3 + T^(1/3)) A for central coefficients.
  - `norm_of_energy_bound` (L96): ||f|| <= sqrt C Z^((R+eps)/2) (2 + T^(1/6)) sqrt A. `square_root_cost` (L88): 3 + T^(1/3) <= (2 + T^(1/6))^2.

- **SieveSmoothed.lean** (274 lines). Compact smoothing and quantitative GCD descent. Imports SieveGcd, SieveInitial, SieveRanges.
  - `coprimeNorm M N` (L201) = ||operator(gramMatrix(freeRange N, rowMajorant) M)||. It is a concrete norm with no estimate built in.
  - `smoothed_le_coprimeNorm` (L207): the smoothed energy <= coprimeNorm(M,N) sum|a|^2.
  - `quantitative_gcd_descent` (L110): sum_z |sum_j row a_j|^2 <= C B^eps H sum|a|^2. The residual bound H is a hypothesis, so this is a conditional input.
  - `smoothed_poisson` (L140): the smoothed sum = M sum_k sum_{i,j coprime} dualTerm.

- **SieveUncoupling.lean** (150 lines). Uncoupling of the repeated-prime cross kernel. Imports SievePairPoisson.
  - `cross_factor` (L28): crossKernel(U,V,R,T,K) = crossPhase conj(rowValue(K,U)) rowValue(K,V) conj(rowValue(KV,R)) rowValue(KU,T). Exact.
  - `finite_bilinear` (L58): |sum_k w_k f_k g_k|^2 <= (sum|f|^2)(sum|g|^2) for |w_k| <= 1.
  - `product_energy_bound` (L110): sum_{D,K} |sum_I a_I rowValue(DK, I)|^2 <= C L^eps squaredNorm(Qs, columns) coefficientMass.

- **SieveWindow.lean** (184 lines). Uniform separation of the actual radial Fourier weight on dyadic boxes. Imports SieveBilinear.
  - `radial_separation` (L45): for each R > 0 there is a Schwartz b with (1+R)^m int |b| <= C, uniformly in the entries.
  - `separated_family_bound` (L90): |sum_i c_i Wtilde(R exp(w_i - u_i - v_i))| <= (C/(1+R)^m) E.
  - `separated_groups_bound` (L146): the grouped version, with no loss in the number of groups.

## 2. Overview

**What the Sieve files prove.** A sextic large sieve. The objects are operator norms of the row-value matrix rowValue(R, I), with R supported and I sixth-power-free, in two forms: theta (both families sixth-free) and lambda (rows unrestricted, the "completed" form). The cubic machinery (Poisson, Mobius, operator) and the quadratic Gram bound come from the baseline. The cubic multiplicities 4 and 2 are replaced by e and 6 - e (SievePairPoisson). The final statement is `OptimalBound` (SexticSieve), proved by `SieveOptimal.optimal_bound` with constant 512 C and majorant A + B + A^(5/6) B^(1/3) + A^(1/3) B^(5/6).

**The sieve improvement.** `SieveImprovement` is a scalar iteration in the pattern of the baseline HeathBrownIteration. Each step does three things:
1. HasExponent alpha (alpha >= 7/6) gives HasCompletedExponent alpha, via sixth-root descent, theta reversal (256), and the absorption M^(1/3) N^(5/6) <= M^alpha + M^(1/6) N.
2. The completed growth bound feeds the Poisson recursion lambda <= C N^eps estimate(alpha).
3. The result is HasExponent(step alpha), with step alpha = (12 alpha - 7)/(6 alpha - 1).

The fixed point is 7/6, with contraction 5/6. Starting at alpha = 2 (trivial Gram bound), the iteration reaches any alpha < 7/6 + delta in finitely many steps. The threshold 7/6 is where the AM-GM absorption in step 1 works.

**Principal part.** In Principal*, "principal" is the main volume term, which cancels when two rectangles of equal area T are compared. The bound is C Z^eps (1+|t|)^J prod 256 M_i sqrt(T prod P_i) L^(-alpha), with alpha < 4/5 (inferred). Its only fourth-power step is PrincipalCubic: a fresh squarefree cubic d in A d^2 forces d^4 | sixthRemainder(z), and the row count is 768 6^{omega(Q)} C^(1/6) Z^(M/6 - 2 delta/3). "Slots" are injective assignments of marked primes.

**Feeds.** Central coefficients reach the source moment through `central_reference` and `two_scale_reference`, which bound the common-tuple energy by C (MN)^eps referenceMajorant A. These are used by ReferenceConvolution(Energy) and the Kernel mass files. The Principal bounds are imported or called by MixedPrincipalCentered, MixedExceptionalDictionary, MixedActualColumns and OuterFreshCount. These consumers are outside H; I checked only the import lines and a few call sites.

## 3. Exponent constants and what they mean

Summary by constant. The full file-and-line inventory of every rational, integer-power and prefactor literal is in Appendix A.

| Constant | Where it appears | Meaning |
|---|---|---|
| 1/6 | SieveDescent L29, L41, L77; SieveExponent L23, L78, L96-97, L117, L145; SieveReference L15, L24, L30 | Sixth root: N(D) <= A^(1/6), roots_card, and the descent radius R <= A^(1/6). Also the secondary term M^(1/6) N of HasCompletedExponent and referenceMajorant. |
| 1/6 | SieveGrowthAlgebra L17 (secondary coefficient) and many other lines (see A.1; dyadic V-term) | Secondary Poisson term 2 (2N/M)^(1/6) N^(1/6). |
| 1/6 | SieveImprovement L122; SievePoissonRecurrence L43, L88, L126, L179; SievePoissonSeries L37, L109, L182, L269 | Hypothesis eps < 1/6 for the Poisson and growth lemmas. |
| 1/6 | PrincipalCubic L80; PrincipalExceptional L61 | C^(1/6) and Cr^(1/6) from the row count, and Z^((R-2g)/6). |
| 5/6 | SieveExponent L15, L61-66, L75-76, L102; SieveOptimal L22-46; SieveReference L15, L25-38; SieveImprovement L32-184 | Exponent of M in the shape M^(5/6) N^(1/3) and in the majorant A^(5/6) B^(1/3). Preserved by enlargement: enlargement(alpha)(5/6) + 1/3 = step(alpha). |
| 1/3 | SieveExponent L15, L61, L65, L71, L102; SieveImprovement L52, L80, L96; SieveOptimal L22-46; SieveReference L38; SieveReferenceScales L24-98 | Exponent of N in M^(5/6) N^(1/3), and of T in T^(1/3). |
| 7/6 | SieveExponent L60, L67, L95, L107; SieveImprovement L16-182 (fixed point of step); SieveOptimal L16, L22, L29-30 | Fixed point of the iteration and threshold of mixed_le, root_shape and completed_of_exponent. ordered_shape takes alpha <= 7/6 + delta (theta_optimal uses arbitrary_close). |
| 4/5 | PrincipalExceptional L25; PrincipalMarked L41; PrincipalPhysical L67; PrincipalQuantitative L54, L162; PrincipalRestricted L60; PrincipalUniform L29; SieveReferenceScales L22, L56 | Range alpha < 4/5 of the principal saving. In SieveReferenceScales it is the cap v <= 4R/5. The two uses look related but I did not verify a link (inferred). |
| 2/3 | PrincipalCubic L65, L81, L89 | fresh_count exponent M/6 - (2/3) delta, from (M - 4 delta)/6. |
| 1/5 | PrincipalKernel L3, L57 | sigma > 1/5 for finite kernel mass. |
| 1/12 | SieveImprovement L120 | Cap eps <= 1/12 in improve. |
| 1/2 and 7/10 | PrincipalExtraction L4 | Header contrast: the old exponent 1/2 - alpha versus the new 1 - alpha, with alpha = 7/10. |
| 4/2 | SievePairPoisson L3 | Header: cubic multiplicities 4/2 replaced by e and 6 - e. |
| 2 | e.g. SieveExponent L25; SieveRanges L87; SieveInitialEnergy | Initial exponent: theta and lambda <= c (A + B^2). |
| 3 | SieveGrowthAlgebra L115-143; SievePoissonSeries L25-219 | (1+tX)^(-3) dyadic decay, and M^(-3 eps) losses. |
| 4 | PrincipalCubic L55-56; SievePoissonSeries L26-177 | d^4 in forced_fourth_power. N^(4 eps) in Poisson series losses. |
| 6 | everywhere (power-free 6; D^6 in SieveCentralReference, SieveDescent) | Sixth powers: the sixth-free condition, sixth-power extraction D^6, six units of Z[omega]. |
| 10, 12, 13 | SievePoissonSeries (10 eps, 12 eps); SievePoissonRecurrence and SieveImprovement (12 eps); SieveImprovement L134-152 (13 eps) | eps-losses. improve takes eps = min(delta/13, 1/12). |
| 16 | SieveOperator L81, L101, L107 | Operator-norm reciprocity loss, with 256 = 16^2 in the squared form. |
| 128 | SieveDescent L41; SieveInitialEnergy L207; PrincipalRectangle L61-80; PrincipalRestricted L86-97; PrincipalUniform L74-75; PrincipalQuantitative L84-85 | Constants in the normalization of profiles and in roots_card. |
| 256 | SieveRanges L73 (theta reversal); SieveOperator L105-107; SieveExponent L125-145; SieveOptimal L80-81; principal slot constants PrincipalMarkedMass L23-62, PrincipalMarked L71, L106, PrincipalPhysical L95, PrincipalExceptional L62, L73, PrincipalQuantitative L188, L255 | Reciprocity loss for theta and for squared norms. The principal slot constant 256 M_i comes from slot_mass. |
| 512 | SieveExponent L114; SieveOptimal L70, L78 | Constant of completed_of_exponent (512 C (D+1)) and of theta_optimal (512 C). |
| 576 | SieveRayCoupling L61; SieveColumnPartition L99, L105, L112 | 576 = 6 x 6 x 16 labels (inferred: 16 = card Coord). |
| 72 | PrincipalCubic L48, L69; PrincipalExceptional L27 | Conductor bound Q <= span(72), with 72 = 2^3 3^2 (inferred). |
| 768 | PrincipalCubic L80; PrincipalExceptional L61 | Constant 768 = 3 x 256 in the fixed-inducing count. |

## 4. New-looking inequalities and reusable pieces

**New-looking sieve-type statements (not classical restatements):**
1. **Completed norm and completed exponent.** lambda(M,N) <= C (MN)^eps (M^alpha + M^(1/6) N) (`HasCompletedExponent`, SieveExponent L21). It comes from theta by sixth-root descent (`lambda_scale_descent`), theta reversal and `root_shape`. The secondary term M^(1/6) N is distinctive (inferred from the statements).
2. **Sextic exponent step.** step(alpha) = (12 alpha - 7)/(6 alpha - 1), with enlargement (12 alpha - 8)/(6 alpha - 1) and T = max(M, N^enlargement) (SieveImprovement L13-14, L69, L117). It is the sextic analogue of the baseline Heath-Brown step.
3. **Self-improving Poisson recursion.** lambda(M,N) <= C N^eps (M + A N^(12 eps) M^(-3 eps) (M^(1-alpha) N^(2 alpha - 1) + M^(5/6) N^(1/3))) (SievePoissonRecurrence L103-106, L179). The input is the growth constant A and the output is the next exponent.
4. **Exact repeated-prime cross coupling.** I = rad(I) sharp(I), and rowValue(I, rad J) conj(rowValue(J, rad I)) = phase rowValue(sharp I, rad J) conj(rowValue(sharp J, rad I)) (SieveCoupling L68, L92). Finite labels in SieveRayCoupling (`gauss_coupling` L84) carry the unit and phase data.
5. **Pair Poisson with multiplicities e and 6 - e** (SievePairPoisson L54-72). The identity actualSextic^(6-e) = (actualSextic^e)^(-1) replaces the cubic 4/2 split.
6. **Forced fourth power.** d^4 | sixthRemainder(z) from a fresh squarefree cubic parameter, because valuations are 2 mod 6 (PrincipalCubic L40-63). Row count with exponent M/6 - (2/3) delta (`fresh_count`, L68-90).
7. **Two-scale reference majorant.** referenceMajorant(Z^R, N) <= Z^R (3 + T^(1/3)) under v <= 4R/5, y <= R/2 (SieveReferenceScales L21-53). The caps match the exponent bookkeeping (inferred).
8. **Equal-area principal saving.** The shape sqrt(T) L^(-alpha) with alpha < 4/5 (PrincipalRectangle L43; PrincipalMarked L41; PrincipalUniform L29).

**Generic pieces that could be reused elsewhere:**
- `operator_norm_le_of_pairing` (SievePoissonBound L31): operator norm from a bilinear bound, with no positivity hypothesis.
- `bound_iff`, `energy_bound` (SieveOperator L36, L44): squaredNorm <= K iff a quadratic-form bound holds.
- `leftBlock_norm`, `rightBlock_norm` (SieveBilinear L37, L49): block tensorisation does not increase operator norm.
- `finite_bilinear` (SieveUncoupling L58): |sum w f g|^2 <= sum|f|^2 sum|g|^2 for |w| <= 1.
- `root_cauchy` (SieveCentralReference L123): weighted Cauchy-Schwarz with N^(-2) weights.
- `common_mobius`, `row_divisor_factor`, `nested_divisor_count`, `gcd_mobius_descent` (SieveGcd L43, L50, L209, L150): divisor and Mobius identities for character rows.
- `theta_reverse` (SieveRanges L73) and `operator_reverse_le` (SieveOperator L79): reciprocity losses 256 and 16.
- `mixed_le` (SieveExponent L60): weighted AM-GM absorption with threshold 7/6.
- `arbitrary_close` (SieveImprovement L181): any gap delta is reached by a finite iteration.
- `fractional_of_two_bounds` (PrincipalRectangle L19): the volume bound and the first-order saving combine into the L^(-alpha) saving for alpha in [0,1], including L < 1.
- `log_ratio_bound` (SieveBoxFamily L47) and `radial_separation` (SieveWindow L45): dyadic log bounds and uniform Fourier separation.
- `norm_of_energy_bound`, `square_root_cost` (SieveReferenceScales L96, L88): square-root transfer of energy bounds.
- `labels_card` and `labels_small_power` (SieveColumnPartition L99-103; SieveFrequencyGeometry L90-95): dyadic label counts with N^eps cost.
- `frequency_sum`, `exists_representation` (SieveFrequencyGeometry L115-165): exact reindexing of finite frequency sums, including the factors 2 and 3.

## 5. Caveats and checks

- **The fourth-power transfer is not in this group.** The identity G(k u^4) = chi(u)^2 G(k) does not appear in the 45 files. Greps for "fourth", "^4" and "u^4" found only comments, the d^4 in PrincipalCubic (L55-56), and N^(4 eps) exponents. The unit phases here are u^e with e = ((N(I) - 1)/6) mod 6 (SieveRayCoupling L31-35). That is the sextic residue symbol at units (inferred).
- **"Principal" has two meanings.** (a) In Principal*, it is the main-term cancellation for equal-product rectangles (inferred from the bounds). (b) In SievePairPoisson, `principalRow` and `principalGauss_eq` (L99-114) are the row and Gauss sum on the full product modulus modulus(I) modulus(J). No principal character object is defined in these files.
- **Conditional lemmas.** `quantitative_gcd_descent` (SieveSmoothed L110) takes the residual bound H as a hypothesis. `matrix_growth`, `coprime_simple`, `lambda_recurrence`, `fixed_dyadic_bound` and `all_series_bound` take the completed-growth hypothesis with constant A. `improve` discharges that hypothesis through `completed_of_exponent`, so the exponent chain is unconditional. The Principal statements carry explicit hypotheses (FixedInducingRow, the primeSupport restriction), which belong to their statements.
- **Stale module-scope comment.** The `SieveRanges` header says "the optimal sieve is still open". `SieveOptimal.optimal_bound` proves it, so the comment is only true for the module's own scope.
- **Meaning of "optimal".** Here it means exponent 7/6 + delta, up to (MN)^eps. It is not a claim about the best constant.
- **Consumers outside H** (import lines, plus a few call sites checked): OuterFreshCount (PrincipalCubic), MixedActualColumns (PrincipalMarked), MixedExceptionalDictionary (PrincipalPhysical), MixedPrincipalCentered (PrincipalPhysical, PrincipalMarked, PrincipalQuantitative), KernelCollisionMass and KernelForwardMass (SieveCentralReference), ReferenceConvolution (SieveCentralReference, SieveReference), ReferenceConvolutionEnergy (SieveReferenceScales).
- **Not verified:** Lean was not run. The source of `actual_forced_fourth_power` (baseline) was not located in the src tree. The full conclusion of `restricted_rectangle` (after its `let E`) was not read. Items marked "(inferred)" were not read directly.

## Appendix A. Literal inventory (generated by grep, 45 files)

Format: constant: file(lines). Lines are 1-based. "2026" (copyright year) is excluded. The integer power `^2` (about 250 occurrences, squared norms) is omitted.

### A.1 Rational literals p/q
- 1/12: SieveImprovement(120) 
- 1/2: PrincipalExtraction(4) 
- 1/3: SieveExponent(15,61,65,71,102) SieveGrowthAlgebra(173) SieveImprovement(52,80,80,96) SieveOptimal(22,24,27,31,36,36,38,40,44,45,46) SievePoissonRecurrence(104,123,165) SieveReference(15,15,25,26,36,38) SieveReferenceScales(24,34,36,38,38,40,40,42,44,44,45,46,61,82,84,89,90,98) 
- 1/5: PrincipalKernel(3,57) 
- 1/6: PrincipalCubic(80) PrincipalExceptional(61) SieveDescent(29,41,77) SieveExponent(23,61,71,71,75,75,76,76,78,79,96,97,117,145) SieveGrowthAlgebra(17,17,19,23,26,41,42,42,42,52,60,67,84,94,96,115,119,120,120,128,135,136,138,143,144,145,156,156,160,160,164,164,173,183,183) SieveImprovement(122) SievePoissonRecurrence(43,47,88,92,115,117,126,130,179,183) SievePoissonSeries(37,109,113,182,186,269,273) SieveReference(15,24,30) SieveReferenceScales(27,29,32,32,89,90,93,99) 
- 2/3: PrincipalCubic(65,81,89) 
- 4/2: SievePairPoisson(3) 
- 4/5: PrincipalExceptional(25) PrincipalMarked(41) PrincipalPhysical(67) PrincipalQuantitative(54,162) PrincipalRestricted(60) PrincipalUniform(29) SieveReferenceScales(22,56) 
- 5/6: SieveExponent(15,61,65,66,75,76,102) SieveGrowthAlgebra(173) SieveImprovement(32,52,57,80,80,96,167,172,173,173,183,184,184) SieveOptimal(22,24,26,27,31,36,36,38,40,44,45,46) SievePoissonRecurrence(104,123,165) SieveReference(15,15,25,26,36,38) SieveReferenceScales(34,36,38,38,40,42,44,45) 
- 7/10: PrincipalExtraction(4) 
- 7/6: SieveExponent(60,67,95,107) SieveImprovement(16,17,17,24,24,27,28,31,32,32,35,37,41,51,60,69,117,162,167,172,182,182) SieveOptimal(16,22,29,30) 

### A.2 Integer exponent literals (^k, ^(k*...)), excluding ^2
- 1: SieveReferenceScales(29) 
- 10: SievePoissonSeries(158,172,192,219,290,312,320) 
- 12: SieveImprovement(100,103,106,108,108,110,138,146,150) SievePoissonRecurrence(34,81,106,141,144,146,173) SievePoissonSeries(279,312) 
- 13: SieveImprovement(134,138,148,152) 
- 3: SieveGrowthAlgebra(115,116,119,143) SievePoissonSeries(25,26,26,86,93,94,158,166,177,177,196,219) 
- 4: PrincipalCubic(55,56) SievePoissonSeries(26,44,100,121,143,144,146,153,158,166,172,177) 
- 6: PrincipalCubic(21,21) PrincipalPhysical(23) SieveCentralReference(18,24,37,43,97,101,104,106,115,116,141,148,201,210) SieveCoupling(53) SieveDescent(21,36,67,77,78,82,83,88,99,101,122) SieveExponent(83,85,87,89,97,121,122,123,124,125,127,129,135,136,138,139,142,142,144,144) SieveGcd(29) SievePoissonSeries(172,177) SieveRanges(104,112) SieveReference(31,57,58,59,60,61,65,70,72,73,75,75,77,77) 

### A.3 Prefactor literals 16, 72, 128, 256, 512, 576, 768
- 128: PrincipalQuantitative(84,85,85) PrincipalRectangle(61,61,61,68,69,69,80,80) PrincipalRestricted(86,86,86,97,97,97) PrincipalUniform(74,75,75) SieveDescent(41) SieveInitialEnergy(207) 
- 16: SieveOperator(81,101,107) 
- 256: PrincipalExceptional(62,73) PrincipalMarked(71,106) PrincipalMarkedMass(23,39,54,55,62) PrincipalPhysical(95) PrincipalQuantitative(188,255) SieveExponent(125,142,144,145) SieveOperator(105,107) SieveOptimal(80,81) SieveRanges(73) 
- 512: SieveExponent(114) SieveOptimal(70,78) 
- 576: SieveColumnPartition(99,105,112) SieveRayCoupling(61) 
- 72: PrincipalCubic(48,69) PrincipalExceptional(27) 
- 768: PrincipalCubic(80) PrincipalExceptional(61) 
