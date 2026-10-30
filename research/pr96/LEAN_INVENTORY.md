# Lean inventory toward the two-slot probe (PR #96 style)

Survey date 2026-10-30. Read-only: grep/find/reading only, no `lake build`, nothing edited outside this folder.
Helper files in this folder: `decls.tsv` (index of all 25,914 declarations of `DL/`: file, line, namespace, kind, name),
`index_decls.py`, `idx.py`, `import_graph.py`, `sinks.py`, `graph.json`.

## 0. Paths, size, and how the OAI proof is wired

Abbreviations used below.
- `DL/`  = `/home/user/lean-env/qrh/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/`
  (symlink to `/home/user/QuasiRiemannTracker/submissions/openai-baseline/src/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/`; use `grep -R`).
- `HC/`  = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/`  (Collet's refinement of OAI; same probe, other parameters).
- `SIL/` = `/home/user/lean-env/qrh/Submissions/arvi_repeated_marks_on_sil_face_20261025/`  (Sil's fork + Arvi additions).

Size of `DL/`: 2,926 files, 486,558 lines, 13.8k theorems + 6.8k lemmas + 4.8k defs. Files per folder (lines): Moments 679 (83k),
Descent 419 (42k), Detector 414 (42k), Reflection 266 (23k), Energy 208 (27k), PrimeRows 182 (18k), Hecke 182 (21k), Inversion 155 (24k),
CubicSieve 91 (37k), Eisenstein 82 (53k), Dictionary 42 (5k), QuadraticSieve 36 (24k), GaussSum 34 (23k), MeanSquare 18 (11k),
RowCompletion 15 (9k), Mellin 11 (8k), Poisson 8 (5k), Arithmetic 7 (5k), Reciprocity 6 (4k), Cusp 5 (3k), PrimeCounting 5 (1k), Fourier 4, ChineseRemainder 3;
54 top-level files (11k). Almost no docstrings (3 `/-!`). Namespaces are not file names (`OAI.ActualEisensteinCubic`, `OAI.CompletedGauss`,
`OAI.CanonicalRowCompletion`, `OAI.CubicKubota`, `OAI.CubicEisenstein`, `OAI.SevenEighths.*`, ...). `grep` finds no `sorry`/`axiom` in `DL/`
(an earlier session, `research/round11/tau_average_scope.md`, ran `#print axioms` on the main theorems: only propext/Classical.choice/Quot.sound).
`.olean` files exist in `/home/user/lean-env/qrh/.lake/build` for the two sibling files cited in section A.

Base objects. `O := HeckeFamily.O := ActualEisensteinCubic.O := 𝓞(CyclotomicField 3 ℚ)` (`DL/Hecke/Family.lean`), `eisEmbedding : O →+* ℂ`
(`ConcreteTraceCRT`), `lambda = 1 - ω`, `goodLambda`, `primaryGenerator (I : Ideal O) : O` (`DL/Arithmetic/IdealMobius.lean:232`),
`Supported I` (`DL/QuadraticSieve/DivisorBlocks.lean:309`: `I ≠ 0 ∧ ∀ P ∈ normalizedFactors I, lambda ∉ P ∧ ringChar (O⧸P) ≠ 2`, i.e. coprime to 6, not necessarily squarefree).

Wiring of the OpenAI proof (the probe-specific part is what a new probe would replace).
1. `DL/Nonvanishing.lean` `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (Dirichlet), `DL/Hecke/Nonvanishing.lean:13`
   `HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re (χ : Character) (hs : 7/8 < s.re) (hpole : ¬(χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0`
   (all finite-order Hecke characters of F with trivial infinity type). Dirichlet follows from Hecke via
   `Hecke/Dirichlet.lean` `LFunction_eq_dirichlet_product : L(character χ, s) = L(χ,s)·L(χ·χ_{-3},s)`.
2. `DL/Detector/FinalAssemblyUnconditional.lean:15` `detector_certified_bands` → `FinalAssemblyCertifiedBands.lean` `chosen_moments_of_certified`
   → `FinalAssemblyChosenData.lean:57` `common_probe_of_chosen_moments : ChosenMomentInput → HeckeCommonProbe.UniformCommonProbe`.
3. Probe definition: `DL/Detector/Physical.lean` (`sexticGauss`, `markedPhysicalProbe`, `compensatedPhysicalProbe`), `Detector/FinalAssemblySource.lean`
   (`normalizedProbe`, `normalizedProbe_low : probe = O(Z^{3/16+loss})`). The probe is `Σ_s Σ_{m∈O} (calibrated numerator)(m)·sexticGauss(s,-m)·W₀(N m/..)·(1/2πi)∫ Z^t e^{t²} spectralRow(t)`,
   with `spectralRow` the completed cubic-theta (Patterson-type) row `Σ_{I,J} columnWeight(I)/√N(I)·cubeWeight(J)·N(I)^{-t}N(J)^{-3t}` and prime "marks/slots" = amplifier pools `pool … (Yp j)` with windows `W j`.
4. High side (probe = signal + error): `DL/PrimeRows/HighFromMoments.lean:18` `actual_high_probe_from_raw_moments`:
   `‖compensatedPhysicalProbe … / normer − HeckeSignal.signal (η.excludePrimes S _) (sourceCorrection η S) (-11/16) Z‖ ≤ (Ct + C·C0·N(η.modulus)^{2·eps})·Z^{β − 11/16 − σ}`.
5. Moment/energy inputs (`SourceMomentBound`, `CountParameters`, `RawMomentInput`) are produced by the huge Moments/Energy/Descent/Reflection/Inversion/Dictionary stack (1,769 files, about 205k lines).
   This stack, `Detector/` and `PrimeRows/` are bespoke to OAI's single sextic Poisson slot with Möbius-weighted rows.

---

## 1. OpenAI's continuation criterion — EXISTS (θ = 7/8 hard-wired in DL; θ-parametrized copy in HC)

Generic analytic core (no Hecke): `DL/Continuation.lean:130`
```
theorem nonzero_of_common_signal (β ω σ c : ℝ) (hω : 0 < ω) (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
  (hL : AnalyticOnNhd ℂ Lregular {s | β - Supremum.continuationMargin β ω σ < s.re}) (hR : …) (hH : AnalyticOnNhd ℂ H {s | 7/8 < s.re})
  (hcontract : ∀ s, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) (hlocal : LocallyIntegrableOn f (Ioi 0)) (hzero : RapidDecayAtZero f)
  (hJ : J =O[atTop] x^(7/8 + c + ω)) (herror : (J - f) =O[atTop] x^(β + c - σ))
  (heq : ∀ s, max (β - margin) 1 < s.re → Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
  {ρ} (hρ : β - margin < ρ.re) (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0
```
(`gaussianMultiplier H s = exp((s-5/6)^2)·H s`; helper files `ContinuationContour/Inversion/PolynomialContour/ShiftedGaussian.lean`, `Supremum.lean`: `continuationMargin β ω σ = min (β-7/8-ω) σ`, `seven_eighths_of_uniform_margin`.)

Hecke specialization: `DL/Hecke/SignalIdentity.lean:103`
`HeckeSignal.nonzero_of_probe_bounds (χ : Character) (H) (J) (β ω σ c) … (hJ : J =O x^(7/8+c+ω)) (herror : J - signal χ H c =O x^(β+c-σ)) … : LFunction χ ρ ≠ 0`
with `signal χ H c x = x^c · mellinInv (-2) (s ↦ exp((s-5/6)^2) H(s)/L(s,χ))` (`Hecke/Signal.lean`, growth in `Hecke/SignalBounds.lean`, `SignalShift.lean`, `ReciprocalGrowth.lean`).

Interface a new probe must fill: `DL/Hecke/CommonProbe.lean:13,23`
```
def PrimitiveContract (ω σ) := ∀ η, IsPrimitiveOnIdeals η.residue → ∃ χ H J,
   (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧ AnalyticOnNhd ℂ H {7/8 < re} ∧ (∀ s, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
   ∧ J =O x^(3/16+ω) ∧ (J - signal χ H (-11/16)) =O x^(beta - 11/16 - σ)
def UniformCommonProbe := 7/8 < beta → ∃ ω σ, 0 < ω ∧ ω < beta - 7/8 ∧ 0 < σ ∧ PrimitiveContract ω σ
theorem beta_le_seven_eighths (h : UniformCommonProbe) : beta ≤ 7/8       -- line 27
theorem hecke_ne_zero_of_common_probe / dirichlet_of_common_probe / zeta_of_common_probe   -- lines 47, 52, 61
```
`beta = sSup (insert (1/2) {Re ρ : L(ρ,χ)=0, χ : Character})` (`Hecke/ZeroSupremum.lean`), reduction to primitive zeros `Hecke/PrimitiveSupremum.lean`
(`exists_primitive_zero_near_beta`) and `Hecke/FiniteDeletion.lean` (`exists_primitive_same_zeros`, `LFunction_eq_of_mask`).

θ-PARAMETRIZED VERSION (outside DL, needed for a target 1049/1250 < 7/8): `HC/Cycle25/Assembly/Continuation.lean` (172 lines, no sorry):
```
def PrimitiveProbeContract (θ c ω σ : ℝ) : Prop := ∀ η primitive, ∃ χ H J, mask ∧ AnalyticOnNhd ℂ H {θ < re} ∧ (∀ s, θ < s.re → ‖H s-1‖ ≤ 1/2)
      ∧ J =O x^(θ+c+ω) ∧ (J - HeckeSignal.signal χ H c) =O x^(beta+c-σ)
def UniformCommonProbe (θ c : ℝ) : Prop := θ < beta → ∃ ω σ, 0<ω ∧ ω<beta-θ ∧ 0<σ ∧ PrimitiveProbeContract θ c ω σ
theorem beta_le_of_common_probe (hθ : 1/2 ≤ θ) (hθ7 : θ ≤ 7/8) (h : UniformCommonProbe θ c) : beta ≤ θ
theorem hecke_ne_zero_of_common_probe / dirichlet_of_hecke / zeta_of_hecke
```
(also `Cycle25.nonzero_of_probe_bounds`, `continuationMargin θ β ω σ`; an older copy `WeightedQRH.UniformCommonProbe (θ c)` in
`HC/Record1252270103Bootstrap/PR67Weighted/WeightedQRH/Continuation.lean:113`.) Collet's final consumer: `HC/Record1252270103Return/Transport/FinalCommonProbe.lean`
(`common_probe_of_finite_numerator : … → Cycle25.UniformCommonProbe theta signalShift`).

Limitations.
- Only `HeckeFamily.Character` (`DL/Hecke/Family.lean`): `modulus ≠ ⊥`, `residue : MulChar (O ⧸ modulus) ℂ`, `unit_trivial : ∀ u : Oˣ, residue u = 1`. No infinity type, so no angular character.
  `beta`, `LFunction`, `signal`, `reciprocal` bounds, `exists_primitive_zero_near_beta` all quantify over this class only.
- 7/8 is a literal in about 87 files of DL (including the Euler-product correction `sourceCorrection_bound : ‖H-1‖ ≤ 1/2 on Re s > 7/8`, `PrincipalSignalComparison.lean`). HC's `Cycle25` fixes this for the abstract criterion only; the Euler correction `H` for Re s > θ must come from the probe (HC re-proves it for its own θ ≈ 0.8747).
- The probe has to be given with `J` for *every* primitive η, with the high-side bound `x^(beta+c-σ)` uniform in terms of the global supremum `beta` (the OAI proof uses that no family member has a zero to the right of beta to bound bad rows).
- The Gaussian multiplier centre 5/6 and the shift c = -11/16 (DL) / free c (HC) are conventions only.

---

## 2. Poisson summation over O with residue-symbol twists / Gauss sums — EXISTS (general; squarefree conductors for the Kummer-specific form)

Plain lattice Poisson over the Eisenstein lattice (Mathlib `Real.fourierChar`, Schwartz functions on ℂ):
- `DL/Poisson/EisensteinLattice.lean:125` `affine_lattice_poisson (f : 𝓢(ℂ,ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ)`, `:307` `actual_eisenstein_periodic_poisson`, `actual_eisenstein_coset_poisson`, `actual_radial_poisson`, `gauss_transform_finite_ideal_crt`.
- Universal twisted form (any function `P` on `O/(c)`): `DL/GaussSum/SexticRadialPoisson.lean:387`
  `EisensteinSchwartzPoisson.actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ,ℂ)) (c : O) (hc : c ≠ 0) (P : O ⧸ span{c} → ℂ) :
     ∑' z, P (z mod c) * f (eisEmbedding z) = (1/‖c‖²) • ∑' h, (∑ r, P r * ψ_c(h r)) * paperFourier f (h/c)`;
  radial version `:499` `actual_radial_paper_poisson_trace` (W : 𝓢(ℝ,ℂ), argument `‖z‖²/K`, dual `paperRadialFourier W (K‖h‖²/‖c‖²)`), compact-support version `:541`.
- Multiplicative twist by a primitive character: `DL/TraceCharacter.lean:106` `primitive_paper_poisson (f : 𝓢(ℂ,ℂ)) (χ : MulChar (O⧸span{c}) ℂ) (hχ : IsPrimitiveOnIdeals χ) :
  ∑' z, χ z * f z = (gaussScalar c χ / N(c)) * ∑' h, χ⁻¹ h * paperFourier f (h/c)`, `:149` `primitive_radial_paper_poisson_normalized`;
  arbitrary residue character mod M through its primitive presentation (conductor, norm_le, `source_mask`): `DL/TraceConductor.lean:110,118`
  `PrimitivePresentation.paper_poisson`, `.radial_paper_poisson`; existence `exists_primitivePresentation`, `ConductorPresentation.exists_primitive_presentation`.
- Kummer-symbol specific (the sextic/cubic/quadratic "slot"): `DL/GaussSum/SexticRadialPoisson.lean:732`
  `ActualEisensteinCubic.canonical_radial_poisson_normalized {ι} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hcop : Pairwise IsCoprime) (hgood : ∀ i, lambda ∉ P i)
     (hchar : ∀ i, ringChar (O⧸P i) ≠ 2) (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (W : 𝓢(ℝ,ℂ)) (scale) :
     ∑' z, finiteSexticRow P hgood j z * W(‖z‖²/scale) = (scale·canonicalNormalizedGauss P hcop hgood j/‖c‖) * ∑' h, star (finiteSexticRow P hgood j h) * paperRadialFourier W (scale‖h‖²/‖c‖²)`,
  with `finiteSexticRow P hgood j a = ∏ᵢ (canonicalSextic (P i) ^ (j i)) (a mod P i)`. Exponent `j i = 1` gives sextic, `2` cubic, `3` quadratic, `4,5` conjugates, so the cubic slot is already covered.
  Also `:773` compact-support variant, `:831` `canonical_disjoint_pair_radial_poisson` (two rows on disjoint prime sets), `GaussSum/CubicTrace.lean` `canonical_radial_poisson_product`,
  `finiteSquarefreeRow_pair_radial_poisson_product`, `GaussSum/MixedConversion.lean` `moebius_pair_radial_poisson_converted`.
- Probe-level Poisson (arbitrary modulus `s`, calibrated numerator with a residue character mod `C.generator`): `DL/Detector/PhysicalPoisson.lean:39`
  `ProbePhysical.physical_row_poisson : ∑' m, calibratedNumerator C A m * sexticGauss s hs (-m) * W(N m/K) = (K/N(C.generator·A)) * ∑' H, actualCongruenceCoefficient C A s hA H * paperRadialFourier W (K N(H)/N((C.generator·A)·s))`.
- Gauss-sum pair correlation: `DL/Moments/Poisson.lean:99` `CenteredMomentPoisson.sextic_gauss_pair_poisson (u v) (Supported …) (W) (K)`.
- Local finite-field transforms: `transform_eq : ∑ x, χ x ψ(a x) = χ⁻¹ a · gaussScalar` (`TraceCharacter.lean:52`, primitive χ), `canonical_finite_prime_gauss_transform*`
  (`GaussSum/SexticRadialPoisson.lean:58–207`), `gauss_transform_finite_ideal_crt`, bracket (exceptional exponents) `CubicSieve/LocalBrackets.lean:437`.

Bad primes / local factors.
- The Kummer-specific form requires every prime coprime to 6 (`lambda ∉ P i`, `ringChar ≠ 2`) and distinct primes (squarefree modulus). Non-squarefree or non-coprime-to-6 moduli
  go through (a) `PrimitivePresentation` (arbitrary M, plus an explicit coprimality mask `source_mask`), (b) `sexticGauss s hs h` (any `s ≠ 0`, defined via the ideal symbol), (c) `GaussSum/PowerfulParts.lean` (powerful/simple split of rows).
- 2-part: `Detector/Phase.lean` `G a := fixedGQuotientValue (a mod 4)`, cocycle `G_mul`, `QuadraticGaussRay`, `quadraticGammaO_formula`, `quadraticGammaTraceLambda_eq_I`.
- λ-part (3): `GaussSum/RamifiedTracePhase.lean`, `Reciprocity/RamifiedSymbol.lean`, ramified tables for theta coefficients (`Eisenstein/RamifiedGaussSeries.lean`, `RamifiedSixBranches.lean`).
- Finite sets of excluded ("source") primes: `Hecke/ModulusRefinement.lean` `Character.excludePrimes`, `PrincipalSignalComparison.sourceCorrection`, `Detector/Local.lean` (`localFactor`, `continuedCorrection`), `Hecke/FiniteEulerFactors.lean`.
- Missing: Poisson with ∞-type test functions (z/|z|)^k·W(|z|²): general `paperFourier f` is there, but the Hankel/J-Bessel transform of an angular profile is not (`paperRadialFourier` is radial only; no "Hankel", "BesselJ", harmonic polynomial anywhere).

---

## 3. Cubic and sextic symbols, reciprocity, Gauss sums — EXISTS (symbols/reciprocity/Gauss sums); no sextic Kubota cocycle

Symbols.
- Local: `DL/GaussSum/FiniteFourier.lean:566` `cubicChar P hgood : MulChar (O⧸P) O` (Euler-criterion `cubicChar_reduce : ≡ x^((NP-1)/3) mod P`, `cubicChar_order`), `:786` `quadraticCharO`,
  `:801` `sexticChar P hgood := cubicChar^2 * quadraticCharO` with `sexticChar_powers : ^2 = cubicChar ∧ ^3 = quadraticCharO ∧ ^6 = 1`; complex version
  `DL/Arithmetic/EisensteinEmbedding.lean:461` `canonicalSextic P hgood : MulChar (O⧸P) ℂ` (`canonicalSextic_pow_six`, `_pow_ne_one`, `_pow_two`, `_pow_three_quadratic`).
- Global cubic Jacobi symbol (values in O): `DL/Reciprocity/CubicJacobi.lean` `primeValue`, `idealSymbol (I : Ideal O) (x : O)`, `symbol x y := idealSymbol (span y) x`, `idealSymbol_mul`, `symbol_mul_denominator`, `idealSymbol_congr`.
- Global sextic symbol on ideals: `DL/Eisenstein/CompactEnergyFamilies.lean:466,484` `localRowValue`, `idealRowHom x : Ideal O →*₀ ℂ` (= (x/I)₆ for I coprime to 6, 0 otherwise; `idealRowHom_prime`, `idealRowHom_norm ≤ 1`).
Reciprocity.
- Cubic: `Reciprocity/CubicJacobi.lean:202` `symbol_reciprocity (a b) (ha hb : ≠ 0) (λ²∣a-1) (λ²∣b-1) : symbol a b = symbol b a`; `:176` `idealSymbol_reciprocity (I J) : idealSymbol I (primaryGenerator J) = idealSymbol J (primaryGenerator I)`;
  prime-level `GaussSum/SquarePhaseFactorization.lean:274` `cubic_reciprocity_primary`; supplements for λ, 3, ω, 2, 7: `Reciprocity/CubicJacobi.lean` (`supplement_case00…22`, `cubicValue_lambda_primary`, `ramified_comparison`), `Reciprocity/RamifiedSymbol.lean` (`symbol_traceLambda_eq_linearRay`, mod-9 periodicity).
- Sextic: `Eisenstein/ConjugateLevelAction.lean:668` `idealRowHom_ideal_reciprocity (I J) (hI : Supported I) (hJ : Supported J) :
  idealRowHom (primaryGenerator J) I = sexticReciprocityPhase (primaryGenerator I) (primaryGenerator J) * idealRowHom (primaryGenerator I) J` (also `:522` primes, `:607`, `:634` primary elements, `:660` ray form);
  `sexticReciprocityPhase a b = quadraticRaySign (residue a) (residue b)` = ±1 depending on residues mod 4; `Detector/Phase.lean` `reciprocitySign_sq`, `Detector/PairPhase.lean` `sexticPair_cube`, `completed_pair_phase`.
Gauss sums (finite-field level uses Mathlib `gaussSum`, `jacobiSum`).
- Values / norms: `TraceCharacter.lean:67–85` `gaussScalar_norm_sq (primitive χ) : ‖g‖² = N(c)`, `normalizedGauss_norm = 1`; `GaussSum/MixedConversion.lean` `norm_localGauss` (|g̃_j| = 1, 0<j<6, p odd);
  cubic: exact cube of the cubic Gauss sum `GaussSum/FiniteFourier.lean:1120` `cubicGauss_cube (ι : O →+* E) … (p primary, P = span{p}) (ψ primitive) : gaussSum (cubicChar P ∘ ι) ψ ^ 3 = -(ι p) * N(P)` (also `GaussSum/CubicTrace.lean:82` `cubicGauss_cube_of_nontrivial`);
  Jacobi sums `FiniteFourier.lean` `cubicJacobi_primary (J ≡ -1 mod λ²)`, `cubicJacobi_product`, `cubicJacobi_unit_multiple`, `cubicJacobi_mul_conj`; reciprocity input `CubicTrace.lean:207` `cubic_primary_frobenius_relation`, `:175` `CubicFrobenius.gauss_cube_residue_relation`.
- Hasse–Davenport-type sextic/cubic/quadratic relation: `GaussSum/CubicNormalization.lean:545`
  `JacobiQuadratic.gauss_sextic_relation (χ) (ψ) … (hχ3 : χ^3 = quadraticChar) (hχ6 : χ^6 = 1) : χ 4 * g(χ) * |F| = g(χ³) * g(χ²)²`, `:611` normalized form;
  `GaussSum/SexticNormalization.lean:24–51` `breveGamma1/2/3` (normalized g(χ^j)/|p|), `breveGamma1_gamma2_relation`; local A5 identities `canonical_A5_jone/jfour/jzero_active` (`Arithmetic/EisensteinEmbedding.lean:~470–560`, `GaussSum/CubicNormalization.lean`).
- Multiplicativity (CRT): `GaussSum/ChineseRemainder.lean` `gauss_sum_crt`, `gauss_sum_trace_crt_of_coprime`; `SexticNormalization.lean` `breveGamma2Product_crt`, `normalizedTraceGaussProduct_crt`; `CubicTrace.lean` `canonicalNormalizedGauss_eq_product`, `principalNormalizedGauss_eq_product`; frequency twist `canonicalNormalizedGauss_frequency_transport`.
- Squarefree-ideal level: `Arithmetic/IdealMobius.lean:411,419` `gaussTwo I hI` (normalized cubic Gauss sum over `O/primaryGenerator I` of the cubic row `cubicRow`), `squarefreeGaussCoefficient I = conj(angularFactor(primaryGenerator I)) * gaussTwo I`.
  `angularFactor a = a/|a|` (`PrimeRows/ActiveGaussFactorization.lean:488`) is only a unit-modulus bookkeeping phase of generators (it is what cancels in `Detector/PhaseCancellation.lean` `completed_phase_cancel`), not a character of the target.
- Cocycles: cubic Kubota `CubicSieve/RayCoefficients.lean:499` `CubicJacobiGlobal.kubota_mul (a b c d e f g h) (hdet) (hdet') (λ²∣a-1) (λ²∣e-1) (3∣b) (3∣c) (3∣g) : symbol (c e + d g) (a e + b g) = symbol c a * symbol g e`
  (and `kubota_mul_of_isCoprime`), giving the character `CubicKubota.character : levelThree →* O` (`value M = symbol (M 1 0) (M 0 0)`), `complexCharacter`, `value_cube`;
  extension to `levelTwo = Γ(3)·SL₂(ℤ)`: `Reciprocity/KubotaCharacter.lean` `levelTwoComplexCharacter`, `complexCharacter_product_well_defined`;
  quadratic Gauss-sum cocycle `Detector/Phase.lean:16` `G_mul : G (a*b) = G a * G b * reciprocitySign a b`.
- Sixth-power invariance/copies: `Mellin/SixthPowerAverage.lean`, `idealRowHom_sixth_mask`, `idealRowHom_argument_pow`, `canonicalSextic_sixth_power_mask`; `Hecke/InverseAmplificationFamily.lean:31` `amplifiedElement u A = u * generator(A)^6`.
Limits: reciprocity needs primary generators and Supported (coprime to 6) ideals; symbols at 2 and λ handled only through the phase/ramified side-tables. No sextic Kubota cocycle / no 6-fold cover (grep for metaplectic/sextic cover: nothing).

---

## 4. Cubic Kubota series / theta function — EXISTS in an L²-spectral form (3-fold cover only); NO sextic cover; no classical Kubota Dirichlet-series functional equation

Construction (all in `DL/Eisenstein/`, 82 files, 53k lines, plus `Reciprocity/KubotaCharacter.lean`, `Cusp/`, `GaussSum/BesselReflection.lean`):
- Cubic Kubota Eisenstein series on hyperbolic 3-space `HyperbolicSpace = SL(2,ℂ)/SU(2)`: `Eisenstein/Rows.lean` `eisenstein`, `HyperbolicSpace.lean:99` `hyperbolicEisenstein s`, automorphy
  `hyperbolicEisenstein_automorphy (M : levelThree) (2 < s.re) : E(M•w) = complexCharacter M * E w`; level group `levelThree = ker (SL₂(O) → SL₂(O/3))`, `globalKubotaKernel : Subgroup SL(2,O)` (`QuadraticSieve/HighKernelGeometry.lean:573`),
  `finiteCubicMultiplier : levelThree →* rootsOfUnity 3 ℂ`; fundamental domain/compact cores `FundamentalDomain.lean`, `QuotientTopology.lean`.
- Continuation: NOT through a functional equation but spectral: `MeromorphicResolvent.lean` `kernelEisensteinL2Correction` (meromorphic), `FredholmAlternative.lean`, `VariationalLaplacian.lean`, `DirichletForm.lean`, `CutoffApproximation.lean`.
- Fourier expansion of the Eisenstein series along the cusp, K-Bessel: `FourierCoefficients.lean` `arithmeticResidueSum`, `arithmeticDirichletSeries (s) (h)`, `scatteringCoefficient`, `eisensteinFourierCoefficient_formula`, `eisensteinFourierCoefficient_bessel`;
  `HyperbolicSpace.lean:569` `schlafliBesselK ν x`; bounds `ResidualFourierBounds.lean` (`schlafliBesselK_cubic_upper/lower`).
- Theta = residue at s = 4/3: `ScatteringCoefficients.lean:83` `cubicEisensteinResidue : KernelQuotientL2` (`_ne_zero`, `_character`, `_eigenvector` (eigenvalue 8/9), `_limit`), pointwise function
  `ScatteringResidues.lean:244` `cubicResidualFunction w = 3π·constantArithmeticResidue·(height w)^(2/3) + cubicResidualNonzeroFunction w` and
  `ResidualFourierExpansion.lean:438` `cubicResidualFunction_automorphy (M : levelThree) : θ(M•w) = complexCharacter M * θ w`, `:445` `cubicResidualFunction_ne_zero`,
  `:499,504,509` `cubicSourceResidualFunction` with `…_automorphy (M : levelTwo) = levelTwoComplexCharacter M * …` and `…_rational_invariant (M : SL(2,ℤ))`.
- Patterson/Kubota coefficients: `GaussFactorization.lean:88` `cubicResidualFourierCoefficient h = cubicBesselNormalizer h * nonzeroScatteringResidue h`; `SourceBesselExpansion.lean:357` `sourceResidualFourierCoefficient h = cubicBesselNormalizer h * sourceArithmeticResidue h`
  (`TranslatedFourierResidues.lean:385` `sourceArithmeticResidue`); explicit structure: supported on squarefree×cube indices (`SquarefreeCoefficients.lean` `sourceArithmeticResidue_squarefree_cube_support`, `thetaSquarefreePart`, `thetaCubePart`),
  multiplicative over primary primes (`PrimeGaussFactors.lean` `sourceResidualFourierCoefficient_primary_product`, `…_prime_factor`), prime-power recurrence/table (`PrimeRecurrence.lean:631` `sourceArithmeticResidue_prime_recurrence`, `PrimeGaussFactors.lean` `sourceArithmeticResidue_prime_power_table`),
  vanishing at valuation 2 (`RamifiedValuation.lean` `sourceResidualFourierCoefficient_prime_power_vanish`, `…_full_squarefree_cube_support`), size bounds (`RamifiedValuation.lean:329` `three_cusp_coefficients_squarefree_cube_bound`),
  λ-part tables (`ScatteringResidues.lean` `explicitRamifiedCoefficient`, `RamifiedGaussSeries.lean`).
- Behaviour at the other cusps: `Cusp/ResiduesModThree.lean:251` `three_cusp_decomposition`, `Eisenstein/FullFrequencyExpansion.lean` `exists_fixed_cusp_decomposition`, `SourceCuspDatum` (`RamifiedValuation.lean`), `finiteTwistCusp`, `translatedCuspFamily_*`.
- Mellin/"functional equation" of the theta Dirichlet series: `GaussSum/BesselReflection.lean:84–183,629` `completedBesselProfile`, `besselMellinFactor q s = 2^{2s-1}Γ(s+1/3)Γ(s+2/3)/(4πq)^{2s+1}`, `continuedBesselDirichlet`, `continuedBesselDirichlet_reflection` (reflection s ↦ 1/2-s with `CubicReflectionKernel.gammaMultiplier`), i.e. the functional equation holds in Bessel/cusp-reflection form for the squarefree×cube-supported series; used by the reflection identity of section 8.
- 3-fold cover correspondences used for cube-power operators: `Reciprocity/CubeCorrespondence.lean` (`cubeCorrespondence*`, `cubeKernelGlobal_intertwining`), `Eisenstein/CubeEigenrelation.lean`, `CubeResidueStrata.lean`, `InverseCorrespondence.lean`.
Missing: (i) 6-fold (sextic) cover, sextic Kubota multiplier or θ₆ (the OAI proof avoids it by splitting sextic Gauss sums into cubic θ₃ coefficients and quadratic phases via `gauss_sextic_relation`);
(ii) the classical functional equation of the Kubota Dirichlet series D(s;m,n) in (s ↦ 1-s) form with scattering matrix and Γ-factors; (iii) Dunn–Radziwiłł-type statements (Patterson bias, cubic-sum asymptotics); (iv) θ₂/Weil representation (quadratic) beyond Gauss-sum phases.

---

## 5. Large sieves

- Cubic (Heath-Brown): EXISTS. `DL/CubicSieve/Sharp.lean:55` `sieveNorm_sharp (ε>0) : ∃ C>0, ∀ M N ≥ 1, sieveNorm M N ≤ C (MN)^ε (M + N + (MN)^(2/3))`, where `sieveNorm M N = ‖[(J/I)₃]_{I∈idealRange M,J∈idealRange N}‖²_op`
  (`CubicSieve/Ideal.lean:14–153`: `Admissible I := Squarefree I ∧ primaryGenerator I ≠ 0`, `idealKernel I J = (primaryGenerator J / I)₃`); energy form `ideal_energy_bound`; proof by the Heath-Brown iteration `HeathBrownIteration.lean` (`step ξ = (6ξ-4)/(3ξ-1)`), `HasCubicExponent`, `ExponentImprovement.lean`.
  Limits: squarefree ideals coprime to 3, ε-loss, scalar (M,N) ranges; no Patterson-bias-corrected version.
- Quadratic over O: EXISTS. `DL/QuadraticSieve/LogarithmicLoss.lean:474,479` `sieveNorm_sharp : ≤ C (MN)^ε (M+N)`, `finite_family_quadratic_large_sieve` (general finite families of injective row/column ideals, arbitrary coefficient vector);
  kernel `quadraticRow J z = (idealSexticRow {J} … J z)^3`, `Admissible I := I ≠ 0 ∧ Squarefree I ∧ ∀ P | I, λ ∉ P ∧ ringChar ≠ 2` (`CoprimeBilinearBound.lean:522`). Base: Pólya–Vinogradov over O `QuadraticSieve/CoefficientCancellation.lean:591` `canonical_polya_vinogradov`, `InitialBound.lean:473` `ideal_initial_quadratic_sieve`.
- Hybrid (quadratic rows × cubic inverse kernel): EXISTS. `DL/Descent/Sharp.lean:83` `InverseMoment.hybridRow_energy : Σ_k |hybridRow Pset nset bset a beta k|² ≤ C (KNBL)^ε (K+NB)·B·(N+L+(NL)^(2/3))` (and `supportedHybridRow_energy`), applied in `Reflection/Energy.lean:46` `actual_reflected_branch_energy`.
- Sextic (de Faveri-type): NOT in DL (the OAI proof never needs it). EXISTS in a sibling package: `SIL/FourthPower/SexticSieve.lean` `Candidate.FourthPower.SexticSieve.OptimalBound` and
  `SIL/FourthPower/SieveOptimal.lean` `Candidate.FourthPower.SieveOptimal.optimal_bound : OptimalBound` (unconditional):
  `∀ ε>0, ∃ C>0, ∀ A B ≥ 1, ∀ rows columns (Supported ∧ PowerFree 6 ∧ N ≤ A / B), ∀ a, Σ_{R∈rows}|Σ_{I∈columns} a_I (R/I)₆|² ≤ C (AB)^ε (A + B + A^(5/6)B^(1/3) + A^(1/3)B^(5/6)) Σ|a_I|²`
  with `rowValue R I = idealRowHom (primaryGenerator R) I`. At A=B=K this is K^(7/6+ε). Proof: iteration `SieveImprovement.step α = (12α-7)/(6α-1) → 7/6` from the quadratic initial bound (`SieveInitial`, `SieveExponent.HasExponent`, `SieveRanges.theta`, reversal `theta_reverse A B ≤ 256 theta B A`).
  34 files, about 6,050 lines (`SIL/FourthPower/Sieve*.lean`, `SexticSieve.lean`); no sorry, `.olean` present. Limits: Supported (coprime to 6), sixth-power-free ideals (not only squarefree), sextic symbol with the row's primary generator; not imported by DL; interface is `Finset (Ideal O)` energies, not the DL `sieveNorm` matrices.
- General multiplicative large sieve over O (Gallagher/Montgomery-Vaughan, Hecke characters of varying conductor, additive large sieve): MISSING. Only orthogonality of ray characters (`RayOrthogonality.lean`, `RayQuotient.lean`, `Hecke/RayFamily.lean`) and the counting shells `Hecke/DetectorRowCount*.lean` (`card_of_energy`, `inverse_count`, `plain_count`, `classified_card_bound`) which take energy bounds as hypotheses.
- OAI's own mean-value statements for the Hecke row family (Möbius polynomials; "long line" U^{1/6}N^{5/6}): `Hecke/InverseAmplificationEndpoint.lean:11` `no_slot_endpoint`; `Descent/Sharp.lean`; `Energy/CertifiedExistence.lean` `certified_bands`. They are specific to the Möbius polynomial of the Hecke family, not general-vector sieves.

---

## 6. Hecke L-functions of F with finite-order characters — EXISTS (analytic continuation, primitive functional equation, strip/convexity bound, log-derivative disc control, Euler product, conductor presentation); NO zero counts/density; NO infinity type

- Objects: `DL/Hecke/Family.lean` `HeckeFamily.Character` (+ `Character.ofResidue`, `elementCoeff`, `coefficients` on O/period, `continuedLattice`), `IdealBridge.lean` `idealCoeff χ : Ideal O →*₀ ℂ`, `LFunction χ s := continuedLattice χ s / 6` (= Σ_I idealCoeff χ I · N(I)^{-s} for Re s > 1, `LFunction_eq_ideal_tsum`);
  operations `Hecke/Operations.lean` (`Character.product/inverse/power`), `ModulusRefinement.lean`, `Conjugation.lean`.
- Analytic continuation: lattice theta + Mathlib `WeakFEPair`: `Hecke/Theta.lean` (`pair`, `completed`, `latticeL`, `completed_functional_equation`), `ThetaSeries.lean`, `MellinIdentity.lean`, `Hecke/Origin.lean` (`poleRemoved`, `poleRemoved_eq : = (s-1) L`), `LFunction_differentiableAt`, `LFunction_entire_nonprincipal`, `CharacterAnalytic.lean`; principal pole/residue `HeckePrincipalResidue.principal_residue_positive`, `Hecke/Reciprocal.lean`.
- Functional equation (primitive characters; Gauss-sum root number of modulus 1): `Hecke/Primitive.lean:136`
  `HeckePrimitive.completedL_functional_equation (c) (χ : MulChar (O⧸span{c}) ℂ) (hu) (hp : IsPrimitiveOnIdeals χ) (s ≠ 0,1) : completedL c χ (1-s) = normalizedGauss c χ * completedL c χ⁻¹ s`
  (`completedL_eq_gamma_mul_LFunction`: `(scale c)^{-s} π^{-s} Γ(s) L`), underlying `GaussianTheta.lean:267,308,314` `theta_functional_equation`, `theta_inversion`, `theta_root_nonzero`; `TraceCharacter.lean` `gaussScalar_norm_sq`.
- Conductor: `TraceConductor.PrimitivePresentation`, `ConductorPresentation.exists_primitive_presentation`, `ConductorBounds.exists_primitive_residue_product_with_norm_and_mask`, `FiniteConductor.exists_primitive_quotient`, `Hecke/FiniteDeletion.lean` `exists_primitive_zero`, `Hecke/Presentation.lean` (`principalCharacter`, `LFunction_principalCharacter`).
- Bounds: `Hecke/Presentation.lean:83` `uniform_strip_bound (η primitive, nonprincipal) (z ∈ closedStrip) : ‖LFunction η z‖ ≤ 36·(…)·N(modulus)^(3/5)·(3+|Im z|)²` (from `Hecke/Strip.lean`, `StripActual.lean` `functional_equation_left`, `LFunction_exp_growth`, `PrincipalStrip.lean`);
  Euler product & non-vanishing on Re s ≥ 1: `Hecke/Euler.lean` `LFunction_ne_zero_of_one_lt_re`, `BoundaryIntegration.lean` `LFunction_ne_zero_of_one_le_re`; reciprocal bounds `ReciprocalBound.lean`, `ReciprocalGrowth.lean:42` `polynomial_reciprocal_bound`;
  zero-free-disc logarithmic control `LogarithmicControl.lean:419` `logarithmic_control` (Borel–Carathéodory, three circles), `Hecke/Logarithmic*.lean` (`disk_control`, `primitive_reciprocal_subpower`), `Hecke/EulerLog.lean`.
- Zeros: only finiteness in rectangles and the maximal real part used by the detector: `Hecke/DetectorZeros.lean` (`zeros_finite`, `zeroMaximum`, `exists_actual_buffered_bin`), `PrimeRows/DetectorZeros.lean` (`detectorMaximum`, `detector_nonzero_above_maximum`). No Jensen/argument principle, no N(σ,T), no zero-density estimate for Hecke or Dirichlet L (PNT+ dependency has zeta-only `KadiriZeroCounting.lean`).
- Prime ideal asymptotics in ray classes: `Hecke/RayPrimes.lean` (`primeLogMass_ratio_tendsto`), `RayPrimeNormalizer.lean`, `PrimeCounting/*`.
- Dirichlet transfer: `Hecke/Dirichlet.lean` `character χ`, `LFunction_eq_dirichlet_product`, `dirichlet_seven_eighths_of_hecke`.
Missing: Hecke characters with infinity type (weight-k theta with harmonic polynomial, its functional equation with Γ(s+k/2), Euler/strip/reciprocal bounds, redefinition of `beta`); non-primitive functional equation; zero counting.

---

## 7. Signal extraction (principal term) and zero-location splitting of non-principal rows — EXISTS for OAI's probe (probe-specific, uses `HeckeFamily.Character` and `beta`)

Signal / principal term.
- Target signal: `Hecke/Signal.lean` `signal`, `contour_shift`, `signal_bound_at_zero`, `signal_rapidDecayAtZero`; `SignalIdentity.lean` `signalMellin_eq_amplitude`, `poleRemoved_mul_signalMellin`.
- Principal frequencies and residues: `PrincipalMellinResidues.lean` (`source_double_residue`, `sourceResidueConstant`, `fixedPrincipalResidue_ne_zero`, `source_ordered_double_shift`), `PrincipalMellinGrowth.lean`, `PrincipalSignalComparison.lean` (`exists_normalized_actual_source_bound`,
  `actual_principal_slot`, `slotMass`, `slotRatio`, `sourceCorrection`, `sourceCorrection_bound : ‖H-1‖ ≤ 1/2 on Re s>7/8`), `PrincipalSlotEstimate.lean` (`principalSlot`, `weighted_principal_product_error`, `actual_principal_slot_error`),
  `Detector/Principal*.lean` (`PrincipalContours`, `PrincipalSplit.compensatedRowTripleIntegral_principal_split`, `PrincipalTransport`, `PrincipalNormalizer`, `HighLFactorization.principalHigh_L_factorization`), `Poisson/PrincipalTruncation.lean`,
  `QuadraticSieve/PrincipalTruncation|PrincipalDifference|PrincipalMajorants.lean` (quadratic principal-term differences), `Hecke/PrincipalStrip.lean`, `PrimeRows/Principal.lean`, `PrimeRows/NormFiberExtraction.lean`.
- Sixth-power frequencies/copies: `Mellin/SixthPowerAverage.lean`, `Detector/Sixth{Series,Frequency,Decomposition,Array,Mask}.lean`, `CenteredExceptionalCount.lean`/`CenteredExceptionalProfile.lean` (sixth-power normal form, counts of rows hitting forced fourth powers).
Zero-location splitting (rows ψ_u·η̄ with possible zeros near β).
- `PrimeRows/RowPartition.lean` (`rowBand`, `dyadicRows`), `PrimeRows/ExhaustivePartition.lean:11` `nonprincipal_rows_partition`, `PrimeRows/DetectorZeros.lean` (`detectorMaximum`, `detector_zero_re_le_maximum`, `detector_nonzero_above_maximum`),
  `PrimeRows/DetectorBins.lean:44` `exists_detector_buffered_bin`, `PrimeRows/BufferedBin.lean` (`sourceDetectorFamily`), `Hecke/DetectorZeros.lean` `exists_actual_buffered_bin`, `Detector.lean:41` `exists_buffered_bin`, `maximal_zero_of_floor_lt`, `simultaneous_saturation`,
  `PrimeRows/Nonprincipal{Boundary,Contour,Shift}.lean` (shift of the non-principal contour), counts `Hecke/DetectorRowCount*.lean`, `PrimeRows/NonfloorCount.lean` (`balanced_adaptive_count_from_raw_moments`, `high_adaptive_count_from_raw_moments`), `Hecke/DetectorSaturation.lean` (`actual_saturation`), `DetectorSimultaneous*.lean`.
- Combined statement: `PrimeRows/HighFromMoments.lean:18` `actual_high_probe_from_raw_moments` (see section 0).
Limits: hard-wired to the OAI probe's row family `u ↦ η·ψ̄_u` (`rayCubeFamily`), a single sextic slot with prime-pool marks, Möbius-weighted rows, exponents (0.51…, 1/200, 13/16, `HighData` budget in `ParametersHighData.lean`); target characters finite order only.

---

## 8. Voronoi-type summation for cubic Gauss sums / Patterson coefficients — PARTIAL (exact reflection identity exists; "Voronoi" never named; no uniform-in-k statement, no Patterson-part/remainder split)

Pieces that exist (this is the "formal library has a general Voronoi for twisted θ₃" of `research/LOG.md:1571`).
- Smoothed reflection of the θ₃ Dirichlet sum twisted by any multiplicative periodic Ψ: `DL/Eisenstein/FullFrequencyExpansion.lean:530`
  `completedT_canonical_smoothed_reflection (Ψ : O →* ℂ) (‖Ψ‖ ≤ 1) (Q) (hperiod : FactorsModulo Q Ψ) (c ≠ 0) (span{c} ≤ span{9}·Q) (W : ℝ → ℂ smooth, support ⊆ [v0,v1], 0 < v0) (X > 0) :
     completedT Ψ W X = thetaDerivativeScalar⁻¹ * ∑ h : O⧸span{c}, finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h * (finiteTwistCusp c hc h).smoothedKernel W X`,
  where `completedT Ψ W X = Σ_{I,J} columnWeight Ψ I/√N(I) · cubeWeight Ψ J · V*(N(I)N(J)³/X)` (`Arithmetic/IdealMobius.lean:471`; `columnWeight = squarefreeGaussCoefficient·Ψ(primaryGenerator)`, `cubeWeight = conj(angular)^3 Ψ^3/N`, i.e. coefficients at n = I·J³).
- Version with a family of sextic twists ∏ᵢ (·/pᵢ)₆^{jᵢ}, jᵢ < 6 (so exponents 2 = cubic, 3 = quadratic, 4 = Ramanujan-sum case are all in scope) over a pairwise coprime odd primary prime family, with marks S:
  `DL/Reflection/MarkedDualSource.lean:43` `InverseReflectedPhase.PrimeFamily.marked_reflected_source … : markedCompletedT (φ * unmarkedSexticTwist P.generator _ j S) W X (marks) = thetaDerivativeScalar⁻¹ * ∑ h : O⧸span{c}, fixedThetaRowCoeff c hc φ h * ∑ A : Finset ι, localInactiveWeight … * mixedReflectedValue …`
  via `DL/Descent/ReflectedDual.lean:46` `mixed_smoothed_eq_reflected`, twist defs `Descent/MixedRow.lean` (`unmarkedSexticTwist`, `mixedPrimeFunction`); the dual side `mixedReflectedValue` is an explicit sum over `ThetaFullIndex` (squarefree×cube, ramified exponent) with the Mellin–Barnes kernel
  `CubicReflectionKernel.paperKernel (Vstar W) (X/(27 (cuspScale)² N(c0∏p)²)·…)` (`Mellin/ReflectedKernel.lean:164`, bounds from `:307`), local dual twists `bracket` (`CubicSieve/LocalBrackets.lean:437`: dual local factor `(χ^{j+2})⁻¹`, j=4 Ramanujan-sum split `GaussSum/ReflectionBrackets.lean:141` `actual_bracket_four_divisibility_split`),
  fixed-cusp geometry `FixedFourierGeometry`, `A4BadPhase`.
- Ingredients: theta automorphy and cusp expansions (section 4), Bessel reflection `GaussSum/BesselReflection.lean` (`continuedBesselDirichlet_reflection`, Γ(s+1/3)Γ(s+2/3) factors), finite Fourier of periodic twists `Eisenstein/FixedThetaTwists.lean` (`fixedThetaTwist_fixed_fourier`), lattice Poisson `Poisson/EisensteinLattice.lean:125`.
- Dual-side energy bounds already derived for OAI's use: `Reflection/Energy.lean:46` `actual_reflected_branch_energy` (via `hybridRow_energy`), `Reflection/Coefficient.lean` `mixed_coefficient_hybrid`, `Reflection/*Energy*` (266 files).
Gaps relative to the paper's "Patterson part + remainder": no separation of the Patterson (diagonal) contribution from the rest; no statement uniform in the number/size of primes in the twist (the earlier survey notes the pipeline is built for Poisson in the row variable u, not a k-indexed family; `research/round11/tau_average_scope.md` §3(a));
only smooth compactly supported W (support in [lo,hi], lo>0); the cusp data `G`, `N` must be supplied (existence `exists_fixedFourierGeometry`); λ- and 2-parts of the index handled by case tables; no evaluation of the dual sum's size; no corrected cubic large sieve (Dunn–Radziwiłł Prop. 9.1).

---

## A. Additional material in sibling packages of the same Lean project

1. θ-parametrized criterion: `HC/Cycle25/Assembly/Continuation.lean` (section 1). 18k lines in `HC/Cycle25/` in total, all OAI-probe refinements (Arithmetic/Assembly/Energy/Numerator).
2. Sextic large sieve: `SIL/FourthPower/` (section 5). The rest of `SIL/FourthPower/` (about 75k lines, `Mixed*`, `Kernel*`, `Native*`) is the fourth-power reference argument for the plain fourth moment with repeated marks, again for OAI's probe.
3. Other packages (`arvi_*`, `sil_density_split_20261026`, `repeated_marks_20261024`) are parameter/density refinements of the same OAI probe: no new Hecke objects, no infinity type, no cubic-slot probe. `grep` of the whole project for angular/Grössen/infinity-type/Voronoi finds nothing beyond the items above.

## B. Not found anywhere (grep over DL, HC, SIL and the other `Submissions/` packages)

- Hecke/Grössen characters with nontrivial infinity type, their L-functions, weight-k theta, Hankel transform in Poisson.
- Any probe with two Poisson slots (second, cubic, slot) or a cubic slot on the Poisson side with amplifiers; "copy sieve" (closest: `Hecke/InverseAmplification*.lean` amplification `u ↦ u·a⁶`, `Mellin/SixthPowerAverage.lean`).
- 6-fold Kubota cover/θ₆; classical Kubota Dirichlet-series functional equation; Patterson-bias-corrected cubic sieve.
- General multiplicative/additive large sieve; zero-density or zero-counting for Hecke/Dirichlet L-functions.

## C. Largest missing pieces (rough sizing; analogues in the repo: CubicSieve 91 files/37k lines, QuadraticSieve 36/24k, sextic sieve 34/6k, Eisenstein 82/53k, Hecke 182/21k)

1. The new probe's own analysis layer (definition of the two-slot amplified probe, both evaluations, principal/signal extraction with the angular twist, copy sieve, error and exponent bookkeeping, the new `PrimitiveProbeContract`). The OAI analogue (Detector+PrimeRows+Moments+Energy+Descent+Reflection+Inversion+Dictionary) is 2,365 files / about 264k lines (plus the probe-specific part of `Hecke/`); a new probe can reuse the Poisson, Gauss-sum, reciprocity, θ₃-reflection and sieve libraries but not the stack. Largest by far.
2. Hecke characters with infinity type (z/|z|)^{6k} and their L-functions: weight-k lattice theta (harmonic polynomial), Poisson/Hankel transform, functional equation with Γ(s+k/2), strip/convexity and reciprocal bounds, Euler-product facts, redefinition of `beta` over the larger family, and `HeckeSignal`/`Continuation` glue. Estimate 10–20k lines (the finite-order analytic core of `Hecke/` is only part of its 21k lines).
3. Voronoi step for the cubic slot in the new setting: instantiate `marked_reflected_source`/`completedT_canonical_smoothed_reflection` for the new twist family uniformly in the parameters, isolate the Patterson (diagonal) part, bound the remainder with `hybridRow_energy`, cubic, quadratic and `SIL optimal_bound`, plus kernel bounds at the dual scale. Estimate 5–15k lines; Patterson-bias-corrected cubic sieve (if needed) is a further large item.
4. Angular Poisson: Fourier transform of (z/|z|)^k W(|z|²) (Hankel/J-Bessel) on O, 2–4k lines.
5. Small: bridging the SIL sextic sieve (Finset-energy interface) to the DL `sieveNorm`/row conventions; Euler correction `H` and `FirstTail` for θ < 7/8 inside the θ-parametrized criterion (HC does this for its own θ); porting `Cycle25.UniformCommonProbe` into DL.

## D. Caveats / unverified

- Nothing was compiled; statements were read from source. Several theorem statements were abbreviated above.
- `marked_reflected_source` and `completedT_canonical_smoothed_reflection` depend on cusp-geometry data (`FixedFourierGeometry`, `ControlledStratumArithmetic`) whose hypotheses I did not fully trace.
- The mapping of the paper's "copy sieve" and "amplified Gauss sums" to `HeckeInverseAmplification`/`amplifiedElement` is a guess from names.
- Which of the HC/SIL packages are intended to be imported together with DL was not checked; they share the `Submissions` lean_lib.
- Counts of files/lines come from `find`/`wc` on the symlink target.
