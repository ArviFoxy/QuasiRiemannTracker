# Collet source step: exponent trace (pool, slots, LOW erasure)

Read-only trace, 2026-10-25. Everything not marked (inferred) is quoted from the Lean or the paper.

Path prefixes:
- `S/` = `/home/user/lean-env/qrh/Submissions/hailey_collet_1252270103/Record1252270103Source/`
- `HC/` = `…/hailey_collet_1252270103/`
- `OB/` = `/home/user/lean-env/qrh/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/Moments/`
- `tex:` = `paper69/sources.tex`

## Summary

**Per unit of pool width a:**

| Quantity | Change |
|---|---|
| MAIN radius | +6 |
| Density 1/P | −1 |
| Centered exponent | +4 (= 5/6·6 − 1; the gate charges 9) |
| RAW excess (RC3) | −1 |
| RAW scale Q | −6 |
| Capacity z | −6B₀/Λ₀, so erasure +6qB₀/Λ₀ |
| LOW, net | −(1 − 6qB₀/Λ₀), which gives (G9) |
| HIGH | +(5 − 6ρ), from (G16) `H` (`HC/Record1252270103Finite/SourceFormulas.lean:48`) |

**Per unit of marked-slot width in u:**

| Quantity | Change |
|---|---|
| Volume A₀ | +1. A₀ and the column size are the same V = X₁X₂∏Pᵢ. |
| MAIN radius | +2 |
| Centered exponent | +1 |
| RAW excess (RC3) | 0 |
| RAW scale Q | 0 |
| Width s₁ passed to the earlier face | +1. Costs Λ₀ in the face budget; erased at rate q beyond min(z, h₀Q). |
| (G9) | charges q per unit of b |

The MAIN radius cancels identically in RC3, so the pool's dilation reaches LOW only through Q. The Lean has no slot-to-frequency transfer: the pool avoids every slot support (`S/Coefficient/SourceAmplifier.lean:78`).

## 1. The MAIN polynomial

**Definition.** `OB/GaussEnergy.lean:34–36`:

    gaussPolynomial S a ha c z = ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

with `gaussRow a z = sexticGauss a z / √N(a)` (:13–15).

**Source instances.**
- `S/Coefficient/SourceAmplifier.lean:21` (`corrected_source_dyadic_main`).
- Literal coefficient: `S/High/GlobalPhysicalMain.lean:34–80`.
- After the first allocation: `S/High/GlobalPhysicalAllocationMain.lean:50–62`, with `Γ I = (√T)⁻¹ * rowWeight τ fixedBadMask 1 1 t I`.

**Columns.**
- `finiteColumns S = S.image finiteTupleProduct` (`OB/SourceMass.lean:521`).
- `finiteTupleProduct v = ∏ i, v i` over `Tuple ι = (ι ⊕ Fin 2) → Ideal O` (`OB/AddedZeroUniform.lean:42,51`).
- `pools = Sum.elim s.slots (plain₁, plain₂)` (`OB/CommonRadialData.lean:34`).
- The Gauss modulus is the primary generator of the column (`OB/SourceRow.lean:49`).

So u = (one prime per live marked slot)·v₀·v₁. Frozen slots leave the child's columns and move into K and D·C.

**Coefficient.** `finiteColumnCoefficient` sums over the tuples with product u (`OB/SourceMass.lean:524`). Each tuple contributes a product of three parts:
- `markedSourceModifier` = μ²(K·∏ᵢvᵢ) · ordinary hole · μ²(A₁v₀A₂v₁) · F(D·∏v). Sources: `S/Collision/Projector.lean:24`, `S/Coefficient/SourceModifier.lean:25`, `S/Coefficient/CoupledProfile.lean:25`.
- `profileCoefficient` = (∏ⱼ νⱼ(vⱼ)·Wⱼ(Nvⱼ/Pⱼ)) · 1[(∏v,R)=1] · rectangle · 1[seed ∣ ∏v] (`OB/SourceProfileMass.lean:27–32`).
- Γ(u), the column character above.

**Valuation, puncture, projectors.**
- Slot primes are distinct and coprime to the frozen part K. The total column valuation is ≤ 2, reached when a slot prime equals an ordinary prime (`tuple_valuation_of_projectors`, `S/Collision/Projector.lean:40`; tex:304).
- The puncture R is a coprimality mask, not a divisor.
- The seed projector is a divisor: 1[s ∣ u].
- The first projector E appears only in the radius.
- The Newton correction is `F ↦ (P/(P − #dividingPool J))·F(D·C·J)`.

**How a slot enters: both ways.**
- The slot prime p is a factor of the Gauss modulus u.
- Its coefficient is a character value times a weight: `ν = idealCoeff (relativeCharacter … θᵢ) I * annularWeight W (Z^wᵢ) σᵢ vᵢ I` (`HC/Record12518109Source/InitialMoment.lean:108–110`).
- Γ(u) = (√T)⁻¹·τ(u)·(fixedBadMask⁶/u)·N(u)^{it} is multiplicative over p (`rowWeight_split`, `OB/SourceRow.lean:14`).

## 2. The pool chain

1. **(CA3).** `S/Coefficient/GaussMask.lean:70`: `gaussRow (p^6*h) = if p ∣ a then 0 else gaussRow h`.
2. **(CA5).** `S/Coefficient/CorrectedAmplifier.lean:67`.
3. **(CA6).** `S/Coefficient/PoolPayment.lean:43`: `‖F_b h‖² ≤ (P.card)⁻¹ * ∑ p, ‖F_b̃ (p^6*h)‖²`. The correction factor is at most 2 (:28).
4. **Ball.** `S/Coefficient/CorrectedDensity.lean:19,53`: `≤ (P.card)⁻¹*((M+6*L)/ell)*gaussEnergy … (Z^(M+6*L))`.
   - `outputRow_norm` (`OB/AmplificationEnergy.lean:18`) supplies the bound N(p⁶h) ≤ Z^{M+6L}.
   - `reciprocal : (P.card)⁻¹ ≤ Z^(-a+loss)` (`S/Pool/FixedCell.lean:34`).
5. **MAIN radius.** `actual_first_main_log` (`S/Coefficient/CorrectedExceptionalFirstPrice.lean:106`):

       2*logb V − M + R + E − c − d + max (d−c) 0 + 6*amp + frequencyLoss + reserve

   - It is built from `firstNominalScale = N E·N R·X²/(K·NC·ND)` with `X = volume s` (`OB/FirstScale.lean:13`).
   - `mainCommonRadius` adds `2σ` with σ = 3a (`OB/AmplifiedRetainedRadius.lean:150`).
   - Matches tex:1527–1530 with M = 1.
6. **Centered exponent.** `firstScalarCost = (V/NC)^{1/3}·MAIN^{5/6}·max(1,Z^L/NC)^{−2α}·Z^{−amp+loss}/Z^{Scalar.left}` (`S/Core/ExceptionalFirstScalar.lean:29–36`).
   - `first_exponent_identity` (`…FirstPrice.lean:82`): `(A−c)/3 + 5·MAIN/6 − Scalar.left = A − 5M/6 + 5amp + 5ω/6 + commonPrice`.
   - The factor Z^{−amp} turns 5a into 4a.
   - `node_centered_payment` (:121) bounds the result by `−highFee − 4a` using the gate `centered_499`: T+9a+h_H < 5/6+αL (`HC/Record1252270103StepScalar/Geometry.lean:41`).
7. **RAW coordinates.** `HC/Cycle61/Physical/InitialMass/SecondHighCoordinates.lean:20–31`:
   - `x0 = −a + (MAIN log − (A−c)) + (g₂−t₂−b₂)`
   - `x2 = M − R − (c−d)₊ + Lc − 6a − ω + ε`

   Hence x2 + MAIN = 2(A−c) + E + Lc + ε.

   `actual_raw_coordinate_identity` (`HC/Record12518109Raw/RawWeight.lean:23`) proves

       x0+x1+x2 − labelSide − labelSurplus = rawExcess = −a−2R−E−Bc+Lc+R0c+g2−t2−b2−σ

   (`HC/Record12518109Source/LowLedger.lean:50`). This is (RC3); A, M and ±6a cancel. `S/High/GlobalPhysicalLowCoordinates.lean:77` then bounds it by ≤ −a−B₁₂−D.
8. **Scale Q.** `modified_deficit_and_coordinate` (`S/Coefficient/RegularLowRetainedRadial.lean:38`): `x 2 = sourceFReal n low b − delta − rho`, with `sourceF = 1−6*sourceA` (`HC/Record1252270103Finite/SourceFormulas.lean:21`).
9. **(G9).** `sourceA` (SourceFormulas.lean:19). `fee_identity` (`StepScalar/Geometry.lean:49`) gives a − q(b+(t−B₀F)/Λ₀) = r.

**A₀.** A₀ = logb V with `volume s = X₁*X₂*∏i, P i` (`OB/AmplificationChildInput.lean:40`). It includes every marked slot of the input.
- `hA : logb Z V ≤ sourceTReal n b + b + plainError` (`ExceptionalFirstScalar.lean:44`); tex:653 and tex:1107.
- Children divide by the frozen common part (`child_volume`, :150).

**Where −a lives.** It is the reciprocal pool cardinality:
- in the centered exponent, the `Z^(-amp+loss)` factor of `firstScalarCost`;
- in the RAW exponent, the leading `−a` of x0.

## 3. Removing a slot block of width d from the columns

**Lean convention: one V plays three roles.**
- Normalization: the energy row is `(√(X₁X₂∏Pᵢ))⁻¹·…` (`OB/RetainedEnergy.lean:14–19`), and `normalizedGaussSource = …/volume s` (`OB/AmplificationChildInput.lean:210`).
- Column size: the column cap is `sourceRadius s = (∏hi)·b₁·b₂·X₁X₂·∏Pᵢ` (`OB/OriginalCommonHarmonic.lean:24`), and `volume s` is X in the MAIN radius.
- RAW slot factors: each is normalized by its own √Pⱼ (`normalizedSlot`, `OB/WholeSlotDeletion.lean:26`).

**Notation.** Let κ be the change in log column size per column, Δ the dilation exponent and ν the change in normalizing volume. From the formulas in §2 (inferred for any variant):

| Quantity | Change |
|---|---|
| MAIN radius | 2κ+Δ |
| Q | −Δ |
| RC3 | 2κ − ν₁ − ν₂ (child normalization A−c; balanced normalization A) |
| Centered | κ/3 + (5/6)(2κ+Δ) − ν, before density terms; κ/3 treats (V/NC)^{1/3} as a column size |

Pool check (κ=ν=0, Δ=6a, density −a): +6a, −6a, −a, +4a, matching §2.

**Slot block with D⁴, κ=−d, Δ=4d (inferred):**

| Term | Collet, per unit | Block leaves u |
|---|---|---|
| A₀ (normalization) | +1 | −d if the block leaves the input; 0 if the normalization keeps the selected scales |
| MAIN radius | +2 (X²) | −2d + 4d = +2d |
| Q | 0 | −4d, so capacity −4dB₀/Λ₀ |
| s₁ to the earlier face | +1 (`three_live_width_bounds`, `S/Coefficient/RegularLowActualCapacityErasure.lean:34`) | −d: avoids q·d of erasure, or frees Λ₀·d of budget |
| RC3 | 0 | 0 if ν=−d; −2d if ν=0, before the D-sum's Cauchy and averaging |
| Coefficient norm | ℓ¹ ≤ C·X₁X₂∏Pⱼ (`OB/SourceProfileMass.lean:44–57`); pointwise ≤ Mⱼ (`OB/EligibleEnergy.lean:17`) | per D: ℓ² mass ×Z^{−d}; summed over D: unchanged |

Net LOW erasure response on the affine branch (inferred): qd(4B₀/Λ₀ − 1).

## 4. The LOW erasure

**Objects.**
- The rows are the second-transformed joint source rows z_l, kept only where `ActualLow` holds: the zero-maximum of the row character's twisted family is < a+2e for every ray label θ (`HC/Cycle61/Moment/LowBranch/Gate.lean:19–28`).
- The erased objects are whole slot factors, bounded pointwise per row: `‖normalizedSlotⱼ‖² ≤ C·Z^(2εd)·Z^(q·wⱼ)` when `a ≤ (1+q)/2`. Sources: `HC/Record12518109Source/LowGate.lean:26–46` and `S/LowErasure/Slots.lean:33`. The bound is uniform over θⱼ and over the height bins `iBin`.
- `S/LowErasure/Finite.lean:24–54` erases ∏_{T∖F} at cost `pay^|T∖F|·Z^(q·Σw)`.
- `S/LowErasure/Partition.lean:23` partitions by row-dependent subsets.
- The erased set is chosen from widths alone (`erase_to_first_cap`, `HC/Record12518109Source/Erasure.lean:12`).

**Order: erasure comes before the earlier face.** `actual_low_erased_positive_family` (`S/High/GlobalPhysicalLowCollectedErasure.lean:41–217`):
- bounds the T-product by `erasurePayment … T F ×` the F-product;
- applies `InitialAffineAt … (SourceFace.mk Bprev lam 0 Bprev 0 hprev)` to the F-product at Z^M, with `m₁+m₂+lam*cap ≤ Bprev*M` and Σ_F w ≤ cap ≤ hprev·M.

**Capacity z.** `three_live_rounded_admission` (`S/Coefficient/RegularLowActualCapacityAdmission.lean:30–94`):
- `Pcap = t−c+f+loss−log d₁−log d₂`, `Q = F−delta−rho`, `cap = min((B*Q−Pcap)/lam, h*Q)`.
- Retained width ≤ cap gives `Admissible n₁ n₂ Σ Q` via `global_first_cap` (`S/Low/RawCaps.lean:26`).
- Erased width ≤ max(0, b−f−z, b−f−hQ) + mesh.
- cap ≥ 0 follows from `three_live_cap_nonneg` (`…CapacityErasure.lean:77`).

**Supporting results.**
- (G13): `raw_low_three_branches` (`S/Low/RawCaps.lean:42`); with losses, `S/Low/CommonCost.lean:21–64`.
- (G11): `RealGeometry` fields `parent_budget_room`, `qcap_room`, `weak_cap` (`StepScalar/Geometry.lean:35–46`).
