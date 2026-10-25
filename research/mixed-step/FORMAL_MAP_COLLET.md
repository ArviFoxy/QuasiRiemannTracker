# Collet's amplifier, its consumers and the step: formal map for the mixed source step

Read-only (2026-10-25); nothing edited or built. "(inf.)" marks inference; the rest is cited.

**Prefixes**
- `C/` = `lean-env/qrh/Submissions/hailey_collet_1252270103/`
- `S/` = `C/Record1252270103Source/`
- `OB/` = `…/openai_baseline/OAI/NumberTheory/DirichletL/Moments/`
- `A/` = `…/arvi_repeated_marks_on_sil_face_20261025/`

## Verdict

- **Reusable as is:** everything from `BalancedInitialSupplier` (`S/Core/InitialRegularToTruncatedBalancedContract.lean:32`, pool-free) up to `nf_step2`, and the whole pool chain.
- **MAIN waist:** the review's μ already contains 6a, so the transfer comes after the pool. The waist is `correctedChildGaussEnergy`.
- **LOW/HIGH waist:** downstream is generic in the slot type, and in `Input` at its leaves, but not in the source. It is pinned to the first-stage child, to one `amp` and to `input.η = columnCharacter`. The narrowest LOW/HIGH waist is `FirstStage` + `Selection`.
- **Size:** about 90–130 modules and 15–25k lines (inf.).

## 1. Dependency chain

### 1a. Pool to MAIN (reusable verbatim)

| # | link | file:line | key data |
|---|---|---|---|
| 1 | (CA5) `corrected_pool_identity`; (CA6) `corrected_pool_bound` | `S/Coefficient/CorrectedAmplifier.lean:67`; `PoolPayment.lean:43` | `‖F_b h‖² ≤ \|P\|⁻¹Σ_p‖F_b̃(p⁶h)‖²` |
| 2 | `corrected_dyadic_energy_ball` | `S/Coefficient/CorrectedDensity.lean:84` | ball `Z^(M+6L)`, factor `(M+6L)/ell` |
| 3 | `corrected_source_dyadic_main` | `S/Coefficient/SourceAmplifier.lean:21` | any `ι`, `S`; coefficient `finiteColumnCoefficient (piFinset S) (sourceModifier A₁ A₂ D F v*β v)*Γ`; needs pool∤slots (`hmarked`), `Z^ell≤Np≤Z^L`, `2B/ell≤\|P\|`, cap `Z^B`, `dyadicScale n≤Z^M` |
| 4 | `actual_marked_corrected_main` | `S/High/GlobalPhysicalMain.lean:34` | `S:=s.pools`, β = squarefree·`profileCoefficient` |
| 5 | `actual_marked_main_ideal_coefficient` | `S/High/GlobalPhysicalCorrectedMain.lean:19` | corrected β = `markedSourceModifier A₁ A₂ 1 K (P/(P−#div)·F(D·J))` |
| 6 | `correctedChildGaussEnergy` (def) | `S/High/GlobalPhysicalAllocationMain.lean:50` | `child s C R B τ t : Input (liveIndices B)`; `Γ=(√T)⁻¹·rowWeight τ fixedBadMask 1 1 t`; `T` = parent volume |
| 7 | `actual_balanced_marked_main` → `actual_selected_marked_main` | `S/High/GlobalPhysicalBalancedMain.lean:28` → `GlobalPhysicalSelectedMain.lean:33` | per first column/allocation: `‖scalar‖²·\|P\|⁻¹((r+6a)/ell)·energy(T=volume s, Z^(r+6a))` |
| 8 | `eventual_selected_main` | `S/Core/InitialRegularToTruncatedMain.lean:29` | `Hmain=firstMainRadius … (3*amp)`; `amplitude ∋ \|alloc\|²/\|P\|` |

### 1b. Second transform to the step

| # | link | file:line | key data |
|---|---|---|---|
| 9 | `actual_corrected_second_reduction` | `S/High/GlobalPhysicalSecondRemainder.lean:44` | any `Input ι`, `card ι≤N`; `Γ=rowWeight s.η … 1 1 s.t`; free `T`, `Λ` |
| 10 | `eventual_selected_second` | `S/Core/InitialRegularToTruncatedSecond.lean:27` (via `GlobalPhysicalSelectedSecond.lean:54`, `…SecondFamily.lean:26`) | consumes row 6 for `child s (C l)…`; emits `regularJointNorm f Q`, `f=mainAllocatedFamily` (`…ToTruncatedFamily.lean:30` = `allocatedFamily`, `S/Low/SelectedExceptionalInitialCapsFamily.lean:81`) |
| 11 | `CorrectedFamilyData` | `S/Low/SelectedExceptionalNormalizedFamily.lean:111` | generic `input : ∀l, Input (slots l)`; modifier fixed to `markedSourceModifier … (poolCorrection pool)` (:137) |
| 12 | `RegularJointSupplier` | `S/Core/InitialRegularToTruncatedContract.lean:50` | `initialInput`; `amp:=sourceAReal`; `P:=primePool…(Z^amp)`; `Hmain`/`Tsec` with `3*amp`; `∀χ₀`; injective (firstLabel, seed) (:82) |
| 13 | `balanced_of_regular` | `S/Core/InitialRegularToTruncatedBalanced.lean:53` | glues row 8 (:80), row 10 (:81), row 12 (:203), the complement (:75, `≤Z^(−amp)`), remainders (:82), `selected_four_payment` (:243) |
| 14 | `truncated_of_regular` | `S/Core/InitialRegularToTruncated.lean:11` | `truncated_of_balanced` ∘ row 13 |
| 15 | `nf_truncated` / `nf_truncated2` | `S/Core/InitialRegularCallbacks.lean:69` / `A/Source/NFStep2.lean:31` | the latter calls `regular_supplier_some_rm` (:79) and row 14 (:90) |
| 16 | `nf_physical_of_truncated` → `nf_step_of_physical` | `S/Core/InitialTruncatedCallbacks.lean:50` → `S/Low/HeightAnchorCallbacks.lean:59` | ends in `uniform_squarefree_source_step` (`HeightAnchorUniform.lean:30`); ours: `nf_physical2`, `nf_step2` (`NFStep2.lean:100,121`) |

### 1c. Centered complement

1. `actual_first_main_log` (`S/Coefficient/CorrectedExceptionalFirstPrice.lean:106`, `logHmain=2logV−M+R+E−c−d+(d−c)₊+6amp+ω`) and `node_centered_payment` (:121, gate `centered_499`)
2. → `firstScalarCost` (`S/Core/ExceptionalFirstScalar.lean:29`) → `actual_first_scalar_cost` (:38, `≤Z^(−fee−4a−p)`)
3. → `ExceptionalFirstSum.lean:55` → `ExceptionalFrozenSum.lean:23` → `ExceptionalFrozenOne.lean:28`
4. → `InitialRegularToTruncatedMainExceptional.lean:39` → `…Saving.lean:35` → row 13.

### 1d. LOW (proof of row 12)

**Bridge.** `regular_supplier_of_points` (`S/High/GlobalPhysicalRegularSupplier.lean:78`) bridges to `Family a Label` through two links:
- `regularMainFamily_joint_norm` (`S/Contraction/SelectedMainExceptionalIdentity.lean:93`);
- `allocatedRegularFamily` (`S/High/GlobalPhysicalRegularFamily.lean:32`). Its `allocated_regular_fields` (:47) fixes `input = child a.s …` and `Hmain = firstMainRadius … (3*amp)`.

It then calls `regular_canonical_joint` (`…RegularCanonicalNorm.lean:61`) and `RegularPointAt` (`…RegularPoints.lean:51`). Both need `FixedCellPoolData P Z amp (amp/2)…` and `F.amp l = amp`.

**`RegularLowAt`** (`S/High/GlobalPhysicalRegularLowAt.lean:49`). Its fields:
- `x := actualHighCoordinates … (logb(volume s)) (sourceAReal)` (:158);
- radius `sourceF−δ−ρ` (:163), with `radius ≤ x 2+θloss` (:187);
- `Σw ≤ bcell` (:172);
- (G11) guard `annularLoss+B₀ρ+2e ≤ B₀F−plainBudget−b` (:185);
- `FixedCellPoolData P Z (sourceAReal) (sourceAReal/2) poolMesh θloss…` (:192).

Proof spine: `regular_low_controls` (:223) → `…RegularLowParameters.lean:45` → `Admission/SelectedRegularLowSource.lean:44` → `SelectedLowBufferedSource.lean:41` → `…MissingBins.lean:41` → `…Reindex.lean:41` → `SelectedLowSource.lean:41`. There it splits:

- **Capacity.** `SelectedLowPaid.lean:30` → `SelectedLowErasure.lean:122` → `three_live_rounded_admission` (`S/Coefficient/RegularLowActualCapacityAdmission.lean:30`; generic `s`).
  - `Q=F−δ−ρ`, `Pcap=t−c+f+loss`, `cap=min((BQ−Pcap)/λ,hQ)`.
  - Erased width `≤ max(0, b−f−…) + mesh`.
- **Payment.** `ModifiedNodePrice` (`S/Coefficient/RegularLowPhysicalPrice.lean:27,52`) → `modified_low_coordinate_payment` (`S/High/GlobalPhysicalModifiedLowPayment.lean:38`; generic reals, `g=a−q(b+(t−BF)/λ)`).
- **Erasure and earlier face.** `RetainedLowPaid.lean:35` → `RetainedLowErasedCollected.lean:37` → `GlobalPhysicalLowGlobalSource.lean:36` → `actual_low_erased_positive_family` (`S/High/GlobalPhysicalLowCollectedErasure.lean:41`).
  - Generic in `s`, modifier, `α` and `SecondInputDatum`.
  - Erases `T∖F` at `erasurePayment`, then applies `InitialAffineAt (SourceFace.mk Bprev lam 0 Bprev 0 hprev)` (`C/Record12518109Source/InitialMoment.lean:94`, `∀M∈[Mmin,Mmax]`).
  - Conditions: `m₁+m₂+λcap ≤ Bprev·M` and `cap ≤ hprev·M`.
  - Pins `datum.input.η = columnCharacter (column l)` (:72).

**RAW coordinates.**
- `actualHighCoordinates` (`C/Cycle61/Physical/InitialMass/SecondHighCoordinates.lean:20`).
- `actual_raw_coordinate_identity` (`C/Record12518109Raw/RawWeight.lean:23`): `x0+x1+x2−labelSide(A)−labelSurplus = rawExcess(a)`.
- `modified_deficit_and_coordinate` (`S/Coefficient/RegularLowRetainedRadial.lean:38`): `x2 = sourceF−δ−ρ`.
- `raw_erasure_identity` (`C/Record12518109Source/LowLedger.lean:59`, generic).

### 1e. HIGH

**Chain.** `Admission/SelectedRegularHighPointSome.lean:92` → `SelectedRegularHighSourceSome.lean:223,535` → `High/GlobalPhysicalPaidSome.lean:44,196` → `HighScalar/LabelPayment.lean:31`.

**What `LabelPayment` needs:** `amp ≤ D·sourceA`, `A ≤ D(t+b)`, `D(b−2e) ≤ live+…`, `D(F−e) ≤ x2+…`, and `ActualGaps` (`S/Core/PhysicalReserve.lean:17`).

**Excess and coordinates.**
- `highJointExcess` (`C/Record12518109Natural/HighAllocation.lean:29`) contains `a(5−6ρ)+νA`.
- HIGH coordinates: `Selection.coordinate` (`S/Admission/SelectedHighCofactorFamilyData.lean:60`) = `cofactorCoordinates` (`…CofactorCoordinates.lean:24`) = `lostWidthCoordinates` (`HighScalar/SingletonLoss.lean:30`).

Our fork replaces this chain with `_rm` versions.

## 2. The waist

1. **Top (pool-free).** `BalancedInitialSupplier`. A mixed `balanced_of_regular` that proves it reuses rows 14–16 and `NFStep2` unchanged.
2. **MAIN.** `correctedChildGaussEnergy` appears only as the output of rows 6–8 and the input of row 10 and its two helpers; `balanced_of_regular` :242 chains them.
   - **New interface theorem:** `correctedChildGaussEnergy(T=V, H) ≤ C·Z^ε·Σ_ξ residualEnergy(T=V_res, H·(2W)⁴)`.
   - **Reuse:** rows 1–8 verbatim.
   - **Pool correction:** D-independent, because pool primes avoid slot primes (`Pool/FixedCell.lean:115,125`) (inf.).
3. **Second transform.** Row 9 takes the residual `Input` as is. Only row 10 and `allocatedFamily` need residual twins.
4. **LOW/HIGH.** All family consumption passes through two structures:
   - `FirstStage` (`S/Admission/SelectedSecondPhase.lean:25`): `input:=child…` (:33), `height:=firstMainRadius…(3*amp)` (:34);
   - `Selection` (`…CofactorFamilyData.lean:18`): `firstInput` (:46), `finalInput` (:47), `full` (:51), `coordinate` (:60).

   Generalize these, plus `allocatedRegularFamily` and `regularMainFamily`. The leaves are then reused: row 9, `actual_low_erased_positive_family`, `InitialAffineAt`, `three_live_rounded_admission`, `modified_low_coordinate_payment`, `raw_erasure_identity`, `HighScalar/*`.

## 3. Genericity

**Slot type: generic.**
- Every layer quantifies `α : Type`.
- Children are typed `liveIndices B : Finset α`.
- `SecondInputDatum` has `slots : Finset α` (`C/Cycle61/Physical/InitialMass/SecondFamily.lean:19`).
- Fewer slots only eases `card ≤ N`.

**Source: not generic.**
- **P1, child hard-wired.** `FirstStage.input`, `allocated_regular_fields` and `Selection.firstInput` fix it. About 16 `child_*` lemmas need residual twins.
- **P2, radius.** `firstMainRadius(volume s, 3*amp)`; the residual needs `3a+2d`. The same pin is in `firstMainFourierScale`, in `RegularPointAt`'s `Tsec`, and in `regular_canonical_joint`'s `Z^(rad+6amp)=Hmain`.
- **P3, one `amp`.** It feeds `FixedCellPoolData` (`card_power`, `reciprocal`, `ell=amp/2`, `depth·amp<5`), `extra`'s `1/|P|`, the radius and the coordinates in the same statements (`RegularLowAt` :158/:192, `RegularPointAt`, `regular_canonical_joint`). It must be split into the pool width `a` and the transfer width `d`.
- **P4, coordinates.** They need `x+d·(5,0,−6,−1)` with `labelSide(A)`.
  - Collet's formula at `(A−d, a+d)` gives `(x0+4d, x1, x2−6d, x3−d)` with `labelSide(A−d)`. RC3 (`−d`) and the HIGH excess (`+d(5−6ρ−ν)`) agree with the review, but `x0` alone is off by `d` (inf.).
  - In the cofactor coordinates `live` also drops by `d`, cancelling `x3−d`. The HIGH charge is then `5−6ρ`, the pool's; O3's figure is `νd` optimistic (inf.).
- **P5, width ledgers.** `Σw≤bcell`, the `InitialGeometry` cells, the `live` ledger and the erased bound `b−f` become `b−d` and `b−f−d`.

**Twist: partial.**
- **T1, ray twist ξ.** `Γ` is hard-coded `rowWeight τ fixedBadMask 1 1 t` (11 files in `S/`). The LOW erasure pins `input.η=columnCharacter` (`…CollectedErasure.lean:72`, `…LowGlobalSource.lean:64`). `Input` has no plain-prime coefficient. Way out (inf.):
  - `columnCharacter` is `fixedPair(η,C,D,E,ξ₁,ξ₂).left`, with `heightCoeff = rowWeight·leftCoefficient·rayCharacter ξ₁` (`OB/FirstPhysicalSourceFixedFamily.lean:19–37`, `OB/FirstMaskedFamily.lean:89`).
  - Column indices carry the ray pair (`C/Cycle61/Physical/InitialMass/ActiveColumns.lean:12`). So the ξ-twisted residual is the residual of column `ξ₁↦ξ₁ξ`.
  - Cost: a ray-shift lemma, plus one family per ξ to keep (firstLabel, seed) injective.
- **T2, `χ_n(f)²` (inf.).** At Collet's child level the frozen part sits in the common `C`, so its twist is already in `τ`. Otherwise the `A`-slot of `rowWeight` (fixed to 1) is needed.

## 4. Where a, F and Q live, and what carries d

**Certificate.**
- `sourceA`, `sourceF`, `scalarGate`, `weakCap`, `densityGate`, `SourceValid`: `C/Record1252270103Finite/SourceFormulas.lean:19,21,22–35,37,40,83`.
- Affine-in-b real twins: `SourceWidth.lean:40–63`.
- `RealGeometry`: `C/Record1252270103StepScalar/Geometry.lean:28–47`. 17 fields, including `centered_499`, `first_tail`, `parent_budget_room` and `fee_identity` (:47).
- Fork: `scalarGate92`, `densityGate2`, `SourceValid2` and `CellRatio`, which uses F (`A/Finite/SourceValid2.lean:15–64`).

**Scale `Q`.**
- `x2=F−δ−ρ` (`RegularLowRetainedRadial.lean:38`).
- Then `RegularLowAt` :163/:185/:187, then the parent call at `M` (§1d).
- HIGH sees it through `ActualGaps` and `D(F−e)≤x2+…`.

**Payment.**
- `fee_identity` (Geometry.lean:47).
- `modified_low_coordinate_payment` (generic): at `(a+d, b−d, F′)` it is exactly `a(1−6qβ)+d(1+q−6qβ) ≥ qX₀+r` (inf.).
- `node_price_with_outer` (`S/Core/PhysicalLowReserveSource.lean:17`).
- `conservative_gain` (`S/Core/PhysicalLowReserve.lean:27`).

**Shortcut (inf.).** Collet's closed forms at the virtual node `n′=(B−L·d, L, cap, q, e, r, fee)` with width `b−d` reproduce `t′=t`, `a′=a+d`, `F′=1−6a−6d`, `T′=T−d` and the mixed fee identity. They get `Lref=49/100−K·b` and the crossing wrong; both must stay at `(n,b)`.

**Modules that must carry d.**
- `SourceFormulas`, `SourceWidth`, `SourceWidthDensity`: `d`, `a≥r`, a pool-only gate for live<d, (G11) at F′.
- `StepScalar/Geometry`, `PhysicalLowReserve(Source)`, `PhysicalReserve`.
- In the fork: `SourceValid2`, `HighGate`, `Fork/…/GlobalInitialCallbacks` (width certificate), `Graph/Chain`, `NFStep2`.

## 5. Size (inf.)

| block | modules | lines |
|---|---|---|
| Transfer lemma in Collet's types: residual `Input`, CRT/D⁴ on `gaussPolynomial (sourceGenerator…)`, grouped average, ray shift. Sil's versions total 1.2k lines in his own types (`A/FourthPower/GaussTransfer`, `MixedSupplierKernel`, `MixedSupplierPositive`, `MixedPhysicalTransfer`). | 6–10 new | 2–3.5k |
| Post-pool MAIN: row 10 wrappers, residual family, centered complement at `σ=3a+2d`, remainders at `H·Z^{4d}`, mixed `balanced_of_regular`. Drawn from 36 modules totalling 4.0k lines. | ~20 | ~3k |
| LOW/HIGH glue: `FirstStage`, `Family`, `Selection`, the bridge, `RegularPointAt`/`RegularLowAt`, the LOW spine, HIGH (~10 already `_rm`). 159 files (22.9k lines) mention some pinned object. | 50–80 | 8–14k |
| Coordinates and identities | 8–12 | ~1.5k |
| Certificate and step | 6–10 | 1–2k + data |
| **Total** | **90–130** | **15–25k** |

For scale, the repeated-marks fork, which touched HIGH only, is 48 files and 7.4k lines.

## 6. Risks

1. **Normalization.** Row 6 normalizes by the parent volume. The transfer must output `T=V_res` (or carry `Z^d`) while the first-layer scalar stays at `A`. Mis-booking this turns `e=1` into `e=0`.
2. **Live < d case.** Labels with live width below `d` need a new LOW gate using the margin `f(1−1/Λ₀)`. `ModifiedNodePrice` assumes only `f≥0`.
3. **`fixedPair` is `Classical.choice`.** The ray-shift identity holds only through `heightCoeff` on `Supported` ideals; each use of `rowWeight`/`idealCoeff` must be checked.
4. **Definitional proofs.** Collet's proofs lean on `rfl` (`allocated_regular_fields`, the decEq transports at `GlobalPhysicalAllocationMain.lean:24–48`). The residual definitions must unfold the same way.
5. **Ledger and transfer unproved.** `c=6`, `e=1` and the O3 charges remain inferred, and the analytic transfer itself is unproved.
