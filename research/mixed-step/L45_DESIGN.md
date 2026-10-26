# L4/L5 design: Collet's downstream on the residual (2026-10-26)

Read-only design; nothing was built. "(inf.)" marks inferences. The rest is cited.

**Prefixes**
- `S/` = `lean-env/qrh/Submissions/hailey_collet_1252270103/Record1252270103Source/`
- `C/` = `…/hailey_collet_1252270103/`
- `OB/` = `…/openai_baseline/OAI/NumberTheory/DirichletL/Moments/`
- `A/` = `…/arvi_repeated_marks_on_sil_face_20261025/`
- `M/` = `…/arvi_mixed_step/` (target tree)

## 0. Verdict: a hybrid

Neither route works alone.

**MAIN side: route 2 (virtual parent).**
- The residual of a transfer of a block `J` of the label's live slots is a literal Collet object:
  `correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _=>1) P (allocRestrict B J) τ' t (V/W) H'`.
  Here `W = ∏_J s.P j`, the pool `P` is the actual one, and `τ'` is ray-shifted (§5).
- So these are reused verbatim, with `s := s.restrict J`:
  - `eventual_selected_main` (`S/Core/InitialRegularToTruncatedMain.lean:29`);
  - `eventual_selected_second` (`…Second.lean:27`; `s`, `R`, `T` common at :32,:43);
  - `mainAllocatedFamily`, `allocatedFamily`, `CorrectedFamilyData`, `child`.
- **No residual twin of `eventual_selected_second` is needed.**

**LOW/HIGH: route 1, only at the coupling layer.**
- `FirstStage` (`S/Admission/SelectedSecondPhase.lean:25`) and `Selection` (`…CofactorFamilyData.lean:18`) stay unchanged. Both are generic in their parent `Input` and take `l : FirstSourceLabel` independently, so we instantiate them at `sv := s.restrict J`. That gives, with nothing generalized:
  - `input = child sv …`;
  - `height = firstMainRadius(volume sv, 3*amp)`;
  - coordinates at `logb Z (volume sv)`;
  - `raw = Z^(-amp)·firstMainRadius(volume sv,3amp)/volume s₁` (`…Coordinates.lean:125`).
- What must be forked is the layer that ties the first layer (columns, scalar, keys of the original `s`) to the second layer (children, selections). This is `Anchor`, `Family`, `Selected`, `PhaseBound`, the amplitude, and the LOW/HIGH spines.
- The fork makes three changes:
  1. **Two parents.** Add `s₀ : Input α₀` (first layer, original). The inherited `s` becomes the second-layer parent `sv`.
  2. **Two amplitudes.** Add `poolAmp = a` for `FixedCellPoolData`, `1/|P|` and `mainExtra`. `amp = a_v` stays for the radius and coordinates.
  3. **Price as a hypothesis**, with a frozen-width margin.
- The new arithmetic, the δ-shift, sits in 4–5 conversion lemmas.

**Certificate: virtual nodes that are genuine `Source`s.**
- Use `vnode n low b k = ⟨n.B−n.L·δ_k, n.L, n.cap, n.q, n.allowance, r_k, n.highFee⟩` at width `b−δ_k`.
- At `vnode k`, Collet's formulas give `t' = t`, `a = r+δ_k`, `F = 1−6r−6δ_k`, and the fee identity. This is the map's shortcut (`FORMAL_MAP_COLLET.md` §4), made exact by choosing the fee `r_k`.
- The fields are rational if the width grid `b` is rational. Otherwise, fall back to a real-field `RNode`.

**No virtual pool** (§1).

## 1. Where the downstream uses the pool, and what is legitimate

| use | where | verdict |
|---|---|---|
| corrected coefficient `poolCorrection P` | `S/Low/SelectedExceptionalNormalizedFamily.lean:137`; `allocatedFamily.pool` `…InitialCapsFamily.lean:91`; `correctedChildGaussEnergy` `S/High/GlobalPhysicalAllocationMain.lean:57` | must be the **actual** `P`. A pool `P_v` here states a different coefficient: **false**. The factor is D-independent because pool primes avoid slots (inf.). |
| modifier caps | `allocatedFamily_polynomialCaps` (:119 `hpool`, `havoid`); `selected_family_absolute` (`cellA` separate) | actual `P` with `FixedCellPoolData P Z a (a/2)`. OK. |
| `1/|P|` in the amplitude | `mainExtra` `S/Admission/SelectedHighPaidComparison.lean:25`; contract `extra` `…Contract.lean:98`. Consumed by `hp'` (`S/Admission/SelectedLowPaidWeight.lean:157`) and `hpay` (`…PaidComparison.lean:109`) through `reciprocal` (`S/Pool/FixedCell.lean:34`), against `raw`'s `Z^(-amp)` | the amplitude is fixed by `eventual_selected_main` with the actual `P`. `FixedCellPoolData P Z a_v` is **false** (card ≈ Z^a). A `P_v` of width a+δ satisfies it, but the actual amplitude is `|P_v|/|P| ≈ Z^δ` larger, so `P_v` silently drops `Z^δ`. **Use the actual P with a δ-shift.** |
| avoidance | `hmarked`, `avoids_canonical_slot` (FixedCell:104) | inherited by `sv` (sub-pools). OK. |
| ball factor `(radius+6a)/ell` | `CorrectedDensity.lean:84` | the pool acted on the original energy, so it is unchanged (actual `a`). |

**Scalar trap (new).**
- For `reflected=false`, `balancedColumnScalar` (`S/High/GlobalPhysicalBalancedColumns.lean:41`) is `|weight·outside|²/Z^{2·outsideExponent(M,A)+left(A)}`. Here `outsideExponent = M−A−…` (`C/Cycle61/…/GeometryPayment.lean:25`) and `Scalar.left = A+…` (`C/Record12518109Assembly/BalancedGeometry.lean:22`). So its square has slope **+1** in its `A`-argument.
- For `reflected=true` the slope is −1.
- So Collet's amplitude evaluated at the virtual parent (`A_v = A−δ`, with a pool of width a+δ) undercounts the actual one by `Z^{2δ}` when `reflected=false`. When `reflected=true` it is exact by luck, because the two `Z^{±δ}` cancel.
- The scalar must stay at the true `A = logb Z (volume s₀)`. The bound on `outside` in `actual_balanced_uniform_high_mass` (`S/High/GlobalPhysicalHighMass.lean:47`) is the original parent's.

**The shift identity.**
- The amplitude carries `Z^{−side(A)}` and `1/|P| ≤ Z^{−a+loss}`. The second layer carries virtual coordinates at `(A_v, a_v)`.
- `balancedGeometrySide` has slope 1 in `A`, as for `virtual_side` (`M/Ledger/Virtual.lean:27`). Hence
  `Z^{−a−side(A)} = Z^{−a_v−side(A_v)} · Z^{(a_v−a)−(A−A_v)}`.
- The forked conversion lemmas take `hshift : a_v − a ≤ A − A_v + κ`, where κ is a loss of order the mesh.
- For the transfer, `A−A_v = δ_act` (exact volume drop) and `a_v−a = δ_k ≈ δ_act`.
- Then the LOW price at `vnode k` uses `rawGap(a+δ, b−δ, F−6δ) = rawGap + δ·den3` (`Virtual.lean:37`). **That is where e = 1 comes out.**

**Silent mis-bookings route 2 would make.**
1. Residual normalized by `V` instead of `V_res`. The family is `(fun _ => volume sv)` while the phase is amplitude/V: this drops `W`, a false e = 2.
2. Transfer output carrying both `∏_J P` and `T/∏_J P`: the count is booked twice, e = 0. L2 must have only the bounded `∏hi·M²`.
3. Scalar at `A_v` with `P_v` (reflected=false): undercounts by `Z^{2δ}` (above).
4. `FixedCellPoolData` at `a_v`, or `P_v` in the modifier: both false.
5. Actual coordinates (`x0+5δ`) against `labelSide(A−δ)`: e = 0 (the plan's trap). The hybrid uses virtual coordinates with the virtual side, and converts the actual amplitude by the shift.

## 2. Pieces, families, nodes

**1. Split by frozen class.**
- Split `Σ_l amplitude_l·E_l` (output of `eventual_selected_main`) by the frozen set `F_l = {i | alloc l (inl i) ≠ 1}`. There are at most `2^N` classes, a constant since `N` is chosen after `α`.
- Within a class all labels have live set `α∖F`, so one `J` serves them all.

**2. Node grid.**
- Fix `g` (rational, chosen before `Z`, small enough that the strict gates still hold at `a+d(b)+2g`), `δ_k = k·g` and `K = ⌈(d(b)+g)/g⌉`.
- Each piece picks `k = max{δ_k ≤ transferable width}`.
- `upward_subset` (`A/FourthPower/GlobalSlotSelection.lean:17`) with target `δ_k−η_Z−mesh` then picks `J'` with `Σ_{J'} w ∈ [δ_k−2mesh, δ_k−η_Z]` (once `η_Z ≤ mesh`), where `η_Z = log_Z(2·16^N)/6`.
- Then `firstMainRadius(volume sv, 3(a+δ_k))` dominates the transfer radius `2·16^{|J'|}·H·W⁴`, and `hshift` holds with κ ≤ 2·mesh.
- Untransferred live width stays live.
- **Why a grid.** Nodes must be fixed before `Z`, because the LOW/HIGH ∃-constants and `regularLowMesh` depend on the node. A fixed grid lets every piece track its own transfer width exactly. Taking the minimum over k ∈ `Fin (K+1)` keeps the constants finite.
- **Two endpoints.**
  - `k = K` (δ ≥ d(b)): ordinary transfer classes.
  - `k = 0`: pool-only (live width < d, §6).
- **Frozen-width margin.** The LOW price at `vnode k` needs frozen width `f ≥ φ_k`, where
  `φ_k = (qX₀ + r − a(1−6qβ) − δ_k·den3)₊ / (q(1−1/Λ₀))`,
  since `raw_erasure_identity` keeps `−(q−q/λ)f` (`Virtual.lean:60`).

**3. Ray families.** One family per transfer ray character `ξ` (§5).

**4. Collisions.** One family per collision pattern and per `D_C` (§7).

`eventual_selected_second` runs once per family, with:
- `Label := {l // class l = c}`;
- `s := sv`, `T := volume sv`, `H := firstMainRadius(volume sv, 3a_v)`;
- `alloc := allocRestrict`, `τ := columnCharacter (rayShift …)`;
- the original amplitudes.

## 3. Module plan (order, sizes)

The vendored sizes are the line counts of the source modules. Statement-level restatement as in PR 76's fork (`research/repeated-marks/fork_source.py`, `fork/ForkAnalysis.lean`) should keep 50–70% of them (inf.).

**Phase 0.** Run `ForkAnalysis.lean`, rooted at `regular_supplier_some_rm` and `balanced_of_regular`.
- Seeds: `Anchor`, `PhaseBound`, `mainExtra`, `SelectedRegularAbsolute.amplitude`, `RealGeometry`, `ModifiedNodePrice`.
- Stop set: `Selection`, `FirstStage`, `child`, `correctedChildGaussEnergy`, `eventual_selected_second`, `CorrectedFamilyData`. This confirms these stay untainted.
- It is one environment load. I did not run it (read-only); my estimates use `grep`.

**New modules**

| # | module (M/) | content | lines |
|---|---|---|---|
| N1 | `Residual/Restrict` | `Input.restrict` (fields pointwise via `i.val`, so `child (s.restrict J)` unfolds like `commonData`); `allocRestrict`; `Initial.restrict` with `initialInput_restrict` (`initialInput` is per-slot, `S/Low/InitialInput.lean:43`, so rfl (inf.)); lemmas `volume_restrict`, `frozenCoefficient_restrict`, `sourceRadius_restrict`, `forcedProfileCost_restrict` | 350–450 |
| N2 | `Residual/RayShift` | `rayShift j ξ` (ξ₁↦ξ₁ξ, or ξ₂↦ξ₂ξ⁻¹ if reflected); live/label/seed/scalar/columnIdeal invariance; energy equality via `FixedPair.left_height` (`OB/FirstPhysicalSourceFixedFamily.lean:27`), `childCharacter_primary` (`OB/ChildRows.lean:21`), `heightCoeff_eq_fixed_rowWeight` | 250–400 |
| N3 | `Residual/Pieces` | class split, patterns, node grid, greedy `J'`, Σ over families | 350–500 |
| N4 | `Ledger/Nodes` (L1) | `vnode`, `r_k`, identities (`sourceT/A/F` at `vnode`), `RealGeometryLow` (RealGeometry minus `low_fee_room`/reference/centered fields) at all k from `SourceValid3`, `ActualGaps_rm (vnode k)` from the mixed HIGH gate (monotone in T and δ (inf.)) | 500–800 |
| N5 | `Ledger/FrozenPrice` (L1) | `actual_low_coordinate_payment_f` (keeps `−(q−q/λ)f`); `MixedNodePrice`; `mixed_node_price` | 250–350 |
| N6 | `Core/Contract3`, `Core/Balanced3` (L4) | `RegularJointSupplier3`; `balanced_of_regular3` (assembly, sums over families, `selected_four_payment` verbatim) | 700–900 |
| N7 | `Source/NFStep3`, `Finite/SourceValid3` (L6) | top-level mirror of `A/Source/NFStep2.lean`; rational width grid; mesh = min over nodes | 600–900 |

**Forked modules**

| block | Collet / PR 76 modules | change | lines (src) |
|---|---|---|---|
| F1 structures | `SelectedRegularSourceData`(+`Keys`, `State`), `SelectedSecondPhase`, `SelectedRegularAbsolute(Data)`, `SelectedHighPaidComparison`, `GlobalPhysicalSelectedMass` | `Anchor3` (+`s₀`, `modifier₀`; `Column`/`label`/`character` read `s₀`); `Family3`/`Selected3` keep `ColumnData`/`Selection` over `a.s`=sv; `amplitude3`/`mainExtra` use `s₀`, `poolAmp`; `PhaseBound3`; `actual_selected_paid_weight3` (statement only) | ~1.3k |
| F2 conversions (δ-shift) | `SelectedLowPaidWeight` (`eventual_`/`uniform_selected_paid_weight`), `uniform_selected_paid_sum`, `GlobalPhysicalBalancedCofactor(_rm)` (`S/High/GlobalPhysicalBalancedCofactor.lean:196–210`), `GlobalPhysicalLowCellPayment`/`RetainedLowPaidCells` (inf.) | `hp'`/`hpay` at `poolAmp`, then `Z^{a_v−a}·Z^{−side(A)} ≤ Z^{κ}·Z^{−side(A_v)}` | ~0.8k |
| F3 LOW spine | `SelectedLowPaid`, `SelectedLowSource`, `…Reindex`, `…MissingBins`, `SelectedLowBufferedSource`, `SelectedRegularLowSource(Data)`, `SelectedRegularLowPoint(Data)`, `GlobalPhysicalRegularLowAt`, `…LowParameters`, `RetainedLowPaid`, `RetainedLowErasedCollected`, `GlobalPhysicalLowGlobalSource`, `…LowCollectedErasure`, `RegularLowPhysicalPrice` | two parents (`α₀`/`α` split; the datum is already type-separate in `rawKey`, `S/Admission/FirstFamilyMask.lean:36`); `hprice` replaces `modified_node_price` | ~4.0k |
| F4 HIGH spine | the 19 node-dependent `A/Fork/…_rm` modules (`SelectedRegularHighSourceSome`, `…HighPointSome`, `…CombinedPointSome`, `…CofactorFamilySome`, `GlobalPhysicalPaidSome`, `BufferedPaidSome`, `AnnularCofactor`, `SectorPayment`, `HighScalar/*`, `RegularPoints`, `RegularControls`, `RegularHighParameters`, `RegularSuppliers`), and the first-layer-coupled `SelectedCofactor`, `AllCofactorPositive`, `AllRawPositive`, `RegularRawPositive` | two parents; `ActualGaps` and gain at `vnode k`; the gain machinery (`PositiveRadius/*`, `WholeActualBinTau`, …) is reused | ~4.5k |
| F5 family/norm bridge | `GlobalPhysicalRegular{Family,Phase,Norm,Normalized,Finite,Cofactor(+Bridge),Dictionary,Small,CanonicalSmall,CanonicalNorm,Supplier,Mesh,Parameters}`, `SelectedRegularCanonicalAbsolute(Data)`, `SelectedRegularGeometryCaps`, `SelectedMainExceptionalIdentity`, `Low/SelectedRegularFibers*` | `allocatedRegularFamily3`, `regularMainFamily3` and their rfl bridges; `RegularPointAt3` (`FixedCellPoolData P Z poolAmp`, `F.amp = a_v`); `regular_supplier3` (∀ k) | ~3.0k |
| F6 MAIN twins (L4) | complement: `…MainExceptionalSaving`, `…MainExceptional`, `ExceptionalFrozenOne`/`FrozenSum`/`FirstSum`/`FirstScalar`, `CorrectedExceptionalFirstPrice`. Remainders: `InitialMainRemainderGap`, `Low/InitialRemainderScalarSumNode`, `…RemainderOne` | two parents and two amps: `(vol child_res)^{1/3}·MAIN_v^{5/6}·Z^{−a}/Z^{left(A)}` (+3δ, gate 9(a+d)); zero term `H_v` (+4δ, gate 5(a+d)) | ~1.5k |

**Totals.**
- About 14 new modules, 3.0–4.3k lines.
- About 65 forked modules, ≈15k source lines, of which roughly 9–11k are restated (inf.).
- This sits inside the plan's L4+L5 = 11–17k, with less semantic risk.

**Order and dependencies.**
1. Phase 0 and N1.
2. In parallel: N2, N3, N4–N5 (L1), and F1→F2.
3. F3 and F4 in parallel, both after F1–F2 and N5.
4. F5.
5. F6.
6. N6. L2/L3 enter only as the hypothesis `TransferContract`, so L4/L5 need not wait for them.
7. N7.

## 4. Signatures

```lean
-- N1
def Input.restrict (s : Input α) (J : Finset α) : Input {i // i ∉ J}
theorem volume_restrict : volume (s.restrict J) = volume s / ∏ j ∈ J, s.P j
def allocRestrict (B : actualAllocations s.pools C) (hJ : J ⊆ liveIndices B.val) :
    actualAllocations (s.restrict J).pools C

-- L2/L3 output, in the waist form (consumed as a hypothesis)
def TransferContract : Prop := ∀ ε>0, ∀ N, ∃ K>0, ∀ᶠ Z in atTop, ∀ {α} [Fintype α], card α ≤ N →
  ∀ (s : Input α) C R L (P : Finset (Ideal O)), PoolAvoids P s →
  ∀ (B : actualAllocations s.pools C) (J) (hJ : J ⊆ liveIndices B.val), NoCollision s J → SeedFree s J L →
  ∀ τ t T H H', 0<T → 2*16^J.card*H*(∏ j∈J, s.P j)^4 ≤ H' →
  correctedChildGaussEnergy s 1 1 1 1 C R L (fun _=>1) P B τ t T H ≤
    K*Z^ε*∑ ξ : RayCharacter, correctedChildGaussEnergy (s.restrict J) 1 1 1 1 C R L (fun _=>1) P
      (allocRestrict B hJ) (childCharacter τ ξ) t (T / ∏ j∈J, s.P j) H'

-- no twin: eventual_selected_second (S/Core/InitialRegularToTruncatedSecond.lean:27) at
--   s := s.restrict J, Label := {l // class l = c}, τ := fun l => columnCharacter (rayShift (column l) ξ),
--   alloc := fun l => allocRestrict (alloc l) _, H := Hv, Tsec := Tsecv, T := volume (s.restrict J)
-- no generalization: FirstStage (s.restrict J) …, Selection (s.restrict J) … at amp := a + δ_k

-- F2, the only new arithmetic
theorem uniform_selected_paid_weight3 … (s₀ : Input α₀) (s : Input α)
  (j : FirstColumnIndex (geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
  (sel : Selection s reflected second (firstLabel s₀ … j) C₂ D₂ R) (a amp κ : ℝ)
  (hshift : amp - a ≤ logb Z (volume s₀) - logb Z (volume s) + κ)
  (hpool : FixedCellPoolData P Z a ell mesh poolLoss BD Bsource depth)
  (hω : ω ≤ (‖balancedColumnScalar reflected s₀ … (logb Z (volume s₀)) … j‖^2*extra*
          ‖frozenCoefficient sel.B₁.val _ R s.ν s.W s.P‖^2/volume s)*
        (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve (firstLabel s₀ … j)/lower)*
        normalizer C₂ D₂ U) … :
  selectedPaidWeight sel ω ≤ C*fac*forcedProfileCost s*(max 1 (forcedProfileCost s))^2*
    Z^(εpref+poolLoss+κ+B*ε+x 0 - balancedGeometrySide reflected (logb Z (volume s))
      (geometryExponents s₀ … j.1.val))     -- x at (logb Z (volume s), amp)

def MixedNodePrice (n low : Source) (b φ : ℝ) : Prop :=   -- ModifiedNodePrice (S/Coefficient/RegularLowPhysicalPrice.lean:27)
  -- with s₀ : Input ι₀ for j, d₂ : SecondInputDatum ι, extra hypothesis φ ≤ f; same conclusion
def RegularJointSupplier3 (K:ℚ) (n low : Source) (b mesh ξ reserve width : ℝ) : Prop
  -- RegularJointSupplier (S/Core/InitialRegularToTruncatedContract.lean:50), plus ∀ k ≤ K, J
  -- (width window), class/frozen bound φ_k ≤ width F, ray ξ; family =
  -- mainAllocatedFamily (s.restrict J) … (allocRestrict) (columnCharacter ∘ rayShift · ξ)
  --   P … Hv Tsecv (fun _ => volume (s.restrict J)) amplitudeOrig …
theorem balanced_of_regular3 (K:ℚ) (n low : Source) (b mesh ξ reserve width : ℝ)
  (hg : MixedGeometry K n low b) (hm : mesh < (n.lowFee:ℝ)/2) … (htr : TransferContract)
  (hreg : RegularJointSupplier3 K n low b mesh ξ reserve width) :
  BalancedInitialSupplier K n low b mesh ξ width      -- reused contract, …BalancedContract.lean:32

def NFStep3 : Prop := ∀ n low h : Source, (51/100:ℝ)≤HeckeZeroSupremum.beta →
  6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK → SourceValid3 n low (some h) →
  ParentGood low → NFAccounting n → P low → P h → P n
theorem nf_step3 : NFStep3
```

The rest of the top-level chain is reused:
- `truncated_of_balanced` needs only `hg.reference_pos` (`S/Core/InitialBalancedToTruncated.lean:60`), a first-layer field.
- `physical_supplier_of_truncated_widths` and `uniform_squarefree_source_step` are taken from `nf_step2`.

## 5. T1: the ray label ξ

- The transfer returns the twist `childCharacter (columnCharacter j) ξ`. On supported ideals its `heightCoeff` is
  `rowWeight η·leftCoefficient·rayCharacter(ξ₁ξ)`,
  which is the `heightCoeff` of `columnCharacter (rayShift j ξ)` (`FixedPair.left_height`).
- `fixedPair` is a `Classical.choice`. So N2 proves only an energy equality, and never equates characters.
- The family then uses column `j' = rayShift j ξ`. It has the same source label, seed, scalar and liveness, which depend only on `j.1` and `j.2.1` (`C/Cycle61/Physical/InitialMass/ActiveColumns.lean:18`).
- Consequences:
  - `stage_character` is rfl;
  - the LOW pin `input.η = columnCharacter (column l)` holds (`S/High/GlobalPhysicalLowCollectedErasure.lean:72`);
  - the dictionary rays are covered by `∀ ray ψ`.
- One family per ξ keeps `(firstLabel, seed)` injective. A transfer key is identical across ξ. The number of ξ is bounded.

## 6. Live width below δ

- Classes with transferable width `< d(b)` take node `k < K`. In the extreme case `k = 0` there is no transfer: `sv = s.restrict ∅`, `a_v = a = r`.
- They are paid by the frozen margin `φ_k ≤ f`. For `k = 0` this is the §1d gate `a(1−6qβ)+q(1−1/Λ₀)f ≥ qX₀+r` for `f ≥ b−d`.
- The first-level frozen width bounds the three-level `f` of `actual_selected_low_price` (`S/Admission/SelectedLowPaid.lean:30`) from below.
- `SourceValid3` needs the §1d gate and, for the full grid, the algebraic `φ_k` lemma (N5).

## 7. Collisions (L3) use the same waist

- For a pattern `C ⊆ J` and a fixed `D_C`, L3 should output
  `ω(D_C)·correctedChildGaussEnergy(sv_{D_C}, …)`.
  Here `sv_{D_C}` is `(s.restrict J)` with the plains shortened by `D_C`. That is a new constructor `Input.shortenPlains`, mirroring `child`'s `residualPool`, `X/N(B(inr k))` and `residual_coverage` (`OB/AmplificationChildInput.lean:63`).
- The `χ_m(D_C)^k` twist goes into `τ`. Its conductor grows by `N(D_C)`, still under `character_cap ≤ Z^5`.
- **Weights.** By my count the weights satisfy `Σ_{D_C} ω ≤ K·Z^ε` (inf.; this needs checking against the plan's `W_C·𝓜_res`). So each `D_C` is its own family and averaging is free. This avoids the `(l, D_C)` injectivity failure.
- **Node.** Pick k with `δ_k ∈ [δ'+w/2, δ'+w]`, re-selecting `J∖C` so that `δ'+w/2` sits in the window. Then:
  - `A−A_v = δ'+2w`;
  - the radius matches `μ+4δ'−w`;
  - `hshift` holds with slack `3w/2`, the plan's "excess even smaller";
  - the passed width is `b−δ'−w ≤ b−δ_k`;
  - the scale is `F−6δ_k ≤ F−6δ'−3w`.
- So the full-transfer gates cover every pattern by monotonicity.

## 8. Risks

1. **Seed suppliers (S).**
   - A pool-level (S) can exclude every slot of an annulus that contains one seed prime, since slots of equal width share a pool. In that case `J` can be empty.
   - Mitigation: in L2, impose `D ⊥ L` inside the D-average. Treat supplier columns as a pattern whose supplier slots are frozen into the common ideal (`C·g`, seed `L/g`). The pattern then takes a lower node with `f` enlarged by the supplier width.
   - Cost: `C`, seed and allocation change per label, which `eventual_selected_second` allows. One family per supplier assignment shape.
2. **Taint wider than the grep estimate.** Run ForkAnalysis first. With the convention "second layer keeps the name `s`", most occurrences need no edit, and the first-layer rewrites are a closed list (`firstLabel`, `geometryFirstSource`, `balancedColumnScalar`, `geometryExponents`, `columnCharacter`/`Ideal`, `rawKey`, `dictionaryRay`, `mainExtra`) that a script can apply.
3. **rfl bridges.**
   - Affected: `allocated_regular_fields`, `regularMainFamily_joint_norm`, and the `decEq` transports (`…AllocationMain.lean:24`).
   - Mitigation: the residual is literally `child (s.restrict J)`, with no new child type. `restrict` uses structure literals.
4. **`fixedPair` choice (T1).** Only energies are compared, on supported ideals.
5. **Uniformity in δ.** The node grid and the windowed greedy selection make all nodes fixed before `Z`. If `b` cannot be made rational, `vnode` needs a real-field `RNode` twin. This retypes the forked statements, mechanically, since `(n.q:ℝ)` stays valid syntax.
6. **The MAIN twins need new gates.** These are not corollaries of Collet's:
   - zero frequency `T+5(a+d)+fee<1`;
   - centered `T+9(a+d)+fee<5/6+0.499·Lref`.

   `mixed_certs.py` already charges `ka → k(a+d)`, so L6 must expose these in `MixedGeometry`.
7. **Pool width `a = r ≈ 10⁻¹²`** forces `mesh < r/2`. This is allowed (the mesh is free), but the mesh must be the minimum over `regularLowMesh(vnode k)` for all k, over `a/2`, and over the HIGH parent mesh.
8. **Collision raw lower bounds.** Shortened plains may break `raw_X1 : Lraw ≤ X₁` (`…InitialCapsFamily.lean:50`). Mitigation: pass `Lref/(2^N·W_C)`, which is only a polynomial cap (inf.).
9. **Normalization.** L2's statement must output `T/∏_J P` with no `∏P` factor. `hshift` makes every mis-booking a proof failure rather than a silent loss.
10. **Size.** About 15k source lines forked. Mitigation: extend `fork_source.py` with a "parent-split" patch class. Semantic edits are confined to F2 and N5.
