# F4 plan: the HIGH spine with two parents (2026-10-26)

Author: F4 agent. Status: plan. The lower chain is being drafted; nothing that imports unfinished
F1 files is compiled yet.

Prefixes: `S/` = Collet `Record1252270103Source/`, `A/` = PR 76 `Fork/Record1252270103Source/`,
`M/` = `Submissions/arvi_mixed_step/ForkMx/Record1252270103Source/`.

## 0. What changes in the HIGH spine, and what does not

The PR 76 `_rm` HIGH statements are already generic in the node: `n low highNode bcell` and
`ActualGaps_rm n low (some highNode) bcell ν reserve` are parameters and hypotheses. So the virtual
node `vnode2 n low b δ θ` at width `b-θ` (LEDGER_INTERFACE v2) is just an instance. **No HIGH module
changes for the node.** These hypotheses stay with the caller:
`D*bcell-δwidth ≤ Σw ≤ D*bcell` (second-layer widths), `logb Z (volume s) ≤ D*(sourceTReal n bcell+bcell)`,
`amp l ≤ D*sourceAReal n low bcell`, `ActualGaps_rm …`.

Three things change.

1. **Two parents.** Every PR 76 HIGH statement takes one `s : Input α` and uses it for both
   layers. It splits into:
   - first layer `s₀ : Input α₀`, `modifier₀` (`markedSourceModifier` over `α₀`): columns, labels,
     characters, `dictionaryRay`, `s₀.η` (unit, keys), and the mass hypotheses
     `s₀.W₁ 0 = 0`, `s₀.W₂ 0 = 0`, `sourceRadius s₀ ≤ Z^B`, `loMass ≤ s₀.lower`, `ap`-support of `s₀.W₁/W₂`,
     `card α₀ ≤ N`;
   - second layer `s : Input α`: `Selection s …`, `datum : _ → SecondInputDatum α`, slots `T`,
     `w σ v θ` over `α`, `s.P j = Z^(w j)`, `s.upper`, `s.lower` (normalized cofactor),
     `s.X₁ … s.Y₂`, `volume s`, `forcedProfileCost s`, `card α ≤ N`.
   - `|logb Z (volume s)| ≤ B` is the **second** layer: it bounds the side box at `A_v = logb Z (volume s)`
     (`balanced_geometry_side_box`). Coordinates and side are both read at `A_v`, so the payment lemmas
     (`HighScalar/*`) are unchanged.
2. **Two amplitudes.** `amp l` (radius, coordinates, `F.amp l = a_v`) and `poolAmp l`
   (`FixedCellPoolData (pool l) Z (poolAmp l) ell …`, `mainExtra s₀ … (poolAmp l) ell`,
   `0 ≤ radius l + 6*poolAmp l ≤ radiusMax`, the HIGH source's `ell := poolAmp/2`).
3. **The δ-shift**, at BalancedCofactor only. The balanced mass becomes the shifted mass
   `Z^(amp l - poolAmp l) * balancedFirstHighMass … s₀ … (column l)`, bounded by the lead's
   `QRH.MixedStep.Downstream.shifted_high_mass_mx` at the virtual side `Av`. New data:
   `amp poolAmp : κ → ℝ`, `shiftLoss : ℝ`,
   `hshift : ∀ l ∈ labels, amp l - poolAmp l ≤ logb Z (volume s₀) - Av + shiftLoss`.
   Every conclusion above BalancedCofactor gains `+ shiftLoss` in the `Z`-exponent (next to `B*εmass`).
   Above BalancedCofactor, `Av := logb Z (volume s)` (second layer).

## 1. Module list (dependency order)

Lines are the source module sizes. The column "needs" lists non-Collet, non-PR 76 imports.

| # | M/ module | source | declarations | change | needs |
|---|---|---|---|---|---|
| 1 | High/GlobalPhysicalRegularRawPositive | A/ (278) | `actual_modified_regular_raw_family_uniform_tau_rm_mx` | α₀/α split (`s₀` = first layer; datum, slots, `w σ v θ` over `α`) | none |
| 2 | High/GlobalPhysicalAllRawPositive | A/ (192) | `actual_modified_all_raw_family_uniform_tau_rm_mx` | α₀/α split | 1 |
| 3 | High/GlobalPhysicalAllCofactorPositive | A/ (225) | `actual_modified_all_cofactor_family_uniform_tau_rm_mx` | α₀/α split | 2 |
| 4 | High/GlobalPhysicalSelectedCofactor | A/ (240) | `actual_modified_selected_cofactor_family_uniform_tau_rm_mx` | α₀/α split | 3 |
| 5 | High/GlobalPhysicalBalancedCofactor | A/ (267) | `actual_modified_balanced_cofactor_family_uniform_tau_rm_mx` | two parents, free `Av`, shifted mass, `hshift`, `+shiftLoss`, `card α₀ ≤ N` and `card α ≤ N` | 4, lead's `Downstream/Shift` |
| 6 | HighScalar/ModifiedPayment | A/ (72) | `modified_retained_high_exponent_rm_mx` | ι₀/ι split (`d2 : SecondInputDatum ι`) | none |
| 7 | HighScalar/NonregularModified | A/ (73) | `nonregular_modified_retained_high_exponent_rm_mx` | ι₀/ι split | none |
| 8 | High/GlobalPhysicalSectorPayment | A/ (96) | `modified_selected_sector_singleton_payment_rm_mx` (reuses `selectedSectorGain_rm`) | ι₀/ι split | 6, 7 |
| 9 | High/GlobalPhysicalAnnularCofactor | A/ (260) | `actual_modified_annular_cofactor_family_uniform_tau_rm_mx` | two parents; `A := logb Z (volume s)`; `amp poolAmp shiftLoss hshift` passed to 5 | 5, 8 |
| 10 | Admission/SelectedHighCofactorFamilySome | A/ (324) | `FamilyStatement_rm_mx`, `actual_selected_annular_cofactor_family_uniform_tau_rm_mx` | two parents; `hcoef` from the lead's `eventual_modified_normalized_cofactor_mx` | 9, lead's `Admission/SelectedHighCofactorCoordinates` |
| 11 | High/GlobalPhysicalPaidSome | A/ (273) | `FamilyStatement_rm_mx`, `actual_selected_annular_cofactor_family_uniform_tau_rm_mx` | `PhaseBound_mx`, `mainExtra s₀ … poolAmp`, pool at `poolAmp`; sum via `uniform_selected_paid_sum_mx` | 10, F1/F2 `SelectedHighPaidComparison` |
| 12 | High/GlobalPhysicalBufferedPaidSome | A/ (326) | `FamilyStatement_rm_mx`, `actual_buffered_selected_cofactor_family_uniform_tau_rm_mx` | as 11, bin split unchanged | 11 |
| 13 | Admission/SelectedRegularHighSource | S/ (54) | `selected_common_caps_mx` | `Family_mx`: first caps from `sourceRadius F.s₀`, `F.zero₁₀/₂₀`; second from the child | F1 `SelectedRegularSourceData` |
| 14 | Admission/SelectedRegularHighSourceSome | A/ (593) | `ModifierAt_rm_mx`, `SourceAt_rm_mx`, `ActualAt_rm_mx`, `FamilyStatement_rm_mx`, `actual_selected_regular_high_source_uniform_tau_rm_mx` | `Anchor_mx`/`Family_mx`/`Selected_mx`; poolAmp; hshift | 12, 13, F1 `…State` (`eventual_selected_retained_data_mx`), F5 `SelectedRegularGeometryCaps` (`eventual_selected_geometry_caps_mx`) |
| 15 | Admission/SelectedRegularHighPointSomeGeometry | S/ (134) | `actual_coordinate_box_mx`, `SharedState_mx` | `Family_mx`; `hsource` for `s₀`, `hV` for `s` | F1 |
| 16 | Admission/SelectedRegularHighPointSome | A/ (251) | `SourceAt_rm_mx`, `actual_point_rm_mx` | two `Canonical` records (`c₀` for `F.s₀`, `c` for `F.s`), `F.amp l = amp`, pool at `poolAmp`, hshift | 14, 15, F5 `GlobalPhysicalRegularPhase` (`actual_regular_phase_mx`) |
| 17 | High/GlobalPhysicalRegularHighParameters | A/ (66) | `regular_some_source_rm_mx` | `ell := poolAmp/2` | 14 |
| 18 | High/GlobalPhysicalRegularControls | A/ (93) | `regular_some_controls_rm_mx` | LOW half from F3 (`regular_low_controls` twin) | 16, 17, F3 |
| 19 | Admission/SelectedRegularCombinedPointSome | A/ (195) | `eventually_actual_point_rm_mx` | LOW/HIGH junction | 16, F3 (`eventually_initial_low_point` twin, `Shared`), F5 (fusion) |
| 20 | High/GlobalPhysicalRegularPoints | A/ (119) | `regular_some_point_source_rm_mx` | concludes F5's `RegularPointAt_mx` | 18, 19, F5 |
| 21 | High/GlobalPhysicalRegularSuppliers | A/ (110) | `regular_supplier_some_rm_mx` | via F5's `regular_supplier_of_points_mx` | 20, F5 |

**No twin needed** (reused verbatim): `HighScalar/LabelPayment`, `NonregularLabels`, `NonregularGain`,
`SingletonLoss` (generic in `l : FirstSourceLabel` and `d2`), `PositiveRadius/*`, `WholeActualBinTau`,
`ActualBinSourceTau`, `RegularRootSupplierTau`, `RootCompletion`, `Max*`, `UniformWeighted`
(no parent), and Collet's `eventual_cofactor_large_raw`, `eventually_marked_packet_extra`,
`first_frequency_ne_zero`, `rawKey` (already split into `ι`/`α`).

Rows 1–10 depend only on Collet, PR 76, the lead's `Downstream/Shift.lean` and the lead's
`eventual_modified_normalized_cofactor_mx`. They are drafted and compiled first.

## 2. Ownership questions for the lead

1. **BalancedCofactor (row 5).** The design lists it under F2. The δ-shift enters there, so I plan to
   write `M/High/GlobalPhysicalBalancedCofactor.lean` myself, using your `shifted_high_mass_mx`
   unchanged. Tell me if you already have it.
2. **GlobalPhysicalRegularPoints (row 20).** Collet's `RegularPointAt` (F5, `RegularPointAt3`) and PR 76's
   `regular_some_point_source_rm` share one path, so they share one ForkMx module. Proposal: you define
   `RegularPointAt_mx` in `M/High/GlobalPhysicalRegularPointAt.lean` (non-path name), or you own
   the whole file and I hand you `regular_some_point_source_rm_mx` as text.
3. **F3/F4 junctions (rows 18, 19).** `regular_some_controls_rm` and `eventually_actual_point_rm` combine
   LOW (`RegularLowAt`, `regular_low_controls`, `eventually_initial_low_point`, `Shared`) with HIGH.
   I will write them once the F3 twins exist.
4. **Collet twins I claim** (listed under "## F4 twins" in HANDOFF.md once it exists):
   `selected_common_caps_mx` (S/Admission/SelectedRegularHighSource), `actual_coordinate_box_mx`,
   `SharedState_mx` (S/Admission/SelectedRegularHighPointSomeGeometry).

## 3. Expected signatures (top of each layer)

### Row 5, the only new arithmetic

```lean
theorem actual_modified_balanced_cofactor_family_uniform_tau_rm_mx {α₀ α : Type}
    [Fintype α₀] [DecidableEq α₀] [Fintype α] [DecidableEq α]
    (ηanchor η₀ …) … (N : ℕ) :   -- PR 76 parameter block, unchanged
    ∃bound, (∀k,0<bound k) ∧ ∃J, ∀τ … ∀P …, ∃control C, 0<C ∧ ∀ᶠZ in atTop, 2≤Z ∧
    ∀{κ DataLabel}[Nonempty κ][Fintype DataLabel],
    ∀(reflected second)(s₀ : Input α₀)(modifier₀ : Tuple α₀→ℂ)(_hη : s₀.η=ηanchor)
      (R seed Wa D ξ hK bin)(column : κ→FirstColumnIndex (geometryFirstSource s₀ modifier₀ …))
      (datum : DataLabel→SecondInputDatum α) … ,
    ∀(a rootError width Bbox target reserve)(i) …,
    ∀(labels)(x coeff)(slots : κ→Finset α)(w σ v : α→ℝ)(t)(θ : α→…) …,
    Squarefree seed→s₀.W₁ 0=0→s₀.W₂ 0=0→sourceRadius s₀≤Z^B→
    ∀(Av : ℝ), |Av|≤B→loMass≤s₀.lower→(∀x,s₀.W₁ x≠0→ap≤x)→(∀x,s₀.W₂ x≠0→ap≤x)→
    ∀(amp poolAmp : κ→ℝ)(shiftLoss : ℝ),
      (∀l∈labels,amp l-poolAmp l≤Real.logb Z (volume s₀.toData)-Av+shiftLoss)→
    … (∀l∈labels,retainedHighExponent … (x l)≤balancedGeometrySide reflected Av
          (geometryExponents s₀ modifier₀ … (column l).1.val)+target-reserve) →
    … Fintype.card α₀≤N→Fintype.card α≤N→ … →
    (∑l∈labels,(Z^(amp l-poolAmp l)*balancedFirstHighMass reflected s₀ modifier₀ … (column l))*
        ‖…‖^2*coeff l) ≤
      geometryHighFactor … * cofactorRestorationCost … *C*Kcontrol*(…)^4*(1+rawGeometryHeight Z τ I)^J*
      Z^(target-reserve+4*width+loss+rootError+2*P.εplain*P.d+(2*P.εslot*P.d)*N+B*εmass+shiftLoss)
```

### Row 10 / 12 (the paid HIGH family)

`FamilyStatement_rm_mx` = PR 76's `FamilyStatement_rm` with: `(s₀ : Input α₀)(Amark… : Ideal O)` for the
first layer (modifier `markedSourceModifier` over `α₀`), `(s : Input α)` for the second; `choose : ∀l, Selection s …
(firstLabel s₀ …)`; mass hypotheses on `s₀`; `|logb Z (volume s)| ≤ B`, `loMass ≤ s.lower` (cofactor) and
`loMass ≤ s₀.lower` (mass); `amp poolAmp : κ→ℝ`, `shiftLoss`, `hshift` with `Av = logb Z (volume s)`;
pool, `radius+6*poolAmp`, `PhaseBound_mx s₀ modifier₀ s … (mainExtra s₀ … (poolAmp l) ell)`; both cards `≤ N`;
conclusion exponent `… + B*εmass + shiftLoss`.

### Row 14 (`ActualAt_rm_mx`, first statement over the structures)

Quantifies over `a : Anchor_mx α₀ α Z`, `fam : Family_mx a Label`, `g : Selected_mx fam Row rows second`; then
PR 76's `ActualAt_rm` with `s₀ := fam.s₀`, `s := fam.s`, `poolAmp : rows→ℝ`, `shiftLoss`, `hshift`.

### Row 20/21 (top)

```lean
theorem regular_some_point_source_rm_mx (hN₀ : card α₀ ≤ N) (hN : card α ≤ N) (high : Source) … (hparent …)
    (hgaps : ∀ν∈Icc (n.q:ℝ) (3/4), ActualGaps_rm n low (some high) bcell ν reserve) :
    ∃degree controls, (0,0)∈controls ∧ ∃C τsource, 0<C ∧ 0<τsource ∧ ∀ᶠZ in atTop, 1<Z ∧
      RegularPointAt_mx (α₀:=α₀) (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low bcell reserve θ mesh ξ width
        τsource N degree controls C Z      -- F5's statement; n = the virtual node
theorem regular_supplier_some_rm_mx … : RegularJointSupplier3 …   -- F5's contract, via regular_supplier_of_points_mx
```

## 4. Hypotheses left for the ledger / assembly

All per instance of the node `(n, low, bcell) = (vnode2 n low b δ θ, low, b-θ)`:
`∀ν∈Icc q (3/4), ActualGaps_rm (vnode2 …) low (some h) (b-θ) ν reserve` (ledger §3);
`F.amp l = sourceAReal (vnode2 …) low (b-θ) = r+δ` (`vnode2R_A`); the second-layer width window
`(b-θ)-δwidth ≤ Σ_res ≤ b-θ` and `logb Z (volume s) ≤ sourceTReal n b + (b-θ)` (both from `θ ≤ δ_act`, §0.3);
`hshift` with `shiftLoss = 2*mesh` (`δ - δ_act ≤ 2 mesh`); `poolAmp = a` with `FixedCellPoolData` at `a`.

## 5. License headers

Every file starts with the source's notice blocks verbatim (for a PR 76 file: its fork note, then the
underlying Collet/Gao notice), then: "Mixed step (L4/L5, F4): fork of <module> (<author>, Apache-2.0);
changes: two parents (s₀ first layer, s second layer), …".
