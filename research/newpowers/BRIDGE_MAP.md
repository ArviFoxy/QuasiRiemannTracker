# BRIDGE_MAP: HIGH rows of PR 83's density leaf -> marked amplitude-class count

Read-only study, 2026-10-28. No `lake`/`lean` was run, nothing was committed.
Every Lean statement quoted below was read in the file and line cited. `[I]` marks an inference that is
not a Lean statement; `[N]` marks a number computed from the Lean definitions in a Python model (scratch,
not Lean-checked).

Paths are relative to `/home/user/lean-env/qrh/Submissions/`.

| tag | directory |
|---|---|
| `LEAF` | `sil_density_split_20261026/Density` |
| `BASE` | `openai_baseline/OAI/NumberTheory/DirichletL/Hecke` |
| `BASEM` | `openai_baseline/OAI/NumberTheory/DirichletL/Moments` |
| `COL` | `hailey_collet_1252270103` |
| `PR76` | `arvi_repeated_marks_on_sil_face_20261025` |

## 0. Verdict

**The best bridge is not the baseline `Fiber` count. It is PR 76's raw-row, regular-core HIGH count on a
fixed natural dictionary, applied to the leaf's HIGH classes.**

PR 76 (`PR76/Fork/Record1252270103Source/PositiveRadius/SomeDictionary.lean:31`) states, for raw rows
`NonzeroFrequency` of the whole-source family of a fixed anchor dictionary, with exactly the zero-bin
guards that `LeafRows.selectBin_spec` produces:

    sum_{h in rows} (prod_{s in slots} max 1 ||labeledRawSlot ... h s||)^2
      <= C (1+rawGeometryHeight Z tau I)^J
         Z^( rho(2a-1) F + (2a-1) S - gainC (2a-1) B lam cap S F + small )

That is the leaf's `high_row_count` times the pointwise slot factor of `high_row_bound`, with the marked
gain `gainC` (eight repeated marks, one detector cutoff per amplitude class) subtracted.

* **Moments consumed from the caller: none.** The only analytic input is
  `UnitFaceSource ⟨B,lam,0,B,0,cap⟩ sourceMesh εm`, which is the leaf's own `hparent` after
  `hparent ε' hε'` (`LEAF/Leaf.lean:152`). The unmarked gates, plain-marked (parent face) and
  inverse-marked (eight copies, overlapping prime lists) fibre moments are produced inside.
* **No 7/37 supply field.** The inverse witness is `z = min(8S, (Q-r)/2)`, the plain witness
  `z = min(S, hQ, (BQ-y)/lam)`; the 7/37 of the baseline `Fiber` does not occur.
* **Raw rows and zero guards fit.** `geometryRowFamily` is definitionally `wholeSourceFamily ... (excluded
  (naturalRow st.character z _).character st.puncture)`, the family PR 76 quantifies over.
* **Gain at the leaf's binding configuration** (`nu = q = 0.65`, `Q = M = 1`) [N]:
  `G_8 = 0.0123` at `S = 0.03` and `0.0133` for `S >= 0.05`. The baseline route with natural moments gives
  about `0.005-0.008`.

Ranking of bridges (details in 2, 3, 4, 5):

| # | bridge | entry point | caller supplies | gain `nu=.65`, `S=.03/.05` [N] | effort | main risk |
|---|---|---|---|---|---|---|
| 1 | PR 76 dictionary-level raw-regular count + finite-core count | `PR76/.../PositiveRadius/SomeDictionary.lean:31`, `COL/Record12518109Gain/ExceptionalCounts.lean:26` | `UnitFaceSource`, zero guards, slot data | .0123 / .0133 | ~1000 Lean lines | height cut, 40-hypothesis plumbing |
| 2 | Collet's unforked twin (same call, `K=1`, six-facet `High.gain`) | `COL/Record1252270103Source/PositiveRadius/SomeDictionary.lean:22` | same | .0058 / .0097 | same call shape; use first as a dry run | none beyond #1 |
| 3 | `NaturalBatch` weighted row sum (free rows only) | `PR76/Source/ActualWeightedK.lean:31`, `PR76/Source/WeightedK.lean:131` | `NaturalBatch` + `UnitFaceSource` | like #1 | more than #1 | raw rows, punctures |
| 4 | Baseline `Fiber`/`Batch` + `Cycle25DetectorRawFiber.Moments` | `COL/Cycle25/Assembly/Count/Adaptive.lean:15` | the four moments, `7/37` supply | .005-.008 | much more than #1 | inverse-marked moment unavailable; supply |
| 5 | Return's face-based count | `sil_density_split_20261026/ReturnD/PhysicalDirect/PhysicalSourceCount.lean:33` | `SourceData` | n/a | not applicable | tied to `SourceData`/`sourceMomentData` |

## 1. What has to be replaced

Current leaf HIGH branch, in order of use:

* Count (unmarked), `LEAF/LeafHigh.lean:102`:

      theorem high_row_count {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character)
          (loss : ℝ) (hloss : 0 < loss) :
          ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ {Z bΦ : ℝ}, 0 < bΦ → ∀ (j : κ) (st : NaturalState Z 0 bΦ),
            st.character = anchors j → st.puncture = 1 → ∀ (hQM ...) (hQη ...) (b T' : ℝ),
            33/40 ≤ b → b ≤ 7/8 → 0 ≤ T' → ∀ rows : Finset O, (∀ z ∈ rows, ∃ hz : st.radial.keep z,
              st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 ∧
              b ≤ Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz T') →
            (rows.card : ℝ) ≤ C*(1+T')^J*(bΦ*Z^st.rowWidth)^(unmarkedDensity (2*b-1)+loss)

  proved from `fixed_natural_dictionary_raw_density` with `highDictionary` (`LeafHigh.lean:96`).
* Pointwise (all slots at full amplitude `nu`), `LEAF/LeafHighRow.lean:58`, conclusion

      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
          (fun k => primePool rayM H 2 (Z^(w k)))
          (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
          (fun k => Z^(w k)) t X₁ X₂‖^2 ≤
        K * (p.control S)^2 * Z^((2*b-1)*(length Z X₁ + length Z X₂ + ∑ k, w k) + 2*ε₁*d*(Fintype.card α + 1))

  (internally `actual_high_retained_row`, `COL/Cycle61/Moment/HighRetainedRows.lean`, which is
  `actual_buffered_retained_plain_factors` (`COL/Cycle61/Moment/BufferedRetainedRows.lean:14`) followed by
  `actual_high_slot_product` (`COL/Cycle61/Moment/HighSlotProduct.lean:~20`)).
* Assembly, `LEAF/LeafHighEnergy.lean:39` (`high_branch`) through `energy_le_classes`
  (`LEAF/LeafRows.lean:113`): classes `BufferIndex e` (chosen bin `selectBin`, `LeafRows.lean:269`;
  `selectBin_spec` :277; `selectBin_high` :294), `R c` pointwise, `N c` count.
* Price: `highTerm nu P s M = nu*(P+s) - 10*nu/(15-6*nu)*M` (`LEAF/Price.lean:45`), `highSup` :52,
  `densityPrice` :123 (`max (lowPart ..) (highSup ..)`), `Price` structure `CubeFree/Price.lean:29`
  (`nonneg`, `mono` in `P`,`s`, `lipP`, `lipS`, `lipM`).
* Seam: `density_priced_source` (`LEAF/Leaf.lean:139`), face hypotheses
  `hface : 0 < B₀ ∧ B₀ ≤ 1 ∧ 0 < c₀`, `hL : 0 < L₀`, `hparent : GlobalSource B₀ L₀ c₀`.

Target: replace `R c * N c` by a class **sum** bound whose exponent is
`rho(nu) M + nu s - G(nu; s, M)` (so that `highTerm` becomes `nu P + nu s - (1-rho) M - G`).

## 2. Bridge 1: PR 76's HIGH fork

### 2.1 What PR 76 proves (stack, bottom to top)

All modules are mechanical `*_rm` forks of Collet's `Record1252270103Source.High` in which the HIGH gain
is `QRH.RepeatedMarks.Source.gainC` (eight copies, `PR76/Source/GainC.lean:48`) and the detector cutoff is
per amplitude class.

| tier | theorem | file:line | row/slot genericity |
|---|---|---|---|
| A fibre | `feedback_fiber_count_K` | `PR76/Source/FiberK.lean:88` | abstract `Row Label Slot`, `Q : Row → Slot → ℂ`, input `FiberMomentsK` (:57) |
| A batch | `weighted_row_sum_K` | `PR76/Source/WeightedK.lean:131` | abstract; sums over amplitude bins, `witness` per bin cutoff `binCutoffK` (:63) |
| B | `ordinary_actual_weighted_row_sum_K` | `PR76/Source/ActualWeightedK.lean:31` | `NaturalBatch` (`COL/Record12518109Gain/ActualSourceFields.lean:87`), free rows |
| C | `actual_max_row_sum_from_zero_bins_uniform_tau_rm` | `PR76/Fork/.../High/ActualBinSourceTau.lean:36` | zero-bin guards -> witnesses + amplitude envelope |
| C raw | `actual_regular_raw_max_from_source_bins_uniform_tau_rm` | `PR76/Fork/.../PositiveRadius/SomeRaw.lean:41` | raw `NonzeroFrequency`, one anchor |
| C dict | `actual_dictionary_regular_raw_max_uniform_tau_rm` | `PR76/Fork/.../PositiveRadius/SomeDictionary.lean:31` | raw rows, anchors `Index → Character`, **entry point** |
| D (NF step only) | `actual_modified_regular_raw_family_uniform_tau_rm` | `PR76/Fork/.../High/GlobalPhysicalRegularRawPositive.lean:45` | first/second joint rows, `key`, `labels`; not reusable |
| D | `actual_buffered_selected_cofactor_family_uniform_tau_rm` | `.../High/GlobalPhysicalBufferedPaidSome.lean:207` (`FamilyStatement_rm` :65) | cofactors, Newton, paid weights; not reusable |
| D | `regular_supplier_some_rm` | `.../High/GlobalPhysicalRegularSuppliers.lean:77` | NF-step supplier |
| top | `nf_step2 : Graph.NFStep2` | `PR76/Source/NFStep2.lean:121` | `GlobalSource n.B n.L n.cap` from LOW and HIGH parents |

Raw-to-free root completion (generic, any nonnegative `f` on `NonzeroFrequency`):
`full_gain_root_completion_rm` (`PR76/Fork/.../High/RootCompletion.lean:37`).
Supported witnesses at every cutoff in `[1,3/2]`: `actual_feedback_witness_family_rm`
(`PR76/Source/WitnessWrappersK.lean:27`), `ordinary_local_witness_family_rm` (:53), built on baseline
`HeckeDetectorSupportedWitness.actual_supported_witness_family` (`BASE/DetectorSupportedWitness.lean:16`).

**The HIGH rows the NF step applies it to are the same objects as the leaf's.** `FamilyStatement_rm`
(`GlobalPhysicalBufferedPaidSome.lean:65`) takes `st : κ → NaturalState Z P.Bmask P.bΦ`,
`RetainedZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) e (Z^P.τ) (select l)` and
`(q+1)/2 ≤ bufferValue e (select l)`, and sums over `highBins e q`
(`COL/Record1252270103Source/High/GlobalPhysicalBufferedPaidSome.lean:44`) =
`{p | (q+1)/2 ≤ bufferValue e p ∧ bufferValue e p ≤ 7/8}`. The leaf's HIGH classes are the same
(`LeafRows.lowRow` :260, `selectBin_high` :294, `LeafHighEnergy` class set `N c`).
`RetainedZeroBin` is `COL/Record1252270103Source/Coefficient/RegularRetainedNaturalBins.lean:22`.

### 2.2 The pivot theorem (verbatim hypotheses of `SomeDictionary.lean:31-`)

    theorem actual_dictionary_regular_raw_max_uniform_tau_rm
        {Index : Type} [Fintype Index] [Nonempty Index] (base : Index→Character) (η₀ : Character)
        (sourceB sourceLam sourceCap sourceMesh : ℝ)
        (hB0 : 22/23≤sourceB) (hB1 : sourceB≤1) (hlam : 1<sourceLam) (hh0 : 0≤sourceCap) (hh1 : sourceCap<1)
        (setup : DensityCountingSetup) (W : ℝ→ℂ)
        (bΦ εm binWidth ζ η dmin dmax rmin Rwidth ε e κ ηw εslot ηslot : ℝ) (I : ℕ) (δ Bmask Broot wmin : ℝ)
        (hδ : 0<δ) (hBmask : 0≤Bmask) (hBroot : 0≤Broot) (hwmin : 0<wmin)
        (hparentSource : QRH.Record12518109Existence.UnitFaceSource
            ⟨sourceB,sourceLam,0,sourceB,0,sourceCap⟩ sourceMesh εm)
        (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
        (hbΦ : 2≤bΦ) (hrad : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bΦ)
        (hbin : 0<binWidth) (hη : 0<η) (hζ : 0<ζ) (hεm : 0<εm)
        (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hrmin : 0<rmin) (hRw : 0≤Rwidth)
        (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hηw : 0≤ηw)
        (hbudget : 288*e+8*κ+2*ηw≤ε/2) (hεslot : 0<εslot) (hηslot : 0≤ηslot)
        (hslotBudget : 8*e*Rwidth+κ≤εslot) (hgap : εslot<rmin*binWidth)
        (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
        (qlo Q mesh : ℝ) (hqlo : 0<qlo) (hQ : qlo≤Q) (hQroot : Q/12≤Broot) (hdlo : dmin≤qlo/2+δ)
        (hdsource : Q+Bmask+δ≤dmax) (hrlower : rmin≤wmin/dmax) (hmesh : 0≤mesh)
        (hmeshmax : mesh≤sourceMesh) (hmeshR : mesh≤Rwidth) :
        ∃J : ℕ,∃C : ℝ,0<C ∧∀τ : ℝ,0<τ →τ<dmin/2 →4*τ<dmin*ηw →2*τ<dmin*ηslot →∀ᶠZ : ℝ in atTop,1<Z ∧
          ∀index : Index,∀(F a : ℝ)(i : ℕ),i≤I →3/4≤a →a≤7/8 →qlo≤F →F≤Q →binWidth≤(2*a-1)/2 →
          ∀{Row : Type}[Nonempty Row](rows : Finset Row)(row : Row→NonzeroFrequency),
          Set.InjOn row (↑rows:Set Row)→∀(slots : Finset Slot)(w σ v : Slot→ℝ)
            (t : Row→ℝ)(θ : Slot→RayQuotient.Characters M H)(mask : Row→Ideal O)(χ : Row→Character),
          (∀h∈rows,rawFrequencyNorm (row h)≤Z^F) →
          (∀h∈rows,¬(wholeRegularDictionary M H hH (base index) η₀).exceptionalCore
              (sixthFrequencyEquiv.symm (row h)).1) →
          (∀h∈rows,mask h≠0) →(∀h∈rows,((mask h).absNorm:ℝ)≤Z^Bmask) →
          (∀h∈rows,∀K,idealCoeff (χ h) K=idealCoeff
            (excluded (naturalRow (base index) (row h).val (row h).property).character (mask h)) K)→
          ∀hn : ∀h∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ h) j).residue≠1,
          (∀h∈rows,∀hh : h∈rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh)
              (3*(i+1:ℕ)*Z^τ)<a+2*e) →
          (∀h∈rows,∀hh : h∈rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ h)) (hn h hh) ((3*i:ℕ)*Z^τ)) →
          (∀s∈slots,wmin≤w s) →(∀s∈slots,(33/50)≤σ s) →(∀s∈slots,σ s≤(33/50)) →
          (∀s∈slots,w s≤mesh*dmin) →
          (∀h∈rows,|t h|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
          (∀h∈rows,∀s∈slots,|t h+v s|+Z^τ/2≤(3*i+2:ℕ)*Z^τ) →
          let S:=∑s∈slots,w s;
          (∑h∈rows,(∏s∈slots,max 1 ‖labeledRawSlot M H hH η₀ W Z w σ v t θ χ h s‖)^2)≤
            C*(1+rawGeometryHeight Z τ I)^J*Z^(rho (2*a-1)*F+(2*a-1)*S
              -QRH.RepeatedMarks.Source.gainC (2*a-1) sourceB sourceLam sourceCap S F
              +dmax*(155*ε+mesh+εm+(2*a-1)*ζ+η)+rho (2*a-1)*δ+2*binWidth*S)

(`M H hH` are section variables: `M : Ideal O`, `[NeZero M]`, `H : Subgroup (O⧸M)ˣ`,
`hH : RayOrthogonality.globalUnits M≤H`; `Slot : Type` with `[Fintype Slot] [DecidableEq Slot]`.)

Supporting definitions: `labeledRawSlot` (`COL/Record12518109Natural/CommonRawWeights.lean:23`) is
`naturalSlot (χ l) (primePool M H 2 (Z^(w k))) (heightCoefficient (fun I => idealCoeff
(relativeCharacter M H hH η₀ (θ k)) I * annularWeight W (Z^(w k)) (σ k) (v k) I) (t l)) (Z^(w k))`;
`rawGeometryHeight Z τ I = (2*Real.pi+6*(I+1:ℕ))*Z^τ` (`COL/Record12518109Natural/RawGeometryHeight.lean:15`);
`rho = QRH.Record1252270103Source.High.rho = unmarkedDensity` by `rho_eq_original`
(`COL/Record1252270103Source/High/Rescale.lean:9`).

### 2.3 Moments consumed (answer to "what moments does it need")

None are passed in. Inside, `ordinary_actual_weighted_row_sum_K` (`PR76/Source/ActualWeightedK.lean:31`)
builds, for every amplitude bin / label / dyadic cell, `FiberMomentsK` (`PR76/Source/FiberK.lean:57`) =
`OrdinaryFiberMoments` (`COL/Record1252270103Source/High/ActualFiber.lean:20`:
`inverseUnmarked`, `plainUnmarked`, `inverseMarked`, `plainMarked B lam h`) plus `inverseRep`
(inverse-marked for `selected ⊆ slots ×ˢ Fin copies`), from:

* `Record12518109GainActualUnmarked.actual_unmarked_fiber_gates`
  (`COL/Record12518109Gain/ActualUnmarkedGates.lean:15`; unmarked inverse and plain, needs
  `DensityCountingSetup` and `51/100 ≤ beta`),
* `ordinary_marked_source_fields_fixedmesh` (`COL/Record1252270103Source/High/SourceFields.lean:26`;
  single-copy inverse-marked and plain-marked on the parent
  face, from `hsource : UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm`),
* `replicated_inverse_source_field` (`PR76/Source/SourceFieldsK.lean:29`), whose analytic input is
  `overlapping_annular_inverse_marked_energy`
  (`COL/Record12518109Gain/Upstream/DeletionInverseOverlap.lean:73`): any finite family of at most `K`
  possibly repeated prime lists. Repeated and equal slot widths are therefore legal, which removes the
  `D.slots_injective` obstruction of the baseline (`Cycle25/Assembly/MomentData.lean`).

Global inputs the caller must still provide: `DensityCountingSetup` (use
`LocalMoment.canonicalDensityCountingSetup`, `COL/Cycle61/Density/CountingSetup.lean:14`), `bΦ` with
`radialMajorant` support (`bRad := max 2 bRad₀` from `radialMajorant_support_bound`,
`BASEM/DetectorEnergyInitialState.lean:68`; recipe in `PR76/Fork/.../High/GlobalPhysicalRegularSuppliers.lean:89-96`), the
wmin/rmin/εslot package (`cardinality_loss_exists`, `COL/Record1252270103Source/Core/PhysicalAnalyticParameters.lean:61`,
`wmin = θ/(N+1)`).

### 2.4 Does the leaf's HIGH data fit the hypotheses?

Mapping, hypothesis by hypothesis:

| PR 76 argument | leaf value | status |
|---|---|---|
| `Index`, `base`, `η₀` | `κ`, `anchors`, `η₀` | fits; add `[Nonempty κ]` |
| `Row := NonzeroFrequency`, `row := id`, `mask := fun _ => st.puncture (= 1)` | `rows.subtype (· ≠ 0)` as in `high_row_count` (`LeafHigh.lean:116-123`) | fits |
| `χ h` | `excluded (naturalRow st.character z _).character st.puncture`; `st.character = anchors j` | `hcoeff` is `rfl`-level |
| zero guards on `wholeSourceFamily M H hH η₀ (χ h)` | `geometryRowMaximum` = `zeroMaximum (geometryRowFamily ..)` and `geometryRowFamily = wholeSourceFamily M H hH η₀ (excluded (naturalRow st.character z _).character st.puncture)` (`COL/Cycle61/Physical/InitialMass/GeometryZeroPartition.lean:18-33`) | definitional match |
| upper `< a+2e` at `3(i+1)Z^τ`, lower `a ≤` at `3iZ^τ` | `RetainedZeroBin .. e T p` (`RegularRetainedNaturalBins.lean:22`): `bufferValue e p ≤ max(3pT)`, `max(3(p+1)T) < bufferValue e p + 2e`; take `T = Z^τ`, `a = bufferValue e p`, `i = p ≤ bufferCount e =: I` | fits when the base height is `Z^τ` (see M1) |
| `3/4 ≤ a ≤ 7/8` | HIGH bins have `bufferValue ≥ (q+1)/2 ≥ 33/40` | fits |
| `qlo ≤ F ≤ Q`, `rawFrequencyNorm ≤ Z^F` | `‖eisEmbedding z‖^2 ≤ bΦ*Z^st.rowWidth`; `F = M + ε'`, `qlo = Mmin`, `Q = Mmax + ε'` | fits (`bΦ ≤ Z^ε'` eventually) |
| `hparentSource` | `hu` of `Leaf.lean:152`: `UnitFaceSource (globalFace B₀ L₀ c₀) unitMesh ((ε/4)/max 1 Mmax)`; `globalFace B lam cap = ⟨B,lam,0,B,0,cap⟩` (`COL/Record1252270103Source/Core/Contract.lean:15`) | fits; `sourceMesh := unitMesh`, `εm := (ε/4)/max 1 Mmax` |
| slot data `slots, w, σ, v, θ, W` | `T`, `w`, `σ = 33/50`, `v'`, `θ`, `W` with `hWs` | fits (`σ` in `[33/50,33/50]` on both sides) |
| slot height | `|t+v' k| + Z^τ/2 ≤ (3i+2)Z^τ`, `|t| + Z^τ/2 ≤ (3i+2)Z^τ` | fits when `|t|+height ≤ Z^τ` (M1) |
| `22/23 ≤ B₀ ≤ 1`, `1 < L₀`, `0 ≤ c₀ < 1` | leaf has `0 < B₀ ≤ 1`, `0 < L₀`, `0 < c₀` | **add hypotheses**; true on the chain: example parent `G(0.99999, 2.5715, 0.1397)` (`research/density/README.md`) [I] |
| `w s ≤ mesh*dmin`, `mesh ≤ sourceMesh` | `w k ≤ mesh_leaf ≤ unitMesh*Mmin` (`Leaf.lean:157-159`, `hmU`); `dmin ≤ Mmin/2 + δ` | **shrink the leaf's mesh to `unitMesh*Mmin/2`** (one-line change in `hmeshPos`/`hmU`) |
| `wmin ≤ w s` for every slot | leaf has only `0 ≤ w k` | M2 |
| `¬exceptionalCore` | leaf rows are `initialKeep` rows; cores of kept raw rows can be exceptional | M3 |

Mismatches and resolutions:

* **M1 height regime (the structural one).** PR 76 fixes the bin heights as `3iZ^τ`, `3(i+1)Z^τ` with
  `i ≤ I` (`I` is an argument before `∃J C`, the `Z`-threshold comes after `τ`); the leaf uses
  `T₀ = (h+1)Z^τ` with `h = ⌈(|t|+height)/Z^τ⌉` unbounded (`Leaf.lean:347`, `LeafHighEnergy.lean:39`
  hypotheses `(h:ℝ) ≤ |t|+height+1`; the bounded-height branch is `by_cases hlarge : Z^c < 1+|t|+height`,
  `Leaf.lean:304`, `c := d*vg/16` :240). The places that need a fixed exponent `τ` and `i ≤ I` are the witness
  supplier (`actual_feedback_witness_family_rm`, `WitnessWrappersK.lean:27-41`: conclusion
  `SupportedWitness (χ u) (Z^d) a ε t (Z^τ) ((Z^d)^(τ/(2*dmax))) i`) and the amplitude envelope
  `HeckePrimeAmplitudeActual.ray_amplitude_bins` (used at `ActualBinSourceTau.lean:~93`). The unmarked density avoids it by
  height-uniform eventual estimates (`COL/LocalMoment/HeightUniformDensity.lean`, "do not manufacture such
  uniformity from pointwise eventual estimates").
  Resolution [I]: cut the bounded-height branch of `density_priced_source` at `|t|+height ≤ Z^τ`
  instead of `Z^c` (take `c := τ`, `h := 0`). Then `binIndex p 0 = p` (`LeafRows.lean:211`) and `i = p ≤ B`.
  The native branch (`Leaf.lean:317`, `hZk`; `k` defined at :245) absorbs `Z^{3/4 Σ w}` with
  `k := ⌈(3/4 N)/τ⌉` instead of `⌈(3/4 N)/c⌉`; only the final `degree` changes. Constraints: `hcτ : 4c+4τ ≤ d*vg/2` holds for `c = τ`
  since `τ ≤ d*vg/16`; `τ*J ≤ ε/16` already holds; add `4τ < dmin*ηw`, `2τ < dmin*ηslot`, `τ < dmin/2`.
  The factor `(1+rawGeometryHeight Z τ I)^J = (1+(2π+6(I+1))Z^τ)^J ≤ const·Z^{τJ}` replaces `(1+T')^J`.
* **M2 small slots.** `NaturalBatch.inverseLarge` needs conductor `< U^{w s}` (`COL/Record12518109Gain/ActualSourceFields.lean:114`), so
  slots below `wmin` cannot enter. Split `T = T_large ∪ T_small`, `T_large = {w ≥ wmin}`:
  small slots by `actual_high_slot_product` (`COL/Cycle61/Moment/HighSlotProduct.lean`) at full amplitude,
  cost `nu·Σ_small w ≤ nu·N·wmin` with `wmin = ε/(8N)`-type (`cardinality_loss_exists`); large slots by
  PR 76. The combined exponent is `rho F + nu S - G(S_large,F)` against the target `rho F + nu S - G(S,F)`;
  the loss `G(S,F) - G(S_large,F) ≤ nu (S - S_large) = nu S_small ≤ nu N wmin` is `gainK_width_mono`
  (`PR76/Gain/Gain.lean:478`: `nu*S - G(S,Q) ≤ nu*L - G(L,Q)` for `S ≤ L`).
* **M3 exceptional cores.** The exceptional free cores form a finite set
  (`FixedUnmarkedDictionary.exceptional_cores_finite`, `COL/Cycle61/Density/NaturalDictionary.lean:93`;
  `exceptionalCore` :106; dictionary `wholeRegularDictionary`, `COL/Record12518109Gain/WholeRegularSetup.lean:35`),
  but all their sixth-power multiples are rows. Count them with
  `finite_core_raw_count` (`COL/Record12518109Gain/ExceptionalCounts.lean:26`):
  `(R.card:ℝ) ≤ (E.card:ℝ)*128*H^(1/6:ℝ)`, and bound them pointwise by the leaf's own `high_row_bound`.
  Exponent check: `F/6 + nu(P+s)` versus `rho F + nu(P+s) - G`; this needs `G ≤ rho F - F/6`, true because
  `gainK_le_cmax` (`PR76/Gain/Gain.lean:565`) gives `G ≤ nu(1-baseXi nu)F = (nu+rho-1)F` and
  `nu + rho - 1 ≤ rho - 1/6` iff `nu ≤ 5/6`. No condition on `s` [I].
  (Do not use `actual_finite_core_raw_maximum`, `ExceptionalSupplier.lean:47`: it carries the crude slot
  exponent `Σ w`, which then requires `(1-nu)s + G ≤ (rho-1/6)F`.)
* **M4 slot identification.** Leaf slot `normalizedSlot st.character st.mask 1 z pool β t P`
  (`BASEM/WholeSlotDeletion.lean:26`, `= (√P)⁻¹ * rowSlot ..`) equals
  `naturalSlot (excluded F.character R) pool (heightCoefficient β t) P` for `st.mask = fixedBadMask *
  idealGenerator st.puncture` (`BASE/../Energy/State.lean`, `NaturalState.mask`) by
  `positive_raw_natural_slot` (`COL/Record1252270103Source/Coefficient/RegularPositiveRawNatural.lean:24`,
  `R := st.puncture ≠ 0`). `max 1 (x^2) = (max 1 x)^2`: `positive_raw_max_square` (same file, :39). The
  `1`-puncture variant is `slot_unit_mask` (`LEAF/LeafRows.lean:38`).
* **M5 pointwise plain factor.** PR 76 bounds the slot-product sum only. The plain factor is
  `‖retainedPositiveRow ..‖^2 ≤ C^2 (Z^d)^((2a-1)(r 0+r 1)+2ε) ∏ ‖normalizedSlot ..‖^2`
  (`actual_buffered_retained_plain_factors`, `BufferedRetainedRows.lean:14`, hypotheses: upper guard
  `zeroMaximum χ hχ (3*(i+1)*Z^τ) < a+2*e`, `hcoeff` with `χ := wholeSourceFamily .. `). New lemma L2 below
  is the first half of `high_row_bound` (it stops before `actual_high_slot_product`).
* **M6 energy assembly.** `energy_le_classes` takes pointwise `R` and counts `N`; PR 76 gives sums. New
  lemma L3 (variant with `hsum`).
* **M7 parameters.** `dmin ≤ qlo/2 + δ`, `Q+Bmask+δ ≤ dmax`, `rmin ≤ wmin/dmax`, `mesh ≤ Rwidth`, budgets
  `288e+8κ+2ηw ≤ ε/2`: arithmetic; the leaf's `ε₁, e, kap, vg, d` recipe (`Leaf.lean:~165-215`) is the same
  kind. The NF-step instantiation is the template: `PR76/Fork/.../High/GlobalPhysicalRegularRawPositive.lean:213`
  (`hc.2 j q a i hiI ha ha' hq0 hq1 hνbin rows (fun l => nonzeroJointSourceRow (key l)) hinjrow ss w σ v t θ
  holes χ hrowq ...`).

### 2.5 The gain and the `Price` axioms

`gainC nu B lam h S Q = gainK nu 8 B lam h (max S 0) (max Q 0)` when `ParentParams nu 8 B lam h`, else `0`
(`PR76/Source/GainC.lean:48`). `ParentParams` (`PR76/Gain/Gain.lean:392`): `0<nu`, `nu≤3/4`, `0≤K`,
`22/23≤B`, `B≤1`, `1<lam`, `0≤h`, `h≤1`. `gainK nu K B lam h S Q = sInf_{p in [0,1/2]} gainP ..`
(`Gain.lean:378`); `gainP = (1-2p)nu S + nu(xiP - baseXi nu Q)`, `xiP` = least of six branch roots with
thresholds `invThr p K x S Q = max (x-2pKS) ((x-pQ)/(1-p))` (:16) and
`plainThr p B lam h x S Q = max (x-2pS) (max (x-2phQ) ((x-2pBQ/lam)/(1-2p/lam)))` (:19).
Properties proved (all in `Gain/Gain.lean`) and the `Price` axiom each gives for
`highTermM nu P s M = nu(P+s) - (1-rho)M - gainC nu B₀ L₀ c₀ s M`:

| `Price` field | lemma |
|---|---|
| `nonneg` (of the high part, via `max` with the low part) | `gainK_nonneg` :424, `gainK_le_nuS` :418 |
| `mono` in `s`: `nu s - G` nondecreasing | `gainK_width_mono` :478 |
| `lipS`: `highTermM(s+δ) ≤ highTermM(s) + nu δ` | `gainK_mono_S` (`PR76/Source/GainC.lean:20`) |
| `lipM` | `gainK_mono_Q` :525 and `gainK_row_loss` :545 (`G(S,F) ≤ G(S,q) + nu(1-baseXi nu)(F-q)`) |
| homogeneity (`M` normalisation) | `gainK_smul` :586 |
| common-width payment (Lemma C) | `gainK_payment` :432 |

## 3. Bridges 2 and 3

### 3.1 Bridge 2: Collet's unforked twin

`QRH.Record1252270103Source.PositiveRadius.Some.actual_dictionary_regular_raw_max_uniform_tau`
(`COL/Record1252270103Source/PositiveRadius/SomeDictionary.lean:22`) has the same hypothesis list and the
same conclusion with `QRH.Record1252270103Source.High.gain` (PR 70's six-facet gain,
`COL/Record1252270103Source/High/Selection.lean:31`: `gain nu B lam h S Q = nu*(xi nu B lam h S Q - baseXi nu*Q)`
with inverse slopes `![1,2]` and offsets `![-S,-Q]`; this is `gainP` at `p=1/2`, `K=1`). Use it as the
dry run for the plumbing; swapping to the `_rm` statement only changes the gain function.
It needs nothing from PR 76's fork.

### 3.2 Bridge 3: `NaturalBatch` weighted row sum

`ordinary_actual_weighted_row_sum_K` (`PR76/Source/ActualWeightedK.lean:31`): arguments
`(copies : ℕ) (hcopies : 1 ≤ copies) (base anchor : Label→Character) (bad : Label→Ideal O)`, the four `bad` side
conditions, `(capacity lam cap sourceMesh : ℝ)` with `22/23≤capacity≤1`, `1<lam`, `0≤cap<1`, `setup`, `W`, `bΦ εm ζ`,
`hsource : UnitFaceSource ⟨capacity,lam,0,capacity,0,cap⟩ sourceMesh εm`, `hβ`; conclusion
`∃J C, 0<C ∧ ∀ᶠ U, 1<U ∧ ∀ B : NaturalBatch M H hH base anchor bad W (33/50) (33/50) U, .. (witness per bin) ..
→ ∑u∈B.rows, ‖∏s∈B.slots, B.Q u s‖^2 ≤ (|BinLabel|·|Label|·(dyadicLength U)^2·C)(1+height)^J
U^(rho (2a-1)+(2a-1)S - gainRep copies (2a-1) capacity lam cap S 1 + 155ε+mesh+εm+(2a-1)ζ+2·binWidth·S)`.
It is for free rows (`B.rows : Finset FreeRow`) and needs the inverse and plain slot representations
(`inverseIdentity`, `plainIdentity`, `COL/Record12518109Gain/ActualSourceFields.lean:87-125`) as `NaturalBatch`
fields; Bridge 1 builds these inside (`PositiveRadius/SomeLabeled.lean`, `SomeUniform.lean`). Use it only if
Bridge 1 fails on the raw/regular split.

## 4. Bridge 4: baseline `Fiber` / `Batch` (the original Q1-Q4, kept for the record)

### 4.1 Chain from `Fiber` + `Moments` to the per-class count

1. Fibre field/moment structures: `Fiber` (`BASE/DetectorRawFiber.lean:16`), `Moments` (:62, parameters
   `Δ c κ C height εm`), Cycle25 variant `Cycle25DetectorRawFiber.Moments` (`COL/Cycle25/Assembly/Count/Moments.lean:14`,
   `original : HeckeDetectorRawFiber.Moments F 0 c κinverse C height εm` plus `plain_marked` with `κplain`),
   `Moments.of_fields` (:60), `BaseMoments` (:36), `MarkedPlainMoment` (:51).
2. Four fibre bounds: `Fiber.inverse_marked_count` (`BASE/DetectorRawBranches.lean:18`),
   `Fiber.plain_marked_count` (:30), `Fiber.plain_unmarked_count` (:42), unmarked inverse; from
   `inverse_fiber_count` (`BASE/DetectorInverseFiberCount.lean:18`), `plain_fiber_count`
   (`BASE/DetectorPlainFiberCount.lean:13`), `no_slot_plain_count` / `no_slot_inverse_count`.
3. Combination at the cutoff: `count_bound_of_source_branches`
   (`COL/Cycle25/Assembly/Count/Optimization.lean:9`) gives `max (shortExponent ..) (longExponent ..)`,
   evaluated at `cutoff δ p κ = 1+δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))`
   (`COL/Cycle25/Assembly/Count/Endpoint.lean:6`) to `rowCount δ p κ` (`max_at_cutoff` :55).
4. Batch sum over bins/labels/dyadic cells: `Batch` (`BASE/DetectorBatch.lean:11`), `Batch.card_bound` (:63);
   most generic entry in the baseline family:
   `Cycle25ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments` (`COL/Cycle25/Assembly/Count/Adaptive.lean:15`):

       ∀ ... (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
         B.rows.Nonempty → (∀u∈B.rows, rowMean .. = q) →
         (∀bin j J K, ∀hne, Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
         (B.rows.card:ℝ) ≤ |Label|·(dyadicLength U)^2·fiberConstant C height K₀·|B.Bin|·
           U^(rowCount (2*a-1) (q/(2*a-1)) κplain + 159*ε + εm + B.mesh + 7*ν)

   packaged as `CountParameters.balanced` (`COL/Cycle25/Assembly/Count/Parameters.lean:15`). Hypotheses:
   `1<U`, `51/100<a`, `2a-1≤3/4`, `0≤ε≤1/1000`, `7/10≤κplain≤3/4`, `0<ν`, `2π allowance+3iT≤height`.
5. `rowCount δ p κ = countingR κ δ p` for `7/10 ≤ κ`:
   `Cycle61.Assembly.Count.rowCount_eq` (`COL/Cycle61/Assembly/Count/ArithmeticIdentity.lean:13`),
   `Record12518109Return.countingR_eq_actual` (`COL/Record12518109Return/CountingBridge.lean:9`);
   `countingR κ d p` is `COL/Cycle61/Arithmetic/Bernstein/Feedback.lean:17`; `countingR κ ν 0 = rho ν` [I].

Row-generic building blocks (no `FreeRow`, no `Fiber`): `Record12518109GainFiber.inverse_fiber_count`
(`COL/Record12518109Gain/FiberPrimitives.lean:38`, `Q : Row → Slot → ℂ`, needs only `0<Σw`, `z ≤ Σw`).

### 4.2 `Fiber` fields against the leaf

| field | needs | leaf offers | mismatch |
|---|---|---|---|
| `rows : Finset FreeRow` | `FreeRow = {u // u≠0 ∧ SixthFree (span {u})}` (`BASE/InverseAmplificationRows.lean:38`) | raw `z : O` | raw to free: counts only via `raw_core_density_uniform` (`COL/Cycle61/Density/ExceptionalLift.lean:17`, `ρ ≥ 2/7`); weighted sums need `full_gain_root_completion_rm` |
| `family : FreeRow → Label → Character` | per-row dictionary | `wholeSourceFamily M H hH η₀ (excluded (naturalRow (anchors j) z _).character 1)`, index `WholeSourceIndex` | changes with the sixth-power part |
| `witness : SupportedWitness ..` | `T`, `allowance`, `i` | zero guards | `actual_supported_witness_family`: `T=Z^τ`, `i ≤ I` (M1) |
| `label,left,right,fixed_*` | dyadic partition | `Batch.fiberRows` | none |
| `row_norm` | `N(u) ≤ U` | `‖eisEmbedding z‖^2 ≤ bΦ Z^M` | `U = Z^d` with `d = M+ε` |
| `rowData, reverse, row_coeff` | coefficient equality with `momentData` | `hc0` of `high_row_count` | none [I] |
| `slots, profile, upper, widths, external, bin, mesh, binWidth` | `physical M H (fun u => u.val) profile upper widths external U u s = canonicalPrimeAmplitude M H u (W s) (b s) (U^(w s)) (z s)` (`BASE/DetectorPhysicalSelection.lean:12`, `BASE/PrimeRow.lean:69`) | twisted slot `naturalSlot (excluded ..) (primePool ..) (relativeCharacter η₀ (θ k) * annularWeight)` | **the baseline slot is the pure-row prime sum `D^{-1/2} Σ conj(idealRowHom u P) W(N P/D) (N P/D)^{z-1}` over the identity ray class: no row character `η`, no anchor/ray twist.** Needs an abstract-`phys` fork of `Fiber`/`Batch`, as `PR76`/`Record12518109Gain` do (`Q : Row → Slot → ℂ`). `σ = 33/50` corresponds to `z.re = 17/50`. |
| `widths_pos`, `widths_mesh`, `mesh_nonneg`, `binWidth_pos` | positive widths | `w k ≥ 0` | zero-width slots must be dropped |
| `supply : 7/37 ≤ Σ widths` | see 4.4 | `Σ w` small | not satisfiable |
| `fixed_bin` | amplitude bin equality | none yet | assembled by `adaptiveFiberK_fields` (`PR76/Source/WeightedK.lean:89`) in PR 76 |

### 4.3 `Moments` fields

* `inverse_raw` (unmarked inverse): `fixed_raw_profiles` (`COL/Cycle25/Assembly/Count/InverseRawField.lean:24`)
  is independent of the slots; available for the leaf's dictionary.
* `plain_unmarked`: zero-slot energy; the leaf already has it (`hceZ`/`hevZ` in `Leaf.lean:216-222`, from
  `Candidate.FourthPower.NativeNonfixedEnergy.canonical_energy`).
* `plain_marked` (`2*F.m + 6*κ*Σselected ≤ 1`, i.e. face `B=1`, `Λ=6κ`): energy identification
  `retainedSourceEnergy_eq_energy` (`BASEM/DetectorPlainStateDictionary.lean:25`) then a `NaturalState` bound
  with profiles `Profiles (1/4) (9/4)`; the general parent face needs `AffineMarkedMoment` (5.2).
* `inverse_marked`: no ready lemma for the leaf's twisted slots; the baseline route
  (`weighted_fiber_reference_energy`, `COL/Cycle25/Assembly/Count/MomentInverseMarkedReferenceFiberEnergy.lean:19`)
  needs distinct widths (disjoint annuli) and `SourceData`. PR 76's `replicated_inverse_source_field` closes this gap.

### 4.4 The `7/37` supply (original Q3)

Consumed at: `Fiber.supply` (`BASE/DetectorRawFiber.lean:46`) and `Fiber.mean_bounds` (:83);
`toFiber` `hsupply` (`BASE/DetectorFiberPartition.lean:74`, field :107); `Batch.supply`
(`BASE/DetectorBatch.lean:33`); wrappers `Fiber.inverse_marked_count` / `plain_marked_count`
(`BASE/DetectorRawBranches.lean:18-40`: `hz' : z ≤ 7/37` then `hz'.trans F.supply`); capacity budgets
`inverse_requested_capacity` (`BASE/DetectorBranchBudget.lean:50`: `(1-r)/2-ν ≤ 7/37`),
`plain_requested_capacity` (:60: `(1-2m)/(9/2+12Δ)-ν ≤ 7/37`), `strict_inverse_capacity`
(`BASE/DetectorRowCountCrossing.lean:95`: `(1-r)/2 ≤ 7/37`), `prime_supply_margin` (:112).
Padding with zero-weight dummies violates `widths_pos` (`DetectorRawFiber.lean:44`, `DetectorBatch.lean:31`);
positive-width dummies must be genuine prime sums, so only the dilution route of
`masked_row_count_transfer` (`COL/Cycle25/Assembly/Count/MaskedCount.lean:79`; Sil's copy
`sil_density_split_20261026/ReturnD/PhysicalDirect/MaskedCount.lean` uses it) is
available, and it dilutes the mean to `p = s/(2·7/37)`: gain about `0.0046` at `nu=0.6`, `s=0.07` [N].
In PR 76's route the supply never appears.

### 4.5 Pointwise side (original Q4)

The leaf's bound has every slot at amplitude `nu`. The amplitude-resolved bound is assembled from
`actual_buffered_retained_plain_factors` (`BufferedRetainedRows.lean:14`, which keeps
`∏ ‖normalizedSlot‖^2`) and `HeckePrimeAmplitudeBins.product_upper`
(`BASE/PrimeAmplitudeBins.lean:118`: `‖∏ Q i‖ ≤ U^((Σ w i * amplitude ..) + mesh*Σ w i)`) with the per-slot cap
`amplitude_upper`. PR 76 packages this as `weighted_bound_of_card_K` (`PR76/Source/WeightedK.lean:19`):
count `<= A U^(rho nu + nu S - G - 2 q S + loss)` times `U^(2qS + 2 binWidth S)` gives
`U^(rho nu + nu S - G + loss + 2 binWidth S)`.

## 5. The parent-face route (coordinator's addendum)

### 5.1 How `(B, Λ, cap)` enter in the return's face-based count

* Natural moment: `plain_marked` with `2*F.m + 6*κplain*Σselected ≤ 1`
  (`COL/Cycle25/Assembly/Count/Moments.lean:17-22`), i.e. the face `B = 1`, `Λ = 6·κplain`, no cap;
  `κplain = D.momentKappa ∈ [7/10, 3/4]` (`COL/Cycle61/Assembly/Count/Data.lean:29-30`), so `Λ ∈ [4.2, 4.5]`.
  The baseline `Moments` has `6*(3/4+2*Δ)` (`BASE/DetectorRawFiber.lean:73`).
  So `momentKappa = Λ/6` and the `1` is `B` [I] (read off the shape of the gate).
* General face: `AffineMarkedMoment F f C height εm` (`COL/Record12518109Count/MarkedFiber.lean:20`):
  `f.plainLo ≤ F.m ≤ f.plainHi`, `f.slotLo ≤ Σselected ≤ f.slotHi`, `2*F.m + f.lam*Σselected ≤ f.B`; with
  `SourceFace ⟨B,lam,plainLo,plainHi,slotLo,slotHi⟩` (`COL/Record12518109Source/InitialMoment.lean:19`).
  `affine_marked_count` (`MarkedFiber.lean:34`) turns it into a count for one fibre.
* Window: `AdmittedWindow naturalκ` (`COL/Record1252270103Return/AdmittedWindow.lean:10`): fields
  `B lam cap sourceCap mLo mHi`, `lam_gt_one : 1<lam`, `cap_le_source`, `cap_small : cap≤7/37`, and the
  value axioms (`inverse_crossing`, `plain_crossing : plainCurve B lam cap δ p (cutoff δ p - crossing δ p) ≤ value δ p`,
  `natural_tail`, `widths`, `long_crossing`, `antitone`). Face of a window: `broadFace w.B w.lam w.sourceCap`
  (`COL/Record1252270103Return/SourceInlet.lean:25`), `plainCurve B lam cap δ p m = 1-2δm-2δp·min cap ((B-2m)/lam)`
  (`CountCurve.lean:8`).
* Envelope: `GenericCount.envelope κ δ p = QRH.Record1252270103Return.envelope admittedBranches κ δ p`
  (`CountScheme.lean:17`) = finite minimum of `countingR κ δ p` and the available window values
  (`finiteEnvelope`, `COL/Record12518109Return/FiniteEnvelope.lean`). `class CountScheme` has
  `naturalκ ∈ [7/10, 3/4]` and `windows : List (AdmittedWindow naturalκ)` (:8).
* Sil's `CountParameters` (`sil_density_split_20261026/ReturnD/PhysicalDirect/CountParameters.lean:28`)
  consumes three moment families per fibre: `Cycle25DetectorRawFiber.Moments .. κplain co κo ..`,
  `Moments .. scheme.naturalκ ca κa ..`, and `∀ w∈scheme.windows, AffineMarkedMoment .. w.face ..`;
  `SourceMomentBound` (`ReturnD/PhysicalDirect/MomentGates.lean:47`) states them for batches with
  `B.data = sourceMomentData ..`, `B.family u j = sourceDetectorFamily ..`, `B.upper = fun _ => b`.

### 5.2 Can the face-based count take the leaf's parent face and rows?

* The leaf's `hparent : GlobalSource B₀ L₀ c₀ = UniformUnitFaceSource (globalFace B₀ L₀ c₀)`
  (`COL/Record1252270103Source/Core/Contract.lean:19`) has the right type for a window face after
  `global_restricts_broad` (`COL/Record1252270103Return/SourceInlet.lean:26`, needs `1/2 ≤ B`) and
  `unit_source_restrict` (:37); `L₀ ≈ 2.3-2.6 > 1` satisfies `lam_gt_one`.
* But the transport to detector moments, `detector_affine_of_unit`
  (`COL/Record1252270103Return/CountSource.lean:35`) is stated for `F : WeightedSourceData D` and the output
  `WeightedAffineFineInput F face` (`COL/Record12518109Count/InitialTransport.lean:26`) quantifies over
  `Batch S.modulus ⊤ (Sum Bool ..) (Fin D.N)` with `B.data = sourceMomentData ..`, `B.profile = fun _ x => (S.w x:ℂ)`,
  `B.upper s = 2`, `(B.external s).re = 17/50`, `B.widths = D.ell s/d`; and `MomentData` requires
  `slots_injective` (`Cycle25/Assembly/MomentData.lean`). The leaf's rows and ray-twisted slots are not of that shape.
  So the transport would have to be re-run (forked) for the leaf's rows.
* The return's `physical_source_amplitude_count` (`Sil .../PhysicalSourceCount.lean:33`, Cycle61 original
  `COL/Cycle61/Assembly/Count/SourceCount.lean:17`) is tied to `SourceData` and the probe rows: unusable.
* Therefore: the face-based route is useful for the scalar side only; the entry that already combines "face moment
  + repeated marks + raw leaf-type rows" is Bridge 1, where the face enters through `UnitFaceSource` and the
  gain `gainC nu B lam cap`, and `Λ = lam` directly.

Face effect [N]: from `Gain.lean` formulas, `G_K(S=.05, Q=1, nu=.65)`:
natural face `(1, 4.5, 1)`: `K=1` `0.0080`, `K=8` `0.0119`; leaf-type parent `(0.9998, 2.5665, 0.10)`: `K=1` `0.0097`,
`K=8` `0.0133`. The face adds `0.0014-0.0017`; the repeated marks (supply `K·S`) add `0.003-0.004`.

## 6. Build plan (original Q5), ordered by dependency

All new code in a fork of the leaf package (`Density/`), namespace `QRH.SilDensitySplit.Density`.

**L0. Dry run against Collet's twin (Bridge 2).** Instantiate `COL/.../SomeDictionary.lean:22` on one class
with `Row := NonzeroFrequency`, `row := id`. Purpose: debug M1-M7 plumbing before depending on PR 76's fork. ~150 lines.

**L1. `high_class_sum_marked`** (new `Density/LeafHighMarked.lean`). Shape:

    theorem high_class_sum_marked {κ} [Fintype κ] [Nonempty κ] {α} [Fintype α] [DecidableEq α]
        (anchors : κ → Character) (η₀ : Character) (B₀ L₀ c₀ sourceMesh εm : ℝ)
        (hB0 : 22/23 ≤ B₀) (hB1 : B₀ ≤ 1) (hL : 1 < L₀) (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1)
        (hparent : UnitFaceSource (globalFace B₀ L₀ c₀) sourceMesh εm) (W ..) (hWs ..) (hW ..)
        (Mmin Mmax e : ℝ) (hβ : 51/100 ≤ HeckeZeroSupremum.beta) ... :
      ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → [small] → ∀ᶠ Z in atTop, 1 < Z ∧
        ∀ j (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 → ... →
        ∀ (p : BufferIndex e), 3/4 ≤ bufferValue e p → bufferValue e p ≤ 7/8 →
        ∀ T θ w σ v' t [|t|+height ≤ Z^τ] ... (rows : Finset O),
          (∀ z ∈ rows, ∃ hz, RetainedZeroBin rayM H hH st η₀ hQM hQη z hz e (Z^τ) p ∧ Φ-weight ≠ 0) →
          ∑ z ∈ rows, (∏ k ∈ T.filter (wmin ≤ w ·), max 1 ‖normalizedSlot st.character st.mask 1 z
              (primePool rayM H 2 (Z^(w k))) (β k) t (Z^(w k))‖)^2
            ≤ C * Z^(τ*J) * Z^(unmarkedDensity ν * M + ν * S' - gainC ν B₀ L₀ c₀ S' M + loss)   -- ν = 2*bufferValue e p - 1
          ∧ (exceptional part) ≤ ... Z^(M/6 + loss)

Proof: regular rows by `actual_dictionary_regular_raw_max_uniform_tau_rm` (hypotheses table 2.4, M4 for
`labeledRawSlot`), exceptional rows by `finite_core_raw_count` + pointwise bound (M3), small slots (M2).
Estimated 300-450 lines. **Riskiest step:** instantiating about 40 hypotheses (dmin/dmax/rmin/Rwidth/budgets,
`hgeom`-type arithmetic) and the regular/exceptional split.

**L2. `high_row_plain_factor`** (`Density/LeafHighRow.lean` variant). First half of `high_row_bound`
(`LeafHighRow.lean:58-200`) ending at

    ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1) pool β P t X₁ X₂‖^2 ≤
      K * (p.control S)^2 * Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
        ∏ k, ‖normalizedSlot st.character st.mask 1 z (pool k) (β k) t (P k)‖^2

from `actual_buffered_retained_plain_factors` instead of `actual_high_retained_row`. ~150 lines, low risk.

**L3. `energy_le_class_sums`** (`LeafRows.lean:113` variant): replace `hrow`/`hcount` by
`hsum : ∀ c, ∀ rows : Finset O, (∀ z∈rows, keep z ∧ Φ(..) ≠ 0 ∧ cls z = c) → ∑ z∈rows, ‖positiveSlotRow ..‖^2 ≤ R' c`,
conclusion `energy .. ≤ diagonalControl Φ * ∑ c, R' c`. Same proof (`Finset.sum_fiberwise`). ~50 lines.

**L4. `high_branch_marked`** (`LeafHighEnergy.lean:39` variant): classes `BufferIndex e`, `R' c` from L1+L2,
exponent `st.rowWidth + highSupM q (..) (∑ w) st.rowWidth + small`. Uses a `high_exponent`-type scalar lemma
(`LeafHigh.lean:46`) with `highTermM`. ~150 lines.

**L5. Marked price** (`Density/Price.lean` variant):

    def highTermM (B₀ L₀ c₀ nu P s M : ℝ) : ℝ :=
      nu*(P+s) - 10*nu/(15-6*nu)*M - QRH.RepeatedMarks.Source.gainC nu B₀ L₀ c₀ s M
    def highSupM (B₀ L₀ c₀ q P s M : ℝ) : ℝ := ⨆ nu : Set.Icc q (3/4:ℝ), highTermM B₀ L₀ c₀ nu P s M
    def markedDensityPrice .. (hL : 0 < L₀) : Price     -- like densityPrice (Price.lean:123)

Axioms from the table in 2.5 (`highSupM_le_add` analog of `highSup_le_add`). `rhoOf` = `unmarkedDensity` =
`rho` by `rho_eq_original`. ~150 lines.

**L6. `density_priced_source_marked`** (`Leaf.lean:139` variant): changes (i) `hface` strengthened with
`22/23 ≤ B₀`, `1 < L₀`, `c₀ < 1`; (ii) mesh `min (unitMesh*Mmin/2) ..`; (iii) bounded-height branch cut at
`Z^τ`, `h := 0` (M1), native branch with `k := ⌈(3/4 N)/τ⌉`; (iv) new `τ` bounds (`τ<dmin/2` etc.);
(v) `hevH` from L4. LOW branch unchanged (it takes `h`; `h = 0` is a special case). ~150 changed lines of 552.

**L7 (outside this bridge).** Gate `highJ_marked` replacing `ds_high_aux` (`Density/StepGates.lean:152`) and the
certificate generator (`research/density/gen_hybrid.py`) for `highTermM`; reuse `PR76/Gain/Bernstein2.lean`
(`checkBox_sound`) and `PR76/Finite/HighGate.lean` (2-D Bernstein in `(nu,p)`, 59 nodes certified there).

Total ~1000-1100 Lean lines. Dependency order: L0, L2, L3, L1, L5, L4, L6.

## 7. Numbers [N]

`gainK nu K B lam h S Q` at `Q = 1` (homogeneous of degree 1, `gainK_smul`), parent `(0.9998, 2.5665, 0.10)`,
computed by re-implementing `invThr`, `plainThr`, `branchRoot`, `xiP`, `gainP` (`PR76/Gain/Gain.lean:16-103`) in
Python and minimising over a 501-point grid of `p in [0,1/2]` (scratch:
`$SCRATCH/p8.py`, `p10.py`).
Binding class: `p = 1/2` in every `K=1` cell; for `K=8` also whenever `S ≥ 0.07` and `nu ≥ 0.6`, but it moves to
`p < 1/2` for small `S` (e.g. `nu=0.65, S=.02`: `p*=0.34`) and at `nu=0.5, S ≤ .03` the cap `G = nu S` (`p=0`) binds:

| nu | S=.02 K=1/8 | S=.03 K=1/8 | S=.05 K=1/8 | S=.07 K=1/8 |
|---|---|---|---|---|
| 0.50 | .0050 / .0100 | .0075 / .0150 | .0125 / .0226 | .0175 / .0252 |
| 0.55 | .0048 / .0110 | .0072 / .0161 | .0120 / .0210 | .0168 / .0221 |
| 0.60 | .0044 / .0118 | .0066 / .0154 | .0111 / .0175 | .0149 / .0180 |
| 0.65 | .0039 / .0109 | .0058 / .0123 | .0097 / .0133 | .0123 / .0133 |
| 0.70 | .0031 / .0076 | .0047 / .0081 | .0073 / .0085 | .0085 / .0085 |
| 0.75 | .0021 / .0038 | .0031 / .0040 | .0040 / .0040 | .0040 / .0040 |

Saturation is at the slot-free branch at `p=1/2` (the inverse cap `(Q-r)/2`), not at the slot width [I]; the face (B, Λ, cap) matters little (natural face `(1,4.5,1)` gives `.0119` instead of `.0133` at `nu=.65`, `S=.05`, `K=8`).
Pointwise bound check: `highTermM` is below `highTerm` by exactly `G`, so the ledger gate gains `G(s, M)` at the
binding `nu = q`.

## 8. Not verified / open

* Nothing here was compiled. Each hypothesis of 2.2 was matched by reading statements; the `Z`-threshold and
  quantifier order (`∃J C ∀τ ∀ᶠZ`, then `∀index F a i ..`) are compatible with the leaf's
  `∃J ∀τ ∃K S ∀ᶠZ` order [I].
* `22/23 ≤ B₀`: PR 76's own node 58 has `B = 0.95609 < 22/23` (`research/repeated-marks/README.md` §9 table);
  it is not used as a HIGH parent there. The density chain has `B ≈ 0.99+` [I]; check the final faces.
* `gainC` is hard-wired to `K = 8`.
* Import weight: `SomeDictionary` imports `PR76/Finite/SourceValid2.lean` (-> `Finite/HighGate.lean`), not the 59 node files.
* `bΦ` of PR 76 (radial majorant support) is unrelated to the leaf's `Φ`-support `bΦ`.
* The exceptional-core estimate (M3) is a derivation [I]: it uses `finite_core_raw_count` and `high_row_bound` only.
