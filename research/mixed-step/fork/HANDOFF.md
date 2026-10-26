# Fork handoff (L4/L5): F1/F2 interfaces for the F4 (HIGH spine) helper

Status 2026-10-26: written by the fork agent (F1/F2 → F3 → F5, F6/N6 if time). The F4 helper may
start compiling now. All files below compile with `mk_mixed.sh` and have standard axioms only.

## Conventions

- **Layout.** A fork of Collet's `Record1252270103Source/<path>.lean` goes to
  `Submissions/arvi_mixed_step/ForkMx/Record1252270103Source/<path>.lean` (module
  `Submissions.arvi_mixed_step.ForkMx.Record1252270103Source.<path>`). If PR 76 also forked that path
  (`arvi_repeated_marks_on_sil_face_20261025/Fork/<same path>`), its `_rm` declarations are re-forked in the
  **same** ForkMx module, which then imports PR 76's fork module (which imports Collet's).
  New, non-forked glue goes to `Submissions/arvi_mixed_step/Downstream/`.
- **Names.** `<name>_mx` in the namespace of the original; a PR 76 declaration `<name>_rm` becomes
  `<name>_rm_mx`. Local instances get a fresh name (e.g. `…DecEq_mx`) to avoid clashes with the original
  module's anonymous instances.
- **License header (Apache-2.0 §4).** A ForkMx module starts with the source file's copyright line
  verbatim, then the fork note:
  ```
  /- Copyright (c) 2026 Hailey Collet. Apache-2.0.
  Mixed step (L4/L5): fork of Record1252270103Source.<path>; changes: two parents, two amplitudes. … -/
  ```
  (For a PR 76 `_rm` source, Collet's copyright line is the one inside PR 76's file; keep it verbatim
  first.) `research/mixed-step/fork/fix_headers.py ForkMx_root` checks/fixes this.
  **Our own notice.** The fork note is preceded by `Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.`
  (same comment, directly before the line `Mixed step …`; in a file that keeps the original's comment
  separate, the note comment starts with it). The same applies to every non-fork file that keeps a
  third-party copyright line (`Transfer/*`, `Downstream/{Balanced3,Contract3}`, `Source/NFStep3`, …).
  `fork/add_mod_line.py DEVROOT` inserts it (idempotent; keeps source mtimes) and `package/make_submission.py`
  refuses a package with a derived file that lacks it. New files carry no copyright line (as in PR 76).
- **Two parents.** First layer = the original input `s₀ : Input α₀` with modifier `modifier₀`
  (columns `geometryFirstSource s₀ modifier₀ …`, `firstLabel`, `columnCharacter`, `columnIdeal`,
  `dictionaryRay`, `rawKey`, `balancedColumnScalar`, `coordinateBlock`, `balancedFirstHighMass`,
  `geometryExponents`, `actual_geometry_norm_caps`, `label_*` lemmas, `mainExtra s₀ …`).
  Second layer = the second-layer parent `s : Input α` (keeps Collet's name): `FirstStage s`, `child s`,
  `Selection s`, `selectedPaidWeight`, `sel.raw`, `volume s`, `firstMainRadius … (volume s) … (3*amp)`,
  `Selection.coordinate` (at `logb Z (volume s)`), slot widths/pools of `s`, `forcedProfileCost s`.
  Mechanical rule: `X.s X.modifier ↦ X.s₀ X.modifier₀`; the scalar's volume argument
  `(Real.logb Z (volume s))` inside `balancedColumnScalar`/`balancedFirstHighMass` ↦ `volume s₀`.
  Everything else keeps `s`. Hypotheses of a Collet lemma that are used for both layers are
  duplicated (`hN₀ : card α₀ ≤ N`, `hlower₀`, `hsource₀`, … for `s₀`).
- **Two amplitudes.** `amp` (= `F.amp l`, the virtual `a_v`) is the radius/coordinate amplitude;
  `poolAmp` (`a`, the actual pool width) is the pool's: `FixedCellPoolData P Z poolAmp (poolAmp/2) …`,
  `mainExtra s₀ C P H0 radius poolAmp ell` (ball factor `(radius+6·poolAmp)/ell`, `ell = poolAmp/2`).
  The pool `P` is always the **actual** pool (never a virtual pool).
- **δ-shift.** It enters the HIGH spine only where the first mass meets the coordinates (PR 76's
  `GlobalPhysicalBalancedCofactor_rm`, around its lines 196–210): use the shifted mass
  `Z^(amp l - poolAmp l) * balancedFirstHighMass reflected s₀ …` (this is what
  `uniform_selected_paid_sum_mx` produces), the side at the virtual volume
  `side l := balancedGeometrySide reflected (logb Z (volume s)) (geometryExponents s₀ … (column l).1.val)`,
  and `QRH.MixedStep.Downstream.shifted_high_mass_mx` with
  `hshift : amp - poolAmp ≤ logb Z (volume s₀) - logb Z (volume s) + κ` in place of
  `actual_balanced_uniform_high_mass`. The loss `κ` is an extra additive exponent.
- **Node facts.** The HIGH spine runs at an abstract node `n` (for the transfer: the ledger's
  `vnode n low b δ` at width `b - δ`). `ActualGaps_rm n low (some high) bcell ν reserve` stays a
  hypothesis exactly as in PR 76. Do not use `RealGeometry`/`ParentGood n`; if a node fact is needed,
  use the fields of `QRH.MixedStep.Downstream.NodeGeometry_mx` (Downstream/Node.lean) or a plain
  hypothesis, and list it here.
- **Proof hygiene.** No `sorry`/`axiom`/`native_decide`/`admit`; `#print axioms` on every top
  theorem. `Finset.prod_le_prod₀`; `simp only [h, ↓reduceIte]` instead of `if_pos`; `grep -R` (symlinks).
- **Resources.** One Lean process for the helper, one for me (memory is binding). Compile with
  `/home/user/lean-env/mk_mixed.sh ForkMx/Record1252270103Source/<path>` in dependency order.

## Files that exist (F1/F2), with the exact signatures

### `ForkMx/…/Admission/SelectedRegularSourceData.lean` (namespace `QRH.Record1252270103Source.Admission.SelectedRegularSourceData`)
```lean
structure Anchor_mx (α₀ α:Type) [Fintype α₀] [Fintype α] (Z:ℝ) where
  s₀ : Input α₀
  modifier₀ : Tuple α₀→ℂ
  s : Input α
  R : Ideal O
  seed : Ideal O
  R_ne : R≠0
  seed_sf : Squarefree seed
  zero₁₀ : s₀.W₁ 0=0
  zero₂₀ : s₀.W₂ 0=0
  zero₁ : s.W₁ 0=0
  zero₂ : s.W₂ 0=0
  D : ℝ
  ξ : ℝ
  reserve : ℝ
  hZ : 1<Z
  hK : 0<Z^D
  bin : ℤ×(Fin 5→ℤ)
  reflected : Bool
  Q : Ideal O
  m : O
-- Anchor_mx.Column/label/character read s₀ modifier₀; childSeed j := j.2.1.val
structure Family_mx {α₀ α:Type} [Fintype α₀] [Fintype α]{Z:ℝ}(anchor:Anchor_mx α₀ α Z)(Label:Type)[Fintype Label] where
  column : Label→anchor.Column
  data : ∀l,ColumnData anchor.s anchor.reflected anchor.R (anchor.childSeed (column l))
    (anchor.label (column l)) (anchor.character (column l))
-- Family_mx: abbrevs s₀ modifier₀ s R seed … zero₁₀ zero₂₀ zero₁ zero₂ …; slots/input/mask/childSeed/Hmain
--   (Hmain l = firstMainRadius reflected (Z^D) (volume s) Z ξ (3*F.amp l) reserve (label)); Complete;
--   datum; first q := firstLabel F.s₀ F.modifier₀ …; Rows; mask_ne; datum_fields;
--   parent_character : (F.datum q).input.η = columnCharacter F.reflected F.s₀ F.modifier₀ … (F.column q.1)
structure Selected_mx {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}
    {a:Anchor_mx α₀ α Z}(F:Family_mx a Label)(Row:Type)(rows:Finset Row)(second:Bool) where
  row : rows→F.Rows
  sel : ∀u,Selection F.s F.reflected second (F.first (row u).val.1)
    (F.datum (row u).val.1).C (F.datum (row u).val.1).D F.R
  first_allocation : ∀u,(sel u).B₁=(F.stage (row u).val.1.1).B
  ψ : rows→RayCharacter
  L : Ideal O
  L_ne : L≠0
  forced_lower : ∀u,L∣(sel u).Cf
  forced_upper : ∀u,(sel u).Cf∣L^2
-- Selected_mx: column (over s₀), datum, z, τ,
--   key u : NonzeroJointSourceLabel (!F.reflected) 1 (fun l=>(fixedParentUnit (!F.reflected) F.s₀.η l:O))
--     := FirstFamily.rawKey F.reflected F.s₀ F.modifier₀ … (G.column u) F.datum F.first (G.row u) rfl second,
--   extra, x (= (G.sel u).coordinate … (F.amp …) …, i.e. at logb Z (volume F.s)), structural, selected_puncture
```

### `ForkMx/…/High/GlobalPhysicalSelectedMass.lean`
`actual_selected_paid_weight_mx {α₀ α} (s₀ modifier₀ s R seed W D Z ξ amp reserve ε hZ hK hε bin reflected second)
 (j : FirstColumnIndex (geometryFirstSource s₀ modifier₀ …)) (C₂ D₂ hC₂ U)
 (sel : Selection s reflected second (firstLabel s₀ modifier₀ … j) C₂ D₂ R) (extra lower ω he hl)
 (hω : <PhaseBound_mx body>) :
 selectedPaidWeight sel ω ≤ (extra*|alloc₂|²*Z^amp/lower*forcedProfileCost s) *
   balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ ε hK bin j * sel.raw U Z D amp ξ reserve`

### `ForkMx/…/Admission/SelectedHighPaidComparison.lean` (namespace `…Admission.SelectedHighPaid`)
```lean
def PhaseBound_mx {α₀ α:Type}[Fintype α₀][Fintype α](s₀:Input α₀)(modifier₀:Tuple α₀→ℂ)
    (s:Input α)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(D Z ξ amp reserve:ℝ)(hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ):Prop :=
  ω≤(‖CoupledFirst.balancedColumnScalar reflected s₀ modifier₀ R seed (Z^D) Z ξ D
    (Real.logb Z (volume s₀)) hK bin
    (fun q=>normPhase (CoupledFirst.coordinateBlock s₀ modifier₀ R seed W (Z^D) Z ξ q)) j‖^2*
    extra*‖frozenCoefficient sel.B₁.val (if reflected then (firstLabel s₀ …j).1.2 else (…).1.1)
      R s.ν s.W s.P‖^2/volume s)*
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve (firstLabel s₀ … j)/lower)*normalizer C₂ D₂ U

theorem uniform_selected_paid_sum_mx (N:ℕ)(B₁ B₂ ε ell lower radiusMax:ℝ)
    (hB₁:0≤B₁)(hB₂:0≤B₂)(hε:0<ε)(hell:0<ell)(hlower:0<lower)(hmax:0≤radiusMax):
    ∃C:ℝ,0<C ∧ ∀{α₀ α:Type}[Fintype α₀][Fintype α](s₀:Input α₀)(s:Input α),
      Fintype.card α₀≤N→Fintype.card α≤N→
    ∀(modifier₀:Tuple α₀→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(D Z ξ reserve εmass:ℝ)
      (hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),0≤εmass→
    ∀{κ:Type}(labels:Finset κ)
      (column:κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
      (C₂ D₂:κ→Ideal O)(U:∀l,Finset (CommonIndex (C₂ l) (D₂ l)))
      (sel:∀l,Selection s reflected second
        (FirstFamily.firstLabel s₀ modifier₀ R seed (Z^D) Z ξ hK bin (column l)) (C₂ l) (D₂ l) R)
      (P:κ→Finset (Ideal O))(amp poolAmp H0 radius mesh loss BD Bsource:κ→ℝ)(depth:κ→ℕ)
      (lossMax:ℝ)(ω cost:κ→ℝ),
      (∀l∈labels,Supported (C₂ l))→
      (∀l∈labels,(C₁ l).absNorm ≤ Z^B₁)→          -- C₁ l = if reflected then (firstLabel s₀ … (column l)).1.2 else ….1.1
      (∀l∈labels,((if second then D₂ l else C₂ l).absNorm:ℝ)≤Z^B₂)→
      (∀l∈labels,FixedCellPoolData (P l) Z (poolAmp l) ell (mesh l) (loss l) (BD l) (Bsource l) (depth l))→
      (∀l∈labels,0<H0 l)→(∀l∈labels,0≤radius l+6*poolAmp l)→
      (∀l∈labels,radius l+6*poolAmp l≤radiusMax)→(∀l∈labels,loss l≤lossMax)→
      (∀l∈labels,PhaseBound_mx s₀ modifier₀ s R seed W D Z ξ (amp l) reserve hK bin reflected second
        (column l) (C₂ l) (D₂ l) (U l) (sel l) (mainExtra s₀ (C₁ l) (P l) (H0 l) (radius l) (poolAmp l) ell) lower (ω l))→
      (∀l∈labels,0≤cost l)→
      (∑l∈labels,cost l*selectedPaidWeight (sel l) (ω l))≤
      (C*Z^(ε+lossMax)*forcedProfileCost s)*
      ∑l∈labels,(Z^(amp l-poolAmp l)*
        CoupledFirst.balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ εmass hK bin (column l))*
        cost l*(sel l).raw (U l) Z D (amp l) ξ reserve
```

### `ForkMx/…/Admission/SelectedRegularAbsoluteData.lean` (namespace `…Admission.SelectedRegularAbsolute`)
```lean
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}
def amplitude_mx (F:Family_mx a Label) (W:𝓢(ℝ,ℂ)) (P:Label→Finset (Ideal O)) (poolAmp:Label→ℝ)
    (H0 radius:Label→ℝ)(ell:ℝ)(l:Label):ℝ :=
  ‖High.CoupledFirst.balancedColumnScalar F.reflected F.s₀ F.modifier₀ F.R F.seed (Z^F.D) Z F.ξ F.D
    (Real.logb Z (volume F.s₀)) F.hK F.bin
    (fun q=>normPhase (High.CoupledFirst.coordinateBlock F.s₀ F.modifier₀ F.R F.seed W (Z^F.D) Z F.ξ q))
    (F.column l)‖^2 * mainExtra F.s₀ (F.stage l).common (P l) (H0 l) (radius l) (poolAmp l) ell *
    ‖frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P‖^2
-- Keep_mx F, datum_mx F keep q, phase_mx F W P poolAmp H0 radius ell keep q (normalized by volume F.s),
-- effectivePhase_mx F W P poolAmp H0 radius ell keep q, amplitude_nonneg_mx (hrad : ∀l,0≤radius l+6*poolAmp l),
-- mainExtra_cap_mx, amplitude_cap_mx (s₀ caps: hN₀ hlower hsource hW1 hW2 hV halloc; s caps: hN hM),
-- datum_common_cap_mx, datum_row_cap_mx, datum_row_power_mx, child_full_pool_cap_mx, child_modifier_cap_mx,
-- finite_family_envelope_mx (… (P)(poolAmp)(H0 radius) …)
```

### `ForkMx/…/High/GlobalPhysicalRegularPhase.lean` (namespace `…High.GlobalPhysical`)
```lean
variable {α₀ α Label:Type}[Fintype α₀][Fintype α][Fintype Label]{Z:ℝ}{a:Anchor_mx α₀ α Z}(F:Family_mx a Label)
def regularFamilyKeep_mx : Admission.SelectedRegularAbsolute.Keep_mx F
def regularFamilyWeight_mx (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)(H0 radius:Label→ℝ)(ell:ℝ) : F.Complete→ℂ
theorem actual_regular_phase_mx (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (hN:Fintype.card α≤N)(hlower:lo≤F.s.lower)
    (hW₁:∀x,F.s.W₁ x≠0→ap≤x)(hW₂:∀x,F.s.W₂ x≠0→ap≤x)
    (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(poolAmp:Label→ℝ)(H0 radius:Label→ℝ)(ell:ℝ)
    (hell:0<ell)(hrad:∀l,0≤radius l+6*poolAmp l)
    {Row:Type}(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)(r:rows):
    PhaseBound_mx F.s₀ F.modifier₀ F.s F.R F.seed W F.D Z F.ξ (F.amp (G.row r).val.1.1)
      F.reserve F.hK F.bin F.reflected second (G.column r)
      (G.datum r).C (G.datum r).D (G.datum r).inactive (G.sel r)
      (mainExtra F.s₀ (F.stage (G.row r).val.1.1).common (P (G.row r).val.1.1)
        (H0 (G.row r).val.1.1) (radius (G.row r).val.1.1) (poolAmp (G.row r).val.1.1) ell)
      (lowerFactor N lo ap)
      (residualWeight F.datum (regularFamilyWeight_mx F W P poolAmp H0 radius ell) (G.row r).val)
```

### `Downstream/Shift.lean` (namespace `QRH.MixedStep.Downstream`)
```lean
theorem balanced_side_shift (reflected : Bool) (A δ : ℝ) (v : Fin 5 → ℝ) :
    balancedGeometrySide reflected (A - δ) v = balancedGeometrySide reflected A v - δ
theorem balanced_side_eq (reflected : Bool) (A Av : ℝ) (v : Fin 5 → ℝ) :
    balancedGeometrySide reflected A v = balancedGeometrySide reflected Av v + (A - Av)
theorem shift_exponent (reflected : Bool) (A₀ Av amp a κ : ℝ) (v : Fin 5 → ℝ)
    (hshift : amp - a ≤ A₀ - Av + κ) :
    (amp - a) - balancedGeometrySide reflected A₀ v ≤ κ - balancedGeometrySide reflected Av v
theorem shifted_high_mass_mx {α₀ : Type} [Fintype α₀] [DecidableEq α₀]
    (reflected : Bool) (N : ℕ) (lo ap : ℝ) (hlo : 0 < lo) (hap : 0 < ap)
    (s₀ : Input α₀) (modifier₀ : Tuple α₀ → ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z ξ B ε : ℝ) (hZ : 1 < Z) (hK : 0 < Z^D)
    (hε : 0 ≤ ε) (hcard : Fintype.card α₀ ≤ N) (hlower : lo ≤ s₀.lower)
    (hs : Squarefree seed) (hz₁ : s₀.W₁ 0 = 0) (hz₂ : s₀.W₂ 0 = 0)
    (hsource : sourceRadius s₀ ≤ Z^B)
    (hs₁ : ∀ x, s₀.W₁ x ≠ 0 → ap ≤ x) (hs₂ : ∀ x, s₀.W₂ x ≠ 0 → ap ≤ x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s₀ modifier₀ R seed (Z^D) Z ξ hK bin))
    (Av amp a κ : ℝ) (hshift : amp - a ≤ Real.logb Z (volume s₀.toData) - Av + κ) :
    Z^(amp - a) * balancedFirstHighMass reflected s₀ modifier₀ R seed W D Z ξ ε hK bin j ≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin * Z^(B*ε + κ) /
        Z^(balancedGeometrySide reflected Av (geometryExponents s₀ modifier₀ R seed (Z^D) Z ξ j.1.val))
```

### `Downstream/Node.lean` (namespace `QRH.MixedStep.Downstream`)
```lean
structure NodeGeometry_mx (n low : Source) (b : ℝ) : Prop where
  lowL_pos : 0 < (low.L:ℝ)
  a_pos : 0 < sourceAReal n low b
  a_small : sourceAReal n low b < 1/75
  a_allowance : 20*(n.allowance:ℝ) < sourceAReal n low b
  parent_budget_room : sourceTReal n b + b + 4*(n.allowance:ℝ) < (low.B:ℝ)*sourceFReal n low b
  B_le_one : n.B ≤ 1
  L_gt_one : 1 < n.L
  cap_lt_one : n.cap < 1
theorem nodeGeometry_of_real (K) (n low) (b) (hg : RealGeometry K n low b) (hn : ParentGood n) : NodeGeometry_mx n low b
```

### Two-parent twins of untainted lemmas (found so far; do not duplicate)
| module (ForkMx/…) | declaration | why |
|---|---|---|
| High/GlobalPhysicalSelectedMass | `actual_selected_paid_weight_mx` | first mass at s₀, selection at s |
| Admission/SelectedHighCoordinatesScalar | `eventual_modified_high_coefficient_mx` | label from s₀, allocation of s |
| Admission/SelectedHighCofactorCoordinates | `eventual_modified_normalized_cofactor_mx` | same |
| Admission/SelectedLowPaidWeight | `eventual_selected_paid_weight_mx`, `uniform_selected_paid_weight_mx` | F2 (LOW), with hshift |

Not needed by F4 and kept on my side (F5): `Initial.anchor_mx`, `Scalar_mx`
(SelectedRegularLowPointData), CombinedPointSome, RegularControls, RegularPoints, RegularSuppliers.

## F4 scope (helper)

Closure modules (closure_mx.tsv): C `Admission/SelectedRegularHighSource` (selected_common_caps),
C `Admission/SelectedRegularHighPointSomeGeometry` (actual_coordinate_box, SharedState),
A `High/GlobalPhysicalPaidSome`, A `High/GlobalPhysicalBufferedPaidSome`,
A `Admission/SelectedRegularHighSourceSome`, A `Admission/SelectedRegularHighPointSome`,
A `High/GlobalPhysicalRegularHighParameters`; plus the coupled twins below them that take one `s` in both
roles (expected: A `Admission/SelectedHighCofactorFamilySome`, A `High/GlobalPhysicalBalancedCofactor`, and
whatever of AnnularCofactor/SelectedCofactor/AllCofactorPositive/AllRawPositive/RegularRawPositive is on the
path). What F5 (me) consumes: `regular_some_source_rm_mx` (HighParameters), `SourceAt_rm_mx` and
`actual_point_rm_mx` (HighPointSome) with two parents: `F : Family_mx a Label`, `G : Selected_mx F …`,
canonical data for both parents (`Canonical … F.s₀` and `Canonical … F.s` if both are needed),
`(hamps : ∀l, F.amp l = amp)`, `hampEq : amp = sourceAReal n low bcell`, the pool at `poolAmp` with
`ell = poolAmp/2`, `omega := residualWeight F.datum (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 radius (poolAmp/2))`,
and `hshift`. Please record each final top signature here when it compiles.

## Requests / notes from the helper
(append below)

## F4 twins
(F4 helper, 2026-10-26 ~02:05. All green with `mk_mixed.sh`, axioms `[propext, Classical.choice, Quot.sound]`.
Paths under `ForkMx/Record1252270103Source/`. Convention as above; `Av`/`V` are free reals where Collet
reads `volume s` of the first-layer input.)

### Keys / State / GeometryCaps (for F3/F5 and HighSourceSome)
Namespace `QRH.Record1252270103Source.Admission.SelectedRegularSourceData` (State, Keys) and
`…Admission.SelectedRegularGeometryCaps` (Caps). Same binders/conclusions as Collet's, over
`a:Anchor_mx α₀ α Z`, `F:Family_mx a Label`, `G:Selected_mx F Row rows second`, with the first-layer
hypotheses on `F.s₀`:
```lean
-- Admission/SelectedRegularSourceDataState
theorem eventual_selected_retained_data_mx (R₀:Ideal O)(hR₀:R₀≠0)(ηanchor:Character)
    (b err ηR ηchar ηwidth:ℝ)(N:ℕ)(hb:0<b)(herr:0<err)(hηR:0<ηR)(hηchar:0<ηchar)(hηwidth:0<ηwidth):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
      (errv annular Afirst Asecond Brow Bradius Binactive Bmask bΦ Mcap ampN:ℝ)
      (w:α→ℝ)(wmin:ℝ)(Tslots:Finset α)(P S A:Finset (Ideal O))(depth:ℕ),
      F.R=R₀→F.s₀.η=ηanchor→F.ξ≤err→sourceRadius F.s₀≤Z^Afirst→
      (∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^Asecond)→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve b N (F.first (G.row u).val.1))→
      … -- the rest verbatim Collet (Brow, Bradius, Binactive, Bmask, Mcap, bΦ, L cap, pools, m, Q, M H hH η₀ e T q, β)
      ∃st hfixed keep select, ∀u, G.extra S A u≠0 ∧ (st u).character=G.τ u ∧ … ∧
        KeyCaps (G.key u) Z (coarseExponent Afirst Asecond Brow) (G.x err errv annular w wmin Tslots u 1) ∧
        rawFrequencyNorm (nonzeroJointSourceRow (G.key u))≤Z^(G.x err errv annular w wmin Tslots u 2)
-- Admission/SelectedRegularSourceDataKeys
theorem eventual_selected_keys_mx (b err:ℝ)(N:ℕ)(hb:0<b)(herr:0<err): -- Collet's, over the _mx structures,
    -- with sourceRadius F.s₀≤Z^Afirst and the MAIN scale at volume F.s
-- Admission/SelectedRegularGeometryCaps
theorem eventual_selected_radius_mx (N:ℕ)            -- Tsec at volume F.s; label of F.s₀
theorem selected_inactive_norm_mx (F) (rows) (second) (G) (hsource:∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^(2:ℝ))
theorem selected_radial_cap_mx (F rows second G) (n low b A₁ A₂ D K Fmark)
    (hmodifier:F.modifier₀=markedSourceModifier A₁ A₂ D K Fmark) (err errv annular w wmin T)
    (hD:F.D=1)(hamp:∀u,F.amp (G.row u).val.1.1=sourceAReal n low b)(hF:sourceFReal n low b≤1)
    (hrho:0≤frequencyLoss Z 32 F.ξ+F.reserve-err) : ∀u,G.x err errv annular w wmin T u 2≤1
theorem eventual_selected_geometry_caps_mx (N:ℕ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α₀ α Label Row:Type}[Fintype α₀][Fintype α][Fintype Label]
      (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(rows:Finset Row)(second:Bool)(G:Selected_mx F Row rows second)
      (n low:Source)(b:ℝ)(A₁ A₂ D K:Ideal O)(Fmark:Ideal O→ℂ)(err errv annular:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α),
      F.modifier₀=markedSourceModifier A₁ A₂ D K Fmark→F.D=1→0≤F.ξ→F.ξ≤1→0≤F.reserve→
      (∀u,F.amp (G.row u).val.1.1=sourceAReal n low b)→0≤sourceAReal n low b→sourceFReal n low b≤1→
      0≤frequencyLoss Z 32 F.ξ+F.reserve-err→(∀u,sourceRadius (F.input (G.row u).val.1.1)≤Z^(2:ℝ))→
      (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
        (3*F.amp (G.row u).val.1.1) F.reserve 2 N (F.first (G.row u).val.1))→
      ∀u,(G.datum u).radius≤Z^(4:ℝ) ∧ ((∏p∈(G.datum u).inactive,p.val).absNorm:ℝ)≤Z^(2:ℝ) ∧
        G.x err errv annular w wmin T u 2≤2
```
`modified_cofactor_coordinate_cap` (Collet) already takes a free volume `A` and is reused unchanged.

### Supporting two-parent twins (untainted single-`s` lemmas)
| module | declaration | change |
|---|---|---|
| Admission/FirstFamilyGeometry | `FirstFamily.eventual_literal_high_frequency_mx` | first label from `s₀ : Input α₀`, datum over `α`, free volume `V` (`0<V`) in the radius hypothesis and coordinates; binder order `… (hfirst) (V ampExponent reserveShift εvolume : ℝ), 0<V → ξ≤εfreq → …` |
| Admission/SelectedSecondKeyCaps | `SelectedSecondKeyCaps.eventual_regular_key_caps_mx` | `original : Input α₀`, blocks over `α`, `… (hz₀₂) (V:ℝ) (hV:0<V)`, Tsec and coordinates at `V` |
| Admission/RetainedGeometryWidth | `RetainedGeometry.main_scale_upper_mx` | `(s₀ modifier₀ …) (j) (V a reserve b : ℝ) (N) (hV : 0<V) …`: `firstMainFourierScale reflected K V Z ξ (3*a) reserve b N (firstLabel s₀ …) ≤ b^(2*N)*K` |
| Coefficient/NonregularRawFamily | `NonregularRawFamily.actual_modified_nonregular_raw_family_mx` | type split (first layer `s₀ : Input α₀`, slots over `α`) |

### HIGH spine, lower chain (type split; shift at BalancedCofactor)
| module | declaration | change |
|---|---|---|
| High/GlobalPhysicalRegularRawPositive | `ModifiedRegularPositive.actual_modified_regular_raw_family_uniform_tau_rm_mx` | type split |
| High/GlobalPhysicalAllRawPositive | `ModifiedAllPositive.actual_modified_all_raw_family_uniform_tau_rm_mx` | type split |
| High/GlobalPhysicalAllCofactorPositive | `ModifiedAllPositive.actual_modified_all_cofactor_family_uniform_tau_rm_mx` | type split |
| High/GlobalPhysicalSelectedCofactor | `ModifiedAllPositive.actual_modified_selected_cofactor_family_uniform_tau_rm_mx` | type split |
| High/GlobalPhysicalBalancedCofactor | `ModifiedAllPositive.actual_modified_balanced_cofactor_family_uniform_tau_rm_mx` | shift: `∀(Av:ℝ),|Av|≤B→loMass≤s₀.lower→…→∀(amp poolAmp:κ→ℝ)(shiftLoss:ℝ),(∀l∈labels,amp l-poolAmp l≤Real.logb Z (volume s₀.toData)-Av+shiftLoss)→…`, side at `Av`, `card α₀≤N→card α≤N`, mass `Z^(amp l-poolAmp l)*balancedFirstHighMass … s₀ …`, exponent `+B*εmass+shiftLoss` |
| HighScalar/ModifiedPayment | `HighScalar.modified_retained_high_exponent_rm_mx` | type split (`s₀ : Input ι₀`, `d2 : SecondInputDatum ι`) |
| HighScalar/NonregularModified | `HighScalar.nonregular_modified_retained_high_exponent_rm_mx` | type split |
| High/GlobalPhysicalSectorPayment | `GlobalPhysical.modified_selected_sector_singleton_payment_rm_mx` | type split |
| High/GlobalPhysicalAnnularCofactor | `ModifiedAllPositive.actual_modified_annular_cofactor_family_uniform_tau_rm_mx` | free `Av` (coordinates, side, `hA : Av≤D*(T+b)`), `(… annular shiftLoss : ℝ)(amp poolAmp live forced : κ→ℝ)`, `hshift` after `hamp` |
| Admission/SelectedHighCofactorFamilySome | `SelectedHighCofactorFamilySome.FamilyStatement_rm_mx`, `…actual_selected_annular_cofactor_family_uniform_tau_rm_mx` | two parents: `(s₀ : Input α₀)(s : Input α)(Amark…)`, `Selection s …`, `(upper bcell reserveGeom err reserveScalar δwidth shiftLoss : ℝ)(amp poolAmp : κ→ℝ)`, `|logb Z (volume s)|≤B→loMass≤s₀.lower→loMass≤s.lower→`, `hshift : ∀l∈labels,amp l-poolAmp l≤logb Z (volume s₀)-logb Z (volume s)+shiftLoss` right after `hamp`, `card α₀≤N→card α≤N`, second-layer `s.upper s.lower s.P s.X₁…`, mass shifted, `+shiftLoss` |
| High/GlobalPhysicalPaidSome | `ModifiedSelectedPaidSome.FamilyStatement_rm_mx`, `…actual_selected_annular_cofactor_family_uniform_tau_rm_mx` | as above + pool block at `poolAmp`, `PhaseBound_mx s₀ modifier₀ s … (mainExtra s₀ … (poolAmp l) ell)` |
| High/GlobalPhysicalBufferedPaidSome | `BufferedSelectedPaidSome.FamilyStatement_rm_mx`, `…actual_buffered_selected_cofactor_family_uniform_tau_rm_mx` | as PaidSome, bins verbatim |

Next (F4): `selected_common_caps_mx` (Admission/SelectedRegularHighSource), HighSourceSome
(`ModifierAt_rm_mx`, `SourceAt_rm_mx`, `ActualAt_rm_mx`, `FamilyStatement_rm_mx`,
`actual_selected_regular_high_source_uniform_tau_rm_mx`), PointSomeGeometry (`actual_coordinate_box_mx`,
`SharedState_mx`), HighPointSome (`SourceAt_rm_mx`, `actual_point_rm_mx`), RegularHighParameters
(`regular_some_source_rm_mx`). Signatures will be added here when green.

## F3 (LOW spine, fork agent)
(2026-10-26 ~02:30; all green with `mk_mixed.sh`, axioms `[propext, Classical.choice, Quot.sound]`.)

Type-split twins (first layer `s : Input α₀`, second-layer slots/datum over `α`; proofs verbatim):
`RetainedLow.actual_key_support_mx` (Admission/RetainedLowCofactorDictionary),
`actual_fixed_seed_low_positive_family_mx` (Admission/RetainedLowPositive),
`actual_fixed_seed_low_collected_family_mx` (Admission/RetainedLowCollected),
`GlobalPhysical.actual_low_erased_positive_family_mx` (High/GlobalPhysicalLowCollectedErasure),
`GlobalPhysical.global_low_erased_positive_family_mx` (High/GlobalPhysicalLowGlobalSource),
`global_low_erased_collected_cells_mx` (Admission/RetainedLowErasedCollected),
`global_low_paid_positive_family_mx` (Admission/RetainedLowPaid).

Two-parent twins (statement shape as Collet's with: `∀(reflected second){α₀}[Fintype α₀][DecidableEq α₀](s₀ : Input α₀)(s : Input α)…`,
`s₀.η = ηanchor`, first-layer objects at `s₀`, the selection/slots/plains/coordinates/side at `s`, the first-layer caps
`s₀.W₁ = p.profile 0 → s₀.W₂ = p.profile 1 → card α₀ ≤ N → 1 ≤ s₀.lower → sourceRadius s₀ ≤ Z^Bmass →` right after
`sourceRadius s ≤ Z^Bmass →`, the pool `∀(P)(poolAmp poolMesh BD Bsource)(depth)(H0 mainRadius), FixedCellPoolData P Z poolAmp ell …`
(`mainExtra` at `s₀`, ball factor `(mainRadius l+6*poolAmp)/ell`), and before the phase hypothesis
`∀κ, sourceAReal n low bcell-poolAmp ≤ logb Z (volume s₀)-logb Z (volume s)+κ → (∀l, φ ≤ (∑i,w i)-∑i∈liveIndices (sel l).B₁.val,w i) →`;
`+κ` in the exponent; `(hprice : QRH.MixedStep.Ledger.MixedNodePrice n low bcell φ)(hlow : ParentGood low)` replace
`(Kgraph)(hg : RealGeometry …)(hn : ParentGood n)(hlow)`):
- `SelectedLowPaid.actual_selected_low_price_mx` (Admission/SelectedLowPaid) — extra `(hφ : φ ≤ (∑i,w i)-∑i∈liveIndices sel.B₁.val,w i)`;
- `SelectedLowSource.global_selected_low_positive_family_mx`, `…Reindex.global_selected_low_positive_family_injective_mx`,
  `…MissingBins.global_selected_low_positive_family_missing_bins_mx`, `SelectedLowBufferedSource.global_selected_low_buffered_positive_family_mx`;
- `SelectedRegularLowSource.selected_nonfixed_mx`, `…apply_actual_family_mx` (Admission/SelectedRegularLowSourceData) and
  `…global_selected_regular_low_buffered_positive_family_mx` (Admission/SelectedRegularLowSource): conclusion over
  `Anchor_mx α₀ α Z := {s₀, modifier₀ := markedSourceModifier …, s, …, zero₁₀, zero₂₀, zero₁, zero₂, …}`, `Family_mx`, `Selected_mx`,
  binders `(hz₁₀ : s₀.W₁ 0=0)(hz₂₀ : s₀.W₂ 0=0)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)`;
- `PhysicalLowGuard.guard_slack_of_geometry_mx`, `eventually_geometry_guard_mx` (Core/PhysicalLowGuard): `NodeGeometry_mx n low b`;
- `GlobalPhysical.regularLowMesh_mx n low b φ θ hprice hlow ha hqhalf hq1 hG hθ`, `regular_low_mesh_positive_mx`,
  `regular_low_slot_supply_mx` (High/GlobalPhysicalRegularLowParameters);
- `GlobalPhysical.RegularLowAt_mx rayModulus Hray hH n low bcell φ ellPool θloss mesh εslot τsource N Mslot W ηanchor η₀ Q hQray Cslot Cpref JL SL CL Z`
  and `regular_low_controls_mx (n low)(bcell φ ellPool θloss)(hprice)(hlow)(hellPool : 0<ellPool)(ha)(hqhalf)(hq1)(hG)(hθ) … (hmesh : mesh ≤ regularLowMesh_mx …) …`
  (High/GlobalPhysicalRegularLowAt). In `RegularLowAt_mx` the pool width `poolAmp` is quantified with the pool and the pool's
  `ell` is the fixed parameter `ellPool` (`ellPool = poolAmp/2` at the call site).

Next (F3): `Admission/SelectedRegularLowPointData` (`Initial.anchor_mx`, `eventually_low_scalar_mx`, `Scalar_mx`, `Shared_mx`, `radial_mx`,
`eventually_selected_frequency_mx`, `selected_common_norm_caps_mx`), `Admission/SelectedRegularLowPoint` (`eventually_initial_low_point_mx`).

## F4 tops for F5 (HIGH spine; green 2026-10-26 ~02:25; axioms `[propext, Classical.choice, Quot.sound]`)
Section variables of both modules (explicit order, as PR 76 with `amp ↦ poolAmp`, since PR 76's `amp`
there only enters as the pool cell width `ell = amp/2`):
`{α₀ α}(M)[NeZero M](H)(hH)(ηanchor η₀)(n low)(setup)(W hWs hW)(bRad hbRad hrad)(reserve θ mesh poolAmp)(N)
(wmin rmin εslot)(hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
(hm:0≤mesh)(hmesh:100*mesh≤θ)(hpoolAmp:0<poolAmp)(R₀ hR₀)(hβ hβhi)`.

* `High/GlobalPhysicalRegularHighParameters`, namespace `…High.GlobalPhysical`:
  `def regular_some_source_rm_mx (high) (hB0 hB1 hlam hcap0 hcap1) (hparent)` := `actual_selected_regular_high_source_uniform_tau_rm_mx … (poolAmp/2) …`
  (type: `SelectedRegularHighSourceSome.FamilyStatement_rm_mx …`, exactly PR 76's specialization).
* `Admission/SelectedRegularHighPointSome`, namespace `…Admission.SelectedRegularHighPointSome`:
  `def SourceAt_rm_mx (high) (hB0 hB1 hlam hcap0 hcap1) (hparent) (J τ P control C Z) : Prop :=
   SelectedRegularHighSourceSome.ActualAt_rm_mx … (poolAmp/2) …` (call: `SourceAt_rm_mx (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low
   setup W hWs hW bRad hbRad hrad reserve θ mesh poolAmp N wmin rmin εslot hf hc hm hmesh hpoolAmp R₀ hR₀ hβ hβhi high hB0 hB1 hlam
   hcap0 hcap1 hparent J τ P control C Z`).
```lean
theorem actual_point_rm_mx (high:Source) (hB0 …) (hB1 …) (hlam …) (hcap0 …) (hcap1 …) (hparent : UnitFaceSource … (100*mesh) θ)
    (hs:SourceAt_rm_mx (α₀:=α₀) (α:=α) M H hH ηanchor η₀ n low setup W hWs hW bRad hbRad hrad reserve θ mesh poolAmp
      N wmin rmin εslot hf hc hm hmesh hpoolAmp R₀ hR₀ hβ hβhi high hB0 hB1 hlam hcap0 hcap1 hparent J (P).τ P control C Z)
    {Label Row:Type}[Fintype Label](rows:Finset Row)[Nonempty rows]
    (a:Anchor_mx α₀ α Z)(F:Family_mx a Label)(second:Bool)(G:Selected_mx F Row rows second)
    (c₀:Canonical M H hH W hW hWs ηanchor η₀ R₀ Z F.hZ F.s₀)(c:Canonical M H hH W hW hWs ηanchor η₀ R₀ Z F.hZ F.s)
    (hR:F.R=R₀)(hmod:F.modifier₀=markedSourceModifier 1 1 1 1 (fun _=>1))
    (hD:F.D=1)(hreserve:F.reserve=θ)(hξ:0≤F.ξ)(hξθ:F.ξ≤θ)
    (bcell r height amp:ℝ)(hamp:0<amp)(hampEq:amp=sourceAReal n low bcell)(hamp1:amp≤1)
    (hamps:∀l,F.amp l=amp)(hN₀:Fintype.card α₀≤N)(hN:Fintype.card α≤N)
    (hnodeB:(n.B:ℝ)≤1)(hnodeL:1≤(n.L:ℝ))(hnodeQ:1/2≤(n.q:ℝ))
    (hallow:θ≤(n.allowance:ℝ))(hallow1:(n.allowance:ℝ)≤1)
    (hw:∀i,0≤c.w i)(hwm:∀i,c.w i≤mesh)
    (hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1)
    (hr:0≤r)(hl1:Z^r≤c.X₁)(hl2:Z^r≤c.X₂)(href:c.Y₂=Z^r)
    (hwidthlo:bcell-θ≤∑i,c.w i)(hwidthhi:(∑i,c.w i)≤bcell)(hbcell:bcell≤1)
    (hOmega:frequencyLoss Z 32 F.ξ+θ≤(n.allowance:ℝ))
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve)
    (hsrc₀:sourceRadius F.s₀≤Z^(2:ℝ))
    (hinj:Function.Injective G.key)
    (hTsec:∀l,F.Tsec (G.row l).val.1.1=firstMainFourierScale F.reflected (Z^F.D) (volume F.s) Z F.ξ
      (3*F.amp (G.row l).val.1.1) F.reserve 2 N (F.first (G.row l).val.1))
    (hLcap:(G.L.absNorm:ℝ)≤Z^(4:ℝ))
    (hm0:F.m≠0)(hQmask:F.Q≤Ideal.span {(72:O)})(hml:goodLambda∣F.m)(hm2:(2:O)∣F.m)(hQM:F.Q≤M)(hQη:F.Q≤η₀.modulus)
    (pool Snew Anew:Finset (Ideal O))(depth:ℕ)(poolLoss BD Bsource:ℝ)
    (hpool:FixedCellPoolData pool Z poolAmp (poolAmp/2) mesh poolLoss BD Bsource depth)
    (hpoolLoss:poolLoss≤θ)(hdepthamp:(depth:ℝ)*poolAmp<5)
    (hS:Snew⊆pool)(hA:Anew⊆Snew)(hdepth:Snew.card≤depth)
    (T:Finset α)(hT:∀l,T⊆(G.sel l).full)
    (hheight:|height|≤Z^(P).τ)(hslotheight:∀i,|height+c.v i|≤Z^(P).τ)
    (Wa:𝓢(ℝ,ℂ))(H0 radius:Label→ℝ)(hH0:∀l,0<H0 l)(hradius0:∀l,0≤radius l+6*poolAmp)(hradius:∀l,radius l+6*poolAmp≤32)
    (hZlarge:(9/4:ℝ)^2≤Z)(habsorb:(2:ℝ)^N*(9/4)^2*Z≤Z^(2:ℝ))(hannular:(2:ℝ)^(3*N)≤Z)
    (shiftLoss:ℝ)(hshift:amp-poolAmp≤Real.logb Z (volume F.s₀.toData)-Real.logb Z (volume F.s.toData)+shiftLoss):
    let e:=highBuffer 1 1 εslot (θ/16)
    let annular:=3*(N:ℝ)*Real.logb Z 2
    let omega:=fun l:rows=>residualWeight F.datum (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 radius (poolAmp/2)) (G.row l).val
    ∃st hfixed keep select,
    SharedState_mx F rows second G M H hH η₀ P e (n.q:ℝ) θ annular wmin c.w T Snew Anew hQM hQη st hfixed keep select ∧
    (∑l∈Finset.univ.filter (fun l:rows=>(n.q+1)/2≤bufferValue e (select l)),
      ‖regularSelectedCentered_mx G Snew Anew T height l‖^2*selectedPaidWeight (G.sel l) (omega l))≤
      Z^shiftLoss*pointBudget n N J θ reserve εslot wmin C Z P control F.s F.reflected F.bin F.ξ c.p
-- here `P` is the PR 76 notation `regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hbound`
-- (section variables `(bound)(hbound)(J)(control)(C Z)` as in PR 76).
```
`pointBudget` is Collet's, unchanged (so `regular_point_budgets_paid` applies); the shift costs the outer factor
`Z^shiftLoss` (`pointBudget_mx_eq` in Admission/SelectedRegularHighPointSomeGeometry). `SharedState_mx` and
`regularSelectedCentered_mx`/`…Corner_mx`/`regular_selected_source_fusion_mx` (High/GlobalPhysicalRegularCofactor) are mine.

**What the second-layer data must satisfy (assembly, not proved by F4).** With `n := vnode2 n₀ low b δ θnode`,
`bcell := b-θnode`, `c` the canonical record of `F.s = s₀.restrict J` (if `Input.restrict` of `initialInput` is
`initialInput` of the restricted slot data, `c := ⟨w∘val, v∘val, ray∘val, …, rfl⟩`):
1. `hwidthhi : Σ_res ≤ b-θnode` and the `B`-part of `hadm`: from `θnode ≤ δ_act` (ledger §0.3); the other parts of
   `hadm` (`0≤m₁,m₂≤B'`, `0≤Σ_res≤cap`) follow from those of `s₀`.
2. `hwidthlo : (b-θnode)-θ ≤ Σ_res`, where `θ` is the HIGH budget of `FixedBudget reserve 100 100 1 θ`
   (`θ < reserve/256`, `θ ≤ 10⁻⁵`): from `b-width ≤ Σ_tot` it needs `δ_act-θnode ≤ θ-width`. So the grid cell
   width and the node slack κ (`θnode = max 0 (δ-κ)`, `δ_act-θnode ≤ κ`) must satisfy **`width + κ ≤ θ`**, i.e. both
   are chosen after the reserve and after `θ` (PR 76 already needs `width ≤ θ`).
3. `hshift` with `amp = r+δ` (node), `poolAmp = a` (actual pool) and `shiftLoss ≥ δ-δ_act` (≤ 2·mesh with the
   window `[δ-2mesh, δ-η]` and `a = r`); the factor `Z^shiftLoss` must be absorbed by the reserve (`shiftLoss ≤ reserve/4`
   suffices against `Z^(-(reserve/2))`).
4. `hsrc₀`, `c₀`: the original canonical input and its source cap (Collet's `c.radius_cap` at the original node).

## F4 issues
(F4 helper, 2026-10-26.) **No mathematical failure found in the HIGH spine**: the PR 76 `_rm` HIGH statements are
generic in the node, so `vnode2` is an instance; the only semantic change is the δ-shift at BalancedCofactor,
proved with the lead's `shifted_high_mass_mx`. One **parameter-order constraint** for the assembly (N7):
* Where: `ForkMx/…/Admission/SelectedRegularHighPointSome.lean:132`
  (`hwidthlo : bcell-θ ≤ Σ c.w`, at `bcell = b-θnode` for the residual), with `θ` the HIGH budget of
  `FixedBudget reserve 100 100 1 θ` (Collet `Core/PhysicalAnalyticParameters.lean:15-16`: `θ ≤ 10⁻⁵`,
  `16θ < reserve/16`), and `reserve ≤ e` (PR 76 `GlobalPhysicalRegularSuppliers.lean:69`). So `θ < e/256`.
* What: from `b-width ≤ Σ_tot`, `Σ_res = Σ_tot-δ_act`, the bound needs `δ_act-θnode ≤ θ-width`. With
  `θnode = max 0 (δ-κ)` and the window `δ_act ≥ δ-2mesh`, this means `κ + width ≲ θ < e/256`.
  LEDGER_INTERFACE §0.4's example `δw = g = κ = 2e` violates it.
* Fix: choose the grid width `δw` and the node slack `κ` after the reserve and after `θ`, e.g.
  `δw, κ ≤ θ/2` (then `g`, `ε` as the ledger says, `mesh ≤ min (κ/2) (θ/100)`). All of them are free small rationals,
  and the ledger's node facts hold for every `0 ≤ θnode ≤ δ ≤ d`, so this is satisfiable. `shiftLoss ≤ 2·mesh` is then
  far below `reserve/4`.

## F5 scope (helper)
(fork agent, 2026-10-26 ~02:25.) **Status of the lead side:** F3 is green, and so are the F5 junctions `High/GlobalPhysicalRegularControls`
(`regular_some_controls_rm_mx`) and `Admission/SelectedRegularCombinedPointSome` (`eventually_actual_point_rm_mx`). The lead is writing
`High/GlobalPhysicalRegularPoints` now (`RegularPointAt_mx`, `regular_some_point_source_rm_mx`; statement below).

**Helper owns: the family/norm bridge.** These are the closure modules 11, 12, 31–37 and 45–51 of `closure_mx.tsv`. Modules 38–44 belong to
F6 (third agent). Fork only the declarations on the path, each as `_mx` at the same relative path under `ForkMx/Record1252270103Source/`:
- `High/GlobalPhysicalRegularNormalized`: regularKey, regularFirstAllocation, regular_datum_slots/input/parent, regularModifier,
  regularRowRay, RegularCofactorBound, RegularNormalizedAt, actual_regular_normalized_newton_collection.
- `High/GlobalPhysicalRegularDictionary`: regular_datum_height, regular_common_residual_height.
- `Low/SelectedRegularFibersGeometry` (9 declarations) and `Low/SelectedRegularFibersSelection` (eventual_regular_full_cost_selection).
- `High/GlobalPhysicalRegularFinite`, `…RegularCofactorBridge`, `…RegularSmall` and `…RegularFamily` (`allocatedRegularFamily_mx`:
  a `Family_mx` built from `Anchor_mx`; the columns are `a.Column`, i.e. first layer `a.s₀`; the allocation is over `a.s.pools`).
- `Admission/SelectedRegularAbsolute` and `…CanonicalAbsoluteData`/`…CanonicalAbsolute`.
- `High/GlobalPhysicalRegularCanonicalSmall`, `…RegularNorm` and `…RegularCanonicalNorm` (`regular_canonical_joint_mx`).
- `Contraction/SelectedMainExceptionalIdentity`: regularMainFamily_mx and the two joint-norm rfl bridges.
- `High/GlobalPhysicalRegularSupplier`:
  - `RegularPointSupplier_mx`;
  - `regular_supplier_of_points_mx : RegularPointSupplier_mx … → RegularJointSupplier_mx …`.

  `RegularJointSupplier_mx` is a new definition written by the helper: the two-parent family body of Collet's `RegularJointSupplier`
  (`Core/InitialRegularToTruncatedContract.lean:50`). Constraints:
  1. Two parents come from `Initial` records `i₀ : Initial (α:=α₀)` and `i : Initial (α:=α)` with `i₀.p = i.p`:
     - the second layer satisfies `InitialGeometry i n b width mesh r` at the node `n`;
     - the first layer has only the face hypotheses of `eventually_initial_caps` on `globalFace B₀ lam₀ cap₀` (fixed before `Z`),
       exactly as in `RegularPointAt_mx` below.

     Raw data, with `i₀`/`i` built inside as in Collet, is also fine if it is easier, but keep the same two-parent content.
  2. Columns, labels, characters, scalar and `common` are read on `s₀ := i₀.input …`:
     - `column : Label → FirstColumnIndex (source s₀ …)`, `chars := columnCharacter reflected s₀ … (column l)`;
     - the scalar is at `Real.logb Z (volume s₀)`;
     - `extra` uses `actualAllocations s₀.pools (common l)` and the ball factor `(radius l + 6*poolAmp)/(poolAmp/2)`.

     The second layer `s := i.input …` carries:
     - `alloc : ∀ l, actualAllocations s.pools (common l)`, the frozen coefficient `frozenCoefficient (alloc l).val (common l) R₀ s.ν s.W s.P`;
     - `Hmain`/`Tsec` at `volume s` and `3*sourceAReal n low b`;
     - `T := fun _ => volume s`.

     (N6 specializes `i := i₀` restricted to `{j // j ∉ J}` and `column := rayShift ∘ column`, and rewrites the frozen coefficient by
     `frozenCoefficient_restrict`.)
  3. The pool is the actual one: `P := primePool rayM H fixedBadPrimes (1/2) 1 (Z^poolAmp)`, with `0 < poolAmp` and `mesh < poolAmp/2`
     (Collet builds it with `eventually_fixed_cell_pool … amp (amp/2) …`; here it is at `poolAmp`).
  4. Node facts are hypotheses: the fields of `Scalar_mx n low b θ mesh ξ width` / `NodeGeometry_mx n low b`, plus whatever else the
     chain needs, as explicit hypotheses. There is no `RealGeometry` and no `ParentGood n`. If a `RealGeometry` field beyond
     `NodeGeometry_mx` is used (e.g. `reference_pos` for `r = 49/100 - K b`), make it a hypothesis and list it.
  5. `∀ κ, sourceAReal n low b - poolAmp ≤ logb Z (volume s₀) - logb Z (volume s) + κ →`, then the frozen margins per label
     `(∀ l, φ ≤ (∑ j, i.w j) - ∑ j ∈ liveIndices (alloc l).val, i.w j)`, before the conclusion.

     The conclusion carries whatever power of `Z^κ` the chain gives: `Z^(κ - reserve/2)` at the point level. Record the exponent you get.

**The helper may assume by statement:**
- F3 tops:
  - `eventually_initial_low_point_mx` (Admission/SelectedRegularLowPoint, green);
  - `Scalar_mx`, `Shared_mx`, `radial_mx`, `Initial.anchor_mx`, `selected_common_norm_caps_mx`, `eventually_selected_frequency_mx`
    (Admission/SelectedRegularLowPointData, green).
- F5 lead tops (`High/GlobalPhysicalRegularPoints`, being written; import it once it is green):
```lean
def RegularPointAt_mx {α₀ α:Type}[Fintype α₀][DecidableEq α₀][Fintype α]
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (ηanchor η₀:Character)(R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)
    (n low:Source)(bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀:ℝ)(N degree:ℕ)
    (controls:Finset (ℕ×ℕ))(C Z:ℝ):Prop:=
    let amp:=sourceAReal n low bcell
    ∀hZ:1<Z,
      ∀(i₀:Initial (α:=α₀) M H Z)(i:Initial (α:=α) M H Z)(r:ℝ),InitialGeometry i n bcell width mesh r→
        i₀.p=i.p→(∀j,0≤ i₀.w j)→
        (globalFace B₀ lam₀ cap₀).Admissible (length Z i₀.X₁) (length Z i₀.X₂) (∑j,i₀.w j) 1→
        1≤ i₀.Y₂→i₀.Y₂≤ i₀.X₁→i₀.Y₂≤ i₀.X₂→
      ∀(seed:Ideal O)(hs:Squarefree seed)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),
      let a:=Initial.anchor_mx i₀ i hH W hW hWs hZ ηanchor η₀ R₀ seed hR₀ hs 1 1 1 1 (fun _=>1) ξ θ bin reflected Q
      ∀{Label:Type}[Fintype Label](F:Family_mx a Label),(∀l,F.amp l=amp)→
      ∀{Row:Type}(rows:Finset Row)(G:Selected_mx F Row rows second),Function.Injective G.key→
        (G.L.absNorm:ℝ)≤Z^(4:ℝ)→
        (∀u,F.Tsec (G.row u).val.1.1=firstMainFourierScale reflected (Z^(1:ℝ)) (volume F.s) Z ξ
          (3*amp) θ 2 N (F.first (G.row u).val.1))→
      ∀(pool S A:Finset (Ideal O))(BD Bsource:ℝ)(depth:ℕ),
        FixedCellPoolData pool Z poolAmp (poolAmp/2) mesh θ BD Bsource depth→
        S⊆pool→A⊆S→S.card≤depth→(depth:ℝ)*poolAmp<5→
      ∀T:Finset α,(∀u,T⊆(G.sel u).full)→
      ∀(t height:ℝ),0≤height→(∀j∈T,|i.freq j|≤height)→
        |t|≤Z^τsource→(∀j,|t+i.freq j|≤Z^τsource)→
      ∀(Wa:𝓢(ℝ,ℂ))(H0 mainRadius:Label→ℝ),(∀l,0<H0 l)→
        (∀l,0≤mainRadius l+6*poolAmp ∧ mainRadius l+6*poolAmp≤32)→
      ∀κ:ℝ,amp-poolAmp≤Real.logb Z (volume F.s₀)-Real.logb Z (volume F.s)+κ→
        (∀u:rows,φ≤(∑j,i.w j)-∑j∈liveIndices (G.sel u).B₁.val,i.w j)→
      (∑u:rows,‖regularSelectedCentered_mx G S A T t u‖^2*
        selectedPaidWeight (G.sel u) (residualWeight F.datum
          (regularFamilyWeight_mx F Wa (fun _=>pool) (fun _=>poolAmp) H0 mainRadius (poolAmp/2)) (G.row u).val))≤
      C*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
        (i.p.control controls)^2*(1+|t|+height)^degree*Z^(κ-(reserve/2))
```
  (`regular_some_point_source_rm_mx … : ∃degree controls,(0,0)∈controls ∧ ∃C τsource,0<C ∧ 0<τsource ∧ ∀ᶠZ in atTop,1<Z ∧
  RegularPointAt_mx … Z`, given `card α₀ ≤ N`, `card α ≤ N`. Its section variables are those of CombinedPointSome below:
  `sc : Scalar_mx`, `hprice : MixedNodePrice n low bcell φ`, `hLowMesh : mesh ≤ regularLowMesh_mx …`, `B₀ lam₀ cap₀` with
  `hB₀ : B₀≤1`, `hlam₀ : 1≤lam₀`, `hcap₀ : cap₀≤1`, `poolAmp`/`hpoolAmp`.)

**Lead keeps:**
- `High/GlobalPhysicalRegularPoints` and `High/GlobalPhysicalRegularSuppliers`. The latter is `regular_supplier_some_rm_mx`, the
  composition `regular_supplier_of_points_mx ∘ regular_some_point_source_rm_mx`, written once the helper's RegularSupplier is green.
- N6 (`Core/Contract3`, `Core/Balanced3`): the residual specialization of `RegularJointSupplier_mx` and `balanced_of_regular3`.

**Do not touch:**
- F6's modules (`ForkMx/…/Core/*MainExceptional*`, `Exceptional*`, `InitialMainRemainderGap`, `Low/InitialRemainder*`, `Contraction/SelectedMainExceptional{Aggregate,Initial,Radical}`,
  `Coefficient/{CorrectedExceptionalFirstPrice,MarkedMainRemainder*}`);
- my F1–F3 modules.

If you need a two-parent twin of one of my lemmas, write it in your module and list it here.

## F3/F5 lead tops (green 2026-10-26 ~02:30; axioms `[propext, Classical.choice, Quot.sound]`)
All paths below are under `ForkMx/Record1252270103Source/`.

* `Admission/SelectedRegularLowPoint`, namespace `…Admission.SelectedRegularLowPoint`.
  `eventually_initial_low_point_mx (n low)(b φ θloss mesh ξ width εslot τsource poolAmp)(sc : Scalar_mx n low b θloss mesh ξ width)
  (hpoolAmp : 0<poolAmp){α₀ α}[Fintype α₀][DecidableEq α₀][Fintype α](N)(hN₀)(hN)(rayM)[NeZero rayM](H)(hH)(W hW hsW)(ηanchor η₀)(Q hQM)(R₀ hR₀)
  (Cslot Cpref JL SL CL)`. Its conclusion is
  `∀ᶠZ, 1<Z ∧ ∀hZ, RegularLowAt_mx … n low b φ (poolAmp/2) θloss mesh εslot τsource N … Z → ∀ i₀ i r, InitialGeometry i n b width mesh r →
  i₀.p = i.p → ∀ seed Am₁ Am₂ Dm Km Fm hs bin reflected second, let a := Initial.anchor_mx i₀ i …; ∀ F : Family_mx a Label, (∀l, F.amp l =
  sourceAReal n low b) → sourceRadius F.s₀ ≤ Z^2 → …`, with:
  - the pool at `poolAmp`;
  - `sh : Shared_mx G …`;
  - `∀κ, hshift → (∀u:rows, φ ≤ ∑ i.w - ∑_{liveIndices (G.sel u).B₁} i.w) → ∀corner`;
  - the bound `… ≤ CL*(i.p.control SL)^2*…*Z^(lowExponent n θloss εslot N+κ)`.
* `High/GlobalPhysicalRegularControls`: `regular_some_controls_rm_mx`. It takes the section variables of the F4 tops plus
  `(bcell φ)(hprice : MixedNodePrice n low bcell φ)(hlow)(ha)(hqhalf)(hq1)(hG)(hLowMesh : mesh ≤ regularLowMesh_mx n low bcell φ θ hprice hlow ha hqhalf hq1 hG hf.positive)(hN : card α ≤ N)(Q hQM hQ hQt hQ72)`
  and `high … hparent`. It gives `∃bound hb J, ∃SH CH Cslot Cpref JL SL CL, … ∀ᶠZ, 2≤Z ∧ RegularLowAt_mx … (poolAmp/2) … ∧ SourceAt_rm_mx … poolAmp …`.
* `Admission/SelectedRegularCombinedPointSome`: `eventually_actual_point_rm_mx (hN₀)(hN)(high …)(hparent)(hgaps)`.
  - Section variables: PR 76's, with `sc : Scalar_mx n low bcell θ mesh ξ width`, `φ`, `poolAmp`/`hpoolAmp`, and
    `B₀ lam₀ cap₀`/`hB₀ hlam₀ hcap₀` (the first-layer face).
  - Conclusion: `∃Cpoint>0, ∀ᶠZ, 1<Z ∧ ∀hZ, RegularLowAt_mx … → SourceAt_rm_mx … → (RegularPointAt_mx body)`.
  - The first-layer cap `sourceRadius F.s₀ ≤ Z^2` comes from Collet's `eventually_initial_caps` on `i₀`, and is fed to both the LOW
    and the HIGH side. LOW and HIGH both pay `Z^κ`, so the bound is `Cpoint*…*Z^(κ-(reserve/2))`.
* `High/GlobalPhysicalRegularPoints`: `RegularPointAt_mx` (statement in "## F5 scope (helper)") and
  `regular_some_point_source_rm_mx (hN₀ : card α₀ ≤ N)(hN : card α ≤ N)(high …)(hparent)(hgaps)`. The latter gives
  `∃degree controls, (0,0)∈controls ∧ ∃C τsource, 0<C ∧ 0<τsource ∧ ∀ᶠZ, 1<Z ∧ RegularPointAt_mx … bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ N degree controls C Z`.

## F6 twins
(F6 agent, 2026-10-26. All green with `mk_mixed.sh` in the order below; `#print axioms` on every declaration:
`[propext, Classical.choice, Quot.sound]`. Paths under `ForkMx/Record1252270103Source/` unless marked `Downstream/`.
Headers: Collet's copyright line first (checked).)

**Conventions used.** First layer = the canonical initial input `s₀ := initialInput … θ w v …` (columns, labels, `C`, seeds,
`τ`, scalar at `logb Z (volume s₀)`, `H0`/pool radius, the MAIN-prefactor allocation card `actualAllocations s₀.pools C`).
Second layer = the transfer residual `s := s₀.restrict J` (`Input.restrict`, N1), which is *definitionally* the initial input of
the restricted slot data (`Downstream/MainRestrict.restrict_initialInput`, `rfl`): allocations, frozen coefficients,
children, `volume s`, `Hmain`/`Tsec` at `(volume s, 3*amp)`. Pool `P = primePool … (Z^a)` at the actual width `a`
(`hell : ell < a`); radius amplitude `amp` with `a ≤ amp ≤ Amix`; δ-shift `amp - a ≤ Σ_{j∈J} w j + κ`
(= `logb Z (volume s₀) - logb Z (volume s) + κ`, `Downstream/MainRestrict.logb_volume_restrict`).
The smoke test (scratch) checks that the complement family of `eventual_selected_second` at `s := s₀.restrict J`,
`W := ballProfile`, `t := fun _ => ht` is `rfl`-equal to the twin's family.

### Tops for N6
```lean
-- Core/InitialRegularToTruncatedMainExceptionalSaving, namespace QRH.Record1252270103Source.ExceptionalPrice
theorem eventually_initial_main_joint_saved_mx {α:Type}[Fintype α][DecidableEq α]
    (N)(hN:card α≤N)(K:ℚ)(n:Source)(b Amix a κ:ℝ)
    (hgate:sourceTReal n b+b+9*Amix+(n.highFee:ℝ)<5/6+(499/1000)*(49/100-(K:ℝ)*b))
    (hκ:(n.allowance:ℝ)+2*κ≤2*Amix-a)
    (hB:(n.B:ℝ)≤1)(hL:1≤(n.L:ℝ))(hcap:(n.cap:ℝ)≤1)(rayM)[NeZero rayM](H)(hH)(Wslot hW hsW)(η η₀)(R₀ hR)(Sbad hbad)
    (ell mesh poolLoss ξ reserve width radiusMax)(depth)(hmesh:0≤mesh)(hgap:mesh<ell)(hell:ell<a)(hloss)(hξ)(hξ1)
    (hreserve)(hdepth)(hradius)(he:0<e)(hξstep)(hrstep)(hwstep)(W Wsecond)(decay)(ε εL δ epsMass epsCount epsCard)(hε…hεa)
    (hsmall:epsCard+poolLoss+ξ/12≤step n)(hfee:0≤fee)(hpayment:2*epsCount+epsMass+δ+4*εL+2*ε≤3*Amix):
    ∀Q,Q≠0→Q≠⊤→Q≤span{72}→∃degree S Ctotal,0<Ctotal ∧ ∀ᶠZ in atTop,1<Z ∧ ∀hZ:1<Z,∀{Label}[Fintype Label],
    ∀θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod,(∀i,0≤w i)→(∀i,w i≤mesh)→
    (globalFace n.B n.L n.cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
    b-e-width≤∑i,w i→∑i,w i≤b→1≤Y₂→Y₂≤X₁→Y₂≤X₂→Y₂=Z^(49/100-K*b)→
    let s₀:=initialInput … θ w v t p … ; let modifier:=markedSourceModifier 1 1 1 1 (fun _=>1)
    ∀(Jset:Finset α)(amp:ℝ),a≤amp→amp≤Amix→amp-a≤(∑j∈Jset,w j)+κ→
    let s:=s₀.restrict Jset
    ∀reflected bin (column:Label→FirstColumnIndex (source s₀ modifier R₀ 1 Z Z ξ _ bin)),Injective (label,seed)→
    ∀hLive,(∀l,N(seed l)≤Z^4)→ let hseed C scalar(at s₀) ; let P:=primePool rayM H Sbad (1/2) 1 (Z^a)
    ∀(alloc:∀l,actualAllocations s.pools (C l))(ht H0 radius:Label→ℝ)(height)(χ₀),0≤height→(∀l,‖ht l‖≤height)→
      (∀l,0<H0 l)→(∀l,0≤radius l+6*a)→(∀l,radius l+6*a≤radiusMax)→
    let extra l:=|bands (H0 l)|*|actualAllocations s₀.pools (C l)|^2/|P|*((radius l+6*a)/ell)
    let amplitude l:=‖scalar l‖^2*extra l*‖frozenCoefficient (alloc l).val (C l) R₀ s.ν s.W s.P‖^2
    let τ l:=columnCharacter reflected s₀ … (column l); Kmain/Tsec at (volume s, 3*amp)
    let f:=mainAllocatedFamily s Wsecond (p.profile 0) (p.profile 1) Z R₀ C seed alloc τ ht P hseed _ _ Kmain Tsec
      (fun _=>volume s) amplitude ξ _ χ₀ (fixedBadMask*idealGenerator R₀)
    ‖∑q,f.phase Q q*(f.block Q q).value Wsecond‖≤Ctotal*(p.control S)^2*(1+height)^degree*G*Z^(-Amix)
-- unsaved form: Core/InitialRegularToTruncatedMainExceptional.eventually_initial_main_joint_mx, same binders without
--   hfee/hpayment, target Z^(-fee-4*Amix+2*epsCount+epsMass+δ+4*εL+2*ε). Constants uniform in Jset (finite max inside).

-- Core/InitialRegularToTruncatedRemainderOne, namespace QRH.Record1252270103Source.InitialRegularToTruncated
theorem eventual_initial_remainder_sums_one_mx (rayM)[NeZero rayM](H)(hH)(Wslot)(hW)(hsW)
    (N)(ell epsMass epsZero epsCount)(hell)(hmass)(hzero)(hcount):
    ∃Czero Ctail,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ,1<Z ∧ ∀{ι}[Fintype ι][DecidableEq ι](hZ:0<Z)(η η₀ R₀ θ w v ht p X₁ X₂ Y₁ Y₂ …),
    let s₀:=initialInput … θ w v ht p …
    ∀(n low:Source)(b width Amix F a κ:ℝ),
      sourceTReal n b+b+4*e<low.B*F→0≤F→F+6*Amix≤1→0≤e→0≤n.L→low.B≤1→width≤step n→
      (globalFace n.B n.L n.cap).Admissible …→b-e-width≤∑w→∑w≤b→card ι≤N→0≤a→0≤κ→κ≤Amix-a→
    ∀(Jset:Finset ι)(amp:ℝ),a≤amp→amp≤Amix→amp-a≤(∑j∈Jset,w j)+κ→
    let s:=s₀.restrict Jset; let allowance:=e; let Cann:=initialCann N
    ∀modifier R W ξ reserve loss saving (hK:0<Z),freq+reserve+2*epsMass+loss+epsZero≤2*e→
    ∀P mesh BD Bsource depth,FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀reflected bin J column (s₀'s, at radius Z),inj→live→(N(seed)≤Z^4)→
    let C:=geometryColumnIdeal … s₀; Hmain j:=firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve (label j)
    let radius j:=literalFirstRadius reflected Z (volume s₀) Z ξ reserve (label j); H0, scalar at s₀
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→∀(alloc:∀j,actualAllocations s.pools (C j))(τ t),(∀j,frozen≠0)→
    let amplitude j:=‖scalar j‖^2*(|bands (H0 j)|*|actualAllocations s₀.pools (C j)|^2/|P|*((radius j+6*a)/ell))*‖frozen(alloc j, s)‖^2
    (∀j,sourceRadius (child s (C j) R (alloc j) (τ j) (t j))≤(Cann/N(C j))*volume s) ∧
    (∑j amplitude j*plainControl(child s …)^2*Hmain j*(Cann/N(C j))^(1+epsZero)*(volume s)^epsZero/N(seed j)
       ≤ Czero*(…)^2*G*Z^(-a-e+2*epsCount)) ∧
    (∑j amplitude j*plainControl(child s …)^2*Hmain j*(volume (child s …)/volume s)*Z^(-saving)/N(seed j)
       ≤ Ctail*(…)^2*G*Z^(-a-e-saving+2*epsCount))
-- Z^1 form: Low/InitialRemainderScalarSumNode.eventual_initial_remainder_sums_mx (namespace …Low.InitialRemainder).
```

**Node facts from the ledger** (`Downstream/MainGates.lean`, namespace `QRH.MixedStep.Downstream`):
`structure MainTwinFacts (K n low b a Amix F κ)` = `centered` (hgate), `room`, `F_nonneg`, `F_amp`, `lowB_le`, `a_pos`, `a_le`,
`kappa_nonneg`, `kappa_le` (κ ≤ Amix-a), `kappa_room` (e+2κ ≤ 2Amix-a);
`mainTwinFacts_of_mixedGeometry (hg : MixedGeometry Kgraph n low h b reserve) (hv : SourceValidC3 n low h)
 (hX : SourceValid3X n low) (κ) (hκ0 : 0≤κ) (hκ : κ≤6*e) : MainTwinFacts Kgraph n low b r (sourceAmp3Real n low b) (sourceF3Real n low b) κ`
(uses `mixed_d_ge_fee : r ≤ sourceDReal n low b` past the crossing, from `6qβ > 1`). So N6 takes `a := n.lowFee`,
`Amix := sourceAmp3Real n low b`, `F := sourceF3Real n low b`, `κ := 2·mesh` (≤ κ_ledger ≤ 6e).

### Module list (lines)
| module | declarations | kind |
|---|---|---|
| Coefficient/CorrectedExceptionalFirstPrice (49) | `scalar_left_shift_mx`, `node_centered_payment_mx` | tainted (closure 38) |
| Core/ExceptionalFirstScalar (93) | `firstScalarCost_mx`, `actual_first_scalar_cost_mx` | tainted (39) |
| Core/ExceptionalFirstErrors (46) | `node_centered_error_guard_mx`, `eventually_centered_error_guard_mx` (bound `≤ e`) | tainted (44) |
| Core/ExceptionalFirstSum (130) | `firstRadialFactor_mx`, `…_nonneg`, `firstRadialFactor_shift_mx`, `selected_first_radical_sum_mx` | tainted (40) |
| Core/ExceptionalFrozenSum (145) | `selected_frozen_first_sum_mx` | tainted (41) |
| Core/ExceptionalFrozenOne (115) | `selected_frozen_first_sum_one_mx` | tainted (42) |
| Low/SelectedExceptionalInitialCapsAudit (64) | `modified_main_frequency_cap_mx` (free `V`) | twin (untainted) |
| Contraction/SelectedMainExceptionalInitial (114) | `eventually_initial_first_family_polynomialCaps_mx` | twin (untainted) |
| Contraction/SelectedMainExceptionalRadical (109) | `eventually_initial_family_radical_mx` | twin (untainted) |
| Contraction/SelectedMainExceptionalAggregate (238) | `eventually_initial_family_aggregate_mx`, `eventually_initial_family_uniform_mx` | twin (untainted) |
| Core/InitialRegularToTruncatedMainExceptional (313) | `profile_control_le_mx`, `eventually_initial_main_joint_mx` | tainted (61) |
| Core/InitialRegularToTruncatedMainExceptionalSaving (142) | `eventually_initial_main_joint_saved_mx` | tainted (62) |
| Core/InitialMainRemainderGap (80) | `node_amplification_gap_mx`, `initial_main_amplification_gap_mx` | tainted (43) |
| Coefficient/MarkedMainRemainderScalar (65) | `actual_main_radius_exponent_mx` (free `V`) | twin (untainted) |
| Low/InitialRemainderScalar (118) | `actual_log_radius_payment_mx`, `remainder_power_payment_mx`, `actual_remainder_admissions_mx` | twin (untainted) |
| Coefficient/MarkedMainRemainderCost (90) | `selected_allocation_remainder_bounds_mx` (card from `s₀`) | twin (untainted) |
| Coefficient/MarkedMainRemainderSum (146) | `zeroAllocationFactor_mx`, `tailAllocationFactor_mx`, `selected_remainder_sums_mx` | twin (untainted) |
| Low/InitialRemainderScalarSum (151) | `eventual_actual_remainder_sums_mx` | twin (untainted) |
| Low/InitialRemainderScalarSumNode (170) | `eventual_initial_remainder_sums_mx` | tainted (63) |
| Core/InitialRegularToTruncatedRemainderOne (155) | `eventual_initial_remainder_sums_one_mx` | tainted (64) |
| Downstream/MainRestrict (109) | `restrict_width_sum`, `restrict_width_le`, `restrict_admissible`, `logb_volume_restrict`, `restrict_initialInput`, `initial_restrict_logb` | glue |
| Downstream/MainGates (112) | `MainTwinFacts`, `mixed_d_ge_fee`, `mainTwinFacts_of_mixedGeometry` | glue |

Build order: CorrectedExceptionalFirstPrice → ExceptionalFirstScalar → ExceptionalFirstErrors → ExceptionalFirstSum →
ExceptionalFrozenSum → ExceptionalFrozenOne → Low/SelectedExceptionalInitialCapsAudit → Contraction/…Initial → …Radical →
…Aggregate → Downstream/MainRestrict → Core/…MainExceptional → …MainExceptionalSaving; Core/InitialMainRemainderGap →
Coefficient/MarkedMainRemainderScalar → Low/InitialRemainderScalar → Coefficient/MarkedMainRemainderCost → …Sum →
Low/InitialRemainderScalarSum → …SumNode → Core/…RemainderOne; Downstream/MainGates (needs Ledger/Geometry).
Closure module 65 (`balanced_of_regular`) is N6, not F6.

## F6 issues
(F6 agent, 2026-10-26.) **No mathematical failure.** Both bookings of the design are confirmed exactly; one gate
attribution is corrected.
1. **Complement (`+3δ`), confirmed.** Against Collet's exponent at `(A₀, a)` the mixed per-label exponent is larger by
   exactly `3(amp-a) + 2κ` (`node_centered_payment_mx`: `left(A₀) = left(Av)+(A₀-Av)`, `2Av-A₀+5amp-a ≤ A₀+4a+3(amp-a)+2κ`).
   `centered_twin` (`T+9Amix+fee < 5/6+0.499·Lref`) pays it at the target `-fee-4·Amix` (stronger than Collet's
   `-fee-4a`) iff `errors + 2κ ≤ 2·Amix - a` (`errors = L·width+5(freq+reserve)/6+loss ≤ e`). Saved target `Z^(-Amix)`.
2. **Zero term (`+4δ`), confirmed; the gate is the parent budget, not `zero_twin`.** The residual MAIN radius costs exactly
   `4(amp-a)+2κ`, so the gap needed is `A₀+6a+4(amp-a)+2κ+3e ≤ 1`. Collet's own zero term never uses `first_tail`
   (`T+5a+fee<1`; `grep` finds no use): it uses `parent_budget_room` (`T+4e < B₀(1-6a)`, `node_amplification_gap`). The mixed
   one uses `MixedGeometry.parent_budget_room` at `F' = 1-6r-6d` (`T+4e < B₀F'`, `B₀ ≤ 1` ⟹ `A₀+6Amix+3e ≤ 1`) and
   `4(amp-a)+2κ ≤ 6(Amix-a)`. `zero_twin` (`T+5Amix+fee<1`) is **unused** by F6 and does not by itself imply the gap
   (`6a+4d+2κ+3e+L·width` vs `5a+5d+fee`: needs `d ≥ a+2κ+4e-fee`). The ledger may keep or drop it.
3. **κ constraint (for N6).** Both tops need `0 ≤ κ ≤ Amix - a` (= `d`) and `e+2κ ≤ 2Amix-a`. With the ledger's grid
   (`κ = 2·mesh ≤ κ_ledger ≤ 6e`, and the F4 constraint `κ ≲ θ < e/256`) both hold, because `d ≥ r > 20e`
   (`mixed_d_ge_fee`, from `SourceValid3X`: `6qβ > 1` makes `d·den3 = qX₀+6qβr ≥ den3·r`). At a node with `J = ∅`, `κ = 0`.
4. **Uniformity in `J`.** The complement constants depend on the residual slot type `{i // i ∉ J}` (Collet's
   `exceptional_complete_family_radical` indexes constants by live sets of the family's slot type). The top takes the finite
   max over `J : Finset α` inside (degree = sup, controls = biUnion, constant = sum), so N6 may pick `J` after `Z`. The remainder
   constants are uniform over all slot types already.
5. **What N6 must match.** (a) The complement family's amplitude is `‖scalar(column l)‖²·extra(s₀ card, a)·‖frozen(alloc l, s)‖²`
   with `alloc l : actualAllocations (s₀.restrict J).pools (C l)`; N6 rewrites the first-selection amplitude by
   `frozenCoefficient_restrict` (N1) and, for ray shifts, applies the top with `column := rayShift ∘ column₀` (labels, seeds,
   scalar invariant, N2), so that `τ l = columnCharacter (column l)`. (b) The remainder amplitude uses
   `radius = literalFirstRadius … (volume s₀)` and `H0` of `s₀` (first selection), the zero/tail sums are exactly
   `eventual_selected_second`'s at `T := volume s`, `H := Hmain` (as in Collet's `balanced_of_regular`).
6. **Error guard.** `eventually_centered_error_guard_mx` bounds the errors by `e` (not by `sourceAReal`), so it needs no
   `RealGeometry`; `hκ` adds the `2κ`.

## N6 (interface between the fork lead and the N3/N6 agent)
(fork agent, 2026-10-26 ~02:35.) **Correction to "## F5 scope (helper)":** `balanced_of_regular3` is the N3/N6 agent's. The fork
lead owns `RegularJointSupplier3` (defined, green) and its proof `regular_supplier3` (pending the helper's
`regular_supplier_of_points_mx`).

`Downstream/Contract3.lean` (namespace `QRH.MixedStep.Downstream`) defines
`RegularJointSupplier3 (K:ℚ)(n low:Source)(b:ℚ)(mesh ξ reserve width:ℝ)(G:NodeGrid)(φ:ℚ→ℝ) : Prop`. It is Collet's
`RegularJointSupplier` (same quantifier prefix, raw data, face, cell, `Y₂ = Z^(49/100-K b)` and first-layer `s`), with three changes:
* pool `P := primePool rayM H fixedBadPrimes (1/2) 1 (Z^r)` with `r := (n.lowFee:ℝ)` (the actual pool width `a = r`);
* after `let P`: `∀ δ ∈ G.nodes, ∀ J : Finset α, (G.theta δ:ℝ) ≤ Σ_J w → Σ_J w ≤ δ → δ - Σ_J w ≤ 2*mesh →`. These are the
  `PieceFacts` fields `theta_le_act`, `act_le_node` and `shift`;
* labels/columns/`hLive` as Collet's, then `∀ alloc (hJ : ∀ l, J ⊆ liveIndices (alloc l).val), (frozen ≠ 0) →
  (∀ l, φ δ ≤ Σ w - Σ_{liveIndices (alloc l)} w) → ∀ (ray : RayCharacter) (χ₀), …`, where `f` is
  `mainAllocatedFamily (s.restrict J) ballProfile (p.profile 0) (p.profile 1) Z R₀ common (seeds) (fun l => allocRestrict s (common l) (alloc l) J (hJ l))
  (fun l => columnCharacter reflected s modifier R₀ 1 Z Z ξ _ bin (rayShift reflected (column l) ray)) (fun _ => ht) P hseed _ _ Hv Tsecv
  (fun _ => volume (s.restrict J)) amplitude ξ _ χ₀ (fixedBadMask*idealGenerator R₀)`, with:
  - `Hv l = firstMainRadius reflected Z (volume (s.restrict J)) Z ξ (3*(r+δ)) reserve (labels l)` (N3's `pieceEnergy` radius with `amp := r`);
  - `Tsecv` likewise, with `N = card α`;
  - `amplitude` the ORIGINAL one (scalar at `logb Z (volume s)`, `extra` over `s.pools` with ball factor `(radius l+6r)/(r/2)`,
    frozen coefficient of `s` and `alloc l`).

  The conclusion is `regularJointNorm f (internalQ Q η₀) ≤ C*(p.control controls)^2*geometryHighFactor …*(1+|ht|+height)^degree*Z^(-σ)`,
  with `degree controls C τ σ` uniform over nodes, blocks and rays.

What `regular_supplier3` will assume (one block per node, all from the ledger at `vnode2 n low b δ (G.theta δ)` with width `b - θ`):
- `MixedNodePrice (vnode2 …) low (b-θ) (φ δ)`, i.e. `mixed_node_price_frozen` or `…_top`;
- `NodeGeometry_mx (vnode2 …) low (b-θ)`, i.e. `nodeGeometry_of_real ∘ realGeometryLow_vnode2`;
- `ActualGaps_rm (vnode2 …) low (some h) (b-θ) ν reserve` for `ν ∈ [q, 3/4]`;
- `mesh ≤ regularLowMesh_mx (vnode2 …) …` at every node, so `mesh` is the minimum over `G.nodes`;
- `sourceDen n low ≠ 0`, for `sourceAReal (vnode2 …) low (b-θ) = r + δ`;
- the grid arithmetic `width + G.κ ≤ θ_fb`. The residual cell width is `width + κ`, and the F4 note gives `hwidthlo`;
- `κ_shift = 2*mesh ≤ reserve/4`.

N3/N6 agent: please check that this is the family your `pieces_transfer` + `eventual_selected_second` produce (piece `k` gives
`J := pieceBlock G w mesh k.2`, `Label := {l // pieceKey alloc trans l = k}`, `column ∘ val`, `alloc ∘ val`). Write requested changes here.

### `regular_supplier3`: statement (fork lead, 2026-10-26 ~02:40, green as a definition)
`Downstream/Contract3.lean` also defines:
```lean
structure NodeFacts3 (n low high:Source)(b:ℚ)(reserve θ mesh:ℝ)(G:NodeGrid)(φ:ℚ→ℝ)
    (hlow:ParentGood low)(ha:0<(n.allowance:ℝ))(hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hθ:0<θ)(δ:ℚ):Prop where
  price : MixedNodePrice (vnode2 n low b δ (G.theta δ)) low ((b-G.theta δ:ℚ):ℝ) (φ δ)
  geometry : NodeGeometry_mx (vnode2 n low b δ (G.theta δ)) low ((b-G.theta δ:ℚ):ℝ)
  gaps : ∀ν∈Set.Icc (n.q:ℝ) (3/4), ActualGaps_rm (vnode2 n low b δ (G.theta δ)) low (some high) ((b-G.theta δ:ℚ):ℝ) ν reserve
  low_mesh : mesh≤regularLowMesh_mx (vnode2 n low b δ (G.theta δ)) low ((b-G.theta δ:ℚ):ℝ) (φ δ) θ price hlow ha hq hq1 hG hθ

def RegularSupplier3Statement (K:ℚ)(n low high:Source)(b:ℚ)(reserve θ mesh ξ width:ℝ)(G:NodeGrid)(φ:ℚ→ℝ):Prop:=
  ∀(hf:FixedBudget reserve 100 100 1 θ)(_:0≤mesh)(_:100*mesh≤θ)(_:0<ξ)(_:ξ≤θ)
    (_:reserve≤(n.allowance:ℝ))(_:0≤(n.highFee:ℝ))(ha:0<(n.allowance:ℝ))(hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (_:ParentGood n)(hlow:ParentGood low)(hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
    (_:(51/100:ℝ)≤HeckeZeroSupremum.beta)(_:HeckeZeroSupremum.beta≤7/8)
    (_:sourceDen n low≠0)(_:0<49/100-(K:ℝ)*b)(_:(b:ℝ)≤1)
    (_:0<(n.lowFee:ℝ))(_:mesh<(n.lowFee:ℝ)/2)(_:θ≤PhysicalLowGuard.step n)
    (_:0≤width)(_:width+G.κ≤θ)
    (_:22/23≤(high.B:ℝ))(_:(high.B:ℝ)≤1)(_:1<(high.L:ℝ))(_:0≤(high.cap:ℝ))(_:(high.cap:ℝ)<1)
    (_:UnitFaceSource (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (_:∀δ∈G.nodes,NodeFacts3 n low high b reserve θ mesh G φ hlow ha hq hq1 hG hf.positive δ),
  RegularJointSupplier3 K n low b mesh ξ θ width G φ
```
- The fork lead will prove `regular_supplier3 : RegularSupplier3Statement K n low high b reserve θ mesh ξ width G φ` for all arguments.
- The conclusion follows Collet's convention: RegularJointSupplier3's `reserve` argument is `θ`, the HIGH budget of `FixedBudget reserve 100 100 1 θ`.
- Everyone downstream (N6 `balanced_of_regular3`, N7 `nf_step3_of`) may take `RegularSupplier3Statement …` or `RegularJointSupplier3 …` as a hypothesis until it is green.
- **If the F5 bridge needs one more hypothesis, it is added here, with notice.** The likely candidates are first-layer facts that `MixedGeometry` already has.
- The cardinality budget is internal (`cardinality_loss_exists`, as in PR 76). `mesh_small` and `θ ≤ allowance/16` follow from `FixedBudget` and
  `reserve ≤ allowance`.
- The shift loss is `κ_shift = 2·mesh ≤ θ/50`. It is absorbed by the reserve inside the bridge, at Collet's `RegularFinite` step, so it needs no hypothesis.
- `regularLowMesh_mx`'s arguments are `n low b φ θ hprice hlow ha hqhalf hq1 hG hθ`, with namespace `QRH.Record1252270103Source.High.GlobalPhysical`.

## Collision families
### Fork-side facts for option (k) (fork lead, 2026-10-26 ~02:45)
* **Is an extended column a column of the first layer?**
  - `FirstColumnIndex (source s₀ modifier R seed K Z ξ hK key) = Σ q : CommonGeometryFiber s₀ modifier R seed K Z ξ key, (src q).divisors × RayCharacter × RayCharacter`
    (`Cycle61/Physical/InitialMass/ActiveColumns.lean:23`).
  - The label `q` is a `SourceCoordinate` of `s₀`. Its pair `(C, D) := q.1.val` lies in `commonLabels` of
    `activeSource (finiteColumns (piFinset s₀.pools)) (coefficient s₀ modifier R seed)`, and its geometry key is `key`
    (`S/High/CoupledFirstLabels.lean:99-107`, `S/High/GlobalPhysicalGeometryBins.lean:70`).
  - So an extended column with common ideal `C·D_f` exists iff `(C·D_f, D′)` is a common label of the first layer's active
    source. Its key will in general be another bin, since the key records the norms of `C` and `D`.
  - This is harmless: a collision family then sits on an anchor with that bin (`Anchor_mx.bin`), and every family has its own anchor.
  - It must also be in `firstLiveColumns … logAnnulus` (`hLive`) for that source.
* **How does `columnCharacter` depend on the column ideal?**
  - `columnCharacter reflected … j = (fixedPair s₀.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹).left/right`
    (`S/Admission/FirstFamilyLabels.lean:32-42`).
  - `fixedPair` is a `Classical.choice`, so characters are never equal by computation.
  - Its specification fixes only the height coefficients on supported ideals (`OB/FirstPhysicalSourceFixedFamily.lean`, `left_height`/`right_height`):
    `heightCoeff left t I = rowWeight η fixedBadMask 1 1 t I · leftCoefficient (primeSubsetGenerator E) (activeConductor C D) (finiteSexticRow (activePrime C D) _ (activeExponent C D)) (primary I) · rayCharacter ξ₁ (primary I)`.
  - So `C` enters only through the inactive set `E`, `activeConductor C D` and the sextic row of the active primes with their net exponents.
* **Consequence.**
  - The LOW pin `input.η = columnCharacter (column l)` holds by construction if the collision family's character is defined as
    `columnCharacter (extended column)`.
  - What then has to be proved is an *energy equality* between the transfer's twisted output and the corrected child energy with
    that character, on supported ideals. This is the same pattern as N2's `rayShift_energy` via `FixedPair.left_height`.
  - That works if the twist `χ(δ_f³)` is the sextic-row factor of the primes of `D_f` with the right net exponents.
  - The second pin, `R = R₀·columnIdeal (column l)`, then holds with the extended column ideal.
  - Plains are shortened by `D_f` (`Input.shortenPlains`). This changes the second-layer parent per family: anchor `s := (s.restrict J).shortenPlains …`.
    The δ-shift becomes `logb Z (volume s₀) − logb Z (volume s_short)`, which includes `log N(D_f)`.
* **Seeds (approved option (1)).** The per-label child seed in `Family_mx` will be done after the F5 bridge is green, as one coordinated
  recompile of `ForkMx/` (F4 helper, N3/N6 agent notified). The F6 complement top (`InitialRegularToTruncatedMainExceptional(_mx)`)
  assumes seed = column divisor and must be generalized by its owner (now N7).

### `Downstream/Supplier3.lean` (fork lead, green; glue for `regular_supplier3`)
- `uniform_regular_constants`: finitely many suppliers of the regular shape, monotone in `(degree, controls, C)` and antitone in
  `(τ, σ)`, have common constants. Applied over `G.nodes ×ˢ univ (Finset α)`.
- `restrict_face_vnode2`: `θ ≤ Σ_J w` and a cell admissible for `globalFace B L cap` give the residual cell admissible for `globalFace (B−Lθ) L cap`.
- `restrict_initialGeometry i n low b δ θ width mesh r κ … J (θ ≤ Σ_J w) (Σ_J w ≤ δ) (δ−θ ≤ κ)`, with conclusion
  `InitialGeometry (Initial'.restrict i J) (vnode2 n low b δ θ) ((b−θ:ℚ):ℝ) (width+κ) mesh r`.
- `residual_shift`: `sourceAReal (vnode2 n low b δ θn) low (b−θn) − r ≤ logb Z (volume s) − logb Z (volume (s.restrict J)) + 2*mesh`,
  given `δ − Σ_J w ≤ 2*mesh`.
- `frozen_margin_restrict`: a frozen margin on the original widths is one on the residual widths and the `allocRestrict` allocation.
- `scalar_vnode2`: `Scalar_mx (vnode2 n low b δ θn) low (b−θn) θ mesh ξ (width+κ)` from the RegularSupplier3Statement budgets and `NodeGeometry_mx`.

### What collision families need on the supplier side (fork lead, after the coordinator's (k) decision, ~02:50)
`RegularJointSupplier3` (plain families) stays as is. Collision families get a sibling `RegularJointSupplierCol3`, which the fork lead
writes once the transfer agent's family shape is in this section. It is proved from the same generic `RegularJointSupplier_mx` (F5 helper).
For that, three facts are needed from the transfer / N3/N6 side:
1. **Parent as an initial input.** The generic supplier (like `RegularPointAt_mx`) takes the second layer as `i.input …` for an `Initial`
   record `i` with `i₀.p = i.p` and `InitialGeometry i n_v b_v width′ mesh r′` at the node. So the shortened residual
   `(s.restrict J).shortenPlains D₀ D₁` must be literally `initialInput` of the restricted slots with plains `X_k/N(D_k)`
   (and `Y_k` scaled so that `Y₁Y₂ = X₁X₂/(N(D₀)N(D₁))`). This holds iff `plainSupportPool` and the profile weights commute with the
   shortening (`{a : D·a ∈ plainSupportPool b X Y} = plainSupportPool b (X/N D) (Y/N D)`, and `W(N(Da)/X) = W(N(a)/(X/N D))`).
   Please confirm, or give the replacement.
2. **Geometry after shortening.** `InitialGeometry` needs:
   - the face at `vnode2` with the shortened lengths (easier: `length` decreases by `log_Z N(D)`);
   - the cell `b_v − width′ ≤ Σ_res ≤ b_v`;
   - the reference `Y₂′ = Z^{r′}` with `0 ≤ r′`, `Z^{r′} ≤ X_k/N(D_k)`.

   The last one is design risk 8: shortened plains may break the long corners. Which `r′` does the transfer use?
3. **Amplitudes.** The generic chain bounds a family whose amplitudes are built from *its own* columns: the extended column's scalar,
   `extra` and frozen coefficient, as in Collet's `RegularJointSupplier`. The balanced assembly carries the original amplitude of
   label `l` times `ω(D)`. N3/N6 must state how `amplitude_orig(l)·ω(D)` compares to the extended family's amplitude, or the extended
   family must be run with the original amplitudes. The second needs a `PhaseBound` for the original scalar at the extended column,
   which is new.

The δ-shift for a collision family, `a_v − r ≤ logb V₀ − logb V_short + κ` with `logb V₀ − logb V_short = Σ_J w + log_Z(N D₀ N D₁)`,
is already of the form `RegularPointAt_mx` takes. The node and `κ` are chosen as in design §7.

### N3/N6 indexing of collision families (N3/N6 agent, 2026-10-26 ~04:35)
**Families in the balanced assembly.** For a piece `k` (block `J_k = pieceBlock G w mesh k.2`, node `δ_k`) and a ray `ξ`, N3 carries the
plain family `(k, ξ)` (built: `pieceEnergy`, `pieces_transfer(_plain)`) and, next to it, one collision family `(k, ξ, f)` for each
`f ∈ coll s J_k`, with outer weight `ω f`:
```
Σ_l a_l E_l ≤ K·Mmax^(2N)·Z^(Aε)·Σ_{k∈pieces} Σ_ξ ( Σ_{l : {l // pieceKey alloc trans l = k}} a_l·pieceEnergy … k ξ l
      + Σ_{f ∈ coll s J_k} ω f · Σ_{l : {l // pieceKey alloc trans l = k ∧ collMem … l f}} a_l·collEnergy … k ξ f l )
```
(to be proved as `pieces_transfer_coll` in `Downstream/Families.lean`, same proof pattern as `pieces_sum_of_labels`, once the label-level
statement below exists). N6 then runs `eventual_selected_second` once per plain family and once per collision family, and sums
`Σ_f ω f·(family bound) ≤ (Σ_f ω f)·max ≤ K''·max` (`collisionWeight_sum`).

**Label-level statement N3 needs from L3** (the (Col)-free twin of `transfer_waist_column`; same hypotheses minus `NoCollision`;
(S) as `SeedFree s J L` until the seed generalization lands):
```
E(s; B; c; T := volume s; H) ≤ K·∏_{j∈J} M_j²·Z^(Aε)·( Σ_ξ E(s.restrict J; columnIdeal c; L; allocRestrict B J hJ;
        columnCharacter (rayShift c ξ); volume (s.restrict J); H_v)
    + Σ_{f ∈ coll s J} ω f · Σ_ξ (if h : collMem s B c J f then
        E(shortParent s J f; columnIdeal (extColumn c f h ξ); L; collAlloc s B J f h;
          columnCharacter (extColumn c f h ξ); volume (shortParent s J f); H_coll c f) else 0) )
```
- `coll s J : Finset (CollisionDatum J)` and `ω f` depend on `(s, J)` only (R1). `shortParent s J f := (s.restrict J).shortenPlains (D₀ f) (D₁ f) _ _`
  is common to the family `(k, ξ, f)`.
- `extColumn c f h ξ : FirstColumnIndex (source s modifier R₀ 1 Z Z ξ₀ hK (extBin c f h))` is the extended column `(C·D², D′)`
  (coordinator's option (k)), ray-shifted by `ξ`. `collMem` is the membership/label condition (`(C·D_f², D′)` a live common label;
  `collAlloc` a valid allocation of `shortParent`). `H_coll c f` is the MAIN radius at `volume (shortParent …)` and the collision node's
  amplitude (design §7: the node `δ′+w`).
- Please give `T` as `volume (shortParent s J f)` and keep a shared `K·∏_J M_j²·Z^(Aε)` in front of both sums.

**Three points to settle (with the fork lead's items 1–3 above):**
1. **Bins.** A family `(k, ξ, f)` must have one bin (one `source … bin'`). If `extBin c f h` depends on the label, N6 splits the family
   by `bin'`. That is harmless only if, for fixed `(bin, f)`, the possible `bin'` are boundedly many (each key component shifts by a fixed
   amount plus a rounding). The RHS factor `geometryHighFactor reflected … bin'` is `2^{±bin'.2 1}`. It must be `≤ C·geometryHighFactor
   … bin`, so either the component `.2 1` is unchanged by `C ↦ C·D²` or the change is paid. Please confirm which components move.
2. **Amplitudes.** N6 carries the original `a_l` inside each collision family (with `ω f` outside). Proposed route: a pointwise lemma
   `a_l ≤ Camp·Z^(xamp)·amplitude_ext(l, f)`, where `amplitude_ext = ‖scalar(extColumn)‖²·extra(extColumn)·‖frozen(collAlloc)‖²` (Collet's
   formula for the extended family). The energies are `≥ 0`, so N6 replaces `a_l` before calling `eventual_selected_second`, and
   `RegularJointSupplierCol3`/F6 run with the extended family's own amplitudes. The exponent `xamp` must fit in the collision node's
   extra room (`log_Z N(D_f)` in the δ-shift). This lemma is first-layer arithmetic (scalars, `extra`, frozen coefficients), so the
   transfer agent or the fork lead would prove it. The alternative is the fork lead's "run the extended family with the original
   amplitudes" (new `PhaseBound`).
3. **Node and radius.** The transfer's collision radius is `H'/N(D_f)`. Since `firstMainRadius ∝ V²·Z^(6·amp)`, this equals
   `firstMainRadius(V_short, 3·amp_c)` at the shortened volume `V_short = V_J/N(D_f)` with `amp_c = r + δ_k + log_Z N(D_f)/6`. The δ-shift
   then holds with room: `amp_c − r ≤ Σ_J w + log_Z N(D_f) + κ` because `logb V₀ − logb V_short = Σ_J w + log_Z(N D₀·N D₁)`. But
   `δ_k + log_Z N(D_f)/6` can exceed `d` at the top node, which is outside the ledger's node range (`0 ≤ θ ≤ δ ≤ d`). Design §7 avoids this
   by re-selecting `J∖C` and pricing the collision family at a lower node `δ ∈ [δ′+w/2, δ′+w]`. **Needed before `pieces_transfer_coll`:**
   the exact collision radius (as `firstMainRadius` at some volume and amplitude) and the collision node formula. N3 then provides the
   window/frozen/shift facts for that node, as it does for the plain node.

### Change to `RegularJointSupplier3`: per-label seeds (fork lead, 2026-10-26 ~02:55; green)
This implements the approved option (1): no-(S) labels `(l, L′)`. Where the definition had
`Function.Injective (fun l => (firstLabel … (column l), (column l).2.1.val)) → ∀ hLive, let hseed := live_projector_squarefree …`,
it now reads
```lean
  ∀column:Label→FirstColumnIndex (source s modifier R₀ 1 Z Z ξ _ bin),
  ∀_hLive:∀l,column l∈firstLiveColumns (source s modifier R₀ 1 Z Z ξ _ bin) (fun _=>logAnnulus),
  ∀(seed:Label→Ideal O)(hseed:∀l,Squarefree (seed l)),(∀l,seed l∣(column l).2.1.val)→
    Function.Injective (fun l=>(firstLabel s modifier R₀ 1 Z Z ξ _ bin (column l), seed l))→
  …
  let f:=mainAllocatedFamily (s.restrict J) ballProfile (p.profile 0) (p.profile 1) Z R₀ common seed (allocRestrict …) chars (fun _=>ht) P hseed …
```
- The plain case is `seed := fun l => (column l).2.1.val` with `hseed := live_projector_squarefree … (hLive l)`.
- Injectivity over `(firstLabel, seed)` is the family's obligation. For residual seeds, split the families by the transferred seed
  part `L_l/L′`; then injectivity follows from the original `(firstLabel, L_l)` injectivity.
- `Downstream/Balanced3.lean` and `Source/NFStep3.lean` import `Contract3`. Please rebuild them against the new definition.

## N7 (top theorem `nf_step3`; N7 agent, 2026-10-26 ~02:58; all green, axioms `[propext, Classical.choice, Quot.sound]`)
Build order, after `Downstream/Contract3`, `Downstream/MainGates`, `Downstream/Families`:
`ForkMx/Record1252270103Source/Core/InitialBalancedToTruncated` (90 lines) → `Source/NFPhysical3` (112) → `Source/NFStep3` (297).
`Source/NFStep3` was rebuilt against the per-label-seed `RegularJointSupplier3` (02:55). It treats `RegularJointSupplier3` and
`RegularSupplier3Statement` as opaque hypotheses.

**Tops.**
```lean
-- ForkMx/…/Core/InitialBalancedToTruncated.lean, namespace QRH.Record1252270103Source.InitialRegularToTruncated
-- (checked: Collet's `truncated_of_balanced` reads only `hg.reference_pos`, at `1 ≤ Y₂ = Z^(49/100-K b)`)
theorem truncated_of_balanced_mx (K:ℚ)(n low:Source)(b mesh ξ width:ℝ)(href:0<49/100-(K:ℝ)*b)
    (h:BalancedInitialSupplier K n low b mesh ξ width) :
    FixedSubsetTruncatedSupplier (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ) (crossing n low:ℝ) (K:ℝ) mesh ξ 0 b width
-- Source/NFPhysical3.lean, namespace QRH.MixedStep.Source
theorem reference_cells3 (n low h) (hv : SourceValidC3 n low h) (δ) (hδ : 0 < δ) :
    FiniteReferenceCells (crossing n low) n.cap natK δ (upperWidthCell (crossing n low) n.cap δ)   -- gate 9 at b = cap
def MixedTruncatedAt (n low : Source) (δw : ℝ) : Prop :=   -- Collet's NFTruncatedInlet at one width delta, K = natK
  ∀ ε > 0, ∀ b ∈ activeWidthGrid (crossing n low) n.cap δw, ∃ m x, 0 < m ∧ 0 < x ∧ ∀ mesh ξ, 0 < mesh → mesh ≤ m → 0 < ξ → ξ ≤ x →
    FixedSubsetTruncatedSupplier n.B n.L n.cap (crossing n low) natK mesh ξ ε b δw
theorem nf_physical3_of (n low h) (hv : SourceValid3 n low h) (δw) (hδ : 0 < δw) (htr : MixedTruncatedAt n low δw) :
    ∀ ε > 0, ∃ mesh ξ, 0 < mesh ∧ 0 < ξ ∧ InitialMarkedPhysicalSupplier n.B n.L n.cap (crossing n low) natK mesh ξ ε (upperWidthCell …)
theorem nf_step3_of_truncated (n low h) (hβ) (hK) (hv : SourceValid3 n low h) (hlow : ParentGood low) (hp : P low)
    (δw) (hδ : 0 < δw) (htr : MixedTruncatedAt n low δw) : P n
-- Source/NFStep3.lean, namespace QRH.MixedStep.Source
def RegularSupplier3Holds : Prop := ∀ K n low high b reserve θ mesh ξ width G φ,
  RegularSupplier3Statement K n low high b reserve θ mesh ξ width G φ          -- = the fork lead's `regular_supplier3`
def BalancedOfRegular3Statement : Prop := ∀ K n low b mesh ξ reserve width G φ Amix F εf, <the 31 hypotheses of
  balanced_of_regular3, copied verbatim from Downstream/Balanced3.lean as of 02:53, PlainTransfer and hreg included> →
  BalancedInitialSupplier K n low (b:ℝ) mesh ξ width                             -- = the N3/N6 agent's `balanced_of_regular3`
theorem nf_truncated3_of (hreg : RegularSupplier3Holds) (hbal : BalancedOfRegular3Statement) (htr : PlainTransfer)
    (n low h) (hβ) (hK) (hv : SourceValid3 n low h) (hX : SourceValid3X n low) (hlow : ParentGood low) (ha : NFAccounting n)
    (hG : P low) (hGH : P h) : ∃ δw : ℝ, 0 < δw ∧ MixedTruncatedAt n low δw
theorem nf_step3_of (hreg : RegularSupplier3Holds) (hbal : BalancedOfRegular3Statement) (htr : PlainTransfer) :
    QRH.MixedStep.Graph.NFStep3
```

**Parameter choice in `nf_truncated3_of`, in order.** No field is missing and no constraints conflict.
1. `reserve` comes from `mixed_geometry_of_valid3` (uniform in `b`).
2. `σ, θ` come from Collet's `fixed_regular_setup n (min reserve step)`, giving `FixedBudget σ 100 100 1 θ`, `σ ≤ reserve`, `σ ≤ e`,
   `θ ≤ step` and `θ ≤ 1/100000`. The HIGH parent mesh `mh` comes from `selected_high_parent_mesh (some h) θ` and `P h`.
3. One rational `q₀` with `0 < q₀ ≤ min (θ/2) (2e)` is the width delta, the grid step and the grid slack: `δw = g = κ = q₀`, and
   `εf = 3q₀`. Then `δw + κ ≤ θ`, `δw + g + κ = εf ≤ 6e`, `κ ≤ 6e` (for `top_slack`) and `δw ≤ step`.
   - No `nfWidthDelta`/width certificate is needed. The reference cells come from scalar gate 9 (`reference_cells3`), and the width
     bound comes from `q₀ ≤ θ/2`.
   - The grid widths are rational (`activeWidthGrid_rat`).
4. For each grid width `b : ℚ`:
   - `G = ⟨q₀, q₀, sourceD n low b⟩`, with `d_nonneg` from `MixedGeometry`.
   - `φ = mixedPhi G b εf`: `0` at `d`, `((b - θ δ : ℚ):ℝ) - εf` below `d`.
   - Node facts: price from `price_top`/`price_frozen`; geometry from `node_low` + `node_shape`; gaps from
     `gaps` + `actualGapsK_mono (σ ≤ reserve)` + `actualGaps_rm_of_K`.
   - `Lmin > 0` is the minimum of `regularLowMesh_mx` over `G.nodes`.
5. Bounds on `mesh` and `ξ`:
   - `mesh ≤ min(Lmin, r/4, θ/100, q₀/2, d/2 if d > 0, mh/100)`. This gives `2·mesh ≤ g, κ, d`, `mesh < r/2`, `100·mesh ≤ θ`,
     `100·mesh ≤ mh`, and `κ_shift = 2·mesh ≤ 6e` for `mainTwinFacts_of_mixedGeometry`.
   - `ξ ≤ min θ step`, which also gives `ξ ≤ 1`.
   - `reserve := θ` in `RegularJointSupplier3`/`balanced_of_regular3`, with `0 ≤ θ ≤ 1` and `θ ≤ step`.
6. `Amix = sourceAmp3Real n low b` and `F = sourceF3Real n low b`. `hAd` holds with equality, from `d_rat`. `hAsmall` is `amp_small`.
7. Other inputs:
   - `β ≤ 7/8` comes from `hK`.
   - The strict HIGH cap `h.cap < 1` comes from `SourceValidC3`'s high-parent conjunct, because `GainParametersK` only has `≤`.
   - `0 ≤ highFee` and `0 < e` come from `NFAccounting`.

**Finishing.** Once `regular_supplier3` and `balanced_of_regular3` are green, the remaining code is:
```lean
theorem nf_step3_of_transfer (htr : PlainTransfer) : QRH.MixedStep.Graph.NFStep3 :=
  nf_step3_of (fun K n low high b reserve θ mesh ξ width G φ => regular_supplier3 K n low high b reserve θ mesh ξ width G φ)
    (fun K n low b mesh ξ reserve width G φ Amix F εf => balanced_of_regular3 K n low b mesh ξ reserve width G φ Amix F εf) htr
```
`nf_step3 : NFStep3` then still needs `PlainTransfer` (`Downstream/Families.lean`), which is the open design point. If
`balanced_of_regular3` drops or replaces `PlainTransfer`, for example after the per-label-seed change, I update
`BalancedOfRegular3Statement` and `nf_step3_of` to match. **Owners: please tell N7 when a statement changes.**

### `High/GlobalPhysicalRegularSuppliers` (fork lead, green, partial)
`regular_point_supplier_rm_mx (n low high)(bcell φ reserve θ mesh ξ width poolAmp)(B₀ lam₀ cap₀)(hB₀ hlam₀ hcap₀)(hf)(sc : Scalar_mx …)(hpoolAmp)
(hmesh hwidth hbcell hr hfee hq hq1 hG)(hprice)(hLowMesh)(hβ hβhi)(hB0 hB1 hlam hcap0 hcap1)(hparent)(hgaps)` gives:
`∀ α₀ α [Fintype α₀][DecidableEq α₀][Fintype α], card α ≤ card α₀ → ∀ M … R₀ hR₀, ∃ degree controls, (0,0)∈controls ∧ ∃ C τsource, 0<C ∧ 0<τsource ∧
∀ᶠ Z, 1<Z ∧ RegularPointAt_mx (α₀:=α₀) (α:=α) … n low bcell φ reserve θ mesh ξ width τsource poolAmp B₀ lam₀ cap₀ (card α₀) degree controls C Z`.
This is PR 76's `regular_supplier_some_rm` up to the point supplier. `regular_supplier_some_rm_mx` (the composition with the helper's
`regular_supplier_of_points_mx`) is added when the bridge is green.

### Uniformization step of `regular_supplier3` (fork lead, green)
- `Downstream/Contract3.lean`: `RegularJointSupplier3At K n low b mesh ξ reserve width G φ δ`. This is the body of `RegularJointSupplier3` at one
  node `δ`, with the block quantified before the constants (`… ∀ R₀, R₀≠0 → ∀ J : Finset α, ∃ degree controls C τ σ, …`) and the window as
  `∀ _hθJ _hJδ _hsh`.
- `Downstream/Supplier3.lean`: `regular_supplier3_of_at … (h : ∀ δ ∈ G.nodes, RegularJointSupplier3At … δ) : RegularJointSupplier3 …`. The
  constants are max/sum/inf/union over `G.nodes ×ˢ univ`; `mono_five` is the monotone product.
- **Remaining for `regular_supplier3`:** `RegularJointSupplier3At … δ` at each node, from `NodeFacts3` and the F5 helper's
  `regular_supplier_of_points_mx` / `RegularJointSupplier_mx` (at `α₀ := α`, `α' := {i // i ∉ J}`, node `vnode2 n low b δ (G.theta δ)`),
  together with `regular_point_supplier_rm_mx`, `scalar_vnode2`, `restrict_initialGeometry`, `residual_shift` and `frozen_margin_restrict`.

### Fork-side answer to N3/N6 point 1 (bins) (fork lead)
- The geometry key is `(sourceRatioIndex q, geometryIndex q)` with `geometryIndex q i = ⌊log₂ N(geometryIdeals q i)⌋` and
  `geometryIdeals q = ![C, D, commonRadical C D, (activeConductor C D), (primeSubsetGenerator E)]`, where `(C, D) = q.1.val`
  (`S/High/GlobalPhysicalGeometryBins.lean:42-58`).
- `geometryHighFactor reflected C₀ bin` depends **only on component 1**, `⌊log₂ N(D)⌋`: it is `2·C₀²·2^(bin.2 1)` if `reflected = false`
  and `2^(−bin.2 1)` if `reflected = true` (`Cycle61/Physical/InitialMass/GeometryHighPayment.lean:31`, `GeometryScalarCompensation.lean:17`).
- So for `reflected = false` (column ideal `C`): extending `C ↦ C·D_f²` with the second ideal unchanged leaves the factor unchanged. If the
  second ideal must also grow, for the `sameSupport` field of `FirstBlockSource`, the factor grows by `2^(Δ comp 1)` and must be paid.
- For `reflected = true` (column ideal `D`): `D ↦ D·D_f²` raises component 1, so `2^(−bin.2 1)` only decreases. This is free.
- Components 0 and 2–4 shift by amounts fixed by `f`, up to a floor rounding of at most 1 each. So for fixed `(bin, f)` there are at most
  `2^4` bins `bin′`, plus whatever the ratio index does.

## Seeds without changing `Family_mx` (coordinator, 2026-10-26 ~10:55)
The "approved option (1)" (a per-label child seed field in `Family_mx`) is **not needed** and was reverted after a trial.
Residual seeds `L′ ∣ (column l).2.1.val` of the transfer without (S) are handled on the consumer side by *columns*:
* `QRH.MixedStep.SeedColumn.seedColumn j L′ h` (`ForkMx/…/Admission/SelectedRegularSeedColumn.lean`, green) is the column with the label
  and the rays of `j` and the residual divisor `L′`. It exists because `FirstBlockSource.divisors` is `divisorPool … = ⋃ idealDivisors` (closed
  under divisors, `divisors_dvd`); it is live iff `j` is live and `L′` is squarefree (`seedColumn_live`).
* `firstLabel`, `columnIdeal`, `columnCharacter`, `H0`, `balancedColumnScalar`, `extra` and the frozen coefficient depend only on the label
  `j.1` and the rays, not on the divisor. So the plain family `allocatedRegularFamily_mx a col′ …` on `col′ l := seedColumn (rayShift … (column l) ray) (seed l) _`
  has child seed `seed l` and the **original** amplitude. All plain statements (F5 bridge 46–50, `RegularPointAt_mx`) apply to it unchanged.
* `RegularJointSupplier3`'s per-label `seed` is thus proved from the plain `RegularJointSupplier_mx` at `col′`; its injectivity hypothesis
  `(firstLabel, seed)` is exactly the plain injectivity of `col′`.
