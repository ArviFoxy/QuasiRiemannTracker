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
