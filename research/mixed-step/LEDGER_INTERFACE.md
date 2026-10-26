# Ledger interface (N4 / N5 / N7-gates) for the fork agent

Status: **planned signatures, v1 (2026-10-26)**. Written by the ledger agent before the modules
exist. I will keep this file in sync with the Lean as it lands; append requests at the end
("## Requests from the fork agent") and I will read them before finalizing.

Namespace `QRH.MixedStep.Ledger`. Modules (build order):
`Ledger/Nodes.lean` → `Ledger/FrozenPrice.lean` → `Ledger/Gaps.lean` → `Ledger/Geometry.lean`.
All `Source`, `sourceT/A/F`, `sourceTReal/AReal/FReal`, `crossing` are Collet's
(`Record1252270103Finite`); `sourceD`, `sourceDen3`, `sourceX0`, `sourceF3`, `sourceDReal`, … are
`QRH.MixedStep.Finite` (Finite/SourceValid3.lean, Finite/HighGate3.lean).

## 0. Decisions (read these first)

1. **Rational nodes.** The width grid is made rational: replace the real width delta by any
   rational `δw ∈ (0, δ]` (all uses of the width delta — `0<δ`, `δ≤1`, `|loss|δ≤e`,
   `2|loss|δ≤margin`, `FiniteReferenceCells` — are monotone in `δ`, so this is free). Grid points
   `min cap (cross + i·δw)` are then rationals. So `b : ℚ` and nodes are genuine `Source`s; no `RNode`.
2. **Node set.** For a width `b` the nodes are `δ ∈ {k·g : k·g < d} ∪ {d}` with `d = sourceD n low b`
   (rational). The **top node is `δ = d` exactly**, not `⌈d/g⌉·g`: then the top node's gates are
   literally the `SourceValid3` gates and no margin/`2g` slack is needed anywhere. Every per-node fact
   below is proved for **every rational `δ ∈ [0, d]`**, so any finite grid inside `[0,d]` works.
3. **Frozen hypothesis (changed from the design's `φ_k`).** The design's
   `φ_k = (qX₀ + r − a(1−6qβ) − δ_k·den3)₊/(q(1−1/Λ₀))` makes the *affine* LOW branch pay, but the
   *upper-cap* branch then needs Collet's weak cap at the node scale `F_k = 1 − 6r − 6δ_k`, and that is
   **false** at `δ = 0` on our chain (fan step 1, `b = cap = 0.075`: `cap₀F − (B₀F − t)/Λ₀ = −8.0e−3`
   at `F = 1 − 6r`; `weakCap3` only checks `F = F'`). So the price for non-top nodes is stated with
   the frozen hypothesis **`(b − δ) − ε ≤ f`** (`0 ≤ ε ≤ 6e`), which is what the grid gives anyway:
   a class at node `k` (top excluded) has transferable width `< δ_{k+1}`, total width `≥ b − δw`,
   hence first-level frozen width `f ≥ b − δw − δ_{k+1} = (b − δ_k) − (g + δw)`. Choose `g + δw ≤ ε ≤ 6e`.
   With that hypothesis neither the weak cap nor the fee identity is used at non-top nodes.
   The top node (`δ = d`, fee `r_K = r`) takes `φ = 0` (any `f ≥ 0`).
4. **One new gate:** `sourceDen n low ≠ 0` (Collet's `1 − 6qB₀/Λ₀`). Without it
   `sourceAReal (vnode …) = (…)/0 = 0 ≠ r + δ`. It is NOT implied by `SourceValid3` (all its gates are
   polynomial in `qβ`; `den3 = den + q > 0` is the only related one). On the chain `den < 0`
   (fan: `den ≤ −0.2095`; family pieces: `den = 2⁻¹⁵ − q` exactly, since `q` is chosen with
   `den3 = 2⁻¹⁵`). Proposed predicate: `SourceValid3X n low := sourceDen n low ≠ 0`; certificate form
   `0 < 6*n.q*low.B - low.L`.

## 1. Nodes (`Ledger/Nodes.lean`)

```lean
/-- fee of the virtual node: Collet's `sourceA` then equals `r + δ` -/
def vfee (n low : Source) (b δ : ℚ) : ℚ :=
  n.lowFee*(1 - 6*n.q*(low.B/low.L)) + δ*sourceDen3 n low - n.q*sourceX0 n low b
def vnode (n low : Source) (b δ : ℚ) : Source :=
  ⟨n.B - n.L*δ, n.L, n.cap, n.q, n.allowance, vfee n low b δ, n.highFee⟩
-- node width: (b - δ)
theorem vnode_T : sourceT (vnode n low b δ) (b - δ) = sourceT n b
theorem vnode_A (hden : sourceDen n low ≠ 0) (hL : low.L ≠ 0) :
    sourceA (vnode n low b δ) low (b - δ) = n.lowFee + δ
theorem vnode_F (hden) (hL) : sourceF (vnode n low b δ) low (b - δ) = 1 - 6*n.lowFee - 6*δ
theorem vnodeR_T/A/F : the same for sourceTReal/AReal/FReal at ((b - δ : ℚ) : ℝ)
theorem vfee_top (hden3 : sourceDen3 n low ≠ 0) (hL) : vfee n low b (sourceD n low b) = n.lowFee
theorem vfee_sub : vfee n low b δ - n.lowFee = (δ - sourceD n low b)*sourceDen3 n low   -- (hden3, hL)
-- vnode .L/.q/.allowance/.highFee/.cap are n's (rfl)

/-- RealGeometry minus denominator_pos, low_fee_room, weak_cap and the first-layer
    reference/centered/tail fields; plus `denominator_ne`. -/
structure RealGeometryLow (n low : Source) (b : ℝ) : Prop where
  lowL_pos : 0<(low.L:ℝ)
  denominator_ne : (sourceDen n low:ℝ) ≠ 0
  width_room : 2*(n.allowance:ℝ)<b
  a_pos : 0<sourceAReal n low b
  a_small : sourceAReal n low b<1/75
  raw_factor_room : (sourceTReal n b+b)/2+4*(n.allowance:ℝ)<sourceFReal n low b
  parent_budget_room : sourceTReal n b+b+4*(n.allowance:ℝ)<(low.B:ℝ)*sourceFReal n low b
  qcap_room : (n.q:ℝ)*(low.cap:ℝ)<1
  a_allowance : 20*(n.allowance:ℝ)<sourceAReal n low b
  fee_identity : sourceAReal n low b-(n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=(n.lowFee:ℝ)

theorem realGeometryLow_vnode (hv : SourceValid3 n low h) (hX : sourceDen n low ≠ 0)
    (he : 0 < (n.allowance:ℝ)) {b δ : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ sourceD n low b) :
    RealGeometryLow (vnode n low b δ) low ((b - δ : ℚ) : ℝ)
```
Only `1 < n.L` of `ParentGood n` is consumed by Collet's LOW spine (`hn.2.2.1`); `(vnode …).L = n.L`.
`ParentGood (vnode …)` would also need `0 < n.B − n.L·δ`, which is not implied by the gates
(numerically ≥ 0.96 on the chain); avoid it.

## 2. Price (`Ledger/FrozenPrice.lean`)

```lean
/-- ModifiedNodePrice (Coefficient/RegularLowPhysicalPrice.lean:27) with two parents —
    the first label `j` over `s₀ : Input ι₀`, the second datum over `ι` — and the frozen
    hypothesis `φ ≤ f`. Everything else (order of binders, the 12 numeric guards, `x`, the
    erasure bound, the conclusion `≤ -8*e`) is verbatim. -/
def MixedNodePrice (n low : Source) (b φ : ℝ) : Prop :=
  ∀(ι₀:Type)[Fintype ι₀][DecidableEq ι₀](ι:Type)[Fintype ι][DecidableEq ι],
  ∀(s₀:Input ι₀)(A₁ A₂ Dmark Kmark R seed:Ideal O)(Fmark:Ideal O→ℂ)
    (H Z ξ:ℝ)(hH:0<H)(bin:ℤ×(Fin 5→ℤ)),
  ∀j:FirstColumnIndex (CoupledFirst.geometryFirstSource s₀
    (markedSourceModifier A₁ A₂ Dmark Kmark Fmark) R seed H Z ξ hH bin),
  ∀(reflected second:Bool)(d₂:SecondInputDatum ι)(U:Finset (CommonIndex d₂.C d₂.D)),
  ∀(M A reserve width err errv c f loss rho mesh erased radial radialRound outer:ℝ),
    1<Z → 0≤width → width≤PhysicalLowGuard.step n → 0≤loss → 0≤rho →
    rho≤(n.allowance:ℝ)/4 → loss≤(n.allowance:ℝ)/4 → mesh≤(n.allowance:ℝ)/4 →
    err≤(n.allowance:ℝ)/4 → errv≤(n.allowance:ℝ)/4 → radialRound≤(n.allowance:ℝ)/4 →
    outer≤4*(n.allowance:ℝ) →
  let l:=FirstFamily.firstLabel s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
    R seed H Z ξ hH bin j;
  let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l d₂.C d₂.D U
    Z M A (sourceAReal n low b) ξ reserve err) errv;
    labelC reflected l Z≤c → 0≤f → φ≤f →
    erased≤max 0 (max
      (b-f-((low.B:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-
        (plainBudget n b width-c+f+loss))/(low.L:ℝ))
      (b-f-(low.cap:ℝ)*(sourceFReal n low b-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh →
    radial≤x 2+radialRound →
    x 0+x 1+radial-balancedGeometrySide reflected A
      (CoupledFirst.geometryExponents s₀ (markedSourceModifier A₁ A₂ Dmark Kmark Fmark)
        R seed H Z ξ j.1.val)+(n.q:ℝ)*erased+outer≤-8*(n.allowance:ℝ)

-- top node, any frozen width
theorem mixed_node_price_top (hv : SourceValid3 n low h) (hX : sourceDen n low ≠ 0)
    (he : 0 < (n.allowance:ℝ)) {b : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    MixedNodePrice (vnode n low b (sourceD n low b)) low ((b - sourceD n low b : ℚ):ℝ) 0
-- every node, frozen width at least (b-δ) - ε
theorem mixed_node_price_frozen (same hyps) {δ : ℚ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ sourceD n low b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 6*(n.allowance:ℝ)) :
    MixedNodePrice (vnode n low b δ) low ((b - δ : ℚ):ℝ) (((b - δ : ℚ):ℝ) - ε)
```
Notes for the fork:
* `A` is free (pass `logb Z (volume sv)` = the virtual side volume); the shift identity is yours (F2).
* The residual's total width is `≤ (b−δ) + 2·mesh'` (window `[δ−2mesh', δ−η_Z]`). Use the price at node
  width `b−δ` with `mesh := 3·mesh'` (`max 0 (max (X+2m) (Y+2m)) ≤ max 0 (max X Y) + 2m`).
* `erased ≤ …` is exactly Collet's form at the node; `plainBudget (vnode …) (b−δ) width = t + L·width`
  because `sourceT (vnode …) (b−δ) = sourceT n b`.
* Also proved: `actual_low_coordinate_payment_f` (Collet's `actual_low_coordinate_payment` without the
  weak-cap hypothesis, keeping the frozen terms): RHS `-min a (g + q*min ((1-1/λ)*f) (f - ((B*F-t)/λ - h*F))) + …`.

## 3. HIGH gaps (`Ledger/Gaps.lean`)

```lean
theorem mixed_uniform_reserve (hv : SourceValid3 n low h) (hX : sourceDen n low ≠ 0)
    (he : 0 < (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      ∀ δ : ℚ, 0 ≤ δ → δ ≤ sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
        QRH.RepeatedMarks.Source.ActualGapsK (vnode n low b δ) low h ((b - δ : ℚ):ℝ) ν reserve
-- hence ActualGaps_rm (vnode n low b δ) low (some h) ((b-δ:ℚ):ℝ) ν reserve (actualGaps_rm_of_K)
```
Proof route (no assumption): the gap at node `δ` is `≥` the certified mixed gap. Base
`physicalBase ν (r+δ) (T−δ) ≤ physicalBase ν (r+d) T` (slope `5−6ρ−ν ≥ 0` in δ, and `−ν·d` in T);
gain `gainK` is monotone in `S = b−δ−2e ≥ b−d−2e` and `F = 1−6r−6δ−e ≥ F'−e`; the three family gaps
decrease in δ (slopes `−4+6ρ−3ν`, `−3`, `−4+6ρ−3ν`) and at `δ = d` equal the `densityGate3` values
`+ d`. Cell condition at the node follows from `CellRatio3` (`2S_v − F_v ≤ 2S−F' − 2d … ≤ 0`).

## 4. Bundle (`Ledger/Geometry.lean`)

```lean
def SourceValid3X (n low : Source) : Prop := sourceDen n low ≠ 0     -- the one new gate

structure MixedGeometry (Kgraph : ℚ) (n low h : Source) (b : ℚ) (reserve : ℝ) : Prop where
  -- shape: ParentGood n, ParentGood low, GainParametersK h, 1/2 ≤ q < 3/4, 0 < e, den ≠ 0, b ∈ [cross, cap]
  -- first layer at the actual width b, A := r + d, F' := 1-6r-6d, T := t+b (all real):
  --   d_nonneg, live_room (2e + d < b), amp_small (A < 1/75), raw_factor_room, parent_budget_room (F'),
  --   weak_cap (F'), low_fee_room, a_allowance, qcap_room, reference_pos, reference_gap,
  --   centered_twin  : T + 9A + fee < 5/6 + 499/1000*Lref      (= scalarGate3 11)
  --   zero_twin      : T + 5A + fee < 1                        (= scalarGate3 12)
  --   second_tail / mixed_tail / reference_tail with A          (= scalarGate3 13/14/15)
  --   cell (2(b-2e) ≤ F'-e), mixed_payment (r(1-6qβ) + d·den3 = qX₀ + r)
  -- nodes, for every rational δ ∈ [0,d]:
  node_low    : ∀ δ:ℚ, 0≤δ → δ≤sourceD n low b → RealGeometryLow (vnode n low b δ) low ((b-δ:ℚ):ℝ)
  node_amp    : ∀ δ, … → sourceAReal (vnode n low b δ) low ((b-δ:ℚ):ℝ) = n.lowFee + δ   (≥ r, so mesh<r/2 ⇒ mesh<a_v/2)
  price_top   : MixedNodePrice (vnode n low b (sourceD n low b)) low ((b-sourceD n low b:ℚ):ℝ) 0
  price_frozen: ∀ δ, … → ∀ ε, 0≤ε → ε≤6e → MixedNodePrice (vnode n low b δ) low ((b-δ:ℚ):ℝ) (((b-δ:ℚ):ℝ)-ε)
  gaps        : ∀ δ, … → ∀ ν ∈ Icc q (3/4), ActualGapsK (vnode n low b δ) low h ((b-δ:ℚ):ℝ) ν reserve

theorem mixed_geometry_of_valid3 (hv : SourceValid3 n low h) (hX : SourceValid3X n low)
    (he : 0 < (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      MixedGeometry (9/2) n low h b reserve
```
`he` comes from `NFAccounting n` (`nf_accounting_positive`). The reserve is chosen before the
width, as in `nf_actual_uniform_reserve_K`.

## Requests from the fork agent
(append below)
