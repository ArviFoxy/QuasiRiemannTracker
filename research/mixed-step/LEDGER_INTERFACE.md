# Ledger interface (N4 / N5 / N7-gates) for the fork agent

Status: **v2 (2026-10-26)**. §1 and §2 are BUILT (exact statements below, axioms clean).
§3 (Gaps) and §4 (MixedGeometry) are planned signatures, being built now.
Append requests at the end ("## Requests from the fork agent").

Namespace `QRH.MixedStep.Ledger`. Modules (build order):
`Ledger/Nodes.lean` (built) → `Ledger/FrozenPrice.lean` (built) → `Ledger/Gaps.lean` → `Ledger/Geometry.lean`.
`Source`, `sourceT/A/F`, `sourceTReal/AReal/FReal`, `crossing`, `sourceDen` are Collet's
(`Record1252270103Finite`); `sourceD`, `sourceDen3`, `sourceX0`, `sourceF3Real`, `sourceDReal`,
`SourceValidC3`, `SourceValid3`, `SourceValid3X` are `QRH.MixedStep.Finite`.
`plainBudget` is `QRH.Record1252270103Source.PhysicalLowReserve.plainBudget`.

## 0. Decisions

1. **Rational nodes.** The width grid is made rational: replace the real width delta by any
   rational `δw ∈ (0, δ]` (every use of the width delta is monotone in it). Grid points
   `min cap (cross + i·δw)` are rationals, so `b : ℚ` and nodes are genuine `Source`s; no `RNode`.
2. **Nodes.** For a width `b`, `d = sourceD n low b` (rational). Nodes are `δ ∈ {k·g : k·g < d} ∪ {d}`;
   the **top node is `δ = d` exactly**. Every per-node fact is proved for every rational
   `0 ≤ θ ≤ δ ≤ d`, so any finite grid inside `[0,d]` works.
3. **Two-parameter node (fork request, done).** `vnode2 n low b δ θ`: budget and width shifted by `θ`
   (node width `b − θ`), amplifier shifted by `δ`. With greedy window `δ_act ∈ [δ − 2mesh, δ − η]`,
   take a *rational* `θ ≤ δ − 2mesh` fixed before the mesh, e.g. `θ = max 0 (δ − κ)` with a fixed
   rational `κ` and `mesh ≤ κ/2`. Then `Σ_res ≤ b − θ` and `m₁ + m₂ + L·Σ_res ≤ B − L·θ`.
   `RealGeometryLow` and the HIGH gaps hold for **all** `0 ≤ θ ≤ δ ≤ d` with no slack condition
   (`T` drops by `θ ≥ 0`, which only helps). The frozen price needs nothing new; the top price needs
   `q·(d − θ) ≤ 6e` (fee `r − q(d−θ) ≥ 14e` from gate 8 `r > 20e`). So choose `κ ≤ 6e`.
   `vnode n low b δ := vnode2 n low b δ δ` (definitionally).
4. **Frozen hypothesis.** Non-top nodes are priced under `(b − θ) − ε ≤ f` with `0 ≤ ε ≤ 6e`
   (`f` = frozen width at the node). The grid gives it: a class at node `k` (top excluded) has
   transferable width `< δ_{k+1}`, total width `≥ b − δw`, so `f ≥ b − δw − δ_{k+1}
   = (b − θ) − (δw + g + (δ_k − θ))`. Choose `δw + g + κ ≤ ε ≤ 6e` (e.g. `δw = g = κ = 2e`, `ε = 6e`).
   The design's fee margin `φ_k` is NOT enough: with it the upper-cap branch needs Collet's weak cap at
   the node scale `F = 1 − 6r − 6δ`, which is false at `δ = 0` on the chain (fan step 1, `b = cap = 0.075`:
   `cap₀F − (B₀F − t)/Λ₀ = −8.0e−3` at `F = 1 − 6r`). The top node takes `φ = 0` (any `f ≥ 0`).
5. **The one new gate** is the coordinator's `SourceValid3X n low := 0 < 6*n.q*low.B − low.L`
   (Finite/SourceValid3X.lean); I use `sourceDen_ne_of_valid3X` (needs `0 < low.L`, from `ParentGood low`).
   It makes `sourceAReal (vnode2 …) = r + δ`; it is not implied by `SourceValid3`.
6. Hypotheses of every node theorem: `hv : SourceValidC3 n low h` (= `hv.1` of `SourceValid3`),
   `hlow : ParentGood low`, `hden : sourceDen n low ≠ 0`, `he : 0 ≤ (n.allowance:ℝ)`,
   `hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)`.

## 1. Nodes (`Ledger/Nodes.lean`, BUILT)

```lean
def vfee (n low : Source) (b δ : ℚ) : ℚ :=
  n.lowFee*(1 - 6*n.q*(low.B/low.L)) + δ*sourceDen3 n low - n.q*sourceX0 n low b
def vfee2 (n low : Source) (b δ θ : ℚ) : ℚ := vfee n low b δ - n.q*(δ - θ)
def vnode2 (n low : Source) (b δ θ : ℚ) : Source :=
  ⟨n.B - n.L*θ, n.L, n.cap, n.q, n.allowance, vfee2 n low b δ θ, n.highFee⟩
def vnode (n low : Source) (b δ : ℚ) : Source := vnode2 n low b δ δ
-- simp lemmas vnode2_B/L/cap/q/allowance/lowFee/highFee (rfl), vnode_* likewise
theorem vnode2_T : sourceT (vnode2 n low b δ θ) (b - θ) = sourceT n b
theorem vnode2_A (hden : sourceDen n low ≠ 0) : sourceA (vnode2 n low b δ θ) low (b - θ) = n.lowFee + δ
theorem vnode2_F (hden) : sourceF (vnode2 n low b δ θ) low (b - θ) = 1 - 6*n.lowFee - 6*δ
theorem vnode2R_T : sourceTReal (vnode2 n low b δ θ) ((b - θ : ℚ) : ℝ) = sourceTReal n (b:ℝ)
theorem vnode2R_A (hden) : sourceAReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) = (n.lowFee:ℝ) + (δ:ℝ)
theorem vnode2R_F (hden) : sourceFReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) = 1 - 6*(n.lowFee:ℝ) - 6*(δ:ℝ)
theorem vfee_top (hden3 : sourceDen3 n low ≠ 0) : vfee n low b (sourceD n low b) = n.lowFee
theorem vfee2_top (hden3) : vfee2 n low b (sourceD n low b) θ = n.lowFee - n.q*(sourceD n low b - θ)
theorem vfee_sub (hden3) : vfee n low b δ - n.lowFee = (δ - sourceD n low b)*sourceDen3 n low
theorem vnode2_amp_ge (hden) (hδ0 : 0 ≤ δ) : (n.lowFee:ℝ) ≤ sourceAReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ)

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

theorem realGeometryLow_vnode2 (n low h : Source) (hv : SourceValidC3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ))
    {b δ θ : ℚ} (hb : (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ δ) (hδ : δ ≤ sourceD n low b) :
    RealGeometryLow (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ)
```
Dropped from Collet's `RealGeometry`: `denominator_pos` (node denominator is negative),
`low_fee_room` (node fee `< r` below the top), `weak_cap` (false at `δ = 0`), and the first-layer
fields `reference_*`, `centered_499`, `*_tail` (they live in `MixedGeometry`, at the actual `b`).
Only `1 < n.L` of `ParentGood n` is consumed by Collet's LOW spine (`hn.2.2.1`); `(vnode2 …).L = n.L`.
`ParentGood (vnode2 …)` would also need `0 < n.B − n.L·θ`: not implied by the gates (≥ 0.96 on the chain).

## 2. Price (`Ledger/FrozenPrice.lean`, BUILT)

```lean
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
-- (the file opens `scoped Classical` like Collet's RegularLowPhysicalPrice.lean)

theorem mixed_node_price_frozen (n low h : Source) (hv : SourceValidC3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0≤(n.allowance:ℝ))
    {b δ θ : ℚ} (hb : (b:ℝ)∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hθ0 : 0≤θ) (hθ : θ≤δ) (hδ : δ≤sourceD n low b)
    {ε : ℝ} (hε0 : 0≤ε) (hε : ε≤6*(n.allowance:ℝ)) :
    MixedNodePrice (vnode2 n low b δ θ) low ((b-θ:ℚ):ℝ) (((b-θ:ℚ):ℝ)-ε)

theorem mixed_node_price_top (n low h : Source) (hv : SourceValidC3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0≤(n.allowance:ℝ))
    {b θ : ℚ} (hb : (b:ℝ)∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hθ0 : 0≤θ) (hθ : θ≤sourceD n low b)
    (hslack : (n.q:ℝ)*((sourceD n low b:ℝ)-θ)≤6*(n.allowance:ℝ)) :
    MixedNodePrice (vnode2 n low b (sourceD n low b) θ) low ((b-θ:ℚ):ℝ) 0
```
Generic forms (any `Source n'`): `mixed_node_price_frozen_of (hg : RealGeometryLow n low b) … :
MixedNodePrice n low b (b-ε)`; `mixed_node_price_top_of (hg) (hfee : 14*e ≤ n.lowFee)
(hweak : (B₀F−t)/Λ₀ ≤ cap₀F) : MixedNodePrice n low b 0`.
Coordinate lemmas: `actual_low_coordinate_payment_f`, `modified_low_coordinate_payment_f` (two
parents; Collet's statement without the weak cap, RHS
`-min a (g+q*min ((1-1/lam)*f) (f-((B*F-t)/lam-h*F))) + q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound`).
Design-φ material: `phiK`, `phiK_spec`, `pool_only_gate` (§1d, from gate 5), `mixed_node_price_phi`
(needs the weak cap at the node as a hypothesis).

Notes for the fork:
* `A` is free (pass the virtual side volume); the shift identity is yours (F2).
* `plainBudget (vnode2 …) ((b−θ:ℚ):ℝ) width = sourceTReal n b + n.L·width` (`vnode2R_T`).
* If the residual width exceeds `b − θ` by `w ≥ 0`, use `mesh := mesh' + w`
  (`max 0 (max (X+w) (Y+w)) ≤ max 0 (max X Y) + w`); with `θ ≤ δ_act` no excess remains.

## 3. HIGH gaps (`Ledger/Gaps.lean`, building)

```lean
theorem mixed_uniform_reserve (n low h : Source) (hv : SourceValid3 n low h) (hlow : ParentGood low)
    (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      ∀ δ θ : ℚ, 0 ≤ θ → θ ≤ δ → δ ≤ sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
        QRH.RepeatedMarks.Source.ActualGapsK (vnode2 n low b δ θ) low h ((b - θ : ℚ):ℝ) ν reserve
-- and the ActualGaps_rm form via actualGaps_rm_of_K
```

## 4. Bundle (`Ledger/Geometry.lean`, building)

`structure MixedGeometry (Kgraph : ℚ) (n low h : Source) (b : ℚ) (reserve : ℝ) : Prop` with the
first-layer facts at the actual width `b` (`A := r + d`, `F' := 1−6r−6d`, `T := t+b`; MAIN twins
`T + 9A + fee < 5/6 + 0.499·Lref` (= scalarGate3 11) and `T + 5A + fee < 1` (= 12), tails 13–15,
reference, weak cap at `F'`, cell, mixed payment) and, for all rational `0 ≤ θ ≤ δ ≤ d`:
`node_low` (RealGeometryLow), `node_amp`, `price_frozen`, `price_top` (with `q(d−θ) ≤ 6e`), `gaps`.

```lean
theorem mixed_geometry_of_valid3 (n low h : Source) (hv : SourceValid3 n low h)
    (hX : SourceValid3X n low) (hlow : ParentGood low) (he : 0 < (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      MixedGeometry (9/2) n low h b reserve
```

## Requests from the fork agent
(append below)

* (via coordinator, 2026-10-26) Two-parameter node `vnode2 n low b δ θ`, B/width shift `θ ≤ δ`,
  amplitude/fee shift `δ`. **Done**, see §0.3, §1, §2; §3/§4 are stated for `vnode2`.
