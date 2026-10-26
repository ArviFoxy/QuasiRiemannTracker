
## L2 transfer

**Where.** `lean-env/qrh/Submissions/arvi_mixed_step/Transfer/`, namespace `QRH.MixedStep.Transfer`, 12 modules (~2.0k lines). Each builds with `mk_mixed.sh Transfer/<Name>` in 6–10 s. Order: Split → Factor → Rays → Identity → Positive → Bounds → Main; Residual and Select after Split; PoolRows after Rays; Pool after Main and PoolRows; Allocation after Pool. No `sorry`/`axiom`/`native_decide`. `#print axioms` on every top theorem gives `[propext, Classical.choice, Quot.sound]`.

**Proved (top level).**
- `collet_main_selected_transfer` (Main), the (S) form. For ε > 0 and N, there is C > 0 such that for every `s : Input ι` with `card ι ≤ N`, every `J : Finset ι`, A₁ A₂ Dc K R L, F, τ, t, T, n, Z, M, W:
  - hypotheses: `dyadicScale n ≤ Z^M`, `∏_{j∈J} s.hi j * s.P j ≤ W`, (S), (F), (Col);
    - (S): `∀ j ∈ J, ∀ p ∈ s.slots j, ¬p ∣ L`;
    - (F): `∀ v ∈ piFinset s.pools, F(Dc*∏v) = F(Dc*∏(restPart J v))`, which is trivial for F = 1;
    - (Col): `∀ v ∈ piFinset s.pools, tupleCoefficient s (markedSourceModifier A₁ A₂ Dc K F) R L v ≠ 0 → IsCoprime (∏_{j∈J} v(inl j)) (v(inr 0)*v(inr 1))`;
  - conclusion: there is `rows : Finset O` with each `r ≠ 0` and `normValue r ≤ Z^M*W^4`, and
    `Σ' h, dyadicWeight n (normValue h) * ‖G h‖² ≤ C * (∏_{j∈J} s.hi j * s.M j²) * (Z^M*W^4)^ε * Σ_ξ Σ_{r∈rows} ‖G'_ξ r‖²`;
  - here `G` is Collet's source polynomial with coefficient `CoupledFirst.coefficient s (markedSourceModifier A₁ A₂ Dc K F) R L I * ((√T)⁻¹ * rowWeight τ fixedBadMask 1 1 t I)`;
  - and `G'_ξ` is the same on `residualInput s J : Input {i // i ∉ J}`, with `(√(T/∏_{j∈J} s.P j))⁻¹` and `rowWeight (childCharacter τ ξ) …`.
- `collet_main_selected_transfer_gen` (Main): the same with (S) replaced by the weaker tuple-level (S'):
  `∀ v ∈ piFinset s.pools, tupleCoefficient … v ≠ 0 → IsCoprime L (∏_{j∈J} v(inl j))`.
  - (S) ⟹ (S') is `seed_free_of_slots`.
  - (S') also holds when the projectors exclude the seed primes from the selected slots.
  - Proof idea (`tuple_factor_masked_gen`): if L is not coprime to D, then the original coefficient vanishes by (S'), and the residual coefficient times [D⊥n] vanishes because L ∣ n.
- `collet_main_selected_transfer_one`: the same with F = 1, so only (S) and (Col) are assumed.
- `transfer_identity` (Identity) is the exact (T):
  `G k = Σ_{χ,ξ} π_{χξ} Σ_{u∈selBox} selScalar u χ k · G'_ξ(primaryGenerator(selProduct u)^4 * k)`.
- `collet_main_selected_transfer_pool` (Pool) chains the transfer into Collet's pool (rows version of `actual_marked_main_ideal_coefficient`).
  - RHS: `C·∏hi M²·(Z^M W⁴)^ε·Σ_ξ |P|⁻¹((M'+6·upper)/ell)·(gaussEnergy residual_corrected_ξ ballProfile (Z^(M'+6·upper))).re`.
  - Extra hypotheses: `Z^M W⁴ ≤ Z^M'`, `0 ≤ hi j` on J, Collet's pool premises, `sourceRadius (residualInput s J) ≤ Z^B`.
  - It uses (S'), as does `allocation_selected_transfer_pool`.
- `allocation_selected_transfer_pool` (Allocation) is the mixed twin of Collet's `actual_marked_allocation_main`. Each allocation B gets its own block `Jsel B ⊆ liveIndices B`.
- Helpers:
  - `residualInputAt s J η t` and `sourceRadius_residual` (Residual);
  - `select_block`, i.e. `upward_subset` over the slots allowed by (S) (Select).

**Booking (why no W).** Every selected scalar is at most `A₀ = (√∏_J P)⁻¹ ∏_J M` (`selScalar_norm_le`). The active count is at most `∏_J 128·hi_j·P_j` (`activeSel_card`). Their product is therefore at most `128^{|J|} ∏_J hi_j M_j²` (`activeSel_mass`): the Cauchy–Schwarz count cancels against the renormalization V → V/∏_J P. The only other losses are:
- 256² from the ray table;
- the divisor fibre `#div(r)^{|J|} ≤ max(1,C_δ)^N·N(r)^ε` with δ = ε/(N+1).

So C = 256²·128^N·max(1,C_δ)^N.

**What worked.**
- `row_rays_fourth` (Rays) is stated through `primaryGaussRow`, so unsupported columns need no case split.
- The mask [D⊥n] stays on the left of the identity. (Col) and the squarefree projector `sq(K·D·M)` supply it in `tuple_factor_masked`.
- Under (S), [L ∣ Dn] = [L ∣ n].
- The pushforward counts fibres of (u,k) ↦ d(u)⁴k directly (`selected_fiber_card`: each u_j divides (r)). No grouping by D is needed.
- When the active set is empty (e.g. some hi_j < 0), take rows = ∅.

**Gotchas.**
- `grep -r` does not follow the `hailey_collet_1252270103` and `openai_baseline` symlinks in Submissions; use `grep -R`.
- DecidableEq mismatch on `Fintype.piFinset (·).pools`.
  - Collet's lemmas, stated under `open scoped Classical` without `[DecidableEq κ]`, elaborate a different instance from a `[DecidableEq κ]` binder.
  - Defeq checks then unfold piFinset and hit maxHeartbeats (3 min).
  - Fix: restate with a `[DecidableEq κ]` binder (PoolRows), then transport with `congr; exact Subsingleton.elim _ _` (`coefficient_eq_box`) or with Collet's `source_gauss_dyadic_pool_decEq`.
- In this Mathlib, `Finset.prod_le_prod` is the ordered-monoid version; use `Finset.prod_le_prod₀`. `dif_pos` and `if_pos` are deprecated; use `simp only [h, ↓reduceIte]`.

**Open.**
- (Col) is assumed (collision columns, L3).
- (S') is assumed. Sil's suppliers, i.e. selected primes that divide the seed in nonzero tuples, are not ported.
- Converting slot widths into `∏_J hi_j P_j ≤ W` is left to the ledger (L1, L5).

## Ledger (N4/N5/N7)

**Where.** `lean-env/qrh/Submissions/arvi_mixed_step/Ledger/`, namespace `QRH.MixedStep.Ledger`:
`Nodes.lean` (369 lines) → `FrozenPrice.lean` (581) and `Gaps.lean` (365) → `Geometry.lean` (236).
Each builds with `mk_mixed.sh Ledger/<Name>` in about 25 s. No `sorry`/`axiom`/`native_decide`;
`#print axioms` on every top theorem gives `[propext, Classical.choice, Quot.sound]`.
Interface with exact statements: `research/mixed-step/LEDGER_INTERFACE.md` (v3).

**Decision: rational nodes.** The width grid is made rational at zero cost: every use of the width
delta (`0<δ`, `δ≤1`, `|loss|δ≤e`, `2|loss|δ≤margin`, `FiniteReferenceCells`) is monotone in it, so a
rational `δq ∈ (0, δ]` works (`exists_rat_width_delta`); the grid points `min cap (cross + i·δq)` are
then rational (`activeWidthGrid_rat`). So `b : ℚ`, the node fee is rational, nodes are genuine
Collet `Source`s, and no real-field `RNode` twin is needed.

**Proved (top level).**
- Nodes: `vnode2 n low b δ θ = ⟨B − Lθ, L, cap, q, e, vfee2, fee⟩` at width `b − θ`, with
  `vfee2 = r(1−6qβ) + δ·den3 − qX₀ − q(δ−θ)`; `vnode := vnode2 · · · δ δ`. `vnode2_T` (`t` unchanged),
  `vnode2_A` (`sourceA = r + δ`, needs `sourceDen ≠ 0`), `vnode2_F`, real forms `vnode2R_*`,
  `vfee_top` (`vfee(d) = r`), `vfee2_top`, `vfee_sub`.
- `realGeometryLow_vnode2`: `RealGeometryLow` (Collet's `RealGeometry` minus `denominator_pos`,
  `low_fee_room`, `weak_cap` and the first-layer fields, plus `denominator_ne`) at every rational
  `0 ≤ θ ≤ δ ≤ d`, from `SourceValidC3`. The node quantities are affine in `δ`, and the
  `SourceValid3` gates are their values at `δ = d` with the right slope sign
  (e.g. `B₀F_v − T_v − 4e = gate5 + 6B₀(d−δ) + θ`).
- `sourceDReal_nonneg`: `d ≥ 0` on the cell (`X₀ ≥ Le/Λ₀` past the crossing).
- `raw_low_three_branches_f`, `actual_erasure_three_branch_payment_f`, `actual_low_coordinate_payment_f`,
  `modified_low_coordinate_payment_f` (two parents: label over `s₀ : Input ι₀`, second pair any
  supported `(C, D)`): Collet's LOW payment without the weak cap, keeping both frozen terms; RHS
  `−min a (g + q·min((1−1/λ)f, f − ((BF−t)/λ − hF))) + …`.
- `MixedNodePrice n low b φ` (Collet's `ModifiedNodePrice` with two parents and `φ ≤ f`);
  `mixed_price_of_gain` (price from `13.5e ≤ min(a, frozenGain)`); `mixed_node_price_frozen`
  (every node, `φ = (b−θ) − ε`, `0 ≤ ε ≤ 6e`: the frozen gain is `≥ a − qε` in both cap branches,
  using only `parent_budget_room`, `a_small`, `a_allowance`); `mixed_node_price_top` (`δ = d`,
  `φ = 0`, needs `q(d−θ) ≤ 6e`: fee `r − q(d−θ) ≥ 14e` from gate 8, weak cap from `weakCap3`).
- `phiK`, `phiK_spec` (the design's fee margin restores the fee in the affine branch),
  `pool_only_gate` (§1d, from gate 5 and `d ≥ 0`, for `f ≥ b − s`, `s(Λ₀−1) ≤ 4e`),
  `mixed_node_price_phi` (design's price, with the node weak cap as an explicit hypothesis).
- `gainK_mono_S`, `gainK_mono`; `high3_uniform_reserve` (mixed twin of `high_uniform_reserve`);
  `density3_uniform_margin` (the three sectors of `SourceValidC3`, via Bernstein at the two endpoints
  and affinity in `b`); `node_base_le` (`physicalBase ν (r+δ) (T−θ) ≤ physicalBase ν (r+d) T`, using
  `5 − 6ρ ≥ 0` for `ν ≥ 1/2`, `rho_le`); `node_family_ge` (family gaps exceed the certified ones by
  `θ + (d−δ)(5−6ρ+3ν)`, `θ + 4(d−δ)`, `θ + (d−δ)(5−6ρ+3ν)`); `mixed_uniform_reserve`
  (`ActualGapsK (vnode2 …) low h (b−θ) ν reserve`, one reserve for all `b`, nodes, `ν`) and
  `mixed_uniform_reserve_rm` (`ActualGaps_rm` form). The monotonicity in `T` and `δ` is proved.
- `MixedGeometry`, `mixed_geometry_of_valid3` (from `SourceValid3`, `SourceValid3X`, `ParentGood low`,
  `0 < e`), `main_twins_of_valid3`.

**Disproved / dead ends.**
- *The design's frozen margin `φ_k` alone does not pay.* With `f ≥ φ_k` the affine LOW branch pays,
  but the upper-cap branch needs Collet's weak cap at the node scale `F = 1 − 6r − 6δ`. `weakCap3`
  checks only `F = F'` and the weak cap is decreasing in `F` when `β > cap₀` (always on the chain).
  Counterexample (`research/mixed-step` data, fan step 1, `b = cap = 3/40`): weak cap at `F = 1 − 6r`
  is `−8.0015e−3` (at `F'`: `+4.17e−3`); with `f = φ_0 = 9.57e−3` the upper-branch gain is
  `−4.07e−3 < 13.5e`. The upper branch needs `f ≳ 0.015`. Fix used: price non-top nodes under
  `f ≥ (b−θ) − ε`, which the grid supplies anyway (live width at a non-top node `< g + 2mesh`);
  then neither the weak cap nor the fee identity is used. Chain minimum of the weak cap at
  `F = 1−6r`: `−8.0e−3` (fan 1); at `F'`: `+3.5e−4` (piece 6).
- *`sourceDen ≠ 0` is not implied by `SourceValid3`.* All its gates are polynomial in `qβ`;
  `den3 = den + q > 0` is the only related one. Without it `sourceAReal (vnode …) = (…)/0 = 0`.
  Added by the coordinator as `SourceValid3X := 0 < 6qB₀ − Λ₀` (chain: `den ≤ −0.2095` on the fan;
  `den = 2⁻¹⁵ − q` on family pieces).
- *`ParentGood (vnode …)`* needs `0 < n.B − n.L·θ`; not implied by the gates (needs a lower bound on
  `t`; chain minimum of `B − L·d` is `0.961`). Not needed: Collet's LOW spine reads only `1 < n.L`
  from `ParentGood n` (`hn.2.2.1`); the fork's `NodeGeometry_mx` takes `B ≤ 1`, `1 < L`, `cap < 1`
  (`vnode2_shape`).
- *Uniform `δ_k = k·g` top node* (`δ_K ∈ [d+g, d+2g)`) would need margins for every gate at
  `δ > d`; using the top node `δ = d` exactly (rational, since `b` is) avoids all margins.

**Gotchas.**
- `simp only [..., hbθ]` with `hbθ : ((b−θ:ℚ):ℝ) = b − θ` rewrites inside `sourceTReal (vnode2 …) ↑(b−θ)`
  before the node identities can fire; state the identities also at `(b:ℝ) − θ`.
- `norm_num` on a gate `0 < (sourceDen3 n low:ℝ)` returns the ℚ statement; recast with `exact_mod_cast`.
- In this Mathlib, `add_le_add_right h a : a + b ≤ a + c`; use `add_le_add h le_rfl`.
- linarith treats `q*(1-1/L)*f` and `q*((1-1/L)*f)` as different atoms; supply the `ring` equation.
- `pgrep -f "<file>"` in a wait loop matches the loop's own shell; don't use it.

**Open (for the fork / N3).**
- Choose the grid: nodes `{k·g < d} ∪ {d}`, `θ = max 0 (δ − κ)`, `mesh ≤ κ/2`, `δw + g + κ ≤ ε ≤ 6e`.
- The first-level frozen width bound `f ≥ (b−θ) − ε` at non-top nodes is the fork's (from
  `b − δw ≤ Σw` and transferable width `< δ_{k+1}`).
