
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
