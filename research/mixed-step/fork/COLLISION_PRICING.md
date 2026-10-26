# Collision families at the plain node: pricing (Phase 0a, 2026-10-26)

**Result: no new gate.** Take a collision family `(piece k, ray ξ, pattern (Q,σ), colliding product D)`:
- second-layer parent `P_D = (s.restrict J).shortenPlains D₀ D₁`,
- amplitude `a_l·ω(D)`,
- character `twistChar (columnCharacter …) (δ³)`, which is the dictionary at `u₀ = δ³`,
- the plain node's virtual amplitude `amp = a + δ_k`.

Its zero, complement and tail terms are bounded by the plain family's terms for the same labels, times `ω(D)·N(D)^(−c)`
with `c > 0`. The only new ingredient is the regular part: `RegularJointSupplier3` at `P_D` with `u₀ = δ³` (Phases 2
and 3).

## Complement (main exceptional twin)
`eventually_initial_main_joint_mx` (`ForkMx/…/Core/InitialRegularToTruncatedMainExceptional.lean`) has two steps:
1. The family bound `eventually_initial_family_uniform_mx` on the second-layer input gives
   `‖complement‖ ≤ CJ·control²·Z^(small)·Σ_l price(l)`.
2. The first-key price lemma `selected_frozen_first_sum_one_mx` bounds `Σ_l price(l)`. The centered gate `hgate`
   is used only here.

The price is
`price(l) = (amp_l / vol s)·(Kmain_l / lower)·(max 1 (Y₂ / N C_l))^(−0.998)·vol(child_l)·(4·freqRadius Tsec_l)^(1/6) / N(seed_l)`.

Collision family against the plain family, same label `l` (`w = log_Z N(D)`):

| factor | plain | collision | ratio |
|---|---|---|---|
| `amp_l / vol s` | `a_l / V_J` | `a_l ω(D) / (V_J / N D)` | `ω(D)·N(D)` |
| `Kmain_l = firstMainRadius(V, 3amp)` (∝ `V²`, `firstNominalScale ∝ X²`) | `V_J²·…` | `(V_J/N D)²·…` | `N(D)^(−2)` |
| `(max 1 (Y₂/N C))^(−0.998)` | `Y₂` | `Y₂' ≥ Y₂ / N(D)` | `≤ N(D)^(0.998)` |
| `vol(child_l)` (child lengths `X_k / N(A_k)`) | `V_child` | `V_child / N(D)` | `N(D)^(−1)` |
| `Tsec_l = (bᴺ V / N C)² / Kmain_l` | | | `1` |
| `N(seed_l)` | | | `1` |

So `price_D(l) ≤ ω(D)·N(D)^(−1.002)·price(l)`.

The collision complement is therefore paid by the plain price lemma, with the original `Y₂` and the original gate.
That lemma bounds `Σ_l price(l)` for any labels, so it can be called with the plain quantities of the same labels.

**Zero and tail terms** (`eventual_selected_second`).
- zero: `H_l·Λ_l^(1+ε)·T^ε·control²/N(seed)` with `H_l = Kmain_l`, ratio `N(D)^(−2)`.
- tail: `H_l·(vol(child)/T)·Z^(−saving)`, ratio `N(D)^(−2)`.

Both are dominated by the plain terms paid in `Balanced3` (`control_payment_mx` / `mixed_control_payment_mx`).

**Radius.** The collision needs radius `≈ H'·Z^(−5w)`. The family runs at `Kmain(V_D, 3amp) = H'·N(D)^(−2) ≥` that.
`E(R_needed) ≤ E(Kmain)` because the ball energy is monotone in the radius.

## Corner normalization (needed for the family bound and the supplier at `P_D`)
The plain lengths of `P_D` are exact: `X_k' = X_k / N(D_k)` and `Y_k' = Y_k / N(D_k)`.
- `Y` enters the coefficient through `idealRectangle = W₁(·/X₁)W₂(·/X₂) − W₁(·/Y₁)W₂(·/Y₂)`, so it cannot be
  padded.
- `InitialGeometry` needs `Y₂' = Z^(r')`, `Z^(r') ≤ X₁'` and `Z^(r') ≤ X₂'`. The second always holds
  (`Y₂ ≤ X₂`, both sides divided by `N(D₁)`). The first can fail when `X₁ < Y₂·N(D₀)/N(D₁)`, i.e. near the
  corner `x₁ ≈ r` with a side-0 collision.

The fix is to relabel: swap the plains and swap X ↔ Y,
`(X₁'', X₂'', Y₁'', Y₂'') = (Y₂', Y₁', X₂', X₁')`, with the profiles swapped.
- The rectangle changes sign and the plain coordinates are permuted, so energies are equal.
- The reference becomes `r'' = log_Z X₁' ≥ r − w`.
- `long_left` is `X₁' ≤ Y₂'`, the case condition. `long_right` is `X₁' ≤ Y₁'`, true since `Y₁ ≥ X₁`.
- The face is unchanged. `globalFace` only sees `m₁ + m₂ + λ·Σw`, and `Y₁'Y₂' = X₁'X₂'`.

The supplier currently assumes `i₀.p = i.p` (same profiles in both layers). Phase 3 must lift that, or state the
second layer with its own profiles.

## Character and mask
- Character: `NaturalRow η (z·δ³)` = `NaturalRow η z` twisted by `idealRowHom (δ³)` (`rowTwist`, `idealRowHom_argument_mul`).
  The multiplier `u₀` in `jointFirstFrequency` / `effectiveRow` is free in Cycle61.
- Conductor: `twistChar τ A` has conductor at most `rowConductorBound (childCharacter τ 1) fixedBadMask 1 A`, which is
  `N(τ.modulus ⊓ 12)·N(fixedBadMask)·N(72)·N(A)`, far below `Z^5`.
- Mask: `idealRowHom (δ³) P = actualSextic P (δ³ mod P)`, which is 0 for `P ∣ δ`. So tuples not coprime to `D`
  vanish and the mask stays `R₀ · columnIdeal`.
