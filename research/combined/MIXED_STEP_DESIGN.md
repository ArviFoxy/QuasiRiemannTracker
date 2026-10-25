# A mixed fourth/sixth-power source step: design notes (2026-10-25)

Working notes, to be checked against the code map in `../mixed-step/` (subagent, in progress).

## 1. The two mechanisms, side by side

**Collet's step** (paper69 `sources.tex`, Ch. 26 (CA1)–(CA6), Ch. 28 §6 (G9)–(G13)).
- The parent face `G(B₀, Λ₀, h₀)` handles slots up to its capacity `z`.
- Slot width beyond the capacity (the excess `X`) is erased at cost `q` per unit (the
  `q·max{0, b − f − z, …}` term of (G12)).
- The erasure is paid by a separate amplifier pool of width `a` (primes avoiding the slots) through
  the exact identity `F_b(h) = (1/P)Σ_p F_b̃(p⁶h)` (CA5). It saves `a` (density `1/P`) and costs `6a`
  of plain length.
- That length shrinks the parent's capacity by `6a·B₀/Λ₀`, which raises the excess.
- So `a(1 − 6qB₀/Λ₀) ≥ qX`, i.e. `a = qX/(1 − 6qB₀/Λ₀)` (G9).
- The face family saturates the denominator (`den = 2⁻¹⁵`), which gives the flow slope
  `Λ ≈ 6qB`.

**Sil's selection** (`MixedFirstPaidCosts.Gates`).
- Selected slots of log-volume `d` are absorbed by the fourth-power transfer
  `Σ_i b_i χ_{a_i}(D)² G_{a_i}(k) = F(D⁴k)`. Their own twists are what the transfer removes.
- Averaging over the selected family gives the density `W ≥ Z^d`.
- Gates:
  - mixed: `P + 2S + 4d < R`;
  - native: `(3/4)·S < d`, where `S` is the unselected live width;
  - `W ≥ Z^d`.
- So the saving `d` pays the native loss `κS` of the slots left live.

## 2. The analogy

| Sil (initial face) | Collet's step |
|---|---|
| native loss `κ` per unit of live unselected slot width | erasure cost `q` per unit of excess slot width |
| density saving `d` from the selected slot family | density saving `a` from the prime pool |
| selected slots cost `4` in length (dilation `D⁴`) | pool costs `6` in length (dilation `p⁶`) |
| selected slots leave the moment (twists absorbed) | pool primes avoid the slots; the excess stays and is erased |

## 3. A mixed step budget (simplified model)

- Select width `d` out of the excess `X` for the transfer.
- Its effect on the excess: `−d` (it leaves) `+ 4dB₀/Λ₀` (its dilation shrinks the capacity).
- Payment condition, with an optional pool `a`:

  `a(1 − 6qB₀/Λ₀) + d(1 + q − 4qB₀/Λ₀) ≥ qX`, with `0 ≤ d ≤ X`.

- At the pure step's saturation `Λ₀ = 6qB₀` the pool is useless, but the transfer's coefficient is
  `q + 1/3 > 0`. So `d = qX/(q + 1/3) < X` pays the excess, and the step can go beyond the pure
  saturation.
- With all of the excess selected (`d = X`), the condition is `1 + q − 4qB₀/Λ₀ ≥ q`, i.e.
  `Λ₀ ≥ 4qB₀`. That is an exchange rate 4 instead of 6 at the LOW level.

**Caveats.** This model omits:
1. any base cost of live slot width in the step's moment (Sil's `2S`);
2. Sil's declared-width term `−2d`;
3. the transfer's requirements: fifth-power-free moduli, multipliers coprime to the rows, and the
   divisor fibres of `(D, k) ↦ D⁴k`;
4. the HIGH gate, whose binding density `q*` sets the flow.

The earlier float model, `Q_eff = min(6q, (2 + 6q)/(1 + q))`, assumed Sil's base 2 carries over.
It gives θ* ≈ 0.8745898. The simplified model above, with no base cost, would allow `Q_eff → 4q`,
which is much stronger and therefore suspicious. Which one is right depends on how the step's
moment charges live slot width. That accounting is in Collet's (RC3)/(G12) and in our
`Source/` fork, and it is the first thing to settle.

## 4. Feasibility outline (if the accounting holds)

- **Reuse from Sil.**
  - `GaussTransfer` (`fourth_power`, `whole_column`), `PositiveFamily.actual_average`;
  - the selection (`GlobalSlotSelection`, generic in the fraction up to constants);
  - the capacity lemmas (generic in the slope).
- **New.**
  - A step-level moment in which the excess slots are split into selected (transferred) and erased
    parts.
  - The payment lemma replacing (G9)–(G13).
  - New `SourceValid` conjuncts and certificates.
- **Size.** Large, comparable to a substantial part of Sil's development. It is worth it only if
  the corrected model keeps a gain ≥ 1e-5 (the current float model says 1.75e-5).
