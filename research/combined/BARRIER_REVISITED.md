# The "exchange rate 6" barrier, revisited after Sil's fourth-power transfer

Our barrier note (`../barriers/README.md`, atom 2) said:

> Why it does not move: exact invariance cannot use a denser multiplier set. Twisted multipliers
> (`p³`, `p²`) orthogonalize rather than amplify.

Sil's PR 74 moves exactly this exchange rate for the natural source face: slot cost `9/2 = 6κ` →
`93/25 = 2 + 4·(43/100)`, the first improvement of this atom since the baseline. This note says
precisely where the recorded barrier was wrong, where it is still right, and what that means for
our proof.

## 1. Two kinds of amplification

Both use multipliers `D` (products of primes) acting on one index of a bilinear object. They differ
in which index the multiplier enters.

**(G) Gauss-type: the multiplier enters the frequency, the row is the modulus.**
- The object is `P(k) = Σ_i b_i G_{a_i}(k)` with sextic Gauss sums `G_a(k) = Σ_x χ_a(x) e(kx/a)`. The
  rows are the moduli `a_i` and the frequency `k`.
- *Sixth powers:* `G_a(D⁶k) = G_a(k)` for `D` coprime to `a`. This is exact invariance with density
  `X^{1/6}`.
- *Fourth powers (Sil, `GaussTransfer.fourth_power`):* for fifth-power-free `a`,
  `G_a(D⁴k) = χ_a(D)²·G_a(k)`. It is 0 when `gcd(D, a) ≠ 1` (`fifth_free_nonunit_zero`).
  - The phase `χ_a(D)²` depends on the multiplier and the row, **not on the frequency**.
  - Hence (`whole_column`) the row family twisted by these phases is the *same* polynomial at the
    dilated frequency: `Σ_i b_i χ_{a_i}(D)² G_{a_i}(k) = P(D⁴k)`.
  - Mean squares over `(D, k)` of twisted row families therefore transfer to the energy of `P` on
    the dilated set, with divisor-bounded fibres (`PositiveFamily.actual_average`). This is an
    exact energy transfer, not a cancellation.

**(M) Möbius-type: the multiplier enters the argument, the row is the argument.**
- The object is the inverse moment row `M_u(D) = Σ_n μ(n)ν(n) χ_n(u)^ε W(q_n/D)` (OpenAI 7/8,
  "Amplification on sixth-power-free rows", `paper.tex` §12343). The character belongs to the
  summation variable `n`, and the row `u` is its argument.
- *Sixth powers:* `χ_n(ua⁶) = χ_n(u)`, so `M_{ua⁶} = M_u` (plus the exact shared-prime identity).
  These are copies, and they give `e(r) = max(1, (1+5r)/6)`.
- *Fourth powers:* `χ_n(ua⁴) = χ_n(u)·χ_n(a)⁴`. The factor `χ_n(a)⁴` is a cubic character **of the
  summation variable `n`**. So `M_{ua⁴}` is `M_u` twisted by a cubic character mod `a`, i.e. `M_u`
  with one extra slot `a`. It is not a copy.
  - Averaging `|M_{ua⁴}|²` over `a` does not control `|M_u|²`: the twists can kill each row.
  - Here the recorded barrier is right.

## 2. What exactly was wrong

The barrier was argued for (M)-type uses: the long Möbius line, and the 11/12 base `A_{p⁶} = A₁`,
which is also argument-type. It was then stated for the whole exchange rate. In (G)-type uses the
twist is a function of `(D, row)` only. It factors out of every frequency, so it is harmless in any
per-row mean square, and the whole-column identity even turns it into an exact transfer.
- Amplification by `D⁴` instead of `D⁶` means multiplier density `X^{1/4}` instead of `X^{1/6}`.
  The frequency grows by 4 per unit of multiplier width instead of 6.
- Sil also needs the multipliers coprime to the moduli and the moduli fifth-power-free; the
  vanishing lemma handles the rest.

**The ledger** (`MixedLedger`, `GlobalSlotSelection`, `OuterFreshMixedCapacity`).
- In the mixed gate `P + 2S + 4d < R`, unselected live slot width costs 2, and the selected width
  `d` (the slots absorbed into the dilation) costs 4, plus 2 through the declared width.
- So the cost per unit of total width is `2 + 4φ` with `φ = d/(total)`.
- The native gate `κ·(unselected) < d`, with `κ = 3/4 = 2β − 1`, forces `φ > κ/(1+κ) = 3/7`.
  So the cost is above `(2 + 6κ)/(1 + κ) = 26/7`.
- That beats `6κ` exactly when `6κ² > 2`, i.e. `κ > 1/√3 ≈ 0.577`. At κ = 3/4: 3.714 < 4.5.

## 3. The Möbius side, read the other way: absorbing a slot into the row

For (M) the same identity runs backwards. A Möbius row with a cubic slot `χ_n(a)⁴` equals the
unmarked row `M_{ua⁴}`, the analogue of `whole_column`.
- So a slot of width `w` can be traded for row length `4w`.
- In our marked inverse moment the budget is `r + 2z ≤ m`, a slot cost of 2 per unit, which is
  cheaper than 4. So the trade does not help the count (checked: absorbing all slots turns
  `r + 2z` into `r + 4z`).

## 4. Consequences for our proof

| place where the rate 6 binds (`../barriers/README.md`) | type | fourth powers? |
|---|---|---|
| natural source face (`6κ`) | (G) | yes: Sil's 93/25, used in our current submission |
| source step: plain descent `Λ ≈ 6qB`, LOW amplifier `1 − 6qB₀/Λ₀` | (G), to be confirmed | plausible: "mixed step", cost `min(6q, (2+6q)/(1+q))`; float θ* ≈ 0.8745898 (−1.75e-5) |
| long Möbius moment `(1+5r)/6` | (M) | no in direct form (the copies are twisted); slot absorption costs 4 > 2 |
| 11/12 base `A_{p⁶} = A₁` | (M) | no, same reason |

The mixed step is being studied separately (`../mixed-step/`, in progress). Its feasibility depends
on whether the step's LOW amplification is the same Gauss-type family as the natural face. Sil's
modules prove only the initial face, with no LOW parent.

## 5. Open questions this raises

1. **Is there a denser multiplier family? No: 4 is the least exponent (answered).**
   - For `D` coprime to `a`, every exponent works: `G_a(D^e k) = χ̄_a(D^e)G_a(k) = χ_a(D)^{−e}G_a(k)`.
   - But the transfer is useful only when the phase is the slot's own twist, so that the twisted
     row family is the polynomial at the dilated frequency. That twist is the cubic character
     `(P/a)₃ = χ_a(P)²`, as a function of the row `a`.
   - So `−e ≡ 2 (mod 6)`, i.e. `e ≡ 4 (mod 6)`, and the least positive exponent is 4.
   - The fifth-free vanishing (`p^{n+1} | D^e k` for `n < 4`) asks for `e ≥ 4` as well, but the phase
     condition alone already rules out squares and cubes.
   - So the density `X^{1/4}` is optimal among transfers of this kind.
2. **The native gate's 3/4.** In Sil's argument `κ = 3/4` comes from β ≤ 7/8. In a step at density
   `q` the analogue of the gate would use `q`. Whether the step's HIGH gate tolerates the selection
   is the crux for the mixed step.
3. **Sextic large sieve.** Sil also proves an unconditional sextic large sieve (`Sieve*`,
   `OptimalBound`, exponent `7/6 + δ`). That is the formal input our single-mark route to P1
   lacked (`../round11/`). Re-pricing that route with it is a separate, concrete task.
