# Probe redesign (round 6, 2026-10-25): no free direction

Question: can a different probe (other slot operations, other mark placements, other numerators,
other ways of handling bad rows) lower θ by 1e-5 at fixed sources?

Answer: no. Every deformation tried is either an exact reparametrization of `(x, y, ℓ, h)` or loses
the principal residue. A gain has to come from the inputs the probe consumes: `R`, `C`, the energy
room, or a joint same-zero count.

## Model

- `model69.py`, `genmodel.py`, `spcap2.py`: float model of the final balance on the count envelope
  of `model69` with faces 58/52 of `repeated-marks/cchain_k8b.json` and `s_P = 9/200`. It reproduces
  θ = 0.8747289 at `h = 0.802`, `ℓ = 0.167751`.
- Binding: only the top-row endpoint `d = h` (`new_top`) binds, at `δ = 0.455`, `p = 1/2`,
  `R = 0.60369`, `C = 0.03306`. Interior endpoints have at least 4e-3 slack (`edges_diag.py`).
- With `s_P = 9/200` the slot-capacity cap is about 3e-3 above `C`. With Collet's `s_P = 1/25` the
  optimum sits on the capacity kink `h* = 4ℓ/(B_P − Λ_P s_P)` (`spcap.py`, `spcap2.py`).

The top-row balance is

    log(bad/signal) = a − θ + h(3R/4 − 5/12) + ℓ(1/2 + δp) − δpC/2,   C = (B_P h − 4ℓ)/Λ_P.

The `4ℓ` in `C` is the top-row numerator length `N − M = 2ℓ`, counted in the fourth moment. The
optimal `h` is where the `h`-coefficient of the top row vanishes: `3R/4 − 5/12 = δpB_P/(2Λ_P)`.

## Exchange rates (`sens45.py`)

| lever | dθ per unit |
|---|---|
| shift of `θ_low` | +0.78 |
| uniform shift of the bad-row exponent `E` | +0.222 (`epsE = 1e-4` gives −2.22e-5) |
| count `R` | +0.135 |
| slot capacity `C` | −0.026 |
| energy room `M = 1 − ℓ + ε` | −0.063 (`epsM = 1e-3` gives −6.26e-5) |

For 1e-5: 4.5e-5 off `E`, or 1.3e-5 off `θ_low`, or 1.6e-4 of energy room, or 7.4e-5 off `R`.

## Closed redesigns

1. **General slot operation** (`alpha_family.py`, symbolic). Mark the term
   `I(Xp^{α₁}, Yp^{α₂}, Zp^{α₃})` with a rescaled partner as in (16.4). Then
   `θ_low = [11/12 + ℓ(11α₃ − 14)/12]/(1 + (α₃ − 1)ℓ)` and the top row is
   `a − θ + h(3R/4 − 5/12) + ℓ[1/2 + δp + (α₃ − 1)(a − θ)]`. `α₁, α₂` cancel identically, and `α₃` is
   the reparametrization `Z ↦ Z^{1+(α₃−1)ℓ}`, `ℓ ↦ ℓ/(1 + (α₃ − 1)ℓ)`. So Δθ = 0: the probe is rigid.
2. **Energy room for a low-side loss.** Run past the wall `M + 2z = N + ε`, or freeze a width of
   slots. Room is worth 0.063 per unit. If the low bound pays `λ` per unit, Δθ = (0.78λ − 0.063)ε.
   The known `λ = 1/2` (unmarked over-threshold law `Z^{2M−N}`, MF2.42/43) loses 0.33ε. Break-even
   needs `λ < 0.08`, which is a new marked-energy estimate, not a probe change.
3. **Inverse-type numerator.** The numerator must carry `ζ_K(w)`; its pole at `w = 1` is the
   principal residue. A Möbius weight gives `1/ζ_K(w)` and kills the signal. Pricing the full slot
   product through a second moment raises `E` by `h(1 − R)/4 − δp(ℓ − C/2) = 0.0795 − 0.0344`, so
   Δθ ≈ +0.010 (`hoelder_shapes.py`). Break-even needs `R ≥ 0.83`.
4. **Slot primes outside the theta index.** Gauss-moduli marks are `y → y + ℓ` with no signal
   gain. `m`-side marks move the principal row to `H = dr⁶` (signal divided by `q_d`, `O(1)` in
   total). A separate factor `Σ c_p χ_p^k(m)` twists the signal to `1/L(s, ηχ_p²)`.
5. **Rejected without a model:**
   - two channels (only `u = 1` has the numerator pole and the target denominator);
   - row weights (multiplicative weights are combinations of probes at `X/d`);
   - bad rows other than via Hölder (`min(pointwise, Hölder + credit)` is optimal for the given
     information; the two differ by 6e-4 in `E` at the binding point);
   - `η = 1` decoupling (slot and denominator characters both come from the theta index at `p`);
   - short-interval slots (the saturated factor `P^{a−7/6}` does not depend on the interval);
   - plain or Möbius slots;
   - `p⁴ | A` or cube marks.

The coherence of marks and their cost are one factor: the twisted multiplicativity
`a₀(pn′) = a₀(p)a₀(n′)χ_{n′}(p)⁴` makes the signals add at `H = r⁶`, and the same twist puts `p²`
into the reflection conductor.

Assumptions: exponent-level bookkeeping from (189)–(199), (192), (216)–(223) and NR1–NR6,
logarithms and smooth weights ignored, every moment and large-sieve input fixed as in the sources.
