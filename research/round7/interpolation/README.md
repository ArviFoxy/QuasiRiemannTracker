# Round 7: the interpolation lemma for zero clusters (2026-10-25, negative)

Question: can a single-L-function argument ("interpolation lemma") show that a row whose Möbius
profile dips at the corner `(r*, t*)` while saturating at both ends must have so many zeros near
`Re = a` that such rows are rarer than `U^{R − 7.5e-5}`?

Answer: no. An explicit analytic model meets every pointwise, zero-free and Phragmén–Lindelöf
constraint the count uses and realizes the corner, the dip included. Rigorous ΔR = 0.

**Proved (elementary).**
- Gram identity at reflected points: with `z_j = U^{r(ρ_j − a)}/L′(ρ_j)` and `W ≥ 0`,
  `Σ_i z̄_i F_r(2a − ρ̄_i) = ∫ W(e^w) |g(r + w/log U)|² dw`. A dip at every point of the box is a dip
  of one positive local-energy profile; positivity alone forces nothing.
- Ingham rigidity: a dip on an `r`-interval of length `ℓ` needs zero density at least
  `m*/(2π)·log U = 0.0659 log U` per unit height near `Re = a` (Beurling threshold, spacing
  `15.18/log U`).

**Nearly rigorous (Littlewood + unmarked plain fourth moment, edge terms not handled).** Rows with
zero density ν at `Re ≥ a − o(1)` number at most `U^{1 − 4πδν}`; this beats `U^{R − 7.5e-5}` only for
`ν ≥ 0.06930`, 5.2% above the threshold. At `ν = m*/(2π)` it gives `1 − 2δm* = 0.6236` (the P line
without slots) against `R = 0.6042`; the shortfall is exactly the P line's slot term 0.0194. So a
lossless interpolation (ΔR = −0.059, Δθ ≈ −7.8e-3) holds outside the band `[0.0659, 0.0693)·log U`,
and the model below lies inside it.

**The obstruction: a resonance model.** With `Y = U^{−m₁(s − a)}` and `P | 1 + cY^{k₂}` (`|c| = 1`,
`deg P = d`, `d m₁ = m*`, `k₂ m₁ = t*`): `L ≈ P(Y)`, `L·A = 1 + c U^{−t*(s − a)}` with `A` of length
`r*`. The zeros form a `d`-of-`k₂` sub-lattice with density exactly `m*/(2π)`; with a Beatty choice of
occupied sites every coefficient of `P` and `1/P` has modulus at most 1 (checked for d = 5, 9, 14, 24,
43); `M_r ≡ 0` on `(r*, t*) + t*ℤ`; M is saturated at `r*` and `t*`, S at `m*`. The identity
`r* + m* = t*` is exactly this factorization. The model saturates I, P and L at once, so counting such
rows below R needs a new family or arithmetic input (an atom-level gain), not an interpolation.

Numerics: `pot_lp.py` (potential-theory LP: about 0.023 log U zeros needed without a pointwise
bound), `finiteL.py`, `circle_lp.py` (tight clusters need 1.44 log U zeros, excluded by Jensen + PL;
crystals need rotating residue phases), `resonance_model.py`, `resonance_patterns.py`. Notes:
`notes.txt`.
