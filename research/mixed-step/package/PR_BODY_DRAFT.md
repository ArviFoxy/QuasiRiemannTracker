QRH-Result: arvi-mixed-step-20261026
QRH-Bound: 437037/500000
QRH-Decimal: 0.874074

Proves that every Dirichlet L-function L(s, χ), for every positive modulus, is nonzero for Re(s) > 437037/500000 = 0.874074, excluding the principal pole.

For comparison:
- current verified bound: 0.8746075 (PR #76, ours). This submission builds on it and imports its package unchanged.

The gain, −5.3e-4 against PR #76, comes mainly from one new theorem, a **mixed source step**, which puts Sil's fourth-power transfer inside Collet's pool step. Two smaller additions are needed to collect it: a face family whose cap grows along its last piece, and **Lemma W** in the final return, which opens the return's count windows to the faces' proved domain.

## The new theorem: the mixed source step

**The old constraint.** In Collet's NF source step from a face (B₀, Λ₀) to (B, Λ), the LOW price is paid by a pool of fresh sixth-power amplifiers of width a, at rate `1 − 6qB₀/Λ₀`. So a step descends only while `Λ₀ > 6qB₀`.

**The mixed step.** It keeps the pool and also selects a block J of the input's own live slots, of total width δ. Sil's identity `G(D⁴k) = χ(D)²G(k)` moves that block from the column into the row label at the first MAIN layer.
- **No loss from Cauchy–Schwarz.** After Cauchy–Schwarz over the selected products (D, χ, ξ), the count exactly cancels the renormalization `V → V/∏_J P`.
- **The saving.** Booked against the original first-layer target, the residual saves exactly δ. This works because Collet's label side has slope 1 in the volume.
- **The payment.** The LOW payment becomes `a(1 − 6qβ) + δ(1 + q − 6qβ) ≥ qX₀ + r`, with β = B₀/Λ₀. So the step descends whenever `Λ₀ > 6qB₀/(1 + q)`.
- **Special columns.** Collision columns p²m are handled by a mod-p² sublattice lemma. Seed-supplier columns are handled by a supplier split.

**In Lean**, the step is `nf_step3 : NFStep3` (`Source/NFStep3.lean`):
- the transfer at Collet's first MAIN layer: `Transfer/`, `Collision/`, `Residual/`;
- virtual nodes and gates from the certificates: `Ledger/`;
- Collet's LOW/HIGH waist forked with two parents (the original input for the first layer, the residual for the second) and two amplitudes (pool a, transfer a + δ): `ForkMx/`, `Downstream/`.

Collet's main-layer machinery is reused unchanged on the residual.

## The source chain

1. **Start.** Sil's fourth-power face `GlobalSource (99999/100000) (93/25) (3/50)`, imported from PR #76 (`Graph/Start.lean`), at s = 0.016.
2. **Fan.** 46 mixed steps (`Fan/Steps.lean`) take the slope from 3.72 to 2.5220. They are faces through one point on Sil's line and reach the stall line `L/B = 6q/(1+q)`, q = 0.7499.
3. **Face family.** A fine face family follows the stall line as q decreases: 8 polynomial pieces, each with 2^16 grid steps and uniform certificates (`Family/`). The threshold `q = (1 − den)L₀/(6B₀ − L₀)` makes the mixed denominator exactly `2⁻¹⁵` at every step. The selected width `δ = Nd/Dd` makes every gate times `Dd` a polynomial in the grid variable.
4. **Cap ramp.** On the last piece the face cap grows as `cp(y) = 3/40 + y/100` (`Family/Validity3c.lean`: the step certificate with the parent's cap `cp(y − Dy)`; 5 cap guards).
5. **Final faces.** count face (0.9638418, 2.0972320), cap 111411/1310720 ≈ 0.0850; physical face (0.9657869, 2.1306183), cap 527267/6553600 ≈ 0.0805.

## The final return

Collet's return, forked as in PR #76, at the new faces:
- **Switch bound.** The receipt is `dMinus > 3/4`; all of its uses need only `dMinus > 1/2`, so it is stated as that.
- **Lemma W (count windows).** Collet's count certificate uses three conservative windows: the lower plain window `m₋ = 2/5`, the width window `s₊ < cap`, and a fixed natural-tail join at `m_H`. Lemma W opens them to the faces' proved domain and joins the natural tail at the crossover `m_X = (K·B − Λ)/(2(K − Λ))`, where the face width equals the natural width `(1 − 2m)/K`. The plain envelope is then continuous and decreasing, so every plain witness at `m ≥ m*` is counted at the branch's rate. It is an instance of Collet's generic count theorems (`count_from_piecewise_moments`, per-window `mHi`); no new analytic input.
- **Transport.** h = 403/500, with the transport bounds relaxed to `h < 807/1000`, `ell < 1710/10000` (all proofs unchanged).
- **Result.** It closes at 437037/500000 (exact θ* = 0.8740728): 33 row rectangles, 14 admission windows.

## Local checks

(to be filled after the full build: build, axioms, canonical wrapper, metadata check, export size and time)

## Research notes

- The mixed step, the exact model, the formalization plan and the design of the downstream fork: https://github.com/ArviFoxy/QuasiRiemannTracker/tree/ccr-48c53b87-r20g37/research/mixed-step

## Credits

- Sil, for the fourth-power transfer of Gauss sums and the source face this builds on.
- Hailey Collet, for the finite ordinary source moments, the NF theorem and the return framework.
- OpenAI, for the analytic framework and the 7/8 baseline.

Research, Lean development and drafting were substantially AI-assisted with Anthropic's Claude (Claude Code).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
