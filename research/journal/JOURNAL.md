# Research journal

Running log of hypotheses, probes, proofs and dead ends, newest entry last. Each entry has a date, a question,
what was done, the result with its evidence tag, and the next step.

Tags: **[Lean]** compiled Lean (standard axioms), **[numerical]** computed, **[derived]** our derivation,
**[idea]** not yet examined, **[dead]** ruled out (with the reason).

Bar: every submission must improve on the best merged θ by at least 5e-5. Best merged today: **0.87387234**
(PR #94, ours). Next target: **θ ≤ 0.87382234**.

Lean work for these entries lives in `research/lean/arvi_research/` (mirrored to the Lean environment at
`Submissions/arvi_research/`).

---

## 2026-10-29 · E1. Where the gap can come from (value map + barriers)

**Question.** What can the current return absorb, and which input limits us?

**Result** (`face-region/value/README.md`) [numerical, global check over the whole return grid]:
- The return can absorb −1.8e-4 (whole window). With slot cap 1/10, any strong enough shape stops at −6.3e-5.
- Today's continuous shape: −1.36e-6. Past the floor q = 1/2: −3.1e-6 at best.
- The density step is self-consistent with the shape: at every binding point both binding facets put the witness at
  the parent face's tangency with the envelope [derived], so reading the whole shape adds nothing at first order.
- The slope is pinned by the HIGH count. As a zero-density exponent A: today 2.25 (marked) to 2.37 (unmarked);
  the bar needs A ≲ 2.226; DH (A = 2) gives −6.3e-5 (cap 1/10) to −1.8e-4 (cap 0.12).
- A plain fourth moment with slots at budget 1 crosses the bar at slot cost 2.27 (today 2.57).

**Library-only gains** (proven inputs only): per-class combination with PR 93's joint count (merged upstream)
−1.56e-5; exact-curve retune −1.4e-6; reusing θ ≤ 0.87387 in the native step ≈ −1e-6. Total ≈ −1.9e-5.

**Next.** New math on the HIGH count. Lead: PR 93's selected-norm iteration gives DH-strength counts
(J(ν, ν) = 1 − ν) for rows whose short prime slots carry the zero (slot slope δ > 1/2). Question: can every HIGH
row be shown to carry such slots ("zero-forced marks")? Price first: E2.

## 2026-10-29 · E2. What excluding weakly marked classes is worth

**Question.** In the per-class combination (ours ⊕ PR 93), how much is gained if HIGH rows can be shown to have slot
amplitude class p ≥ p₀, or if PR 93's δ-cutoff could be lowered, or if every class had J = 1 − ν?

**Probe.** `newpowers/combo/perclass2.py` (modes `excl<p0>`, `cut<c>`, `dhall`), the continuum chain of
`newpowers/ta/ode2.py` plus the exact return toolchain (same pipeline as `combo/README.md`).

**Result** [numerical; per-class model of `combo/README.md`, floor 1/2]:

| mode | θ | vs merged 0.87387234 |
|---|---|---|
| ours ⊕ PR 93 per class (cut δ > 1/2) | 0.873855426 | −1.69e-5 |
| + low classes p < 0.25 excluded | 0.873855532 | −1.68e-5 (no help: binding class is above 0.25) |
| + low classes p < 0.4 excluded | 0.873838905 | −3.34e-5 |
| PR 93's cut lowered to δ ≥ 0.45 | 0.873849543 | −2.28e-5 |
| **every class counted at J(ν, ν) = 1 − ν** ("zero-forced marks") | **0.873809315** | **−6.30e-5** (cap-1/10 ceiling; the curve stays at B ≈ 1 down to the floor) |

So only full forcing clears the bar: every HIGH row must carry short prime slots of slope δ = ν (> 1/2), not
just slots slightly above 1/2. With the slot cap raised to 0.12 the same forcing is worth up to −1.8e-4 (E1).

**Next.** E3: the zero-forced marks lemma.

## 2026-10-29 · E3. Zero-forced marks: does a zero force its short prime slots to amplitude ν/2?

**Setting.** Collet's slot of row u is `canonicalPrimeAmplitude` = D^{-1/2} Σ_{P ~ D, P ∈ identity class}
χ̄_u(P) W(N P/D) (N P/D)^{z−1} (`Hecke/PrimeRow.lean:69`), with amplitude log|·|/log D binned and capped at ν/2.
Batches evaluate all their slots at fixed points z_s (`Batch.external`).

**Heuristic [derived].** Mellin inversion plus the explicit formula: the slot is
−(1/h)Σ_ψ ψ̄(C) Σ_ρ m_ρ Ŵ(ρ − w) D^{ρ − 1/2}/log D + small, over the zeros ρ of the twists L(s, ψχ̄_u). The zero
ρ₀ = β₀ + iγ₀ contributes modulus |Ŵ(ν/2 + iΔ)| D^{ν/2}/(h log D), with Δ = γ₀ − Im w. So a slot evaluated within
O(1) of the zero's height has amplitude ν/2 (full class, δ = ν) unless other zeros with Re ρ ≥ β₀ − η and
|Im ρ − γ₀| = O(1) cancel it. Zeros further left are smaller by D^{-η}.

**Cancellation.**
- Zeros of the same L-function near ρ₀ carry nearly equal residues Ŵ(ρ − w), so they add rather than cancel.
- Zeros at moderate separation rotate with log D; a mean square over slot scales D_m (Montgomery–Vaughan) keeps a
  positive fraction of scales large.
- The real risk: near-coincident zeros of *different* twists ψχ̄_u whose class weights ψ̄(C) have opposite phase.
  Such rows need their own count.

**Tools available in this Lean environment.** Mathlib: `BorelCaratheodory`, `JensenFormula`, `Hadamard`,
`PhragmenLindelof`. PrimeNumberTheoremAnd: `StrongPNT.FinalBound`, a general Landau lemma
(f′/f − Σ_{|ρ|≤r} m_ρ/(z−ρ) = O(log B) on a smaller disc), applied to ζ in `LogDerivZetaFinalBound`, with contour
shifts `ShiftTwoBound` etc. The baseline's `HeckeFamily.LFunction` is `latticeL` (theta continuation,
differentiable off {0, 1}).

**Plan.**
- E3a: how PR 93 measures a HIGH row's slot amplitude and selects rows (integration point).
- E3b: math note with the precise lemma.
- E3c: toy numerics on cancellation.
- E3d: Lean, starting with the analytic inputs for latticeL (convexity bound, Euler product at Re s = 3/2, −L′/L series).

**Correction (same day) [derived].** In the density step's HIGH leaf the slots are the *configuration's* slots, at
the configuration's heights v_i, not at the zero's height γ_u. So a zero cannot force them; p is whatever those
slots happen to be. The forcing argument applies to *auxiliary* slots: prime pools evaluated at the zero's own
height window, used only to select rows in the count (PR 93's `SelectedSlotData`), never in the energy's
pointwise bound. If every HIGH row (outside a negligible set) is selected by auxiliary slots of slope ν > 1/2,
PR 93's iteration counts all HIGH rows at J(ν, ν) = 1 − ν. That is the `dhall` scenario (−6.3e-5), i.e. a
density-hypothesis zero count N(σ) ≪ H^{2(1−σ)+ε} for σ > 3/4 for the natural dictionary.

**E3c result: forcing fails against clusters** [numerical toy `zero-forced-marks/forcing_de.py`,
`logs/forcing_de_x*.log`, plus derivation]:
- With a global adversary (extra zeros with real part in [β₀ − 0.06, β₀] and height in [−3, 3]), the forcing
  ratio max over scales/weights of |S|/|c₀| drops to 0.86 (k = 1 extra zero), 0.30 (k = 2) and 0.08 (k = 3), for
  log-scales x ∈ [10, 20].
- Constant-factor losses are harmless asymptotically (x = w log Z → ∞). But a Gaussian-spread cluster kills
  every slot at scales ≥ Z^{w₁} once its height spread σ satisfies σ w₁ log Z ≳ √(2 log k) [derived]. That
  needs only k ≈ C/w₁ off-line zeros (local zero density ≤ C log Z per unit height allows it).
- So rows with a modest off-line cluster can escape forcing, and nothing available counts them below the
  ordinary HIGH count (a k-fold cluster saves only a factor k). **Zero-forced marks ⟺ a multiplicity-sensitive
  zero count with a power saving** — the pair-zero lemma that rounds 3–5 already named (`LOG.md` §597, §1017).
  [dead, pending a pair-zero idea]

**Side fact recorded.** PR 93's selected norm, at its fixed point, bounds the energy of a polynomial of length
Z^a ≤ Z over rows selected by short slots of slope δ > 1/2 by Z^{a} + Z^{1−δ+δa} ≤ 2Z: the *ideal face* on
selected rows (the unselected family only has L + B²) [derived from `SelectedNormIteration.lean`].

## 2026-10-29 · E5. The selected-norm leaf: price slots by their own amplitude

**Idea.** The cube-free native step (Sil, `CubeFree/Step.lean`) deletes slots at the zero-free rate κ = 3/4: its
leaf price is κ·deletionNeed, and the ledger (`LedgerAt`: price ≤ u, with the packed envelope H = 1 + t − 6u)
turns this into the native gates, whose overshoot gate stops the line at Λ = 6κB/(1+κ) = 2.5714B. Split the
leaf's rows by the amplitude of their own retained slots instead:
- rows on which some subset D of the slots (width ≥ smin) has mass ≥ Z^{δ·w(D)}, δ = 0.500001: PR 93's
  `ActualSelectedSlotNorm` (proved: `NaturalUniformNear.natural_selected_cell_norm` →
  `FineCanonicalFromNorm.actual_norm`) bounds the all-source large-sieve constant of these rows by
  C Z^{loss}(X + Y^{1−δ}X^δ), so their energy is ≤ Z^{max(P+s, M)+loss}: price (P + s − M)₊;
- all other rows: every such subset has mass < Z^{δ w(D)}, so deleting the greedy set costs δ·deletionNeed.
New price: max((P + s − M)₊, δ·deletionNeed) + small. The rows with slot amplitude in (1/2, 3/4] move from
deletion at 3/4 to the ideal-level norm bound.

**Ledger [derived].** Selected branch: PC + s − H ≤ (B − 1) − (L − 1)S − cg + 5u + 2tl ≤ u whenever
a ≤ (L − 1)/4 and 4·mesh + 2tl ≤ 1 − B. Deletion branch: Sil's native ledger with κ → K = δ. So the native gates
hold with nativeK → K = 1/2 + η, plus a ≤ (L−1)/4: the overshoot moves from Λ > 2.5714B to Λ > 2B; the
principal gate L > 2 + 4.5a then binds.

**Native line** [numerical, `selected-leaf/native_line.py`]: from PR 76's G(0.99999, 3.72, 0.06), B stays
0.99999 down to L = 2.0054 (principal gate), caps 0.0748 (L = 2.5715), 0.099 (2.1), 0.108 (2.05), 0.138 (end).

**Value** [numerical, global check, `selected-leaf/price_line.py`]:

| count face from the line | θ* | Δθ |
|---|---|---|
| (0.99999, 2.2, cap 0.089) | 0.87386587 | −6.5e-6 |
| (0.99999, 2.1, cap 0.099) | 0.87381889 | **−5.35e-5** (bar) |
| (0.99999, 2.05, cap 0.1085) | 0.87371954 | −1.53e-4 |
| (0.99999, 2.02, cap 0.1205) | 0.87369209 | **−1.80e-4** (the current return's ceiling) |

**Audit so far.**
- The leaf energy (`Moments/InductionEnergy.energy`) is Σ'_z [keep z]·‖positiveSlotRow z‖²·Re Φ(‖z‖²/K), a
  nonnegative row sum, so a row split is legitimate.
- positiveSlotRow is one polynomial Σ_I c(I) χ_{m⁶Vz}(I); `selectedNorm` is the squared operator norm of
  [χ_z(I)]; the primal bound follows via `FiniteSieveOperator.operator_conjTranspose_norm`.
- Our faces and PR 93's norm use the same slot σ = 33/50 (`UniformSource.lean:30`).
- PR 93's own leaf (`FinePointwiseSupplier.priced_source`) already proves a `PricedPackedSource` from the same
  norm, but only through its HIGH count, so the natural-state bridging exists in Lean.
- Still to check in Lean: the coefficient ℓ² mass of the product polynomial (divisor bound), the subset
  selection (2^{|T|} cores, fixed before Z), and that Sil's root-chain provider is generic in the price.
