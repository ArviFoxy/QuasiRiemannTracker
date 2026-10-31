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

## 2026-10-29 · E5b. The sixth-root sum breaks the selected leaf unless the plain sum is dualized

**Problem [derived].** The packed leaf's rows are z = u·r⁶ (u sixth-free). PR 93's selected norm is per root:
for the cores u at root r (norm ≤ Y_r = Z^{M−6ρ}, ρ = log_Z N(r)) it gives X + Y_r^{1−δ}X^δ, X the source
length. The diagonal X does not decay in r and there are ≈ Z^ρ roots of size ρ, so summing over roots gives
Z^{P+s+M/6}: selected price (P + s − 5M/6)₊, not (P + s − M)₊. This is sharp for arbitrary coefficients: one
small core u with |P(u)|² ≈ X is repeated at Z^{M/6} roots. PR 93 only uses the norm for **counts**, which decay
per root ((H/N(r)⁶)^R, R ≥ 1/4, `FineDetectorCount.natural_root_count_of_uniform_free_counts`), so it never
meets this.
- With the diluted price, the selected branch has effective κ = 5/6. That is exactly the baseline unmarked
  count at ν = 1/2 (κ_u = 10/(15 − 6ν) = 5/6): E5 without new input gains nothing.
- Rescue routes considered:
  - R1: dualize the plain sums (I-side Poisson) inside the norm.
  - R2: per-root parent contracts at M − 6ρ (needs punctured or masked contracts down the whole chain).
  - R3: root-capped contracts plus count reassembly at the return.
  - Splitting roots at τ, with 3/4-deletion for big roots, fails: the K-native line needs κ ≤ K on those rows.

**Model [numerical, `selected-leaf/root_ledger.py`].** For each root ρ, the selected exponent is
ρ + max(X_eff, (1−δ)y + δX_eff), with y = M − 6ρ. X_eff is P + s (no structure), or uses a pointwise
Pólya–Vinogradov bound on the plain sums ('pv'), or the plain sums dualized inside the norm,
X_eff = Σ min(x_i, y − x_i) + s ('dual'). The scan covers the whole cube-free side geometry along the
K = 0.501 native line, L = 2.6 → 2.05:

| X_eff | worst price − u | where |
|---|---|---|
| plain | +0.161 | S ≈ 0.004, t = 0, x₁ = x₂ ≈ 0.495 |
| pv | +0.029 (≈ 1/36) | the same |
| dual | ≤ 0 | (deletion branch at equality: the K-native ledger) |

The small-S, t = 0, balanced-plain corner kills every variant except the dual: there P ≈ M, and only a
dual shorter than the row count lets Y_r dominate at the medium roots (y ≈ 0.8P). Dualizing **one** plain sum
(the longer) gives the same exponent: the dilution is (M − 2 max x_i)₊/6 ≤ (M − P)/6.

**R1 sketch [derived; to formalize].** For a sixth-free core u the row character is χ_{D'}·λ·[coprime]. Here
χ_{D'} is primitive mod the squarefree D' (the primes of m⁶Vu with exponent ≢ 0 mod 6), λ is a function
mod 36 (primary normalization) and the coprimality runs over the fixed primes of mV.
- Poisson on O (`Poisson/EisensteinLattice.actual_eisenstein_periodic_poisson`) together with
  g(χ, ξ) = χ̄(ξ)g(χ, 1) and |g(χ, 1)|² = N(D') rewrites the smooth sum of length X as
  (g/N(D'))·Σ_ξ χ̄(ξ)G(|ξ|²/N(D')), whose effective length is N(D')/X.
- Conjugating and using reciprocity puts the dual in the same family idealRowHom(u)(·).
- A dyadic split of N(D') and a Mellin separation on Re s = 0 pull the row dependence out as a unimodular
  factor. PR 93's norm then applies to the sources ξ·I₂·I_slots, with a divisor-bound ℓ² mass.

**E5b continued: R1 in the library [Lean, read].** The I-side dualization R1 needs is in the baseline:
- `actual_original_twisted_reflection` (any non-principal `Character`);
- the full energy engine `UniformOriginalComparison.actual_original_comparison`: reflection, Möbius/Euler
  corrections, separation of the conductor-dependent dual weight, and the discarded part;
- the leaf polynomial as poly·poly·slots of the row character: `positiveSlotRow_eq_product` /
  `positiveSlotRow_eq_polynomials`;
- the radical conductor bound `exists_row_character_radical`.

What is left for R1:
- bound the engine's separated energies E with PR 93's per-root selected norm;
- the root decomposition and the root sum.

Even with the weaker dual length that the engine gives (root primes in the redundant set:
y_dual = M − 5ρ), the ledger scan passes along the whole K = 0.501 line. The worst case is the deletion branch
at equality; the selected branch has margin ≈ 0.003.

**E5 in Lean, first layers [Lean, built; `research/lean/arvi_selected_leaf/`].**
- `Price.lean`: `selExcess`, `selPrice`, `maxPrice`, `e5Price K = max(K·deletionNeed, selExcess)`, all as Sil
  `Price`s.
- `Gates.lean`: `E5Gates` (Sil's native gates with 3/4 → K), `e5Data`, `e5_ledger`, `stepGates_of_e5`.
  The selected branch of the ledger needs nothing beyond the principal gate L > 2 + 9a/2.
- `Step.lean`: `e5_step`, i.e. Sil's generic `cubefree_step` with the generic root-chain provider. The only
  input is the leaf `E5Leaf` (the packed source at `e5Price` from the parent face).
- `Curve.lean`: the line c(Λ) = 1/10 + (3/50)(5143/2000 − Λ), a = 1/250, K = 501/1000, steps ≤ 1e-5, from
  the merged native end (2.5715, 1/10) down to Λ = 101/50 (cap ≈ 0.133). `e5_sources` proves every face
  given `LineLeaf`.
- `R1Statement.lean`: `SelectedRootEnergy K`, the precise analytic input. On rows with
  Z^{K w(D)} ≤ ∏_D ‖normalizedSlot‖², the energy is ≤ Z^{M + selExcess + ε}.

**Value of the line [numerical, `selected-leaf/cap_scan.py`].** Physical face at L = 2.02 or 2.05:
- count face (0.99999, 2.1, cap ≥ 0.12): θ* = 0.87369209 (−1.80e-4, the return's ceiling);
- count face (0.99999, 2.2, cap 0.12): θ* = 0.87377159 (−1.0e-4);
- count face (0.99999, 2.2, cap 0.10): −6.3e-5.

The Lean line reaches cap 0.128 at L = 2.1.

## 2026-10-30 · R1 in Lean, the E5 retune and the fresh look

**R1 [Lean, proved; `research/lean/arvi_selected_leaf/R1/`].** `selectedRootEnergy K : SelectedRootEnergy K` for
`K ∈ [0.500001, 3/4]` (`R1/Cap.lean`), axioms `propext, Classical.choice, Quot.sound`. The analytic input of the selected leaf,
`SelectedRootEnergy K` for every cut `K ∈ [0.500001, 3/4]`, is proved by:
- **Root split.** The heavy-row energy splits exactly over sixth-root classes (`RootSplit`).
- **Direct route per class.** PR 93's selected norm (`ClassBound.direct_class`).
- **Reflected route per class.** The baseline's reflected radial engine with the radical row character, whose
  conductor is ≲ N(u)N(g) = Z^M N(r)^{-5} (`Reflected`, `ReflectedClass`). The separated energies are bounded
  by the same norm.
- **Root sum.** ζ_K(1+η) plus the interpolation min(a,b) ≤ a^{1-θ}b^θ (`RootSum.root_class_sum`).
- **Exponent arithmetic.** Done in `Arith.bracket_bound`.
- **Reductions.** To X₂ ≤ X₁ (`Swap`) and to slot weight ≤ Mcap + 1 (`Peel`), the latter at no exponent cost.

The proof actually gives the slightly stronger price (P + s + (M − 2ℓ₁)₊/5 − M)₊, with ℓ₁ the longer length.

Compile time: the per-base core `Body.cap_body` takes 32 s. An earlier version took 7 min because of
`nlinarith`/`linarith` in a context of ~150 hypotheses and `set` over the large goal. Rule now in memory: small
lemmas, `linarith only`, no `set` on big goals.

**E5 retune [numerical, exact mirror; `research/return-tuning/E5_RETUNE.md`].** θ = 0.87350266 from the
E5 face at Λ = 101/50, against the merged 0.87387234.

**Fresh look [numerical, exact mirror; `research/fresh-look/REPORT.md`].**
- Freeing the natural join and the plain floor of the count return (sMinus 3/100 → 27/1000, mMinus
  377/1000 → 3/10) gives θ = 0.87343238.
- Extending the E5 line to Λ = 401/200 (a = 1/1000) gives 0.87341198.
- The transport floor margin 1/200 → 1/1000 gives 0.87339298 (moderate Lean).
- The final theorem no longer needs the density chain, a large cut of the import closure.

The Lean retune and the line extension are in progress.

## 2026-10-30 · The selected-leaf PR, and where the next 5e-5 must come from

**PR [Lean, standard axioms].** arvi-selected-leaf proves β ≤ 43670599/50000000 = 0.87341198, 4.60e-4 below #94.
The final theorem imports no density chain (4486 modules in the closure). Branch `submission-arvi-selected-leaf` on
the fork; body `selected-leaf/PR_BODY.md`, figure `selected-leaf/faces.png`. Next bar: **θ ≤ 0.87336198**.

**Binding [numerical, exact mirror].**
- The binding point is the newTop edge, uncapped count branch, at δ* ≈ 0.452, p = 1/2.
- A drop of E by ΔE at fixed θ moves θ by about 0.2 ΔE.
- The count v ≈ 0.602 balances three constraints [derived]:
  - inverse 1 − δ(x + (1−x)r);
  - face plain 1 − 2δm − 2δx(B − 2m)/Λ;
  - long 1 − δ + (5/6 − δ)(t − 1).
- So dv = −0.48 Δ_inverse − 0.28 Δ_long − 0.24 Δ_plain, and the bar needs Δv ≈ −0.00042.

**Engineering levers [numerical, exact].** h scan at Λ = 401/200:

| h | θ |
|---|---|
| 0.806 | 0.87339298 |
| 0.810 | 0.87338966 |
| 0.815 | 0.87339900 |

- θ is not monotone in h; past 0.81 another edge binds.
- Going past h = 0.806 needs a larger transport box, and `BoundsN` reaches all 119 ReturnD modules.
- Best ≈ −2.2e-5, or ≈ −2.8e-5 with the 2′ line extension. **[dead]** for the bar on its own.

**Faces are saturated [derived].** The end face dominates every face of both lines: same B, least Λ, largest
cap. So no combination of the proven faces lowers the plain count.

**The square-root barrier, twice [Lean, read].**
- PR 93's selected norm needs δ ≥ 1/2 + gap, in the near estimate (`cell_sector_norm`). The amplification step
  itself (`uniform_slot_crossing`) works for every δ ∈ [0, 1].
- PR 93's joint count needs 2pδ > 1/2, and the binding point has 2pδ = 0.452.
- K < 1/2 would let the selected-leaf line pass Λ = 2B, since the deletion gate is 6KB/(1+K).
  K = 0.48 gives Λ ≈ 1.95, worth ≈ −8e-5 at the Λ sensitivity, if the R1 price allows.

**Long exponent.** The 5/6 is the baseline's sextic amplification (Lemma 17.6, P = (H/U)^{1/6}). No known result
improves it (literature note of 2026-10-24).

**Next.**
- Trace where PR 93's near estimate uses δ > 1/2.
- Price a sub-square-root selected norm.
- Test whether the joint count reaches 2pδ ≈ 0.45.

## 2026-10-30 · The square-root barrier is a fixed point; #96 as a source of ideas

**Sub-square-root selection is dead with this method [Lean, read; trace of JointDetector/].**
- PR 93's selected norm uses δ > 1/2 in exactly one mechanism, the contraction of `squarefree_selected_norm`.
  - Each amplify-and-reflect round maps the exponent of the row term as e ↦ 2δ − 1 + ρe, with ρ = (1 − δ)/δ.
  - The fixed point δ gives Y^(1−δ) L^δ, and the iteration converges to it iff ρ < 1, i.e. iff δ > 1/2
    (`Contraction.ratio_lt_one`, `uniform_depth`, `SelectedContraction`, `SelectedNormIteration`).
- Below 1/2 the fixed point repels. The best bound, with no rounds, is L + Y^((1−δ²)/δ) L^δ, never better than the
  trivial min(LY, L + Y²). So the selected norm does not degrade gracefully below 1/2; it breaks. [dead]
- The joint count J(ν, δ) = 3(1−δ)(1−ν)/(3 − ν − 2δ) is smooth through 1/2. Its cutoff comes from the norm alone.
- Independently, the native step's principal gate L > 2 + 9a/2 caps every face line at Λ ≈ 2. So K < 1/2 would buy
  at most ≈ −7e-6 even with a working norm. [dead]

**Banked levers [numerical, exact].** Line to Λ = 2001/1000 with h = 0.81 (needs the transport box widened, floor
margin < 1/200): θ = 0.87338366, −2.83e-5. Not enough on its own; 2.17e-5 short of the bar.

**Row constants [numerical, exact; `fresh-look/scripts/const_sens.py`].**

| change | Δθ |
|---|---|
| 13/75 − 1/7500 | −2.22e-5 |
| 9/100 + 1e-4 | −1.66e-5 |
| 3/4 − 1e-4 | −1.00e-5 |

**Correction [Lean, read; trace of ReturnD/PhysicalDirect].** 13/75 and 9/100 are not independent knobs. They are r − 1/6
and r − 1/4 with r = 17/50, the baseline's frequency exponent, and they enter only as r(h − d). That vanishes at the binding
edge d = dp = h. The scan above moved them separately, which no proof allows. [dead]

The row is the physical numerator's error exponent against the signal:
- Hölder 4/3, 4 against the diagonal fourth moment gives (3/4)d·count + d/4;
- the face's slot capacity gives −δpC/2;
- the main-slot supremum gives δpℓ;
- slot weights, the label line υ = 1/2 and the Mellin weight give −ℓ/2, −y/2 and δ/2.

So the only live levers at the binding row are the count R, C(dp) through (B, Λ), and h through the floor margin.
One open idea [unverified]: use a lower w-line than υ = 1/2 for the slot rows, as the floor estimate already does. It
needs the row-growth bound below Re w = 1/2.

**PR #96 (liqsweep, paper claim 1049/1250 = 0.8392, no Lean).**
- It keeps OpenAI's continuation criterion with a new probe: a sextic and a cubic Poisson slot with Gauss-sum
  amplifiers, a Hecke target twisted by the angular character, and a copy sieve.
- The 13/15 floor of OpenAI's architecture (Lean, #53) does not apply to it; its own floor in the same exponent model
  is 35/48.
- At 0.8392 every estimate but the square-factor tail closes with large margins (remainder 0.049, non-polar 0.119,
  Poisson rows ≥ 0.039). The tail closes with 4.25e-6.
- The baseline Lean library already has the cubic Kubota machinery (`Eisenstein/`, `kubota_mul`,
  `globalKubotaKernel`).
- Idea: a simplified two-slot probe at a modest target (B ≈ 0.86–0.87) might close with classical inputs only.
  Analyses running: the constraint system with classical inputs, and the Lean inventory.

## 2026-10-30 · What #96 can teach us (T96)

**Question.** Can the two-slot sextic–cubic probe of #96 (paper claim 0.8392, no Lean) give a Lean-verified bound
below 0.87336 with less than the whole paper?

**Constraint system [numerical, re-derived; `pr96/CONSTRAINTS.md`].**
- It reproduces the paper's binding numbers exactly (x* = 940749/4e6, E = 313583/4e6) and the ladder of the paper's
  own ablation script.
- Closing points at the paper's geometry:

  | estimate | closes at |
  |---|---|
  | true-size row | .770 |
  | remainder (D) | .784 |
  | direct row | .799 |
  | Poisson rows | ≈ .800 |
  | e = 1 cells | .804 |
  | copy cells (needs a half-plane ≤ .8924 for four L-functions mod 12; OpenAI's 7/8 suffices) | .822 |
  | square-factor tail | .839, the only one that binds |

- The tail with weaker inputs:

  | inputs | B |
  |---|---|
  | de Faveri's sieve and its chart only | **.8791** |
  | + Voronoi chart dpx | .8656 |
  | + graded inverse theorem GS1 | .8652 |
  | + both | .8547 |
  | + block sieve and r1ext (the paper) | .8392 |

- Without the structural theorems the Patterson part only gives B = 1. These are the non-polar vanishing (via the
  Weyl element of the twisted cubic series), the K-chart, the tree form, cube-full absorption, and the layer and
  non-core calculus. The non-polar vanishing is indispensable.

**Lean inventory [read; `pr96/LEAN_INVENTORY.md`].**
- Available:
  - the criterion with free θ (Collet);
  - sextic and cubic Poisson over Z[ω], symbols, reciprocity and Gauss sums;
  - the cubic, quadratic and hybrid sieves, and a sextic sieve at de Faveri strength (Sil, in #76);
  - partial cubic Kubota theory (residual function automorphy, Patterson's coefficients).
- Missing:
  - the whole probe layer (OpenAI's one-slot analogue is ≈ 264k lines);
  - Hecke characters with ∞-type for the angular twist;
  - the cubic-slot Voronoi split;
  - zero-density estimates.

**Verdict.**
- There is no cheap transplant into our architecture. Our binding sits in the return's count, at the square-root
  barrier and the slot-cost-2 wall, where #96's tools do not act.
- A Lean version of #96 below 0.8733 needs most of its new mathematics (structural machinery plus dpx or GS1) on top
  of a new probe layer: a multi-month formalization, and only if the paper is right.
- Standalone pieces could be formalized as verification of the paper with no θ gain yet: GS1 (the graded inverse
  theorem, a self-contained large-sieve statement) and the non-polar vanishing.

## 2026-10-30 · Sub-square-root selection and higher moments in the return

**Sub-square-root joint count [numerical model; `subroot/word_count.py`].**
- Model: PR 93's three-word minimax (r ≤ 1, m ≤ 1/2, r + m ≥ 1, envelope g(w) − νw) at the binding point, where
  ν = δ_sel = 0.452.
- Count by choice of selected-norm exponent g:

  | g | count |
  |---|---|
  | ideal fixed point (as if PR 93's norm held at δ < 1/2) | **0.548** |
  | one amplification against the true sextic sieve Θ₆ | 0.715 |
  | plain Θ₆ | 0.747 |

  The return's count there is ≈ 0.602–0.607.
- So the ideal norm would gain a lot (Δcount ≈ −0.055). But the selected norm would have to be about 75% of the way
  from Θ₆ to the ideal: for −5e-5, an effective slope ≈ 0.23 at rows of slope 0.452.
- One-step amplification is far too weak, and the iteration diverges below 1/2. What is needed is a large-values
  theorem below the N^(3/4) threshold for sextic families, i.e. Guth–Maynard class.
- **Open problem (new math, long).** A sub-3/4 large-values estimate for the sextic row family strong enough to put
  the joint count below 0.606 at ν = 0.452.

**Label line υ < 1/2 [derived].** Dead. The packet's normalisation Y^(υ−1) and the polynomial's mean square Y^(1−2υ)
cancel exactly.

**Higher moments in the physical row [Lean, read; derived].**
- The count's weights 3/4 and 1/4 come from Hölder (4/3, 4) against Σ|S|⁴|Q|² ≤ U^(1+ε), which is exactly the
  physical face (`InitialAffineAt` with `physicalFace`).
- A sixth-moment face, Σ|S|⁶|Q|² ≤ U^(M6), would give weights 5/6 and 1/6. That wins iff M6 < 3/2 − R/2 ≈ 1.197.
  At M6 = 1.1 it would be worth about −2.6e-3.
- The plain sextic sieve gives M6 ≈ 1.75 (S of length U^0.567). So it needs a new face family for cubes of the row
  polynomial. **Open problem (new math).**

**Smaller checks [numerical / read].**
- Physical cap raised to the face's cap 13399/100000 (capP branch): the exact pipeline fails even at the bottom of the
  search window. The capP guards need the smaller cap. [dead]
- Upstream #97 is our selected-leaf PR, now open.
- Upstream #95 (Bebel, 0.87383570): a large generated set of source chains (restart, curved, adaptive) and six
  return variants for the density-chain architecture. Its κ-feedback is the one our return already has. No ingredient
  adds to the selected-leaf line. [no transplant]

**State of the next bar (θ ≤ 0.87336198).**
- Library and engineering levers top out at −2.83e-5: transport box to h = 0.81 plus the line to 2001/1000.
- The remaining ≥ 2.2e-5 needs new mathematics. Candidates, in order of quantified payoff:
  1. A large-values bound for the sextic row family below the N^(3/4) threshold, strong enough to put PR 93's joint
     count below 0.606 at ν = 0.452 (ideal: 0.548, i.e. up to Δcount −0.055).
  2. The B1/B2 bottlenecks of the baseline's count: no known approach.
  3. A switch to the #96 architecture: multi-month formalization.

**Collet's count combined with PR 93's three words [derived; Lean, read].**
- Collet's fibers (`common_witness_count_bound`) are (r, m) with r + m ≥ t. On each fiber the bounds are: inverse
  marked (r ∈ [23/37, 1)), no-slot inverse (the long exponent for r ≥ 1), and plain via the face (m ∈ [mLo, mHi]).
- The face amplifies the marked slots with effective slope δ/Λ ≈ 0.2254. PR 93's minimax with that slope gives
  J(0.452, 0.2254) = 0.6072, about equal to Collet's count.
- At the binding fiber (r ≈ 0.76, m ≈ 0.38, r + m ≈ 1.14):
  - PR 93's 2m word, face-amplified, is exactly Collet's plain bound;
  - its r word (if the face applied to the inverse piece) equals Collet's inverse bound, both ≈ 0.602;
  - its r + m word gives 0.625.
- Same worst fiber, same value, so the per-fiber minimum gains nothing. [dead]

**Literature [read].**
- Guth–Maynard (arXiv 2405.20552): large values below N^(3/4) in the t-aspect.
- Chen–Gupta–Li (arXiv 2507.08296): the q-aspect for all characters mod q, (qT)^(7(1−σ)/3), via sums over affine maps
  with a GCD twist.
- Neither covers a thin fixed-order family of varying modulus, such as our sextic rows. Carrying the method there is
  open research.

**The three walls at the binding point [derived].**
- With the banked −2.83e-5, the remaining 2.2e-5 needs only ≈ 2% in one parameter: the plain count's effective
  selection slope δ/Λ ≈ 0.2254 → 0.23, i.e. a face with Λ ≈ 1.97 in the plain count.
  - P(m) = 1 − 2δm − 2δx(B − 2m)/Λ, with ∂P/∂(1/Λ) = −0.1085 at m ≈ 0.38.
  - The count moves by 0.24 ΔP, about −3.1e-5 in θ.
- Every way to that 2% meets one of three walls:
  1. **Principal gate.** L > 2 + 9a/2 in the native step caps every face line at Λ ≈ 2 (slot cost 2), and the
     overshoot gate meets it there for K ≥ 1/2.
  2. **Square-root barrier.** Any selected norm, selected face or R1 needs slope > 1/2; the binding slots have
     slope 0.452.
  3. **Sextic amplification.** It fixes the long-word slope at 5/6.
- Plan for the most promising wall (2): `subroot/README.md`. It is a Guth–Maynard-type bound for the thin sextic row
  family. By sextic reciprocity the trace method's kernels become Heath-Brown-type sums over moduli, where #96's
  graded inverse theorem would play the role of additive energy.

## 2026-10-30 · The three-word count is a zero-density calculator; Guth–Maynard buys nothing here

**Upstream [read].** PR #97 passed the hosted verification at 03:47 UTC: status PASS on Lean, nanoda and
con-ron, head 62b12e08 (record `records/97/62b12e08…/arvi-selected-leaf/40993815914-1.json` on `admission-records`).

**Calibration [numerical, model; `subroot/zd_calibration.py`].** PR 93's three-word minimax with t-aspect large-value
inputs (ν = 2σ − 1, words of length N = T^w) reproduces the known zero-density exponents A(σ) = count/(1 − σ):

| input | model | literature |
|---|---|---|
| mean value T + N | 2.3547 at σ = 0.726 | Ingham 3/(2 − σ) = 2.3548 |
| Huxley N²V⁻² + TN⁴V⁻⁶ | 2.1425 at σ = 0.8 | 3/(3σ − 1) = 2.1429 |
| Guth–Maynard N²V⁻² + N^(18/5)V⁻⁴ + TN^(12/5)V⁻⁴ | 2.3075 / 2.2624 / 2.1425 at σ = 0.7 / 0.726 / 0.8 | 15/(3 + 5σ) = 30/13 / 2.2624 / 2.1429 |

**Price of a Guth–Maynard transplant [numerical, model].**
- At the binding point σ = (1 + ν)/2 = 0.726, GM gives count 0.6199 (A = 2.262).
- The return already has 0.6072 (A = 2.215). The bar needs ≤ 0.6063, and DH would give 0.548.
- Word by word at the binding fiber (r ≈ 0.76, m ≈ 0.38, t ≈ 1.14):

  | word | GM | the return |
  |---|---|---|
  | r | 0.617 | inverse 0.602 |
  | 2m | 0.617 | plain 0.602 |
  | r + m | 0.625 | long 0.601 |

  Adding GM's bounds lowers no word there, so the maximum does not move.
- **Why.** The slot amplification lengthens the inverse word to x + (1 − x)r ≈ 0.88. At that length the mean value
  theorem beats GM, which only helps short words.
- **Verdict.** Sub-square-root selection would need large values beyond Guth–Maynard: beyond the state of the art for ζ
  itself at σ = 0.726 with N ≈ T^0.88, where nothing known beats the mean value theorem. Thread SR is **[dead]** as a
  route to the bar. The return's count is already past the ζ analogue because of the prime-slot structure (the
  inverse amplification and the face), not because of large-value technology.

**Wall 1 traced [Lean, read; `CubeFree/RootParameters.lean`, `StepData.lean`].**
- The "principal" gate L > 2 + 9a/2 is not about principal characters. It is the first gap of Sil's centered root
  reference (CF (7.1)–(7.2)), needed only on the high branch P + S + 3u > 5/6.
  - The reference exponent l must satisfy l > (3/2)(P + S + 3u − 5/6), to pay the excess with α = 2/3.
  - It must also satisfy l < (P − S − 1/2)/2, to fit inside the plain part.
  - The gap is 1 − P − 2S − 9u/2. On the face P + LS ≤ B it becomes (1 − B) + (L − 2)S − 9u/2.
- At the binding plain length P = 2m ≈ 0.76, the end face's slot (B − P)/Λ = 0.1197 sits at the gate's (1 − P)/2 = 0.12.
- A saving rate α = 1 instead of 2/3 would turn the gate into P + 3S + 6u < 7/6, which is looser for P > 2/3.
- But a line below Λ ≈ 2 also needs the overshoot gate, K < Λ/(6B − Λ) (≈ 0.489 for Λ = 1.97), and K < 1/2 is
  wall 2. So two new estimates for ≈ −3e-5. [not pursued]

## 2026-10-30 · What each new input is worth; Λ = 2 is the method's limit, not the diagonal

**Worth table [numerical, float model of the newTop row; `frontier/worth.py`, base reproduces 0.87341197].**

| hypothetical input | Δθ |
|---|---|
| long slope 5/6 → 0.8313 / 0.8283 / 0.8226 | −1.0e-5 / −2.5e-5 / **−5.4e-5** |
| long slope → 0.80 / 0.75 | −1.7e-4 / −4.4e-4 |
| face Λ = 2.000 / **1.97** / 1.9 / 1.8 (B = 0.99999, the line's cap) | −7e-6 / **−5.1e-5** / −1.6e-4 / −3.3e-4 |

The face is worth more than the plain-count sensitivity alone suggested (−3.1e-5 for Λ = 1.97): Λ also sets the
physical slot capacity C = (2y − (2 − B)d)/Λ.

**What a face asserts [Lean, read].**
- `globalFace_admissible_iff`: (m₁, m₂, s) is admissible iff s ≤ cap·M and m₁ + m₂ + λs ≤ BM.
- `InitialAffineAt`: the energy Σ'_z ‖positiveSlotRow z‖² Φ(‖z‖²/Z^M) is ≤ C·Z^{M+ε}, where `positiveSlotRow` =
  (plain sum X₁)·(plain sum X₂)·∏ᵢ(prime pool at Z^{wᵢ}) (`InductionEnergy.energy`, `positive_squared_absolute`).
  Each slot enters the row polynomial once.
- So the diagonal limit is λ = 1: total length X₁ + X₂ + Σw ≤ M. That is the ideal face, i.e. PR 93's fixed
  point on selected rows and the outer line P + s ≤ 1 of D8c.

**Correction to "the three walls" [derived].**
- Λ ≈ 2 is the fixed point of the native step's induction, not a diagonal barrier.
  - Overshoot gives Λ > 6KB/(1 + K), and K ≥ 1/2 is the square-root cut of the selected branch.
  - Sil's root reference gives P + 2S + 9u/2 < 1.
- The 6 is the sextic-root cost of selected width ((6B₀ − L₀)u in the deletion need).
- A face proved some other way, at Λ ≈ 1.97 with B ≈ 1 in the plain range 0.76–0.87 and slot range
  0.06–0.12, would clear the bar alone. This is new math, but not a classical-frontier problem like B2.

**GS1 does not supply it [read; #96 paper, `02_ch_arithmetic.tex`, Thm D6SF].**
- The graded inverse theorem bounds the sextic large sieve with family c (N c ≤ A) and columns b (N b ~ B,
  B ≤ A ≤ B²) by the diagonal, plus C Z^ε(B + A^{1/6}B + A^{2/3}B^{1/2} + A(K/K₀)^{1/6}), plus positive block
  operators. The blocks carry the correlation of β with sextic symbols (m₀/n₁)₆ of small modulus.
- For our slot words B = Z^{len}, A = Z^M with len ≈ 0.88M, and the term A^{2/3}B^{1/2} = Z^{(2/3 + len/2)M} already
  exceeds Z^M once len > 2M/3.
- So GS1 cannot give a diagonal face at our lengths. A sub-2 face has to use the smooth structure of the two plain
  factors (Poisson, reflection), as Sil's step does, with a cheaper cost for selected width than 6.

## 2026-10-30 · Faces past Λ = 2: the root reference is the wall, and its 2 = 3/2 + 1/2

**Density-type continuation [numerical, float model; scratch `worth/density_past2.py`].**
- At the end face, dθ/dB = −0.0161 and dθ/dΛ = +0.00144. So trading B for Λ past 2 pays iff the slope
  s0 = dB/dΛ is below **0.089**.
- Examples ignoring the reference gate:

  | s0 | Λ | Δθ |
  |---|---|---|
  | 0.06 | 1.9 | −5.3e-5 |
  | 0.04 | 1.9 | −8.9e-5 |
  | 0.08 | 1.9 | −1.7e-5 |
  | 0.12 | 1.9 | +5.6e-5 |

- #94's density chain did pass Λ = 2 (step 120: (0.9656, 1.9665), cap 0.1) at s0 ≈ 0.08. Density steps have no
  overshoot barrier.

**The reference gate caps every face of Sil's machinery at P + 2S ≤ 1 [Lean, read; derived].**
- The gate is evaluated at the worst slot width S = cap: B < 1 − (2 − Λ)·cap − 9u/2 (`ReferenceAt`, density
  `principal`). Its slope is the cap, 0.12–0.134, above the break-even 0.089.
- Equivalently, the union of admissible faces lies in {P + 2S ≤ 1}. At the count's plain 0.76 that gives S ≤ 0.12,
  and at the physical plain 0.865 it gives S ≤ 0.0675. The end face is already at 0.1197 and 0.0673.
- So neither density steps nor K < 1/2 move the return without a better reference. Wall 1 proper is the reference.

**Anatomy of the 2 (`mixed-step/SIL_LEDGER_TRACE.md`, re-read) [Lean, read].**
- Reference interval (`FourthPower/MixedLedger.lean`):
  - lower = (3/2)(P + s + 7d/3 − 5R/6), from the exceptional component (16KW⁴)^{5/6}/W with saving (2/3)l;
  - upper = (P − s − R/2 − d)/2, from the short reference's conductor R + d;
  - width = R − P − 2s − 4d. So 2 = 3/2 + 1/2 per unit live width (and 4 = 7/2 + 1/2 per unit selected width).
- The rate 2/3 is a worst case, not a parameter. `MixedInnerExceptionalBlock.scalar_common_saving` gives
  (cd)^{−1/3}·min((c/x)^α, (d/x)^α) ≤ x^{−2/3} for any α ≥ 2/3, with equality at c = d = x (both common divisors
  maximal), where α does not enter. The FP range 2/3 ≤ α < 4/5 therefore buys nothing, and Sil's cube-free fork
  takes α_e < 2/3.
- With a saving rate α′ the interval is nonempty iff (5/3 − α′/2)R > (2 − α′)P + (2 + α′)S:

  | α′ | slot at plain 0.76 | slot at plain 0.865 |
  |---|---|---|
  | 2/3 (today) | 0.120 | 0.0675 |
  | 3/4 | 0.124 | 0.0765 |
  | 4/5 | 0.127 | 0.082 |

  The selected cost would also drop (7/2 → (1/α′)(7/3)), which lowers the overshoot fixed point.

**New-math target (precise).** A better bound for the inner exceptional block when the common divisors C, E of the
fourth-power transfer have norm ≈ L/prefixNorm, i.e. an effective saving rate above 2/3 in the worst configuration.
At α′ = 3/4 the physical slot alone moves as far as a face at Λ ≈ 1.76 would. That is a sub-2 face from improving one
lemma of Sil's machinery, with no classical-frontier input. Next: read the FP block (`MixedInnerExceptional*`) and
find which estimate produces (N C·N E)^{−1/3}.

**The other half: the short reference is the optimal sextic large sieve at its diagonal [Lean, read; derived].**
- `MixedFirstReferenceActualCaps.centered_reference_gates` feeds the short-reference energy
  (`MixedFirstActualReference.uniform_actual_reference`: one plain side ≤ Z^l, energy ≤ N(η)K·Z^ε, i.e. diagonal).
  It needs two conditions:
  - (a) l + (R + d)/2 + S ≤ (4/5)R;
  - (b) R + d + 2l − P + S ≤ R/2.
- These are exactly the thresholds where the cross terms of Θ₆(A, B) = A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6} stay
  below A = Z^R: A^{5/6}B^{1/3} ≤ A ⟺ B ≤ A^{1/2}, and A^{1/3}B^{5/6} ≤ A ⟺ B ≤ A^{4/5}. [inferred from the match;
  the finite bound that consumes (a) and (b), `MixedFirstReferenceEnergy` hbound, is not traced yet]
- de Faveri (arXiv 2610.04045, Thm 1.1) proves Θ_n(A, B) ≪ (AB)^ε(A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n}) and
  conjectures it optimal. Optimality is proved for n = 3, 4 by Gauss-sum (metaplectic) biases (Dunn–Radziwiłł;
  de Faveri–Dunn–Hoffstein). So R/2 and 4R/5 are sharp **for general coefficients**.
- If the threshold in (b) were γR, the gate would read P + 2S < (3/4 + γ/2)R. Gate (a) reads P + (5/3)S < (31/30)R
  today, or < (19/18)R with 5/6 in place of 4/5.

  | thresholds | slot at plain 0.76 | slot at plain 0.865 |
  |---|---|---|
  | (1/2, 4/5) today | 0.120 | 0.0675 |
  | (2/3, 5/6), the GS1 terms without blocks | 0.162 | 0.109 |

- #96's graded inverse theorem (Thm D6SF) says the excess over A + B comes only from blocks: correlations of β with
  (m₀/n₁)₆ for N m₀ ≤ K₀. Its non-block terms are A^{1/6}B and A^{2/3}B^{1/2}, i.e. thresholds 5/6 and 2/3.
- The short reference's β is smooth × slot primes (the row's Gauss sum is a unimodular row factor after Poisson,
  as in R1). Its correlation with (m₀/·)₆ is a smooth or prime sum twisted by a small-modulus character, which is
  small unless m₀ is trivial [heuristic].

**Two independent new-math targets now define the face region beyond P + 2S ≤ 1.**
1. The exceptional block's saving rate (2/3, the worst case of maximal common divisors). An agent is tracing its
   origin.
2. A structured sextic large sieve at the short reference: diagonal up to B ≤ A^{2/3} for smooth × prime vectors,
   e.g. GS1 plus a no-block lemma.

GS1 is a paper theorem (#96, not in Lean). Either target also needs the native or density machinery forked to
carry the new gate, which is a large Lean project. Payoff scale: the physical slot 0.0675 → 0.08–0.11, i.e. a
Λ-equivalent of 1.2–1.7, i.e. −1e-4 to −5e-4 if the steps can reach those faces.

**Exceptional block traced (agent report, re-checked where cited) [Lean, read; agent's algebra marked D].**
- **No large sieve is involved.** The sizes are exact finite-field Gauss correlations (baseline `Local`, `Unequal`,
  `Partition`) plus the sextic-remainder row count (θ = 1/6, `ChildRows:67`). The 5/6 is 1 − θ and is not
  tradable. The local saving per prime satisfies `localSaving` ≥ (c + d)/3 (baseline `SecondLedger:36,42`).
- **The 2/3 is sharp for the lemma, not for the method.** The extremal configuration is C = E squarefree with every
  common prime of type c = d = 1. There the chain discards a second forcing factor f^{−1/3}
  (`forcing_third_ge_one`, `MixedInnerExceptionalLedger:141`). Keeping it gives a per-prime saving
  ≥ (3/8)(c + d) [D], with equality only at (2, 2), i.e. rate 3/4. A generalized forcing count for v_P(A) = 2k
  might reach rate α < 4/5 [I].
- **But this is the FP version (PR 76's `FourthPower/`).** The cube-free fork that proves our native line has
  α < 2/3 by structure (`CubeFree/RootParameters.lean`: "cube-free columns forbid FP's α ≥ 2/3"; WP-J principal
  ledger). Target 1 therefore does not apply to the current line. It would apply to an FP-based step, which is weaker
  overall (PR 76 ended near (0.968, 2.91)).

**Past Λ = 2 inside Sil's framework there are two walls, not one [derived].**
- **Native steps.** The overshoot gives Λ > 6KB/(1 + K) = 2.0027B at K = 0.501. The 6 is the sixth-power packing
  cost of selected width ("c = 6 confirmed", `mixed-step/`), independent of the reference. So target 2 alone moves the
  native end only from 2.005 to about 2.003.
- **Density steps.** `face-region/CONTINUUM.md` gives σ = (B − κ)/(Λ − κ) with κ(q) = 4(5 − 3q)/(25 − 18q) and
  q = 0.999Λ/(6B − Λ). At the end face q = 0.501, κ = 0.8753, σ = **0.110**, above the break-even 0.089. So
  density continuation loses even without the reference gate. It would pay iff the HIGH count gave κ > 0.902 at
  q ≈ 1/2.
- **Conclusion.** A face past Λ = 2 needs K < 1/2 or κ(1/2) > 0.902 (both a square-root-barrier problem), and in
  addition a relaxed reference (target 2). A sub-2 face from outside Sil's framework (a new face-proving method)
  remains open and unpriced. [Face thread: double wall within the framework]

## 2026-10-30 · Fresh look (second run): the count is a two-fibre game; the architecture limit is 0.87338197

**Report [numerical, LP model validated against N/J to 8e-10; agent scratch `fresh3/`, re-checked where cited].**
- **The count is a max–min game with two binding fibres.** It is F1 = (r, m) = (0.753, 0.376), where inverse equals
  plain, against the long fibre F2 = (t, 0), at one cutoff t* = 1.129 (δ* = 0.426 at the banked design). The LP dual
  weights are inverse 0.50, plain 0.25 and long 0.26.
- **The binding point is forced.** Edge slacks are oldSmall 0.11, oldSwitch 7.9e-3, newSwitch 1.2e-2 and
  newTop 5.6e-8; the windows lose nothing. Correction to 2026-10-30 "binding": θ*(h) has an interior minimum at
  h ≈ 0.8097 (0.87338197); no other edge binds there.
- **The architecture limit is 0.87338197–0.87338228**, i.e. −2.97e-5. It needs h = 0.8097, the `BoundsN` h-box
  widened, `floor_margin` 1/200 → ≤ 1/1000, and the line to Λ = 2.0001. The bar is still 2.0e-5 below it.
- **Single atoms that would reach the bar from the architecture limit:**

  | atom | now | needed |
  |---|---|---|
  | long slope | 5/6 | 0.83280 (−0.064%) [correction: with the pivot at t = 1 the bar needs 0.8283, λ = 0.1717] |
  | slot cost in the inverse word | 2 | 1.9882 |
  | Λ in the count face alone | 2 | 1.9767 |
  | Λ in the count and physical faces | 2 | ≈ 1.987 |
  | p_max | 1/2 | 0.4934 |
  | fibre margin κ (r + m ≥ t + κ, or r ≤ t − κ) | 0 | 0.00147 |

**Assessment [Lean, read; derived].**
- **p_max = 1/2 is sharp.** The slot amplitude cap q ≤ δ/2 is the zero's own explicit-formula contribution
  D^{a−1/2} (E3). No tightening without more zeros. [dead]
- **Multi-cutoff decoupling (the agent's lead 1) is weak.** Each witness at cutoff t is a pair of saturated blocks
  at one frequency: an inverse (Möbius) block with r ∈ [t − 1/2, t] and a plain block with m ∈ [0, 1/2], r + m ≥ t
  (`Hecke/DetectorRawFiber`, `DetectorSupportedWitness.fiber_lengths`). At two cutoffs the inverse blocks lie on
  different dyadic ranges of the Möbius sum, so nothing forces a correlation. With independent witnesses
  min(V(t₁), V(t₂)) ≥ V(t*). [weak; not pursued]
- **Long slope.** −0.064% is tiny, but the needed gain sits at the length barrier of the long Möbius moment (a power
  beyond H ≈ D for Möbius twisted by sextic symbols). That is classical (twisted Chowla). [hard]
- **The slot cost 2 also appears in the inverse word.** `Moments.inverse_marked` needs r + 2Σw < 1 and
  2r + 8Σw < 3. These come from OpenAI's `InverseMarkedReferenceFiberEnergy.fiber_reference_energy`, not from
  Sil's reference. The ideal cost is 1, and 1.9882 would reach the bar with the banked engineering. **Next: trace
  this 2.**

**The inverse word's slot cost 2 is P1 [Lean, read].**
- The chain is `Moments.inverse_marked` ← `InverseMarkedReferenceFiberEnergy.fiber_reference_energy` ←
  `deleted_source_energy` ← `padded_source_energy` ← `original_source_energy` (`InverseMarkedReferenceSourceEnergy`)
  ← `Inversion/InitialResidualUniformEnergy` ← … ← `InitialRetainedWindow`. The two conditions enter there as
  `CanonicalMargins` (`Descent/Basic.lean`: c ≤ F − M − Q − z and c ≤ 4F − 3M − 6z), consumed by the reflected-short
  estimates (`Inversion/ReflectedShort*`, `ShortCanonicalNormalization`).
- That is OpenAI's marked inverse moment, which `P1_PROBLEM.md` (2026-10-25) states in self-contained form. After
  reflection the columns are cubic theta coefficients times slot sums, c(n) = g̃(n)·Σ_P a(P)N(P)^{−1/2}(n/P)₃‾. A slot
  cost below 2 needs these theta dilates to be nearly orthogonal to the quadratic row space beyond N = K. Rounds 7–9
  reduced this to "block decoupling", which is numerically true but unproven.
- So this atom is P1: Patterson/Kummer structure again.

**Every single atom that would reach the bar is a known hard problem.**

| atom | problem |
|---|---|
| long slope | B2: twisted Chowla for Möbius |
| inverse slot cost | P1: theta coefficients against quadratic rows |
| face Λ | Sil's reference (Θ₆ diagonal at √A, exceptional rate 2/3) together with the square-root cut |
| p_max | sharp (the zero's own explicit-formula term) |
| fibre margin | no correlation is forced between witnesses at different cutoffs |

The common thread is the Gauss-sum (metaplectic) bias that makes the cubic and sextic large sieves sharp for general
vectors. Every route needs a structured statement: these specific vectors (theta dilates, slot words, Möbius) avoid
the bias.

**Literature check, 2026 [read, web search].**
- de Faveri–Dunn–Hoffstein, arXiv 2607.07911 (July 2026): the cubic and quartic large sieves are unconditionally
  non-orthogonal, and the obstruction is the Gauss-sum bias.
- de Faveri, arXiv 2610.04045 (Oct 2026): the optimal Θ_n.
- No result was found on structured vectors (Möbius, prime-supported, theta dilates) beating the bias or the length
  barrier for thin cubic or sextic families.
- So all three remaining targets are open research problems (B2, P1, a structured Θ₆ at the short reference). Of
  these, P1 has the strongest support: block decoupling is numerically true (rounds 7–9).

**State of the next bar.**
- Banked engineering reaches 0.87338228: −7.4e-6 from extending the line to Λ = 2.0001 (no fork), and the rest
  from h = 0.8097 (needs the 119-module ReturnD fork).
- The remaining 2.0e-5 needs one of the hard problems.
- No PR is possible at the 5e-5 rule without new mathematics.

**P1: the route the literature suggests [read; derived].**
- P1 asks for ‖S‖²_op ≤ N^{2−η} for the K × L matrix of twisted theta central values S(k, P) (N = KL). The bound
  ‖S‖⁴_op ≤ Tr((SS*)²) reduces it to a fourth-moment (Schatten-4) asymptotic. With "random" sizes,
  Tr((SS*)²) ≈ KLN²(K + L), which gives ‖S‖²_op ≲ N^{3/2}max(K, L)^{1/2} < N². That is the earlier rounds'
  "SM + MM" (single-mark F_P ≤ N^{2−η}, mixed moments ≤ N^{4−2η}).
- The natural tool for such moments of quadratic twists of θ₃ ⊗ ψ_P is a multiple Dirichlet series in (s, w).
- Recent results:
  - Dunn, arXiv 2403.13151 (ANT 2025): power saving for coefficients of a fixed cubic metaplectic **cusp** form over
    primes, via a bilinear large sieve with kernel ρ_f.
  - arXiv 2607.27131 (2026): power-saving second moments of cubic L-functions over Q(√−3), via multiple Dirichlet
    series.
  - arXiv 2608.25812: twisted modular second moments, via a Kloosterman large sieve.

  None treats quadratic twists of the cubic **theta** series, so P1 stays open. A paper proof would be a research
  project (multiple Dirichlet series for twisted θ₃); a Lean proof is far beyond reach.

**Decision.** No new-math route to the next bar is short. I will bank the engineering limit in Lean as a verified
research result (θ = 0.87338228), so a future lever only needs its own 2.03e-5:
1. the selected-leaf line to Λ = 2.0001 at K = 0.500001 and a = 1e-5;
2. the ReturnD fork with `floor_margin` ≤ 1/1000 and h-box ≥ 0.81;
3. the return retuned at h = 0.8097.

## 2026-10-30 · The engineering limit is banked in Lean: θ = 43669114/50000000 = 0.87338228

**Result [Lean, built; `lean/arvi_bank/`].** `QRH.ArviBank.beta_le_theta : β ≤ 43669114/50000000` and
`dirichlet_nonvanishing_bank` (`L(χ, s) ≠ 0` for Re s > 0.87338228). Both depend only on `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `admit`, `axiom` or `native_decide` in the package.
- Δθ = −2.97e-5 against #97. That is not a PR under the 5e-5 rule. The bar 0.87336198 is 2.03e-5 further down.
- It has three parts:
  1. the selected-leaf line continued to Λ = 20001/10000 (K = 500001/1000000, a = 1/100000, step 1/400000000);
  2. the 119-module transport fork with `BoundsN` h < 81/100 and floor margin 1/1000 (was 806/1000 and 1/200);
  3. the return retuned at c = 6330886/50000000, h = 8097/10000, faces (99999/100000, 20001/10000, 33571/250000)
     and three new windows.
- It is the exact mirror of the float model's architecture limit (0.87338197–0.87338228, "Fresh look (second
  run)"). So the model and the Lean pipeline agree to the last digit at the limit.
- Build: 150 modules, per-module times summing to 17.5 min (slowest: `Tuning.EdgeCertificates` 33 s). On a cold
  container the first build is dominated by I/O (≈ 10 min loading Mathlib's .olean files at 15–20 MB/s).
- One fix was needed: the transport has a second copy of `h_interval` in its `Transport` namespace, which still read
  806/1000.

**What this changes.** Any new lever is now priced from 0.87338228. The single-atom table of the second fresh look
applies as stated: long slope 0.83280 (corrected later: 0.8283 with the pivot at t = 1), inverse slot cost 1.9882, Λ ≈ 1.987 in both faces, p_max 0.4934, fibre
margin 0.00147. Each is a hard problem (B2, P1, Sil's reference plus the square-root cut, sharp, no forced
correlation).

## 2026-10-30 · What a witness says, and why the long word is a deletion amplifier

**The witness [Lean, read; baseline `Hecke/DetectorWitnessRows`, `DetectorSaturation.actual_saturation`].**
- The detector gives one dyadic pair (Möbius block of length U^r, plain block of length U^m) whose product block
  is ≥ 1/polylog at the zero (`exists_dyadic_zero_witness`).
- `simultaneous_upper` bounds each block by the zero-free region to the right of a + 2e (the `zeroMaximum`
  hypothesis): ‖block‖² ≤ U^{(2a−1)·length + ε}. With the product lower bound this forces **both blocks to be
  saturated**: ‖M‖² ≥ U^{(2a−1)r − 2ε} and ‖S‖² ≥ U^{(2a−1)m − 2ε}. It also forces m ≤ 1/2 + 75ε.
- So F2 = (t, 0) only says "a zero exists and the Möbius block at the cutoff is saturated". That is what a pole of
  1/L does at every scale unless nearby zeros cancel it. F1 says, in addition, that a block of the L-function's
  head (length t/3) is saturated, which is a genuine large-value event.
- Closed form at Λ = 2, B = 1, p = 1/2, long slope 5/6: F1(t) = 1 − δ/2 − δt/3 and F2(t) = 1/6 + (5/6 − δ)t, so
  t* = (5 − 3δ)/(5 − 4δ). At δ = 0.426 this gives t* = 1.1293, matching the LP game.

**The long word's 5/6 is a deletion amplifier [Lean, read; `InverseAmplificationFamily`, `RawMoment`].**
- Row u becomes u·π⁶ for primes π of norm ≈ V. Since (n/π)₆⁶ = 1, the character χ_{uπ⁶} is χ_u with the prime π
  deleted (`amplified_prime_mask`). By `prime_column`, M_u(D) = M_{uπ⁶}(D) − χ_u(π)N(π)^{−1/2}M_{uπ⁶}(D/π), and
  the second term cannot carry the spike.
- `RawMoment` is diagonal for all rows of norm ≤ H once H ≥ D^{1+c}. Take H = UV⁶ = D. That gives V copies of each
  row for a family of size V⁶, so Σ_u|M_u(D)|² ≲ U^{1/6}D^{5/6} and the word is (1 + 5r)/6 − δr.
- The loss V⁵ is intrinsic to deletion: the copies χ_{uπ⁶} ≈ χ_u are not mutually orthogonal, so only the dilution
  inside the full family of norm ≤ H makes the bound work.

**Why the known tools do not touch r > 1 [derived].**
- Slots do not help even at the ideal cost 1. A Ramaré-type split μ·ω_V = −(prime slot)·(shorter Möbius) keeps the
  total length at r > 1.
- Dualizing in the rows (reciprocity, then Poisson) turns the off-diagonal into the dual family's off-diagonal
  scaled by U/D, and the N-term reappears. This is P1's "any positivity step re-creates the N term" in the Möbius
  setting. Twisted Chowla (B2) is the honest name for it.
- Pretentiousness (Halász) is blind at polynomial scale. A saturated plain block saves only N^{0.274} over the
  trivial bound, and Halász needs savings below polylog.
- Burgess at m = 0.376 saves at most q^{0.016}. The witness needs N^{0.274}, so the zero-free-region bound is far
  stronger.

## 2026-10-30 · One master parameter: the slot cost 2

**Model [numerical; `frontier/slotcost.py`, the LP game plus the newTop row; it reproduces the Lean bank
0.87338228 exactly].**
- Write c for the price of slot width:
  - in the inverse word: r + cΣw ≤ 1, so I(r) = 1 − δr − (2δp/c)(1 − r);
  - in both faces: Λ = c·(2.0001/2).
- θ* against c, at the banked design:

  | c | all three places | inverse word only |
  |---|---|---|
  | 1.995 | −1.60e-5 | −8.4e-6 |
  | 1.992 | **−2.56e-5** | −1.35e-5 |
  | 1.990 | −3.20e-5 | −1.69e-5 |
  | 1.985 | −4.81e-5 | −2.55e-5 |
  | 1.980 | −6.43e-5 | −3.41e-5 |

- So **c ≈ 1.9936 in all three places reaches the bar**. That is a 0.32% saving on the price of prime slots. The
  inverse word alone needs 1.9882, as in the single-atom table.

**Why one parameter [derived].**
- At F1 the inverse and plain words balance at r = 2m whatever c is. In both words the slot term is the only place
  where prime polynomials meet the sextic large sieve.
- With c = 1 both words become 1 − δ (density hypothesis). The long word then matters only because t* > 1.
- In both places the 2 is the large sieve's √-barrier for prime vectors. Smooth-weighted prime vectors avoid the
  main Gauss-sum bias: Heath-Brown–Patterson give Σ_P g̃(P)W(P/X) ≪ X^{5/6+ε}. But after reflection the slot
  becomes a character sum in the dual variable (P1), and there the N-term returns.
- The literature (2026) has no unconditional refinement. Dunn–Radziwiłł's "cubic large sieve with correction
  term" (Annals 2024) needs GRH, and arXiv 2607.07911 proves only non-orthogonality.

**Per-row levels [Lean, read; `Transport/HighApproximation`].** Each row u carries its own family
(`rayCubeFamily M H hH u`) and its own discretized zero maximum a_u = 51/100 + e·grid(u). The count at depth d is
the number of rows whose rightmost zero lies at (1 + d)/2. So at the binding (d ≈ 0.43–0.45) every counted row's
family is zero-free right of ≈ 0.72. The GRH that Dunn–Radziwiłł need is for other L-functions, the ones in their
Type II/III analysis, so this per-row quasi-GRH does not obviously substitute for it. [open question, not pursued]

## 2026-10-30 · Dunn–Radziwiłł's corrected cubic large sieve as a route to the slot cost

**What the paper proves [read; arXiv 2109.07463v3, Thm 1.4, Props 8.1, 9.1, 9.2, Def 3.1].**
- Assume GRH for Hecke L-functions over Q(ω). Take sequences β in C_η(B, w): squarefree, w-rough, and satisfying
  the cancellation axiom (3.2), i.e. ≪ (B/N(u))^{1/2+η+ε} against every non-trivial twist (b/|b|)^ℓ (k/b)₃ N(b)^{it}.
  For these, Prop 9.2 bounds the cubic large sieve for c_b = β_b g̃(b), minus an explicit theta main term, by
  A^{2/3}B^{5/3}/w^{9/10} + X^ε B^{2+2η} + (AB)^{2/3−ρ}B + X^ε B^{29/12}A^{−1/12} + A^{1/6+ε}B^{5/3},
  provided B² ≫ A^{1+ε}. Here 0 < η ≤ 1/4 and ρ = ρ(ε) < 1/10000.
- Against the diagonal AB (with ‖β‖² ≍ B), the binding term is (AB)^{2/3−ρ}B. The sieve is therefore diagonal up to
  **B ≤ A^{(1+3ρ)/(2−3ρ)} ≈ A^{1/2 + 9ρ/4}**, i.e. it breaks the √-barrier by 9ρ/4.

**Translation into our atom [derived].**
- A diagonal threshold A^{1/2+κ} turns the slot cost 2 into 1/(1/2 + κ) = 2/(1 + 2κ) (heuristic: each word's 2
  is taken to be the √-barrier).
- The master target c = 1.9936 needs κ ≈ 1.6e-3, so **ρ ≳ 7.1e-4**. The proved ρ < 1e-4 gives c ≥ 1.9991, worth at
  most ≈ 3e-6 even if it transferred to all three places.
- Remark 8.1 says ρ(ε) = 11ε/12 − 12ε² is acceptable in the Type-I estimate (Prop 8.1). With ε near 0.038 that is
  ρ ≈ 0.0175 (slot cost ≈ 1.85), but the propositions are stated only for ε < 1/10000. Whether larger ε survives
  the other error terms is unchecked.

**Obstacles, in order.**
1. **GRH.** It enters in Prop 8.1 to impose squarefreeness by Möbius inversion, and in Lemmas 6.1/6.2 to put
   w-rough indicators in C_η. Inside our continuation argument every Hecke L-function over Q(√−3) is zero-free
   right of β ≤ 7/8, which gives Möbius sums ≪ D^{β+ε}.
   - **Checked for Prop 8.1 [derived from the proof, paper-level sketch].** RH is used only on the Möbius sum over c
     ~ C, twisted by (c/|c|)^{3ℓ}, at real part 1/2.
   - Large C (C ≥ (UN(r))^{1/12}): quasi-GRH(7/8) costs C^{3/8}, so U^{1+ε}/C³ becomes U·C^{−21/8}. That is
     U^{0.78}N(r)^{−0.22}, still below U^{5/6−ρ}N(r)^{−1/6−ρ} for ρ ≤ 0.05.
   - Small C: E(C, U) ≪ U^{1/12}N(r)^{7/12} becomes U^{0.115}N(r)^{0.615}. The asymptotic then needs
     U ≥ N(r)^{2.47} instead of N(r)^{7/3}.
   - So **Prop 8.1 survives the bootstrap hypothesis**, and its large-C part even allows ρ up to ≈ 1/20. The small ρ
     in the paper comes from bookkeeping (ε < 1/10000), not from this step.
   - Lemmas 6.1/6.2 are not needed for slot vectors; obstacle 2 replaces them.
2. **The slot sequence is not in C_η with η ≤ 1/4.** For smooth prime slots c_P = W(P), the sequence is
   β = W·g̃‾. Axiom (3.2) then asks for twisted cubic Gauss sums over primes ≪ B^{3/4}. Heath-Brown–Patterson give
   only B^{5/6} (η = 1/3); the untwisted sum is excluded from (3.2) and has Patterson's B^{5/6} main term.
   - **Softening [derived, unchecked].** In Prop 9.2, η appears only in the term X^ε B^{2+2η}. Against the
     diagonal AB that term costs nothing for B ≤ A^{1/(1+2η)}, i.e. B ≤ A^{0.6} at η = 1/3, and our regime is
     B ≈ A^{1/2+κ}. The twists that arise are dual variables with N(k) ≤ B²/A = A^{2κ}, so a polynomial loss in
     N(k) is harmless. If η ≤ 1/4 is only a convenience, Heath-Brown–Patterson suffice and smooth prime vectors
     enter unconditionally.
   - Then, for the **cubic** family, Props 8.1 and 9.2 would give, inside the bootstrap, a diagonal large sieve for
     smooth prime vectors up to A^{1/2 + 9ρ/4}. ρ is limited by Prop 8.1's error terms, which allow up to ≈ 1/20
     (slot cost ≈ 1.8). That is far more than the bar needs, if everything holds. **To verify before any further
     investment:** whether Prop 9.2's proof uses η ≤ 1/4 anywhere else, and how ρ propagates from Prop 8.1 into
     Prop 9.2.
3. **The family is wrong.** Our slot costs live in the sextic large sieve (faces, Sil's √A reference) and in the
   quadratic-row/cubic-theta matrix of P1 (inverse word). A sextic or hybrid analogue of Prop 9.2 is needed; the
   sextic theta function has no explicit coefficients (Kazhdan–Patterson).
4. **Lean.** Metaplectic theta and Kubota series, level-aspect Voronoi for cubic Gauss sums, Heath-Brown's
   recursive sieve. The baseline has only partial cubic Kubota theory.

**Verdict.** This is the first literature-backed mechanism that breaks the √-barrier for theta-uncorrelated
w-rough vectors, which is exactly the master parameter. The proved size (ρ < 1e-4, under GRH, cubic family only)
is about 7× short of the bar. Getting there needs obstacles 1–3 solved on paper, then 4. Recorded as the leading
long-term route to the slot-cost atom; nothing bankable now.

**Sharper reading of D–R §9 [derived from the paper's proofs; paper-level, unchecked against every step].**
- **η ≤ 1/4 is only a convenience.** In Prop 9.2 it is used once ("since η ≤ 1/4 we have AB^{2η} ≤ X", line
  ≈ 3575 of the text), and that holds for every η ≤ 1/2.
- The dual h-sum is bounded through axiom (3.2). That is the X^ε B^{2+2η} term, i.e. B^{8/3} at η = 1/3.
- **ρ is bookkeeping.** The binding cross-term error (AB)^{2/3−ρ}B comes from Prop 8.1's large-C error. The proof
  of Prop 8.1 actually gives U^{3/4}N(r)^{−1/4}, and in the cross term that is **(AB)^{7/12}·B**, i.e. ρ = 1/12.
  The other Type-I error gives B^{29/12}A^{−1/12}.
- **Result for smooth prime vectors c_P = W(P) (β = W·g̃‾, η = 1/3 from Heath-Brown–Patterson), π = γ = 1,
  w ~ B.** Against the diagonal AB:

  | term | diagonal while |
  |---|---|
  | B^{8/3} | B ≤ A^{3/5} |
  | (AB)^{7/12}B | B ≤ A^{5/7} |
  | B^{29/12}A^{−1/12} | B ≤ A^{13/17} |
  | A^{1/6}B^{5/3} | B ≤ A^{5/4} |
  | A^{2/3}B^{5/3}/w^{9/10} | always |
  | theta main term A^{2/3}B^{4/3}/log²B (Patterson's prime bias) | B ≤ A |
  | (1 + B²/A)^{−1000}X² | B ≥ A^{1/2+ε} |

  So **the cubic large sieve is diagonal for smooth prime vectors up to B ≈ A^{3/5}**, against A^{1/2} for general
  vectors.
- Under the bootstrap's quasi-GRH(7/8) instead of RH, the two Type-I errors become (AB)^{0.615}B and
  A^{−0.052}B^{2.448}. Those are diagonal up to A^{0.627} and A^{0.727}, so the A^{3/5} threshold stands.
- If Heath-Brown–Patterson's twisted prime sums lose N(h)^c in the twist, the threshold becomes
  (1 + 2c)/(5/3 + 4c): 0.571 at c = 1/6, still past 1/2.
- In slot-cost terms: cost 1/0.6 ≈ 1.67 for **purely prime, cubic** slots.

**Why it is not yet our atom.**
- (i) The face's vector is plain × prime, with P₁ and P₂ not w-rough, and D–R's framework needs w-rough squarefree
  support. That is the "smooth × prime" sieve of target 1 in `frontier/README.md`.
- (ii) Our families are sextic (faces) and quadratic-row/cubic-theta (P1), not cubic.
- (iii) Checked since: D₁ (9.37) carries only the diagonal X^{1+ε}(1 + (B²/A)^{−1000}) and w-terms; D₂ (9.40)
  carries AB^{2η} + B^{2+2η}; T (9.18) carries A^{1/6}B^{5/3}. No hidden (AB)^{2/3} term. Lemma 9.2 only serves
  Prop 9.1 (squarefree moduli), and Prop 9.2's form (all a) is the one rows need. Still unchecked: the twist
  uniformity in Heath-Brown–Patterson, and whether Prop 8.1's stated U^{5/6−ρ} is weaker than its proof only for
  convenience (the displayed bounds (8.6), (8.9) give U^{3/4}N(r)^{−1/4}).
- (iv) The whole metaplectic stack is absent from Lean.

Still, this is the first concrete evidence that **the √-barrier is not intrinsic for prime vectors**. It turns
target 1 into "D–R's dispersion for (smooth × prime) vectors in the sextic family".

**Sextic extension: literature [read; web].**
- de Faveri, arXiv 2610.04045 (Thm 1.1): Θ_n(A, B) ≪ (AB)^ε(A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n}), expected
  optimal. For n = 6 this is diagonal exactly up to B = A^{1/2}, for general vectors. That is the √-barrier our
  faces inherit.
- Its zero-density corollary gives 1 − δ_6(0.7265) = 0.762 for the sextic family, far above our extremal count
  0.607. Not an input.
- Sextic theta series on the 6-fold cover of GL2 (Brøker–Hoffstein, arXiv 1312.0568): τ(π)², τ(π²) and τ(π⁴) are
  computed, partly only conjecturally. So a sextic level-aspect Voronoi formula, which D–R §5 needs, is not
  available off the shelf.
- Quartic analogue (Lin, arXiv 2306.11875): Gauss sums over primes ≪ X^{5/6+ε} + X^{3/4+ε}|ℓ|^{3/2+ε}, with an
  X^{3/4} bias conjectured. This supports the pattern "bias X^{1/2+1/n}", i.e. X^{2/3} expected for sextic.
- So target 0 needs, at minimum, a sextic or hybrid (quadratic × cubic) Type-I estimate with level uniformity. That
  is open research.

## 2026-10-30 · Fresh look 3 (count game): no new word; the slot cost is a row-inflation rate

**Report [agent; numbers re-checked against the closed form].**
- At δ = 0.426: s₀ = (5 − 3δ)/(15 − 12δ) = 0.37642, t* = 3s₀ = 1.12925, I(2s₀) = P(s₀) = L(3s₀) = 0.62665. Dual
  weights: I 0.494, P 0.247, L 0.258.
- For −1.7e-4 in the count:

  | change | needed |
  |---|---|
  | inverse slot cost alone | Λ_I = 1.9871 |
  | plain face alone | Λ_P = 1.9745 |
  | long slope | 0.83275 |
  | I and P together | 1.9913 |

  These agree with the full-θ* model (`slotcost.py`: 1.9882 for the inverse word, 1.9936 in all three places,
  the physical face included).

**What it adds [derived; the identity checked].**
- **Slot cost = row-inflation rate.** χ_{uP²} = χ_u·(·/P)₃, since (·/P)₆² = (·/P)₃. A cubic slot of width w acts
  like inflating the row family by U^{2w}: rate 2.
- On the same scale:

  | row twist | effect | rate |
  |---|---|---|
  | u ↦ uP⁶ | deletion (the long word) | 6 |
  | u ↦ uP³ | quadratic twist | 3 |
  | u ↦ uP² | cubic twist (the slots) | 2 |
  | u ↦ uP | sextic twist | 1, the ideal |

  So the master parameter is the exchange rate of a Kummer twist, which explains why it is exactly 2 in both the
  inverse and the plain word.
- A rate-6 mixed word on M_r·B_m returns exactly L(r + m), so F1 already sits on the L-line. A mixed word helps
  only at an exchange rate below 6. Enlarging the deletion ball to make room for slots never pays:
  ∂count/∂v = 5 − 6δ/Λ > 0, even at Λ = 1.
- Its "T1": treat the cubic-θ bias as a finite-rank term. Twisted multiplicativity g̃(n)(n/P)₃‾ = g̃(nP)/g̃(P)
  aligns every slot twist with one residual direction (Patterson's residue at 5/6), so subtract it and look for a
  power saving in the remainder. P1 with η ≈ 0.0076 then gives Λ_I ≈ 1.987. This is the same correction-term idea
  as the Dunn–Radziwiłł thread, aimed at P1. [speculative]
- Dead ends it checked:
  - extra saturated heights per row (nothing forces companions; the tails come from Re = 1/2 zeros);
  - a zero-density budget;
  - sharp-cutoff slots;
  - plain blocks (m ≤ 1/(1 + δ) = 0.70, not binding);
  - Zhang/Polymath smooth moduli;
  - Euler-product moments (circular).
- Its "rigid progression of extremal zeros" picture of the adversary is a heuristic model. I have not checked it.

**Verdict.** No new provable word. The fresh look agrees that the cheap lever is the shared rate-2 slot cost
(I and P, 74% of the dual weight), and that L is locked behind twisted Chowla. Both live leads are correction-term
large sieves: Dunn–Radziwiłł for the faces' prime slots (target 0) and a θ-bias subtraction for P1 (T1).

**Consistency with round 6 [read; `probe-redesign/README.md`].**
- Round 6 found that "the coherence of marks and their cost are one factor". The twisted multiplicativity
  a₀(pn′) = a₀(p)a₀(n′)χ_{n′}(p)⁴ makes the signals add, and it is also what puts p² into the reflection
  conductor.
- A rate-1 (sextic) slot "twists the signal to 1/L(s, ηχ_p²)" and kills it (round 6, item 4).
- So the rate-2 slot cost is the price of coherence. The idea "use sextic slots" is closed. [dead]

**Map of walls by Kummer rate [derived].**

| wall | rate | open problem |
|---|---|---|
| inverse word (weight 0.49) | 2, after reflection | P1 (θ-biased columns in the quadratic sieve) |
| plain word / faces (0.25 + physical) | 2, at Sil's √A reference | target 0/1 |
| | 6 (packing), with K ≥ 1/2 (native step's overshoot 6KB/(1 + K) ≥ 2B) | sub-√ selection or a sub-6 packing |
| long word (0.26) | 6 (deletion) | B2, twisted Chowla |

- Rate 6 sits behind both the long word and the faces' second wall. A Möbius-specific amplifier below rate 6 would
  move both. The fresh look argues that rate 6 is the whole Kummer content of copies, so no copy amplifier does
  better.
- **Target 0 alone is worth ≈ 0.** The faces stop at 6KB/(1 + K) → 2B anyway (journal: "target 2 alone moves the
  native end only from 2.005 to about 2.003"). So the cheapest single route to the bar is still P1 (inverse word
  alone at 1.9882).

**Where D–R's GRH really bites [read; de Faveri–Dunn–Hoffstein arXiv 2607.07911 §2.2].**
- In D–R Theorem 1.4 (the *lower* bound), GRH rules out poles of ψ^{(3)}(a, s) coming from zeros of ζ_K(3s − 2)
  when the contour moves to Re s ≥ 5/6 + ε.
- Under the bootstrap's half-plane (zeros of ζ_K only at Re ≤ 7/8), that contour could only reach
  Re s > (2 + 7/8)/3 ≈ 0.958, which would ruin an asymptotic with main term U^{5/6}.
- Our chain (Prop 8.1 → Prop 9.2, upper bounds only) meets ζ_K only through the Möbius sum over c in (8.2), which
  is bounded directly, and through the exact Voronoi formula (Prop 5.3); I found no ψ^{(3)} contour shift in that
  chain. [to double-check line by line before relying on it]
- dFDH's own unconditional input (2.9) is Lindelöf on average in the twist, Σ_{N(a)≤A}|ψ^{(3)}(a, 1 + ε + it)|² ≪
  A^{1+ε}(1 + |t|)^R, via Zagier-regularized Rankin–Selberg. That is a candidate tool for P1's single-mark piece
  (twisted theta central values on average). [not yet examined]

**Housekeeping [derived].** Task 145 (per-class combination with PR 93's joint count, −1.4e-5 to −1.7e-5 against
the old 0.87387 baseline) is obsolete. It acted on the density steps' HIGH count. The banked line's end face is set
by native steps, whose overshoot gate 6KB/(1 + K) at K ≥ 1/2 sits at 2B. In the return's count the joint count
needs 2pδ > 1/2, while the binding has 2pδ ≈ 0.43. No library-only lever remains on top of the bank.

## 2026-10-30 · The plain word as a moment problem: F1 forces |L(1/2+it)| ≥ U^{0.080} on a window

**Derivation [derived; contour shift].**
- The F1 witness has the plain block B_m (length U^m, m = s₀ = t*/3 = 0.3764) saturated at the zero: normalized
  |B| ≥ U^{m(a−1/2)}, i.e. the unnormalized block is ≥ 1 at Re s = a.
- Write B_m(a + it₀) as a Mellin integral of L(a + it₀ + w), with the block's smooth weight transform in w, and
  move to Re = 1/2 (no pole for a non-principal character). This gives
  ∫|L(1/2 + iτ)||Ŵ(1/2 − a + i(τ − t₀))|dτ ≥ U^{m(a−1/2)} = **U^{δm/2} = U^{0.0802}** at δ = 0.426.
- So F1 rows carry a large value of L on the critical line, averaged over an O(1) window. Fresh look 3 reported
  the same picture.
- Moment counting gives R ≤ U^{1 + ε_{2k} − kδm}, where ε_{2k} is the excess of the 2k-th moment
  Σ_u ∫_window |L|^{2k} over U¹:

  | 2k | Lindelöf on average gives | beats the LP count 0.62665 iff ε_{2k} < |
  |---|---|---|
  | 4 | 0.679 | −0.053 (impossible) |
  | 6 | 0.519 | **0.108** |
  | 8 | 0.359 | **0.268** |

  At δ = 0.452 the thresholds are 0.118 and 0.290.

**What we can prove [derived].**
- Each counted row has its own zero-free region right of (1 + δ)/2, so |L(1/2 + it)|² ≤ U^{δ/2+ε}. Combined with
  a diagonal fourth moment (the face with no slots, p₁ = p₂ = 1/2) this gives ε₆ ≤ δ/2 = 0.213 and ε₈ ≤ δ = 0.426.
  Both are about twice what is needed.
- The global bootstrap half-plane (β ≈ 0.873) is weaker: |L|² ≤ U^{β−1/2} = U^{0.373}.
- The face with slots (the P word) is the "fourth moment + amplifier" version, and it is what the count uses.
- So the plain word improves iff there is a **sextic-family sixth moment with excess < 0.108**, or an eighth moment
  with excess < 0.268, at the binding window. Nothing in the literature gives the second moment of the cubic
  family cleanly. [open; recorded as the moment form of the P wall]

**Upstream [read; git].** PR #97 (arvi-selected-leaf, θ = 43670599/50000000 = 0.87341198) is **merged** into
GTimG/QuasiRiemannTracker main as merge commit e02df3d2 (2026-10-30 08:47 +0100). There are no PRs past #97. The
standing record is therefore ours, and the next bar is unchanged at θ ≤ 0.87336198.

**Open question noted [read; `JointDetector/SelectedNormIteration.lean`].**
- PR 93's reflection step (`squarefree_family_all_to_long`) turns an all-source selected-norm bound
  K(Y + B^q Y^δ) into a long-source exponent q + 2δ − 1. The contraction (1 − δ)/δ < 1 then needs δ > 1/2.
- Heuristically, amplifying by a slot helps only while the amplified length stays in the sieve's diagonal regime,
  and for general sextic vectors that regime stops at √U. If the 1/2 in the contraction is that √-threshold, a
  sieve past √ for the amplified vector would also lower the faces' second wall (K ≥ 1/2).
- But the amplified vector is F·S (general × prime), not purely prime, so DR_PRIME_SIEVE does not apply as stated.
  [hypothesis, unpriced]

## 2026-10-30 · #96's K-chart is the nearest tool to P1 [read; #96 paper ch. 6 §"The K-chart", Thm dpx, Prop dpx]

- **#96 already does "subtract the bias".** Its cubic slot vector is split exactly, by a Voronoi formula, as
  u₂ = u_P + u_D: the Patterson part carries the residues (the θ-bias) and the remainder goes to the sextic and
  cubic sieves. The Patterson part's square-factor tail is #96's binding estimate.
- **The K-chart (its "dpx", worth 0.8791 → 0.8656 in #96's own tail model).** One Cauchy–Schwarz between two
  factors:
  1. the slot factor on the sparse family {e²a′}, by Poisson in a′ followed by "twisted Lindelöf on average" for
     Hecke L-values, Σ_{N(ν)≤H}|L(½ + ε + it, ψξ_ν)|² ≪ Δ₆(H, (HE)^{1/2}) (approximate functional equation plus de
     Faveri's sixth-order sieve);
  2. the K-factor: the functional equation of the cubic Kubota series at index e² turns a quadratically twisted
     cubic Kubota sum into one of dual length R_e = H′/E², and then the quadratic large sieve (Goldmakher–Louvel)
     applies.
- **Relevance.** P1's columns g̃(n)(n/P)₃‾ against rows χ_k are quadratic twists of cubic Kubota sums at index P.
  The K-chart's second factor is exactly the move P1 lacks: shorten the long n-sum (N = KL > K) by the Kubota
  functional equation before using the quadratic sieve. Passed to the P1 deep-dive agent to evaluate.
- Caveat: #96 is an unrefereed preprint, and the K-chart lives in its two-slot architecture.

## 2026-10-30 · P1 deep-dive: no bias to subtract; P1 reduces to one cross-correlation estimate (X)

**Report [agent; key steps re-checked; exponents in powers of Z: K = 0.742, N = 0.871, L = 0.129].**
- **The θ-bias subtraction (fresh look 3's T1) finds nothing to subtract** [standard]. For squarefree k ≠ 1,
  S(k, P) = Σ_n g̃(P; n)χ_k(n)W is the index-P Kubota series twisted by a sextic ξ with ξ³ = χ_k ≠ 1. That series is
  entire (Patterson's cube criterion; also #96 Thm N1(a)). So no finite-rank polar term exists in rows k ≠ 1.
- **Caveats on the P1 statement.**
  - Square rows k = j² carry the Kubota pole. They contribute K^{1/2}N^{5/3}|Ξ|², where Ξ = Σ_P a(P)N(P)^{−2/3}g̃(P)^∓.
    That exceeds N² unless the slot prime sum Σ_P W₁ψg̃^∓ = L^s has s ≤ 0.353, and Heath-Brown gives only s ≤ 5/6.
    **So P1 must be stated for squarefree rows**, with squares handled separately; they are only √K rows.
  - After μ² = Σ_{d²|k}μ(d) and Poisson in k, the h = □ "dual diagonal" has size ≈ √K|Σ_n c(n)e_n|²M_K. The bootstrap
    gives M_K ≪ K^{−(1−β₀)/2} = K^{−1/16}. With biased slot weights (ψ cubic or trivial, s = 5/6) this term sits
    Z^{0.077} above target. Since the total is ≤ N^{2+ε}, the h ≠ □ terms must cancel it. It is a Poisson artefact
    that positivity cannot see.
- **Reduction (Schur) [proved].** P1 for smooth α follows from
  **(X)**: |Σ_k μ²(k)W(N(k)/K) S(k, P)·S(k, P′)‾| ≤ K·N·L^{−η} for P ≠ P′ (on average over P′).
  - The diagonal is ≈ KN.
  - The trivial bound (Cauchy–Schwarz plus Lindelöf on average) is KN.
  - The heuristic truth is K^{1/2}N.
  - The needed saving is only L^η = Z^{0.001}.
  - (X) is a twisted second-moment cross-correlation of two different index-P Kubota series over squarefree
    quadratic twists, at the critical point and in the unbalanced range N = KL > K. Status: unknown, plausible by
    random-matrix and toy numerics, not false.
- **Dunn–Radziwiłł transposed** (rows = slots P, β = Σ b_kχ_k): B/A = K, outside DR's improved range
  B ≤ A^{5/7}. [proved]
- **#96's K-chart.**
  - It is Frobenius-type: one functional equation per (k, P), then Cauchy–Schwarz jointly. For the slot-summed P1
    it gives ‖S‖_F² ≲ N^{2+ε}. That improves the rigorous Frobenius bound from L·N² to N², but it does not beat the
    N-term.
  - For a single mark, Thm N1 (index conductor N(m)¹, twist conductor N(a)²) shortens the n-sum from N to K. The
    quadratic sieve then gives F_P ≲ KN, at an extra K^{0.083} cost for the Möbius contour shift at β₀ = 7/8.
- **Conductor check (mine).**
  - The agent saw a conflict between N1's index conductor N(m)¹ and DR Prop 5.3's dual length N(r)²/X.
  - DR's dual coefficients are supported on r | ν, with φ(r) weights ((5.75)–(5.76)). Their effective length is
    therefore N(r)/X, which agrees with N1.
  - So I read no error in #96 here, but this is unverified numerically: the agent's toy test up to N = 3000 was
    inconclusive.

**Verdict.** P1 is now pinned to one estimate, (X): cross-moments of two different index-P Kubota series over
squarefree quadratic twists, needing only a Z^{0.001} saving over the trivial bound. Every tool in hand (polar
subtraction, D–R's corrected sieve, the K-chart, the bootstrap) misses it. It is the cleanest open target in the
whole frontier.

**(X), literature and first attempts [web; derived].**
- An extended search (2025–2026) finds nothing on mixed or second moments of quadratic twists of the cubic theta
  function or the Kubota series. The nearest are quadratic-character theta-function moments (arXiv 2503.05269) and
  quadratic twists of modular L-functions (arXiv 2208.07343).
- Burgess on the k-sum. Each (n, m) term Σ_{k≤K}(k/nm)₂ (modulus nm ≍ N² = Z^{1.742}, length K = Z^{0.742}) has a
  Burgess saving of Z^{0.044}. Summing |·| over the N² pairs loses Z^{0.83}, so cancellation in (n, m) is
  indispensable.
- Quadratic Poisson is an involution between the k-side (length K) and the h-side (length N²/K). Both sides'
  diagonals are small (KL and NL, because (n/PP′)₃ cancels), and the off-diagonal maps to itself. So (X) is a
  genuinely self-dual bilinear problem in two index-twisted cubic theta sequences. [open]

## 2026-10-30 · B2 pinned: a Möbius sieve past the family size with saving (D/U)^λ, λ ≥ 0.1717

**Derivation [derived; numerical check inline].**
- The long word is count ≤ E(r) − δr, where U^{E(r)} bounds the Möbius mean value Σ_{N(u)≤U}|M_u(D)|²
  (normalized, D = U^r).
- The sixth-power deletion amplifier gives E = (1 + 5r)/6, i.e. U·(D/U)^{5/6}. That is a saving λ = 1/6 against the
  large sieve's N-term D.
- Suppose a Möbius sieve past the family size saves (D/H)^λ over the N-term on a family of size H < D. Amplify to
  H = U^h. The exponent is (5h + 1)/6 + (r − h)(1 − λ), with derivative λ − 1/6 in h. So:
  - λ < 1/6: amplify fully (h = r), which gives back deletion;
  - λ > 1/6: do not amplify at all (h = 1), which gives E = 1 + (r − 1)(1 − λ).
  The two mechanisms never combine.
- The bar needs the envelope at r = t* = 1.129 lowered by 6.5e-4, i.e. **λ ≥ 0.1717** against deletion's 0.1667.
- Equivalent statement (B2): Σ_{N(u)≤U}|Σ_{n~D} μ(n)χ_u(n)|² ≪ U·(D/U)^{0.8283}·D (unnormalized), for D = U^{1.129}.
  That is a 3% better exponent than deletion.
- Known methods:
  - The thin sextic family (U rows) cannot borrow Barban–Davenport–Halberstam: embedding it in all Hecke characters
    mod u ≤ U (size U², diagonal for D ≤ U²) loses the factor U.
  - Deletion is the full Kummer content (fresh look 3).
  - So λ > 1/6 needs Möbius cancellation against the dual sextic sums: twisted Chowla. [open]

**(X) after the Kubota functional equation [derived].**
- The functional equation at index P shortens the n-sum from N to K. The root number ε(k, P) is a sextic character
  of k mod P, so the slot sum becomes A*(k, n′) = Σ_P α_P (k/P)₆ (P/n′)₃‾. That is a prime sum of a Hecke character
  of conductor ≲ K⁴, so the bootstrap gives |A*| ≪ L^{β₀−1/2} = L^{3/8} pointwise, against the trivial L^{1/2}.
- But A* depends on k, which blocks the quadratic sieve. Cauchy–Schwarz over P returns to Σ_P Σ_k|Y_P(k)|² ≈ LK²,
  i.e. N² after renormalizing. The pointwise saving is in sup norm, and the sieve needs L², where the sup bound is
  worse than the average by L^{3/4}.
- The cross form C*(P, P′) = Σ_k (k/PP′⁵)₆ Y_P(k)Ȳ_{P′}(k). Its inner k-sums have modulus ≈ L²K² and length K.
  - Burgess saves Z^{0.044} per (n′, m′) pair, but the triangle inequality over K² pairs loses more.
  - Poisson at modulus L²·n′m′ produces the same form over h ≲ L²K.
  So the bootstrap's pointwise prime-sum savings and the large sieve's averaging do not combine here. [dead end
  recorded]

## 2026-10-30 · Upstream PR #98 takes the engineering limit (θ = 0.8733821435)

**What it is [read; git, `upstream/pr98`, head 72682aa1].**
- Author: Joseph Bebel (author of PR 93). Opened after #97 merged.
- Theorem: all-moduli Dirichlet nonvanishing for Re s > 1746764287/2000000000 = **0.8733821435**, i.e. −2.98e-5
  against #97 and 1.37e-7 below our bank (0.87338228).
- Method: the same three moves as our bank, done independently and slightly further.
  - "Generic native-line induction" on #97's selected-leaf source: the faces end at Λ = 200001/100000 = 2.00001
    (ours: 2.0001).
  - The physical-return geometry widened, as in our ReturnD fork.
  - Five windows instead of our three:
    `[C 9/25..49/100 p≥0], [C 9/25..57/100 p≥3/8], [capP 1/16384..3273/8192 p≥3/8], [capP 9/32..3/8 p≥5/16],
    [C 45/128..3/8 p≥15/32]`.
  - Constants: h = 0.809686724723; count face (0.99999, 2.00001, cap 0.1342894); physical face (0.99999, 2.00001,
    cap 3/25).
- Status: open upstream, not merged; upstream main is still e02df3d2 (#97).

**Consequences.**
- Our bank is superseded, by 1.4e-7. It stays as an independent check that the engineering limit is ≈ −2.98e-5
  (our float estimate of the limit was 0.87338197).
- If #98 merges, the 5e-5 rule moves the bar to θ ≤ **0.8733321435**. Then the whole 5e-5 must come from new math
  on top of the engineering limit, for example (from `frontier/slotcost.py`):
  - slot cost ≈ 1.984 in all three places, or
  - long slope ≈ 0.8226.
- Until it merges, the bar measured from #97 stays at 0.87336198.

## 2026-10-30 · The K ≥ 1/2 wall is a closure property of amplify-and-reflect [Lean, built]

**Question.** Is the faces' second wall (selected leaf only at K > 1/2) an artefact of PR 93's weak start L + B²?
The baseline also has the optimal sextic sieve Θ₆ (Sil's `SieveOptimal`, de Faveri's Θ_n).

**Numerics [numerical; `$SCRATCH/kwall/closure.py`].** Closure of the three rules on a grid in log_B scale. A is
amplification at slope δ; R is reflection n(x) ≤ max(x, x − 1 + n(2 − x)).

| δ | start | n(0) | n(1) |
|---|---|---|---|
| 0.45 | L + B² | 1.100 | 1.550 |
| 0.45 | Θ₆ | 0.717 | 1.167 |
| 0.495 | L + B² | 1.010 | 1.505 |
| 0.495 | Θ₆ | 0.672 | 1.167 |
| 0.51 | either | 0.4905 | 1.0005 |

The fixed point is n(0) = 1 − δ, n(1) = 1. Θ₆ cuts the loss below 1/2 from a full factor B to B^{1/6}, but it
does not remove it. The jump at δ = 1/2 stays.

**Theorem [Lean, built; `lean/arvi_kwall/Closure.lean`].**
- For 1/3 ≤ δ < 1/2, the function n*(x) = max(x, 7/6 + δ(x − 1) + (1 − 2δ)·max(x − 1, 0)) obeys all three rules
  and has n*(1) = 7/6 (`nstar_rules`).
- Hence no proof from the rules gets below B^{7/6} at the balanced point (`no_balanced_bound_below`). The fixed
  point is not derivable (`fixed_point_not_derivable`).
- Axioms: propext, Classical.choice, Quot.sound.

**Mechanism.** One amplify–reflect cycle 1 → y → 2 − y → 1 changes the balanced-point bound by (1 − 2δ)(y − 1).
The two exchange rates are intrinsic:
- amplification gains δ per unit of width, by the definition of selection;
- reflection costs 1 per unit, the √(length ratio) of Poisson.

**Consequence.** The K-wall needs a direct estimate on the selected rows at L = B. In operator-norm form:
‖(χ_z(I))_{z∈W, N(I)≤B}‖² ≤ B^{1+o(1)} for W the large-value set of a prime polynomial at slope δ < 1/2. That is
Guth–Maynard's problem (the top singular value of the restricted matrix) for the thin sextic family, exactly at
the self-dual point of the reflection. [barrier proved; target restated]

**Why Guth–Maynard does not transfer as is [read; GM arXiv 2405.20552 §2, §4–7; derived].**
- GM bound the top singular value of M_{t,n} = n^{it} on a large-value set through tr((M*M)³). They then apply
  Poisson to the kernel Σ_{n~N} n^{i(t−t′)}. That kernel has conductor |t − t′| ≤ T, so near GM's critical length
  N = T^{1/(1+δ)} its dual has length T/N = N^δ, which is short. The rest of the argument (the transform R on the
  dual, the energy of W, equidistribution over affine maps) lives on that short dual.
- Chen–Gupta–Li (all characters to one modulus q) have the same feature: χχ̄′ is again a character mod q, so the
  kernel conductor equals the family size.
- In our thin sextic family the kernel Σ_{N(I)≤B} χ_z(I)·conj(χ_{z′}(I)) = Σ_I (I/zz′⁵)₆ has conductor
  N(zz′) ≈ B², because the moduli multiply. At the balanced length L = B it sits exactly at its self-dual point,
  and Poisson returns a dual of length B.
- So the sextic analogue of GM at the K-wall is GM at the self-dual point of the kernel. GM's own theorem at
  T = N² improves the classical N^{3/2} only to N^{7/5} at V = N^{3/4}, and that already uses the t-aspect's
  additive structure (differences of frequencies), which a family of varying moduli lacks.
- **Verdict.** The K-wall needs a large-values idea for thin families of varying moduli. That is beyond GM and
  Chen–Gupta–Li; it is the same "conductors multiply" obstruction that makes the thin family's large sieve stop
  at √. [open; recorded as the precise form of the faces' second wall]

## 2026-10-30 · One shape for all three walls: non-concentration at a self-dual point

**Common form [derived].** Each remaining wall asks that a structured vector put only a power-small share of its
mass on a structured subspace, exactly where a Poisson map is an involution (so positivity on either side returns
the trivial bound).

| wall | vector | subspace | self-dual map |
|---|---|---|---|
| P1 / (X) | slot-summed theta g̃·A (length N = KL) | span of the K quadratic characters | quadratic Poisson in k (K ↔ N²/K), factor exactly 1 since N = KL |
| B2 (via deletion) | μ on n ~ D | span of the H sextic characters of the complete family, H = D^{1−c′} | Poisson in w at H = D |
| faces' K-wall | sources of length B | selected rows' characters | the kernel Σ_I (I/zz′⁵)₆ at length B, conductor B² |

- In P1 the quadratic step is an isometry up to the factor N (every vector v has ‖Φ*v‖² ≈ N‖v‖², because the K
  rows are nearly orthogonal with N > K). So all room must come from the cubic step: the residual of c_P
  (c_P = conj(g̃)·Φ*S_P, minus its (·/P)₃ part) must put at most L^{−2η} of its mass on the slot span
  {(·/P′)₃}.
- In B2, for the complete family below the self-dual point, the D-term of the large sieve is reached only by
  character-like vectors (a = conj(χ_{w₀})). For generic vectors the rank argument gives the diagonal HD: Φ is
  H × D of rank H with flat spectrum. The Poisson dual's own diagonal D² is not a lower bound, since the dual
  off-diagonal cancels it for random vectors. So "Möbius is not character-like in mean square" is exactly the
  missing statement (twisted Chowla).
- The needed c′ is tiny: c′ = 6.4e-4 for the #97 bar and 0.0138 for the #98 bar (long slope 5(1 − c′)/6).

**Tools that work at self-dual points, and why none applies yet [read; web; derived].**
- *Spectral (Kuznetsov).* For the cubic cover of GL(2) over Q(ω) a Kuznetsov formula exists: Livné–Patterson,
  extended by Louvel. Dunn (arXiv 2403.13151, ANT 2025) uses it for prime sums of a fixed cubic cusp form past the
  2/3 bottleneck. The theta functions are the exceptional spectrum, and they carry the Patterson bias.
  - P1 mixes quadratic rows with cubic theta coefficients, so it lives on the 6-fold cover. There the sextic theta
    coefficients are only partly known (Bröker–Hoffstein, arXiv 1312.0568).
  - The Chinta–Friedberg–Hoffstein conjecture ties squared sextic theta coefficients to cubic Gauss sums.
  - No spectral large sieve for the 6-fold cover is available.
- *Multiple Dirichlet series.* The Kubota series is GL(2)-like with respect to quadratic twists (twist conductor
  N(k)²). So the second moment of its quadratic twists is an affine multiple Dirichlet series, with an infinite
  group and only partial continuation. The exact type is computed in the next entry (two double bonds, not D̃4).
  Even for GL(2) quadratic twists, unconditional results give only log savings (Li, Invent. 2024); the power-saving
  asymptotics of Soundararajan–Young assume GRH.
- *Dispersion (Dunn–Radziwiłł).* It works for prime vectors at the cubic family's balanced range, but not past the
  family size (P1, B2).
- **Verdict.** Each wall needs a power saving at a self-dual point for a structured vector. No 2026 tool supplies
  one in the metaplectic (cubic/sextic) setting. [open; the three walls are one problem in three costumes]

**B2 via deletion just past the self-dual point [Lean, read; `Hecke/InverseAmplificationRaw.RawMoment`,
`Dictionary/InverseRawReference.raw_reference_large`].**
- `RawMoment` gives Σ_{rows of norm ≤ H}‖inverse polynomial at length D‖² ≤ C·H·(HD)^κ for any row set, under the
  gate D^{1+c} ≤ H with c > 0 fixed. The constants depend on c.
- The proof reflects the rows (Poisson over the family of norm ≤ H), expands into canonical squares over the dual
  rows, and applies the quadratic sieve to the reflected cubic-theta columns. So c > 0 is that sieve's balanced
  point.
- Deletion needs H = UV⁶ ≥ D^{1+c}. Running it at H = D^{1−c′} would need the theta–quadratic sieve slightly past
  its balanced point, with a power saving against its N-term. That is P1's type of estimate with slot width 0.
  This confirms in the code that atoms 1 and 2 share one root (LOG 2026-10-24).
- **The strengths differ, though [derived].**
  - Suppose the complete family obeys Σ_{w≤H}|M_w(D)|² ≪ D^{1−η}H^η for H ≤ D, i.e. an N-term saving (H/D)^η.
  - With V copies at H = UV⁶ = D^{1−c′}, deletion gives U^{1/6}D^{5/6}·D^{c′(1/6 − η)}. That beats plain deletion
    iff η > 1/6, and optimizing gives λ = max(1/6, η). This is the "never combine" rule again.
  - So B2 needs the core saving at η ≥ 0.1717 (#97 bar) or 0.1782 (#98 bar), while P1 needs only η ≈ 0.008 or
    ≈ 0.017.
  - Same estimate, a 10–20× stronger saving: a proof of P1 would not by itself move the long word. [derived]

**(X) as a multiple Dirichlet series: the "2" is a double bond [derived; numerical check of the group].**
- Z(s₁, s₂, w) = Σ_k L(s₁, θ_P⊗χ_k)·conj(L(s̄₂, θ_{P′}⊗χ_k))·N(k)^{−w} carries three functional equations. In
  centred coordinates x_i = s_i − 1/2, y = w − 1/2:
  - the Kubota FE in n, whose twist conductor is N(k)² (#96 N1): x₁ ↦ −x₁, y ↦ y + 2x₁;
  - the same in m: x₂ ↦ −x₂, y ↦ y + 2x₂;
  - quadratic Poisson in k (FE of L(w, χ_{nm})): x_i ↦ x_i + y, y ↦ −y.
- Cartan matrix [[2,0,−1],[0,2,−1],[−2,−2,2]]: determinant 0, so the type is **affine**. It is a rank-3 diagram
  with two double bonds, the imaginary root is δ = α₁ + α₂ + 2α₃, and the group is infinite (more than 200
  elements after 12 steps).
- With GL(1)-like twists (shift y + x_i) the same three equations give A3: determinant 4 and the group S4 of order
  24. That is the classical second moment of quadratic Dirichlet L-functions, which has power-saving asymptotics.
  The first moment Σ_k L(s, θ_P⊗χ_k)N(k)^{−w} is of type B2/C2 (determinant 2), finite.
- So the conductor exponent 2 of a quadratic twist of the cubic theta series is exactly what makes the moment
  affine. This is the same position as the fourth moment of quadratic Dirichlet L-functions (affine D̃4):
  - power savings are known over function fields (Bucur–Diaconu; Florea);
  - over number fields they are open unconditionally (Shen assumes GRH; Li gets log savings).
  The obstacle there is growth control of the series near w = 1, past its continuation by Bochner's tube theorem.
- What (X) would need on this route [derived]:
  - the corrected affine series, i.e. its p-parts, so that all three functional equations hold;
  - polynomial growth in a neighbourhood of (x₁, x₂, y) = (0, 0, 1/2 − ε₀) inside the Tits cone x₁ + x₂ + 2y > 0;
  - polynomial dependence on P, P′ and the sieving parameters.
- Sieving the squarefree conditions with a cut A costs:
  - k: tail ≲ KN·K^ε/A;
  - n: tail needs A ≥ L^{(1+η)/4}.
  So ε₀ ≈ 0.05–0.1 suffices, not ε₀ → 0.
- **Verdict.** P1 is an instance of the "affine moment" problem over a number field. It is as hard as the
  number-field fourth moment of quadratic Dirichlet L-functions with a power saving. [open; classification
  settled]
- **Literature check [read; web].**
  - Shen–Stucky (arXiv 2402.01497, 2024) prove the number-field fourth moment of quadratic Dirichlet
    L-functions unconditionally, but with error O(X(log X)^{6+ε}) against a main term of size X(log X)^{10}: a
    log saving. Their "four main terms" are the shifted-moment terms. They write that improving the error "would
    need additional ideas".
  - Power savings for an affine moment exist only over function fields: Diaconu–Paşol–Popa (type D₄^{(1)}),
    Bucur–Diaconu, Florea.
  - (X) needs a power saving, L^{−η} = Z^{−0.001}, in an affine moment over Q(ω). That lies beyond the 2026 state
    of the art for the simplest affine case. The classification stands.

## 2026-10-30 · How much selected norm the leaf needs below K = 1/2 (the K-wall quantified)

**Question.** The closure barrier (`lean/arvi_kwall/`) shows that below slope 1/2 the selected norm can only be
proved up to an excess γ = 1/6 over its fixed point (Θ₆ start). Does the leaf really need γ ≈ 0, or does a weaker
norm price a native step at K < 1/2?

**Model [numerical; `$SCRATCH/kwall/ledger_gamma*.py` on `selected-leaf/root_ledger.py`].**
- The selected-norm term per root becomes max(X, (1 − δ + γ)y + δX).
- Each geometry may also take the parent face on all rows, at price deletionNeed (slots deleted at the trivial
  cost 1), keeping the better of the two prices.
- The scan runs along the native lines K = 0.48 and 0.49.

| what | result |
|---|---|
| selected norm alone, γ = 1/6 | fails by 0.164 at the tiny-slot balanced split (x₁ = x₂ ≈ 0.495, S → 0) |
| best of norm and parent face, no selected norm at all | fails by O(1e-6–1e-5) at the t = 0 corner |
| best of norm and parent face, γ = 0.02–0.06 | fails by +3e-7 to +4.5e-6 at S ≈ 0.03–0.10, x ≈ (0.40–0.47) each |
| γ = 0 (fixed point) | passes with margin ≈ 2.5e-3 |

**Reading.**
- The parent face covers the tiny-slot corner. It cannot cover the t = 0 corner, where the selection pays its 6u
  row cost (M = 1 − 6u), so there the selected norm must carry the price.
- At that corner the effective source length is X_eff ≈ 0.96·y. The tolerance is γ ≲ 0.015 at δ = 0.48: the
  selected norm at length B^{0.96} must be ≤ B^{0.996}.
- For comparison, the full family has Θ₆(0.96) = 1.153 and the Θ₆ closure gives 1.148.
- So the leaf below 1/2 needs a near-fixed-point selected norm next to the balanced point, beating the full
  family by B^{0.157}. The Θ₆ closure is about 11× too weak. This confirms the K-wall at full strength: it is a
  Guth–Maynard-type estimate, and the parent face only relieves the tiny-slot corner. [numerical model; derived]

**(X) by parabolic continuation and Bochner's tube theorem: does not reach the centre [derived; numerical
search].**
- The idea: each pair {σ₁, σ₃} or {σ₂, σ₃} generates a finite group of type B2. So Z(s₁, s₂, w) continues along
  each parabolic while the other variable stays in absolute convergence, with polynomial growth N(m)^{A} in the
  frozen twist. Convex hulls (Bochner) of the two tube regions might then cover (x₁, x₂, y) = (0, 0, 1/2 − ε₀),
  which is all (X) needs.
- The growth enters only through the w-reflection, N(m)^{max(0,−y)}. Moving x₁ left uses the Kubota reflection
  y ↦ y + 2x₁, so A(x₁, y) ≈ max(0, c·(−x₁) − y) with slope c = 2.
- A search over all two-point convex combinations of points in R₁ = {x₂ > 1/2 + A(x₁, y)} and in R₂ (the
  symmetric region) finds no reach of (0, 0, y₀) for y₀ ∈ {0.5, 0.45, 0.3}. This holds for c = 2 and even for
  c = 1 or 1.5.
- The negative coordinate needed to cancel the other point's positive one always costs at least as much growth.
- So the parabolic route fails for (X), as it does for the GL(2) analogue. This is consistent with only log
  savings being known there (Li; Shen–Stucky). [dead end recorded]

## 2026-10-30 · BDFKK (explicit RIP past the square-root bottleneck) against our walls

**What BDFKK do [read; arXiv 1008.4535, Duke 2011].**
- They build explicit p × N matrices with RIP of order k = p^{1/2+ε₀}. Columns are chirps u_{a,b}(x) =
  e_p(ax² + bx)/√p, with (a, b) in **designed** sets:
  - A is tiny (|A| = p^α, α = 1/(8m²)), with reciprocal sums 1/(a − a_j) non-degenerate (2.4);
  - B is a digit set Freiman-isomorphic to a cube, so every large subset has small additive energy (2.5).
- Step 1 (Lemma 1): flat RIP plus coherence µ ≤ 1/k gives RIP. Flat RIP means |⟨Σ_{J₁}u, Σ_{J₂}u⟩| ≤ δk for
  disjoint J₁, J₂.
- Step 2 (Lemma 2): at k = √p, every coherence is an exact Gauss sum, of modulus 1/√p with phase
  e_p(−(b₁−b₂)²/(4(a₁−a₂))). The flat sum becomes bilinear forms e_p(2c·b₁b₂) over the slices of B, with one
  form per pair (a₁, a₂).
- Step 3: if those forms do not cancel beyond √, Balog–Szemerédi–Gowers gives a large subset of B with large
  additive energy, contradicting (2.5). Bourgain's sum-product theorem C, Σ_b E(A, bA) ≪ (·)^{−c₀}|A|³|B| with
  c₀ = 1/10430, supplies the cancellation.
- The gain is ε₁ = c₀γ/20 − 43α/m, about 10⁻⁶ or less (Mixon's explicit value is of order 10⁻²⁸).

**The match [derived].**
- The faces' K-wall *is* a square-root bottleneck. The selected rows W (size ≈ B^{1−δ}) sit in the sextic
  dictionary φ_z = (χ_z(I))_{N(I)≤X}.
  - For δ > 1/2, |W| < √(dimension) and coherence-type arguments (amplify and reflect) suffice.
  - For δ < 1/2 we need RIP-type near-orthogonality of W past √. At δ = 0.48, X = B^{0.96}: |W| = B^{0.52} =
    n^{0.54}, a margin of 0.04 beyond √n.
- The coherences depend only on the quotient character: ⟨φ_z, φ_{z′}⟩ = F(z/z′) with F(w) = Σ_{N(I)≤X} χ_w(I).
  So the flat-RIP sum is Σ_w F(w)·r_{Ω₁/Ω₂}(w), exactly BDFKK's and Guth–Maynard's shape.

**Why it does not transfer [derived].**
1. *Coherence.*
   - Chirps have exact Gauss-sum coherence (modulus 1/√p, explicit phase).
   - Our F(w) is an incomplete sum at its self-dual length (X ≈ √N(w)), with no uniform bound (Pólya–Vinogradov
     is trivial; Burgess saves only B^{0.125}).
   - Its Poisson form carries sextic Gauss sums g(χ_{zz′⁵}), whose Patterson bias is the known obstruction.
2. *Index sets.*
   - BDFKK design A and B to have no additive structure.
   - Our W is a large-value set of a short prime polynomial, so it is given, not designed. The relevant structure
     is the multiplicative energy of W modulo sixth powers, for which there is no bound.
   - Guth–Maynard is the large-value-set analogue (they bound the additive energy of W by another large-value
     argument). It needs a short kernel dual, which fails here (journal: "conductors multiply").
3. *Strength.*
   - BDFKK's ε₀ is about 10⁻⁶ or smaller. The K-wall needs 0.04 past √ (and the selected norm within B^{0.015}
     of its fixed point).
   - Even a successful transfer at BDFKK strength would be worth ~0 in θ. The same holds for P1: a
     sum-product-strength η ~ 10⁻⁶ gives Δθ ~ 10⁻⁹.

**Verdict.** BDFKK confirms the diagnosis (our walls are square-root bottlenecks, broken only through additive
structure of the index set), but not a route. A transfer would need, in order:
- a Gauss-sum-bias subtraction for the quotient-character coherences;
- a multiplicative-energy bound for large-value sets of short prime polynomials in the sextic family;
- a sum-product input for sextic Gauss-sum phases over such sets that is orders of magnitude stronger than c₀ =
  1/10430.
[read; derived; dead end at the needed strength]

## 2026-10-30 · Literature recheck (Oct 2026) and the K-wall corner as a slot-cost statement

**Literature, October 2026 [read; web search].**
- No power-saving second moment of quadratic twists of a GL(2) (or metaplectic) form has appeared. Li
  (arXiv 2208.07343) is still the unconditional asymptotic. Chen–Lin (2603.21739) treats derivatives of
  quadratic twists, and 2608.25812 the family of characters to one modulus (power saving under Selberg's
  eigenvalue conjecture). So P1/(X) stays at the edge.
- Guth–Maynard has been extended to all characters to one modulus: Chen–Gupta–Li (arXiv 2507.08296), giving
  N(σ, q, T) ≪ (qT)^{7(1−σ)/3+ε}. Their key step is a bound for sums over affine maps with a GCD twist. It
  uses the full character group (χχ̄′ is again a character mod q), which our thin sextic family lacks.
  Cossaboom (2609.27715) carries GM to GL(2) in the t-aspect. Neither touches thin families of varying moduli.

**A pointwise rule does not move the K-wall [numerical; `$SCRATCH/kwall/pvbeta.py`].**
- The bootstrap half-plane gives, for a smooth sum of length X twisted by a row of conductor Y,
  |S|²/X ≤ Y^ε·min(X, Y/X)^{2β−1}. (Mellin, shift to Re s = β or 1 − β, convexity in between.) This is
  25% better in the exponent than Pólya–Vinogradov.
- Rule tested: that bound on both plain sums, with the selected norm on the slots only, per root
  (2β−1)m + max(s, (1−δ+γ)y + δs), m = Σ min(x_i, y − x_i). Against the dual norm
  max(m + s, (1−δ+γ)y + δ(m + s)) it loses (2β − 1 − δ)m in the binding regime.
- The ledger agrees: at K = 0.48, L ∈ {2.3, 2.05} and γ ∈ {1/6, 0.05, 0.02} the worst geometry is identical
  with and without the rule. [dead]

**Where the K-wall binds [numerical; same scan].**
- The worst geometry is M = 1 (the t = 0 corner) with both plain sums just below √(conductor)
  (x₁ = x₂ ≈ 0.467) and a slot sliver s ≈ 0.028. At this corner:
  - the parent face fails by [(6 − 2L₀)u + (L₀ − L)S]/L₀, which is O(step);
  - the selected price there is γ − δ(1 − X_eff) with X_eff ≈ 0.962, hence γ ≤ 0.018.
- At that point the selected rows only need the full-family classical bound max(L, B) = B, because
  B^{(1−δ+γ)+δX_eff} ≤ B iff γ ≤ δ(1 − X_eff). So a direct structured face (smooth × smooth × short prime
  slots, slot cost below 2 at P + ΛS ≈ 1) would make the selected norm unnecessary at the corner.
- **Reading.** The K-wall and the faces' slot cost are one atom seen from two mechanisms: amplify–reflect at
  δ < 1/2, or a structured sextic sieve with prime slots costing Λ < 2. The smooth part alone needs a
  Lindelöf-on-average fourth moment of the sextic family at X_eff ≈ 0.96 (Θ₆ gives excess 0.154 there).
  [derived; reclassification, no new route]

## 2026-10-30 · The label line υ = 1/2 is optimal at the binding (closes an open idea from T96)

**Setting [read; Collet's return paper `first-return.tex` (FR10–FR13), `foundations.tex` (195)–(197)].**
- The physical numerator is a triple Mellin integral in (s, w, z), evaluated on (β + e, 1/2, 17/50). The −y/2 in
  E_κ = 1/2 + 13h/75 − y/2 − ℓ/2 − 9d/100 + δ/2 + δp(ℓ − C/2) + (3/4)dR* comes from the label length Y = Z^y on
  Re w = 1/2.
- The Euler-product remainder H is ≪ q_u^ε on the whole box Re w ≥ −1/100, Re(s + w) ≥ 1 + ε₁ (paper (197)), so
  the line could legally move down to Re w ≈ 1 − β. The w-variable also carries the row L-function L(w, ψ_u), of
  conductor q_u ≈ Z^d.

**Price on a line Re w = υ [derived].**
- Hölder (4/3, 4) with the family fourth moment:
  - for υ < 1/2 the functional equation gives Σ_u|L(υ)|⁴ ≈ Z^{d + 4(1/2−υ)d};
  - the exponent is (3/4)dR + d/4 + (1/2 − υ)d + υy, which against υ = 1/2 changes by (1/2 − υ)(d − y);
  - for υ > 1/2 it is (3/4)dR + d/4 + υy, worse by (υ − 1/2)y.
- So υ = 1/2 is optimal iff d > y. At the binding edge newTop d = h ≈ 0.81 > y ≈ 0.47, a lower line loses
  0.34 per unit of (1/2 − υ). For floor rows (d < y) the lower line wins, which is why the floor estimate uses
  it.
- Pointwise bootstrap convexity instead, with log|L(υ)| ≤ (β − υ)d/2 on [1 − β, β]: the exponent is
  dR + (β − υ)d/2 + υy, with slope y − d/2 = +0.065, so it does prefer a low line. But at υ = 1/2 it is already
  ≈ 0.09d above Hölder. At υ = 1 − β it gives 0.854 against Hölder's 0.806 at υ = 1/2 (exponents in log_Z, at
  R = 0.607). A mixture cannot help, because Hölder rises at rate d − y = 0.34 while the pointwise bound falls at
  only 0.065.
- **Verdict.** The label line is not a lever at the binding. [dead; closes the T96-era open idea]

## 2026-10-30 · RIP program (1): formal foundation, and the K-wall reduced to a diluted-bias statement

**Program.** Arvi's direction: attack the square-root barrier as an RIP problem and formalize every step, even
for tiny gains. The K-wall is RIP of the sextic dictionary on a large-value row set W, with |W| = B^{1−δ},
δ < 1/2, beyond √(dimension).

**Formal foundation [Lean, built; `lean/arvi_rip/`; no sorry, standard axioms].**
- `Coherence.lean`:
  - `gershgorin_rip`: coherence μ gives RIP with constant μ(|S| − 1);
  - `welch`: N² ≤ n(N + N(N − 1)μ²);
  - `coherence_order_barrier`: with N ≥ 2n, a coherence certificate has k ≤ 1 + δ√(2n). This is the √-barrier
    for coherence methods, stated formally.
- `FlatRIP.lean`, `flat_rip_on` (BDFKK Lemma 3, fixed support): flat bilinear sums ≤ δ√(|J₁||J₂|) on W give
  |‖Σa_z u_z‖² − ‖a‖²| ≤ 32δ(T + 2^{−T}√|W|)²‖a‖². Every beyond-√ construction passes through this reduction.

**Which rules cannot move the closure [numerical; `$SCRATCH/kwall/closure4.py`, `closure_dr.py`].**
- Adding the trivial Frobenius rule n(x) ≤ x + 1 − δ leaves n(1) = 7/6. The Lean barrier is not an artefact of
  omitting trivial bounds.
- A corrected initial bound that is diagonal up to x = X₀ moves n(1) as follows:

  | X₀ | n(1) |
  |---|---|
  | 0.6 (Dunn–Radziwiłł's proven range for prime vectors) | 7/6, unchanged |
  | 5/7 | 1.149 |
  | 0.96 | 1.021 |

**The mechanism that does break it: dilution of a low-rank bias [numerical + derived].**
- If the excess of the sextic sieve on a thin row set shrinks with the density, i.e. n_W(x) ≤ max(1, x, Θ₆(x) − δ),
  then the closure is exactly the fixed point. At δ = 0.45, 0.48 and 0.49 it gives n(1) = 1 and n(0.96) = 1 − δ + 0.96δ.
- The derivation is short: at x = 1, max(1, 1, 7/6 − δ) = 1 for δ ≥ 1/6; then one amplification step down to
  0.96. So the whole K-wall reduces to that diluted bound.
- **Why it should hold.**
  - The Θ₆ excess comes from the Gauss-sum bias. Sources correlated with ε̄_n are mapped by M to theta-type row
    vectors of uniform magnitude.
  - If M is near-isometric off a low-dimensional bias span V, then for a ∈ C^S:
    ‖M_W a‖² ≤ 2‖M P_{V⊥} a‖² + 2 Σ_{z∈W} |M P_V a(z)|² ≲ (L + B)‖a‖² + (|W|/|F|) B^{7/6}‖a‖².
  - This is beyond √ for every δ > 1/6.
- **What is not enough.**
  - #96's graded inverse theorem (thm:D6SF, cor:GS1) has the right shape: the excess lies on correlations with
    (m₀/·)₆ for small m₀, and it allows subsets of sources.
  - But its residual B + A^{1/6}B + A^{2/3}B^{1/2} multiplies the full ‖β‖² and carries excess ≈ 0.15 at x = 0.96.
    It does not dilute.
  - Dunn–Radziwiłł's corrected cubic sieve is diagonal + rank-one bias + error, but only up to B = A^{3/5}.
- **Exact open statement.**
  - Write 1_W ≤ |T(χ_z)|^{2k}/V^{2k}, with T the selecting slot polynomial, and keep |T|^{2k} on the row side as
    a twist via reciprocity: χ_z(qq′⁵) = (z/qq′⁵)₆.
  - The diagonal q = q′ gives exactly (|W|/|F|) × (full sieve), which is the dilution.
  - The K-wall therefore follows from the decorrelation of the twisted forms
    Σ_z ψ_m(z)|A(χ_z)|² (m = qq′⁵ ≠ sixth power) from their mean: the slot's large values must not align with the
    Gauss-sum bias of the source.
  - A function-field or random-model check, and a proof for the twisted forms with m ≠ 1, are the next steps.
  [conjecture with mechanism; reduces the K-wall to a decorrelation estimate]

## 2026-10-30 · RIP program (2): the sextic Gram matrix is Marchenko–Pastur; slot large-value sets behave like random sets

**Experiment [numerical; `rip/zfamily.py`, `rip/mp_check.py`].**
- Exact sextic residue symbols over Z[ω]:
  - rows: squarefree ideals z with N(z) ∈ [B, 2B], coprime to 6;
  - sources: primary x with squarefree N(x) ≤ L.
- Row Gram matrix G = EEᴴ with E[z, x] = (x/z)₆. All values below are top eigenvalues divided by the mean diagonal
  (≈ the number of sources S).

| B, L | rows / S | full family | MP edge | ρ = 1/2: random / slot large-value / MP | ρ ≈ 0.05: random / slot / MP |
|---|---|---|---|---|---|
| 3000, 6000 | 0.57 | 3.155 | 3.087 | 2.340 / 2.337 / 2.357 | 1.340 / 1.318 / 1.365 |
| 3000, 3000 | 1.15 | 4.270 | 4.287 | 3.015 / 3.036 / 3.087 | 1.484 / 1.471 / 1.533 |
| 3000, 12000 | 0.29 | 2.442 | 2.356 | 1.900 / 1.934 / 1.900 | 1.251 / 1.236 / 1.252 |
| 1500, 3000 (slot norm 120–240) | 0.58 | 2.994 | 3.097 | 2.303 / 2.329 / 2.363 | 1.325 / 1.401 / 1.366 |

- Sets aligned with the top eigenvector (adversarial, not large-value sets) are higher: 2.885 against MP 2.357 at
  B = 3000, ρ = 1/2.

**Reading.**
- At these scales the sextic dictionary is spectrally a random matrix. The top eigenvalue sits at the
  Marchenko–Pastur edge (1 + √(R/S))². A rank-one Gauss-sum bias is not visible: the top five eigenvalues are
  within 3% of each other.
- At L = 4B the full family is 3.6% above MP. This may be the bias starting to show and should be watched at
  larger B.
- Large-value sets of a short prime (slot) polynomial, which is the selection the leaf actually uses, behave like
  random subsets to within about 2%.
- Hence, empirically, ‖M_W‖² ≈ L(1 + √(|W|/L))², which is L(1 + o(1)) for |W| = o(L). That is RIP far beyond √,
  and the K-wall is a property of the proof method, not of the truth. [numerical; strong evidence for the
  diluted-bias conjecture of RIP (1)]

**What is provable now [derived].**
- For a random row subset W of density ρ, matrix Chernoff gives
  E‖Σ_{z∈W} u_z u_z*‖ ≤ ρ‖M‖² + C·L·log(dim) ≤ ρB^{7/6} + C·L·log.
- With ρ = B^{−δ} this is ≤ L·O(log) once δ > 1/6. So for random thin row sets the selected norm reaches the fixed
  point beyond √, using only Θ₆.
- Our W is deterministic. Its selection depends on z only through z mod (slot primes), by reciprocity.
- The bridge from random to large-value sets is the decorrelation of the twisted forms M*D_mM for m ≠ 1, a product
  of slot primes. The numerics say it holds; the proof is open.

## 2026-10-30 · RIP program (3): randomized dictionaries — random RIP beyond √ in Lean, and what transfers to the sextic dictionary

**Arvi's direction.** An explicit RIP dictionary is hard to build, but a random one provably has RIP. So design
a randomized dictionary, and bound both its coherence and its RIP.

**Formal result [Lean, built; `lean/arvi_rip/Hoeffding.lean`, `RandomRIP.lean`; standard axioms, ≈ 9 s each].**
- `card_cond_le`: Hoeffding's inequality in counting form, conditional on the entries outside a set. The
  coefficients may depend on the frozen entries. There is no measure theory: probability is counting over sign
  patterns.
- `exists_rip_sign_explicit`: if 2(N + 1)^{2k}·exp(−δ²n/4) < 1, some n × N sign matrix has unit columns whose
  flat sums are ≤ δ√(|J₁||J₂|) for all disjoint J₁, J₂ of size ≤ k. Through `flat_rip_on` it then has RIP on
  every support of size ≤ k, with constant 32δ(T + 2^{−T}√k)².
- So k ≈ δ²n/(8 log(N + 1)), linear in n, while every coherence certificate stops at k ≲ √n
  (`coherence_order_barrier`). Pairs of singletons give the coherence bound δ from the same theorem.
- The proof uses randomness at exactly one point:
  - `card_bad_le`: given the J₂ columns, the flat sum is a Rademacher sum in the J₁ entries. Its variance is
    |J₁|·‖Σ_{J₂}u‖²/n.
  - `flat_of_not_bad`: that variance is controlled by strong induction on |J₁| + |J₂|. Flat RIP on the smaller
    pairs inside J₂ gives ‖Σ_{J₂}u‖² ≤ 2|J₂| through `flat_rip_on`. This avoids chaos bounds entirely.
  - A union bound over (N + 1)^{2k} pairs finishes.

**Removed (Arvi's review).** This entry used to analyse re-randomizations of the sextic atoms themselves
(thinning rows, re-phasing, sub-selecting sources) and presented them as a test of randomized dictionaries.
They are not randomized dictionaries in the intended sense and say nothing about the proposal, so that analysis
and its Lean file are deleted. The proposal, a dictionary of different atoms with RIP by a positive measure of
operators plus coherence bounds, is RIP program (4).

**The random multiplicative model reproduces the fixed point exactly [derived].**
- Model each row as a random completely multiplicative function f_z with f_z(p) i.i.d. uniform on μ₆
  (Frobenius data at distinct primes are independent coordinates, the CRT heuristic). Then the rows u_z are
  i.i.d. isotropic vectors, E[u_z u_z*] = I on the sources.
- Slot selection |Σ_q c_q f_z(q)| ≥ V tilts only the slot coordinates. Conditionally:
  - E[u_z | selected] is supported on the sources built from slot primes alone, giving a low-rank mean;
  - the rest stays isotropic and independent.
- Matrix Chernoff on the independent part plus the rank-one mean gives ‖M_W‖² ≈ max(L, |W|·(slot energy))
  = B^{max(x, 1−δ+δx)}. That is precisely the closure's fixed point, for every δ, including δ < 1/2.
- This matches RIP (2): slot-selected W is spectrally random to ~2% at B = 3000. So the K-wall is exactly the
  gap between the sextic family and its random multiplicative model on slot-selected rows.

**What transfers, and the exact open step [derived].**
- `flat_of_not_bad` is deterministic. Its induction and the union bound carry over to any dictionary for
  which, for every pair, a large flat sum together with an admissible J₂ norm is "rare".
- For a fixed deterministic W there is no probability to count over. The arithmetic analogue of the union
  bound is a moment bound over all pairs of subsets of W, i.e. high moments tr(G_W^{2p}) with p ≈ log|W|.
  Guth–Maynard reach p = 3 by other means.
- In the multiplicative model the J₁ part is a multiplicative chaos, not a bounded Rademacher sum. Its tails
  are only exp(−t^{2/d}) for degree d (hypercontractivity), so the model proof needs matrix Chernoff (as
  above) rather than flat RIP plus a union bound.
- The rigorous gap: row-independence for a deterministic family of B rows needs equidistribution of z
  (norm ≤ B) in residue classes modulo N(m)·N(x)N(x′), which exceeds B. That is the self-dual wall in CRT
  form, the same object as the open core of RIP (1) (decorrelation of M*D_mM).
- **Verdict.**
  - The randomized-dictionary program gives a clean formal theorem: random dictionaries pass √ through our
    flat-RIP pipeline.
  - It also gives an exact random model whose prediction is the K-wall's fixed point.
  - What remains is a pseudo-randomness theorem for the sextic family against slot-coset tests.
  [Lean, built; derived]

**Next steps.**
1. Formalize matrix Chernoff in the finite counting style of `card_cond_le`, then the multiplicative-model
   theorem: i.i.d. Steinhaus rows conditioned on a slot statistic have selected norm at the fixed point.
2. Look for an arithmetic family whose rows *are* independent at the needed scale, for example rows indexed
   by products over disjoint prime sets, where CRT is exact. Price whether the faces can run on such a family.

## 2026-10-30 · Fresh look 2: new-math directions for −3e-4, and three pricing rules

Report and models: `fresh-look/second/` (`directions.md`; `models/` and `base_models/` run in place). All prices
come from the float model of the newTop row, which reproduces #97 and the bank [numerical, first order].

**Ranked directions [conjecture; prices numerical].**

| rank | direction | −3e-4 needs | −5e-5 needs |
|---|---|---|---|
| D1 | a face proved outside Sil's packing: the twisted fourth moment Σ_z\|X₁X₂Q\|² with a zero-forced prime pool Q, diagonal at prime cost Λ | Λ ≤ 1.82 (5/3: −4.9e-4) | Λ ≤ 1.97 |
| D2 | P1 in its weakest form: a power saving K^{−η₀} in (X) for *fixed* P ≠ P′ (a moment with no main term), giving the joint extension e | η₀ ≈ 0.01 (e ≈ 2.4e-3) | η₀ ≈ 7e-4 |
| D4 | sixth moment of the thin family: window ε₆ or packet μ₆ (thin families have no forced congruence N-term) | ε₆ ≈ 0.10 / μ₆ ≤ 1.144 | 0.115 / 1.152 |
| D3 | sub-√ joint count | slope 0.33 | 0.41 |
| D5–D7 | zero-configuration rigidity; B2 via theta; function-field laboratory | — | — |

**Pricing rules [numerical].**
- **R1.** The landscape is flat from δ* = 0.453 to 0.5. A count theorem valid only below slot slope 1/2 is worth
  at most −7.6e-5, unless it is paired with PR 93's DH-strength joint count J = 1 − ν above 1/2 (in the library,
  unused today), which restores the full −3e-4 for ΔR = 0.0024. "Just below 1/2" is worth nothing in the count.
- **R2.** The binding is a corner in the amplitude class p. A count drop for p ≥ p₀ is worth ≈ 4.1e-3·(1/2 − p₀),
  but the corner's adversary is round 10's: near-critical frequencies above the slot band keep the slots saturated
  while the Möbius blocks go unsaturated.
- **R3.** The e-lever is about 5× weaker at the selected-leaf binding than in `newpowers/R3_return.md`.

**Lead's evaluation [derived].**
- **D1 is the K-wall corner seen from the moment side.** The journal entry "K-wall corner as a slot-cost statement"
  already found that a structured face with prime slots costing Λ < 2 makes the selected norm unnecessary there.
  D1 adds two things:
  - the claim that a direct theorem avoids both of Sil's walls (they belong to the inductive native step, not to
    the moment);
  - a concrete reduction: Davenport–Hasse with the quadratic character turns sextic Gauss sums at primes into
    conjugate cubic ones times a Hecke-character factor, where Heath-Brown–Patterson and Dunn–Radziwiłł dispersion
    apply.

  The crux is the risk the report names: dispersion in the prime pool must be done *before* the smooth factors
  are reflected, or the pool's N(P)² conductor reopens the dead zone (natural face 6κ ≈ 4.5). So D1 is target 0
  plus target 1 of the frontier, with an explicit order of operations to test. Adopted as the main new-math line
  next to the RIP program.
- D2 and D4 have cheap numerical first steps that were never run: single cross-correlations at fixed indices, and
  the packet sixth moment. Delegated to numerics.
- Recorded as dead or capped: pointwise higher-Hölder per-row bounds, and decorrelating bad rows from the packet.

## 2026-10-30 · D1 (direct prime-pool face): first brick in Lean, and the ledger's exact sub-lemmas

**Lean [built; `lean/arvi_primeface/Duplication.lean`, standard axioms, ≈ 8 s].**
- `chi_four_mul_jacobiSum_self`: χ(4)·J(χ, χ) = J(χ, η) over any finite field of odd characteristic. The proof
  counts #{x : x(1 − x) = b} = 1 + η(1 − 4b) via x ↦ 2x − 1, then reindexes c = 4b.
- `gaussSum_duplication`: χ(4)·g(χ)g(χη) = g(χ²)g(η).
- `sextic_duplication`: for χ³ = η, χ(4)·g(χ)g(χ⁴) = g(χ²)g(χ³).
- Numerically checked for p ≤ 109 (`fresh-look/second/checks/hd_check.py`). This is D1's reduction: at primes,
  g̃₆ = χ̄(4)·(J(χ², χ²)/√p)·conj(g̃₃)·g̃₂.

**Numerology of Λ [derived, heuristic].**
- Expand |Q|² in the face Σ_z|X₁X₂Q|². The pairs P = P′ give ‖a‖² × (plain fourth moment), which is diagonal up
  to m₁ + m₂ ≤ 1 (Lemma 18.1).
- The pairs P ≠ P′ are twisted plain fourth moments T(PP′⁵) = Σ_z (PP′⁵/z)₆|X₁X₂(z)|², with twist conductor
  N(PP′) ≈ P₀² = Z^{2s}. Against the diagonal they must save P₀ on average, i.e. N(h)^{1/2} in conductor terms.
- Reflection pays the twist's conductor in the dual length (the dead zone). That is Sil's Λ = 2: budget 2s for
  the conductor P₀².
- If, after Poisson in z, each prime variable enters the dual through a Gauss-sum phase g̃₆(P)(k/P)₆, then summing
  over P with Heath-Brown–Patterson's P₀^{5/6} instead of the trivial P₀ in *both* variables turns the budget 2s
  into (5/3)s. That gives **Λ = 5/3**, the same numerology as Dunn–Radziwiłł's cubic threshold A^{3/5}, and
  Δθ ≈ −4.9e-4.

**The ledger reduces to three statements [conjecture; order of operations as fresh look 2 prescribes: Poisson in
z first, the plain sums kept as Type-I coefficients, no reflection of the plain sums].**
- **(L1) Davenport–Hasse at primes.** [Lean, done.]
- **(L2) Heath-Brown–Patterson twisted by quadratic characters, uniformly.**
  Σ_{N(π)≤X} g̃₃(π)·(k/π)₂·λ(π) ≪ X^{5/6+ε}·N(k)^{c} for Hecke characters λ of bounded conductor and
  N(k) ≤ Z^{0.8}.
  - Route: Vaughan's identity. The Type-I sums are Σ_n g̃₃(n)(k/n)₂: the twisted cubic Kubota series, entire for
    k ≠ □ (P1 deep-dive), bounded by convexity in N(k). The Type-II sums go through the cubic large sieve, which
    is blind to a quadratic twist.
  - With a loss N(k)^c the threshold becomes (1 + 2c)/(5/3 + 4c), still past 1/2 for c ≤ 1/6.
  - Note: (L2) is a *first*-moment statement about the same twisted theta coefficients whose *second* moment is P1.
- **(L3) Phase survival.** In the dual after Poisson in z, the plain factors appear as Type-I coefficients
  (smooth, length Z^{m₁+m₂}) multiplying the pair (P, P′). Their own Gauss-sum factors g̃₆(n) at composite n
  (sextic theta coefficients, Patterson bias n^{2/3}) must not cancel the prime phase. The risk named in fresh
  look 2 (main-term interaction, Patterson's A^{2/3}B^{4/3}) lives here.
- **Go/no-go:** carry (L3) through D–R §9's error terms with c from (L2), and solve for s_max(m₁ + m₂) on the
  window [0.75, 0.87]. Continue only if (1 − m₁ − m₂)/s_max ≤ 1.85.
- Numerics running in parallel: `rip/prime_pool/` (empirical Λ for zero-aligned, random and Patterson-biased
  pools) and `rip/moments_probe/` (D2's fixed-index cross-correlations; D4's packet sixth moment).

## 2026-10-30 · D2 and D4 numerics: fixed-index cross-correlations are random-like; the thin family's sixth moment has no N-term

Scripts, logs and tables: `rip/moments_probe/` (README). Delegated run; the lead re-ran the self-test
(`test_probeB.py`: brute force equals the pipeline, multiplicativity, exact T4/T6 counts).

**D2: fixed-index cross-correlations [numerical].**
- Setup: S(k, P) = Σ_n g̃₃(n)(n/k)₂ conj((n/P)₃)W(N(n)/(K·N(P))), over the 10 or 20 smallest split primes, with
  K ≤ 2·10⁴ (one run to 5·10⁴), at the self-dual point N = K·N(P).
- Diagonal: G_PP ≈ 0.93·R(K)·ΣW², with no N-term, also at N/4 and 4N.
- Off-diagonal: ρ_{PP′} = |G_{PP′}|/√(G_PP G_P′P′) ≈ 0.94·R(K)^{−1/2}. Fitted η = 0.52–0.57 for every pair class,
  with 95% intervals inside [0.43, 0.64]; random surrogates give 0.49–0.52.
- Across 90 pairs, ζ² follows Exp(1), with no outlier pairs and no outlier eigenvalue. The dependence on
  N(P)N(P′) has exponent 0.05 ± 0.07.
- The conjugate pairs carry the exact √2 from S(k̄, P) = conj S(k, P̄).
- **Reading.** (X_fix) holds numerically with η₀ ≈ 1/2, against the η₀ ≈ 0.01 that −3e-4 needs. The obstruction to
  D2 is provability (affine type), not truth.

**D4: sixth moment of short plain sums in the thin sextic family [numerical].**
- M₆ = Σ_u|S_u|⁶/(R N³) stays between 0.09 and 0.59 for m ≤ 0.8, up to N³/R ≈ 10⁷ (B ≤ 1.5·10⁶).
- The full Dirichlet family mod q ≈ R, run through the same code, gives M₆ ≈ N³/q + O(1): 11, 19, 190 and 3105
  for the four values of m.
- Fitted N-term coefficient for the thin family: −1.5e-5 (m = 0.5) and −6.5e-5 (m = 0.43), against 1 for the
  full family. The log-slopes relative to the multiplicative surrogate are +0.007 ± 0.006 and −0.012 ± 0.006,
  where an N-term would give +0.29 and +0.50.
- The thin family even sits 5–13% *below* the random multiplicative surrogate for m ≥ 0.43, with the deficit in
  the extreme tail. Mechanism unknown; it has the opposite sign of an N-term.
- **Reading.** The thin family is Lindelöf on average for plain sums (ε₆ ≈ 0 within ≈ 0.02, against the 0.10
  that −3e-4 needs). The congruence N-term, which is genuine for full families, is absent, as fresh look 2
  predicted.

**Synthesis: one statement behind the K-wall, D1 and D4 [derived].** Every numerical probe says the same thing:
- the sextic Gram matrix is Marchenko–Pastur (RIP (2));
- slot-selected rows are random-like (RIP (2));
- fixed-index cross-correlations are random-like (D2);
- plain products show no N-term (D4).

All of these are instances of one structured large sieve: vectors orthogonal to the theta-bias span (plain
products, prime pools with non-Patterson phases, and their products) are generic for the sextic dictionary, i.e.
‖Ma‖² ≪ (R + ‖a‖-weighted N-term only on the bias span)·‖a‖².
- The K-wall's dilution needs it at L ≈ B^{0.96} on slot-selected rows.
- D1 needs it for plain × plain × prime at total length B^{0.75–0.87} with the prime cost 5/3.
- D4 needs it for plain³ beyond the row count.

The literature has it only in two cases:
- the quadratic family, all vectors (Heath-Brown's quadratic large sieve);
- the cubic family, prime vectors up to A^{3/5} (Dunn–Radziwiłł).

**Program consequence.** Rank the proof attempts by how much of this one statement each needs:
1. D1, prime pool only. Heath-Brown–Patterson plus the phase-survival lemma (L3).
2. The K-wall, which needs an inverse theorem on the full family plus bias delocalization.
3. D4, which needs the full structured sieve for long plain products.

## 2026-10-30 · The thin family's sixth-moment deficit is the functional equation (probe C)

**Question (Arvi).** Why does the thin sextic family's sixth moment of plain sums sit 5–13% *below* the random
multiplicative model, rather than above it as a bias or N-term would?

**Answer [numerical; `rip/moments_probe/probeC.py`, README "Probe C"].**
- **Smooth weights, B = 3·10⁴:** the model's M6 grows monotonically in m (2.19 → 9.11 for m = 0.2 → 0.8). The
  actual M6 rises to ≈ 5.1 at m ≈ 0.4–0.5 and then *falls* (4.30 at 0.7, 3.77 at 0.8), roughly symmetric under
  m ↔ 1 − m.
- **Mechanism.** For N > √(conductor), Poisson writes S_u as a dual sum of length N(u)/N. So the normalized moments
  of genuine characters follow min(m, 1 − m), while random multiplicative functions have no functional equation.
  Check: actual(0.7) = 4.30 against model(0.3) = 4.22.
- **At the self-dual point** the deficit is a stable constant factor: 0.865, 0.777, 0.782 at B = 3·10⁴, 10⁵,
  3·10⁵.
- **Below 1/2** (the D4 packet length 0.43) the family matches the model within ≈ 5–10%.
- **Prime rows** carry a stronger deficit than composite rows for m ≥ 0.45 (≈ 0.72–0.76 against 0.79–0.82 at
  m = 1/2). Mechanism open.
- **The sharp cutoff** is not the cause: with smooth weights the deficit is *larger* at m = 0.7 (0.56 against
  0.77 for the sharp annulus).

**Reading [derived].**
- The right comparison model for the sextic family is "random multiplicative *with* functional equation". For
  moments, that means the multiplicative model at length min(N, N(u)/N), which is the reflection rule of the K-wall
  closure seen numerically.
- The deficit buys no exponent (a constant factor at m = 1/2, reflection beyond).
- It confirms that the family's only structure visible in plain-sum moments is Poisson self-duality: no N-term,
  no bias, no extra correlations.
- For D4 the relevant regime (m ≈ 0.43 < 1/2) is random-multiplicative, i.e. Lindelöf on average with
  multiplicative-model constants.

## 2026-10-30 · D1 (L2) numerics: quadratic twists kill the Patterson bias at primes

`rip/l2_probe/` (README, log). Normalized cubic Gauss sums over primary split primes, X = 10⁶ (78,462 primes),
12 values of k up to N(k) ≈ 4600 [numerical]:
- **Untwisted:** Σ g̃(π) carries the Heath-Brown–Patterson main term (19.9σ, local slope 0.754).
- **Cubic parameter shift:** Σ g̃(k, π) keeps a main term scaling like N(k)^{−1/6}, matching |τ(k)| for the cubic
  theta coefficients at squarefree k.
- **Parameter k²:** Σ g̃(k², π) has none, because theta coefficients vanish at squares.
- **Quadratic twists:** Σ g̃(π)(k/π)₂, and D1's dual combination Σ g̃(π)(k/π)₂ conj (k/π)₃, are random-walk size
  (0.1–2.3σ), with no main term and no visible N(k) growth.

**Reading [derived].**
- (L2)'s premise holds numerically: in D1's dual, the prime pool sees no Patterson bias, and the truth is
  square-root cancellation (Λ → 1) against the provable Heath-Brown–Patterson X^{5/6} (Λ = 5/3).
- What remains is the proof of (L2) uniformly in k, and (L3).

## 2026-10-30 · D1 numerics: the prime-pool face holds far past both lines (Λ_emp ≤ 1.1)

`rip/prime_pool/` (README; `results/results_tables.md`). Delegated run, B = 3·10³ … 10⁷; the lead re-ran
`ppsanity.py`, and all checks pass. Measured F = Σ_z |X₁X₂Q|² against the exact diagonal D, and against Dcop,
which drops rows killed by small primes of the coefficient support [numerical].

- **Nothing happens at either face line.**
  - F/Dcop = 1.00 ± 0.02 out to total length T = 2m + s = 1.25, beyond both m₁ + m₂ + 1.82s = 1 and
    m₁ + m₂ + 2s = 1.
  - All 140 log-slopes d ln(F/Dcop)/d ln B over B = 5·10⁴ … 10⁷ are within 2σ of 0 (max 0.005).
  - Empirical bound: Λ_emp < 1.1 / 0.9 / 0.7 / 0.4 for m = 0.25 / 0.30 / 0.35 / 0.40.
- **Weight variants.** These are behaviour classes, not scenarios to price.
  - Zero-aligned (t = 0, 5, 20), random-phase and smooth-weight pools: all at the diagonal. a_P = 1 and t = 5
    show only a slight deficit switching on at T ≈ 1.
  - Patterson-aligned pools (conjugate sextic Gauss sums, the Θ₆ extremal) on their own: a *bounded* +2–8% plateau
    once P₀² > B, a function of P₀²/B only, not growing with B. Its onset reads Λ ≈ 1.9 (2% threshold) or 1.6 (4%).
    The plain factors do not add to it.
- **Worst case over all pool weights** (sup probe): random-matrix law (1 + √(n/R_eff))². Λ_adv = 1.07 / 0.61 /
  0.41 / 0.29 for m = 0 / 0.25 / 0.35 / 0.40. This is an upper envelope for every zero-forced class.
- **Caveats.**
  - The plain sums have only 4–253 terms and the pools ≤ 186 prime ideals.
  - Zero-forced *row* selection is not reproduced; only the sup probe covers row-dependent alignment.
  - Single-prime pools only.

**Reading [derived].** D1's statement is numerically true with a huge margin: the face behaves like the ideal
face (Λ ≈ 1). The only Λ ≈ 2 feature is the Patterson-aligned pool's bounded few-percent bias, which is exactly
what the D–R corrected sieve subtracts as a main term. The obstruction to D1, as for D2 and D4, is proof
technology:
- (L2), Heath-Brown–Patterson twisted by quadratic characters, has its premise confirmed in `rip/l2_probe/`;
- (L3) is phase survival.

## 2026-10-30 · Attempting D1's proofs: (L2) is classical in averaged form; (L3) reduces to the K-wall or to a plain eighth moment

**(L2), corrected [derived].**
- As first stated, (L2) asked for Heath-Brown–Patterson for Σ_P g̃₃(P)(k/P)₂ uniformly in N(k) ≤ Z^{0.8}. In D1's
  dual, the twist r = r(n, n′, h, P′) has N(r) ≈ Z^{1.7}, while the pool has length P₀ = Z^{0.03–0.14}.
  Heath-Brown–Patterson's Type-I sums (the twisted Kubota series by convexity) give nothing once the conductor
  far exceeds the length, and Burgess needs length ≥ conductor^{1/4}. Individual prime sums are out of reach.
- What a dispersion argument needs is the *average* over twists after Cauchy–Schwarz. That is classical:
  Huxley's large sieve over Q(ω), in dual form with the primes P as moduli, Σ_r |Σ_P a_P (r/P)₆|² ≪
  (#r + P₀²)‖a‖². Unimodular Gauss-sum weights g̃₆(P) are absorbed into a_P.
- So the averaged (L2) holds unconditionally, with square-root cancellation on average, which is better than
  Heath-Brown–Patterson's 5/6.

**(L3) reduction 1, row splitting [Lean, built; `lean/arvi_primeface/RowSplit.lean`].**
- Split the rows by |Q(z)|² ≈ ‖a‖²P₀^σ.
- Classes with σ > 1/2 are exactly PR 93's selected norm at slope σ. At its fixed point max(μ, 1 − σ + σμ),
  every class is harmless on the *ideal* face μ + s ≤ 1 (`class_le_of_fixPt`).
- Classes with σ ≤ 1/2 are the K-wall. With only the full-family bound they carry the excess σs ≤ s/2
  (`low_class_excess_le`).
- So **every row-splitting proof of D1 is the K-wall**. With the K-wall's fixed point at all slopes, the face
  comes out at Λ = 1 (`ideal_face_of_fixPt`). Without it, one is back at PR #97's leaf, with K = 1/2 and Λ = 2.
- This corrects fresh look 2: D1 bypasses the K-wall only through a proof that does not split rows.

**(L3) reduction 2, dispersion without row splitting [derived].**
- Expand |Q|²:
  F = ‖a‖²Σ_z Φ|A|² + Σ_{P≠P′} a_P ā_{P′} T(PP′⁵), with T(h) = Σ_z Φ|A(z)|²ψ_h(z).
- For distinct ordered pairs, the characters ψ_{PP′⁵} = (·/P)₆(·/P′)₆⁵ are distinct primitive characters of
  conductor PP′. So Huxley's large sieve over these twists gives
  Σ_{P≠P′}|T(PP′⁵)|² ≪ (Z + P₀⁴)·Σ_z Φ²|A(z)|⁴, and by Cauchy–Schwarz
  **F ≤ ‖a‖²·[Σ_z Φ|A|² + C·√((Z + P₀⁴)·Σ_z Φ²|A|⁴)]** for every pool with P₀⁴ ≤ Z.
- With the plain fourth moment diagonal (μ ≤ 1) and a plain **eighth** moment at Lindelöf-on-average strength,
  Σ_z|A|⁴ ≪ Z^{1+ε}‖c‖⁴, this gives F ≪ Z^{1+ε}‖c‖²‖a‖² with no face condition at all. That matches the
  prime-pool numerics (F/D ≈ 1 out to total length 1.25).
- The eighth moment is the D4-type statement (thin-family moments of plain products past the row count without
  an N-term). It is numerically true (D4 probes) and open. The general sextic sieve gives only Z^{1.883} at
  2μ = 1.86, and trivial pointwise bounds lose N^{1/2}.
- Hölder splits (Σ|A|^{2p′})^{1/p′}(Σ|Q|^{2p})^{1/p} lose N^{1/p} or worse: checked, no gain over trivial.

**Status.**
- D1 is not independent of the walls. Its two natural proofs reduce to the K-wall (row splitting) or to the
  plain eighth moment (dispersion plus Huxley).
- Both are instances of the structured large sieve for theta-uncorrelated vectors, which every numerical
  probe supports.
- The averaged (L2) is classical; the (L3) part is open in both forms.
- Next proof targets, in order of size:
  - the plain eighth moment past the row count;
  - the K-wall dilution;
  - a dispersion in which the plain sums are reflected before Cauchy–Schwarz (D–R §9-style, with the
    plain-variable theta main terms subtracted).

## 2026-10-30 · D1 dispersion in Lean, and the plain eighth moment is numerically Lindelöf

**Lean [built; `lean/arvi_primeface/Dispersion.lean`, standard axioms, ≈ 8 s].**
- `dispersion`: for row weights b ≥ 0, a pool Q = Σ_P a_Pψ_P with unimodular ψ_P, and a large sieve over the
  twists ψ_P conj ψ_{P′} (P ≠ P′) with constant Δ:
  Σ_z b|Q|² ≤ ‖a‖²·(Σ_z b + √(Δ Σ_z b²)).
- The proof: expansion (`pool_expand`); the diagonal equals Σ b by unimodularity; the off-diagonal by
  Cauchy–Schwarz over the pairs and the large-sieve hypothesis.
- For D1, b = Φ|A|² and Δ ≪ Z + P₀⁴ (Huxley over Q(ω), classical, left as a hypothesis).

**Numerics [`rip/eighth/`].**
- κ₈ = mean|X₁X₂|⁴/(mean|X₁X₂|²)² is 5–7.4 for μ = 0.6–1.0 and B = 3·10⁴ … 3·10⁵, against N-term sizes up to 10⁶.
- It grows slowly with B, below the random multiplicative model past μ ≈ 0.8.

**Consequence [derived].** D1 now rests on exactly two inputs:
- Huxley's large sieve (classical);
- the plain eighth moment Σ_z|X₁X₂|⁴ ≪ Z^{1+ε}‖c‖⁴ for total length ≤ Z (numerically true; open).

The face would then be diagonal for every pool with P₀⁴ ≤ Z and no face condition, worth more than the
Λ = 5/3 price (−4.9e-4). The eighth moment is the same kind of statement as D4: Lindelöf on average for plain
products past the row count in a thin family, where the general sextic sieve loses Z^{0.88}.

## 2026-10-30 · Literature check for the plain eighth moment (D1's remaining input)

[read: web search, abstracts only]
- **Gao–Zhao** (arXiv 2508.14534): shifted moments of cubic and quartic Dirichlet L-functions, with applications
  to moments of cubic and quartic character sums. These are Lindelöf on average with no N-term for thin families,
  but **under GRH**. Their earlier mean values of cubic and quartic characters (arXiv 1902.10987) reach moduli
  only up to the length of the sum.
- **The bootstrap's half-plane does not replace GRH here.** Shifting Perron to Re s = θ + ε (to the right of all
  zeros, where Soundararajan-type bounds work) loses N^{k(2θ−1)} ≈ N^{0.75k} in the 2k-th moment of a character
  sum. This is the pointwise-bootstrap dead end again.
- **Sextic large sieves in the literature** (moments and one-level density of sextic Hecke L-functions; de Faveri)
  are general-vector bounds with the Gauss-bias excess. None is a structured or thin-family Lindelöf statement.

**Verdict.** The plain eighth moment past the row count is not in the literature unconditionally. With GRH it
would follow from Gao–Zhao-type methods; for us it remains the open core, now the cleanest single target behind
D1.

## 2026-10-30 · Upstream PR #99 takes the engineering limit (θ = 0.8733819666)

[read: upstream refs/pull/99/head, submission `2026-10-30-positive-reserve-selected-gap`]
- Joseph Bebel's #99 proves θ = 8733819666133/10¹³ = 0.8733819666. That is 1.8e-7 below #98 and 3.1e-7 below our
  bank.
- Mechanism (from its description): "a reserve-parametric fourth-power seed and a selected-energy adapter for every
  fixed positive gap above one half". That is the selected leaf at K = 1/2 + gap for every gap > 0, i.e. the
  engineering limit K → 1/2⁺ (fresh look 2's architecture limit 0.87338197).
- So the engineering frontier is now fully taken upstream, and any further gain must come from the K-wall or
  another new-math input (the master conjecture, frontier README).
- New bar against the best open PR: θ ≤ 0.8733319666.

## 2026-10-30 · Prime versus composite rows: a coprimality-mask effect (fresh look; correction to probe C)

Report: `rip/moments_probe/PRIMEROWS.md` (scripts `primerows_*.py`, logs `logsP/`; raw runs in
`$SCRATCH/logsP_npz`, regenerable with fixed seeds).

**Mechanism [numerical + derived].**
- **The deficit is the functional equation with the full conductor.**
  - For primary n, χ_u(n) = χ_u(−1)λ_u(n), where λ_u is a Hecke character of conductor u·(1−ω)^c. The exponent c
    is fixed by k = ((N(u) − 1)/6) mod 6 (c = 0 if k = 0, c = 1 if k = 3, c = 2 otherwise), so the dual length is
    3^c·N(u)/N.
  - Poisson over Z[ω] reproduces |S_u| from its dual to 1.8·10⁻³.
  - The deficit is ordered by c (at m = 0.45, B = 1.6·10⁶: ratio 0.79 / 0.82 / 1.00 for c = 0 / 1 / 2).
  - From m ≈ 0.6 on, the random model applied to the dual sum matches the actual M6 to 6–13%.
- **The prime/composite gap comes from the coprimality mask, not from prime moduli.**
  - Composite rows usually contain a small prime q (7 or 13 in 46% of them). Masking q lowers the multiplicative
    surrogate's normalized sixth moment (asymptotically by (1 + 4/q + 1/q²)/(1 − 1/q)²). The actual sum follows its
    shorter dual for m > 1/2, where the mask costs only ≈ 0.90.
  - Decisive tests: a mask transplant (prime rows given composite rows' masks move to the composite ratio: shift
    +0.037 ± 0.007 in log at m = 0.5, positive at 22 of 23 points with m ≥ 0.45), and an artificial mask at π₇
    (it reproduces the genuine π₇·π′ rows within 0.06 ± 0.07).

**Corrections to probe C.**
- The 4-replica surrogate for the prime class at B = 3·10⁵ was 8–12% high for m ≥ 0.5. The prime ratios there are
  0.775 / 0.750 / 0.595, not 0.719 / 0.693 / 0.530.
- There is no prime/composite gap for m ≤ 0.45.

**Open.**
- A residual −0.09 ± 0.03 at m = 0.6.
- The dip at exactly m = 1/2 (below both the direct and the dual random-model predictions) has no analytic account
  yet. A CFKRS-type formula was not attempted.

**Reading for the program [derived].**
- Nothing structural about prime moduli, so no "prime-row dictionary" lever.
- The c-ordering confirms that the only structure in plain-sum moments is Poisson self-duality with the exact
  conductor, including the ramified factor at 1 − ω. That is the same statement as the reflection rule.

## 2026-10-30 · Foundations audit: decision-driving facts now in Lean

Arvi asked which "established" facts behind decisions were not formal. Status after this pass:

| fact (decision it drove) | status |
|---|---|
| Random dictionaries do have RIP beyond √ | Lean: `arvi_rip/RandomRIP.lean` |
| D1 by row splitting is the K-wall | Lean: `arvi_primeface/RowSplit.lean` |
| D1 by dispersion needs only the plain eighth moment (plus Huxley) | Lean: `arvi_primeface/Dispersion.lean` (Huxley as a hypothesis) |
| Hölder and interpolation routes lose against the trivial bound; the pointwise bootstrap rule loses (2β−1−δ)m | **Lean**: `arvi_primeface/Dismissed.lean` |
| Label line υ = 1/2 is optimal at the binding (T96 idea closed) | **Lean**: `arvi_primeface/Exponents.lean` (`label_line_optimal`, `label_pointwise_worse`) |
| D–R prime vectors are diagonal exactly to B = A^{3/5}, slot cost 5/3 (target 0, D1 numerology) | **Lean**, the threshold arithmetic only: `dr_diagonal_iff` (D–R's propositions themselves are external) |
| K-wall corner needs γ ≤ δ(1 − X_eff) | **Lean**: `kwall_corner` |
| Quadratic Davenport–Hasse (D1's first reduction) | Lean: `arvi_primeface/Duplication.lean` |
| K-wall barrier and its exact reduction to dilution | Lean: `arvi_kwall/` |

**Still not formal (with reasons).**
- **The pricing models** (Δθ as a function of Λ, the slot costs, the long slope, e): float re-implementations of the
  Lean certificate chains. Certifying a price means building the chain, which is done only for submissions.
- **External theorems used as inputs:** de Faveri's Θ₆, Huxley's large sieve (an explicit hypothesis where used),
  matrix Chernoff (used only as evidence for random row sets), Heath-Brown–Patterson, and D–R's propositions.
- **Numerical findings** (Marchenko–Pastur, the moments, the prime pool, the prime rows) are tagged [numerical]
  and are not used as proof inputs anywhere.

## 2026-10-30 · RIP program (4): a dictionary of different atoms — wide random features with RIP by counting measure

**Arvi's direction.** Build a dictionary on different principles, from atoms that are not localized in
frequency (ReLU features on a sphere have a wide arc-cosine kernel). Show its RIP by exhibiting a positive
measure of good operators, and tie it to the sextic rows with coherence bounds.

**Construction.**
- A degree-ℓ feature is a product of ℓ Rademacher projections, feat_w(x) = ∏_{i<ℓ} ⟨w_i, x⟩ with w_i ∈ {±1}^d.
- These are the polynomial (Maclaurin) pieces of wide dot-product kernels. ReLU's kernel is a positive mixture
  of them: Σ b_ℓ t^ℓ, with b₀ = 1/2π, b₁ = 1/4 and b₂ = 1/4π.
- The data are the rows' unit vectors x_z = χ_z|_sources/‖·‖. Any separated data would do.

**Formal [Lean: `lean/arvi_rip/WideFeatures.lean`, built, about 13 s; only propext, Classical.choice and Quot.sound].**
- `sum_feat_mul_conj`: averaged over all parameters, the features reproduce ⟨x, y⟩^ℓ exactly. So coherence μ
  becomes μ^ℓ.
- `sum_pi_single`, `sum_pi_pair_eq_zero`, `sum_norm_sq_sum_pi` and `card_filter_le_sum_div`: variance over
  independent draws, and Chebyshev, in counting form.
- **`exists_wide_rip`.** Assume unit data x_z (N points) with pairwise coherence ≤ μ and ℓ¹ norms ≤ C, and
  4N²C^{4ℓ} < mε². Then a positive counting measure of m-feature operators exists (the bad choices are fewer
  than all choices). Its feature vectors satisfy
  |‖Σ_{z∈S} c_z u_z‖² − ‖c‖²| ≤ (ε + (μ^ℓ + ε)(|S| − 1))‖c‖² on every support S.
  So the order is ≈ μ^{−ℓ}, against ≈ μ^{−1} for coherence certificates on the raw data
  (`coherence_order_barrier`).
- `count_le_of_rip`: RIP on S plus |⟪b, u_z⟫| ≥ τ on S gives |S|τ² ≤ (1 + δ)‖b‖².
- `mixture_ge_min`: a mixture of degrees never certifies a smaller count than its best single degree.

**Numerics [`rip/wide/wide_probe.py`, log `wide_B3000_L3000.log`; B = L = 3000, R = 848 rows, S = 778 sources].**
- Coherence: the maximum over all pairs is 4.0/√S. Within slot-selected sets it is 3.1–3.5/√S. Slot selection
  does not inflate it at this scale.
- Slot-selected W of 212 rows (density 0.25). The raw √-barrier is 1/μ_W ≈ 8 rows.

  | kernel | λ range on W |
  |---|---|
  | raw Gram (degree 1) | [0.23, 2.32] (Marchenko–Pastur, not RIP) |
  | degree 2 | [0.94, 1.065] |
  | degree 3 | [0.996, 1.004] |
  | ReLU high-pass, normalized | [0.97, 1.13] |

  The values are the same on random W. So the wide dictionary has RIP far beyond √ on the actual adversarial
  row sets. With m = 3000 sampled features the degree-2 operator has λ in [0.71, 1.33]: sampling noise at this
  m, which shrinks as 1/√m.

**What it does and does not yet buy [derived].**
- The zero supplies a *degree-1* statistic: |⟨a, x_z⟩| ≥ v. Through degree ℓ the count certificate is
  λ_max(ρ_W^{∘ℓ})/v^{2ℓ}, and mixtures cannot beat the best degree (`mixture_ge_min`).
- At the measured large values (v ≈ 1.4–1.9/√S), degrees 2 and 3 certify 10²–10⁵ times more than degree 1
  (log, last block).
- The degree ≥ 2 part was never the obstruction. Θ₆(2x) = 2x for x ≥ 1, so the full-family sieve already makes
  ρ_W^{∘2} diagonal up to B^ε on every W. At the K-wall corner x = 0.96 the excess is 0.013.
- The K-wall therefore sits entirely in the degree-1 part: the linear detector.
- This first construction is correct and does what random features do, but it acts on a part we already control.

**What the next construction has to do (open).** The randomness must reach the degree-1 part. Any dictionary
whose atoms are functions of the row's character vector alone has the sextic Gram as its degree-1 part. Two ways
out remain:
- (a) atoms that use other data of the row (Frobenius data outside the sources, the Archimedean factor n^{−it} in
  (z, t) space, Gauss sums);
- (b) a different detection step, in which a zero forces higher-degree statistics with tensor norms, e.g. products
  of *different* detectors.

A fresh look on exactly this question: entry "RIP (4) fresh look" below (`rip/wide/FRESH_LOOK.md`).

**Product designs, formally [Lean: `lean/arvi_rip/TensorAmplify.lean`].**
- `tensor_ge_amplified`: pairing the rows with other data, x_z ⊗ y_z, and detecting with a ⊗ e is amplification
  by w_z = ⟨e, y_z⟩.
- What is new is only the certificate. Gershgorin for the product needs pointwise coherence μ_xμ_y on pairs
  inside W.
- With square-root pointwise coherence of both factors, this rule would beat the K-wall. At δ = 0.45 the
  exponent is (1 − 2δ)(1 − δ) ≈ 0.05 against the closure's 1/6.
- Unconditionally, Burgess gives μ_x = B^{−1/8} for the plain sums at L = B, and nothing pointwise is known for
  short prime slots.
- So for product designs, the "bounded coherence" half is the binding input: a coherence bound for pairs inside
  the selected set.

## 2026-10-30 · Plain eighth moment: proof strategies (fresh look; agent-derived, not formal)

Source: `rip/eighth/STRATEGIES.md`, with `strat_exponents.py` and `strat_tail.py`. Target: Σ_z|X₁X₂|⁴ ≪ Z^{1+2η}N²
with plain sums of total length Z^μ. D1 by dispersion needs η = 0 on μ ∈ [0.75, 0.87].

- **Prop. 0 [checked: nonnegative sum].** The target forces |X₁X₂(z)|² ≤ Z^{1/2+η}N on every row. So the recorded
  "max/mean ≤ Z^{1/2}" obstacle constrains every proof, not just Hölder's. With the zero-free half-plane
  κ = 0.747 this pointwise bound holds only for μ ≤ 0.670. At μ = 1 the target is the eighth moment of L(½, χ_z),
  which implies |L(½, χ_z)| ≪ Z^{1/8}, beyond Weyl.
- **S1, sorting rows by their rightmost zero [agent-derived].**
  - Uses Littlewood's local Lindelöf bound, the family zero count and the plain fourth moment.
  - Proves the target for μ ≤ 1/3 (de Faveri: 1/4).
  - Gives η(0.93) = 0.340 (de Faveri: 0.442; Hölder: 0.347).
- **Barrier [agent-derived, model].**
  - The round-9 lattice adversary at spacing μ/2 meets every current input and has η = 0.338 at μ = 0.93.
  - It has η > 0 for every μ > 1/2, even with counts at density-hypothesis strength.
  - So no combination of today's inputs (used through lengths only) proves η = 0 past μ = 1/2.
- **Consequence.** D1 by dispersion needs a new kind of input: a joint plain–zero count beyond the density
  hypothesis. The agent recommends deprioritizing D1-by-dispersion. Agreed until such an input appears.
- **Next lemmas, if pursued.**
  - P₄: Patterson asymptotics over 4-fold plain products. This is the S2 recursion's missing piece and needs
    type-A₄ multiple Dirichlet series.
  - Or the D4 sixth moment with ε₆ ≤ 0.153 (S3).

## 2026-10-30 · Replacing M: the large sieve off the theta span V

**Arvi's question.** We do not need RIP for the character matrix M. We need *some* operator that still lets the
proof go through and has the RIP we need. Think of it coordinate-free.

**Coordinate-free reduction [Lean: `lean/arvi_kwall/FlatDilution.lean`, `norm_restrict_le`, standard axioms].**
- Write the row vector y = Ma as Σ_j c_j θ_j + r, with k flat row vectors (|θ_j(z)|² ≤ c/R). Then on every row
  set W: ‖y|_W‖ ≤ √(k c |W|/R)·‖c‖ + ‖r‖, with the last norm over all rows.
- With θ_j = conj G(z,1)·profile, the Gauss sums of the squarefree moduli, which are unimodular and hence flat,
  this gives
  Σ_{z∈W} |⟨a, χ_z⟩|² ≤ (√(k c |W|/R)·‖P_V M‖ + ‖(I − P_V)M‖)²·‖a‖².
- So M′ = (I − P_V)M is the replacement operator.
  - The theta excess is diluted by |W|/R on every thin row set, for free.
  - What remains is a **full-family** bound for M′. No thin-set RIP and no condition on the detector are needed.
- Target: **(LS off V)** ‖(I − P_V)M‖² ≲ (R + S)·B^ε at the balanced point, for a low-dimensional V. With it, the
  K-wall falls (`arvi_kwall/Dilution.lean`: dilution at δ ≥ 1/6 gives the fixed point).

**What V is [read: Xu–Sang, arXiv 2610.17675 (Oct 2026); Dunn–Radziwiłł 2109.07463].**
- Xu–Sang prove a lower bound matching de Faveri's sextic sieve, A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6} (at
  balance Q^{7/6}). The excess is attained by Gauss-sum vectors on the moduli side,
  λ_b ∝ W(N b/L)(N b/L)^{−1/2}·conj G(b,1).
- Their Prop. 3.1: the energy of these vectors is
  C·I(U)²·q^{5/6}L^{−2/3}·Ω(d, e) + O((q/L)(1 + X^{1/12}) + D), with I(U) = ∫U(t)t^{−5/6}dt.
  - The main term is a **rank-one** form in the radial profile U, with one direction per twist class (d, e)
    and weights decaying in d.
  - Profiles with I(U) = 0 have only the error term.
- This is the sextic analogue of Dunn–Radziwiłł's corrected cubic sieve: diagonal plus the rank-one bias
  A^{2/3}|Σ_b β_b N(b)^{−1/6}|² plus error, proved up to B = A^{3/5} for their vector class (`frontier/DR_PRIME_SIEVE.md`).
- So V = span of the theta row vectors conj G(z,1)·χ_z(u)·(N z/B)^{−5/6}·(N z/B)^{−1/2}, over a few small twists.
  It is low-dimensional and flat.

**Numerics [`rip/theta/theta_span.py`, `theta_profile.py`; logs `theta_B*.log`].** Here r = ‖Eᵀc‖²/(S‖c‖²),
and the baseline is a random-phase vector with the same profile.

| B = L | rows R / sources S | theta r (conj G·χ(u₀)) | random-phase r | excess | top singular²/S | off V (rank 1) | MP edge |
|---|---|---|---|---|---|---|---|
| 3000 | 848 / 778 | 1.093 | 0.943 ± 0.025 | +16% (6 sd) | 4.061 | 4.056 | 4.178 |
| 10000 | 2816 / 2610 | 1.133 | 0.958 ± 0.016 | +18% (11 sd) | 4.261 | 4.261 | 4.156 |
| 30000 | 8474 / 7768 | 1.177 | 0.949 ± 0.010 | +24% (23 sd) | 4.550 | 4.550 | 4.180 |

- **The excess is rank one in the profile (B = 10⁴, `theta_profile.py`).**

  | profile | I(U) | excess over random phases |
  |---|---|---|
  | t^{−5/6} | ≠ 0 | +18% (9.7 sd) |
  | flat | ≠ 0 | +20% (13 sd) |
  | linear, centred | 0 | −4.8% (−4.2 sd) |
  | cosine, centred | 0 | +3.0% (1.9 sd) |

  This is Xu–Sang's main-term structure, visible at small size.
- Conjugation and twist matter. conj G variants sit +5–24% above baseline; G variants sit −10–0% below.
- Twisted theta vectors conj G(z)·χ_z(m)·χ_z(u) for small m also carry excess, +11–13% at B = 10⁴, decaying with
  N(m). These are Xu–Sang's twist classes (d, e) with weights Ω(d, e). Plain small-modulus vectors χ_z(m) on
  their own carry none (r within ±4% of baseline).
- **A second structure at the top of the spectrum.**
  - At B = 3·10⁴ the top singular²/S is 4.55, against the Marchenko–Pastur edge 4.18. This is +9%, far beyond
    Tracy–Widom size. At B = 10⁴ it is +2.5%.
  - It is not theta: overlap with the theta direction is ≤ 0.01, and with the 420-dimensional twisted-theta span
    it sits at the random level.
  - It overlaps the block span: the 420 row vectors χ_z(m)·χ_z(u), N(m) ≤ 100, i.e. small-modulus sextic
    characters on the rows (#96's GS1 blocks).
    - At B = 10⁴ the top singular vector has 35% of its mass there, against 15% at random.
    - The block span's compressed top eigenvalue is 2.57, against 1.86 for a random span of the same dimension.
    - The top block combination overlaps the top singular vector at 0.50.
  - At B = 3·10⁴ the top singular vector correlates with single χ_z(m) (N(m) = 4, 7) at about 0.1, ten times the
    random level. Its right vector leans to small sources (corr(|v|², N x) = −0.30).
  - At B = 3·10⁴ the top singular vector has 26% of its mass in the block span (5% at random). The block span's
    compressed top eigenvalue is 2.46, against 1.43 for a random span. That is +72%, up from +38% at 10⁴, so the
    structure grows. The top block combination is a near-uniform sum Σ_m χ_z(m) over small split primes m of
    norm 7–43: a short prime-pool row vector.
  - Block vectors are flat too (|χ_z(m)| = 1 on coprime rows), so they also dilute under `norm_restrict_le`.
    V = theta span ⊕ block span keeps the reduction intact, at dimension k = O(#small m).
- The theta direction is *not* the top of the spectrum. Its overlap with the top singular vectors is ≤ 0.06, and
  removing it (or 12 twist variants) changes the top singular value by < 1.5%. At these sizes the top is the
  Marchenko–Pastur bulk edge. The excess constant is small: the B^{1/6} growth (+16% → +18%) means the theta
  direction would reach the bulk edge only near B ~ 10¹⁰⁺.
- **Detectors.** Their projections onto the source-side theta direction E^T c/‖·‖ are 1.5–3× the random level,
  and fall with B. At B = 10⁴: plain 0.038, smooth plain 0.060, prime pool 0.029, random 1/√S = 0.020. The
  plain sum's theta part is the Patterson bias, ~L^{−1/6} relative, and contributes only A^{5/6}·‖a‖², below the
  diagonal.

**Why (LS off V) is hard: the balanced point is self-dual [derived, heuristic].**
- Poisson in the moduli turns the source Gram into
  S(x, x′) ≈ (B/q)·G(x)·conj G(x′)·c(x, x′)·Σ_k conj χ_k(x)·χ_k(x′)·ŵ(kB/q), with q ≈ N(xx′).
  This is a dual large sieve over moduli k ≲ L²/B, applied to the Gauss-twisted vector a·G.
- At L = B the dual family has the same size B. The balanced problem maps to itself (the fixed point of the
  Heath-Brown/de Faveri recursion), conjugated by the unitary D_G.
- **Theta part.** The dual moduli k = k₀j⁶ act like χ_{k₀} on the sources. Summing ŵ(k₀j⁶B/q) over j gives
  ≈ (q/(k₀B))^{1/6}, which is separable in x and x′. That is one rank-one term per small k₀, with weight
  N(k₀)^{−1/6}: the theta main term above (the eighth-moment fresh look also traced de Faveri's Z^{5/6}L^{1/3} to
  these dual rows).
- **Off V.** The generic dual rows give a balanced sieve for a·G again, so the recursion returns to itself.
- A proof has to break the self-duality: use structure of the twisted class {a·G : a ⊥ V}.
  - At the second level the relevant bias is G·G = G². At primes, G₆² = J̃·G₃ (g(χ)² = J(χ,χ)g(χ²)): a Jacobi-sum
    Hecke character times a **cubic** Gauss sum.
  - So the sextic recursion couples to the cubic theta function at its second step [heuristic]. Davenport–Hasse
    for the quadratic factor is in Lean (`arvi_primeface/Duplication.lean`).
- **Structural route.** V is the residual spectrum (the theta function) of the metaplectic 6-fold cover.
  "Off V" is the cuspidal plus continuous spectrum. (LS off V) would follow from a Deshouillers–Iwaniec-type
  spectral large sieve for metaplectic cusp forms. That is new math, with a clear statement.

**Status.**
- Reduction: formal.
- V: theta part identified from the literature and confirmed numerically: rank one in the profile, flat, growing
  like B^{1/6} with a small constant. A second, block-type part (small-modulus row characters, flat) shows up at
  the top of the spectrum at B = 3·10⁴. Its mechanism is still open (logs `theta_top*.log`, `theta_topspan*.log`).
- (LS off V): open, and the single statement the K-wall now needs.
- **Correction (entry "Where the theta excess lives" below).** V cannot be low-dimensional. Every twist m with
  N(m) ≤ B^{1−6γ} carries its own excess, so the statement above with a few small twists is false asymptotically.
- Numerically it holds trivially at accessible sizes, where everything is Marchenko–Pastur.

## 2026-10-30 · RIP (4) fresh look: what a random dictionary transfers, and the centered fourth moment (M₄)

Agent report `rip/wide/FRESH_LOOK.md` (scripts `wide_tests.py`, `wide_tables.py`; results `wide_B*_s*.json`). The
certificate is in Lean; the rest is the agent's derivation. I re-checked the product inequality and the
diagonal-unitary step, not the Poisson/reciprocity factorization.

**How a random dictionary D can be tied to the sextic rows on W [agent-derived, elementary].**
- *Cross-coherence* (D incoherent with the rows) carries nothing. The standard basis has the minimal cross-coherence
  S^{−1/2} with every flat family, including one whose rows are all equal.
- *Factorization* M_W = A·Y_W with ‖A‖ ≤ c is the same as G_W ≼ c²·Y_W*Y_W (Douglas). For a model whose rows are
  independent given the slot data, Y's Gram concentrates at I + Λ_W, so this is the diluted-bias statement of RIP (1).
  The dual-frame bound of the previous entry is of this type (A = P_W Q^{−1/2}, Y = Q^{1/2}M). It is a
  reformulation, exact as Q → P_W, and useful only through the choice of Q.
- *Gram mixtures* E_ω M_ω M_ω* = G go the right way under Jensen (‖G_W‖ ≤ E‖M_{ω,W}‖²). But if the rows are
  independent across z, the off-diagonal Gram is the Gram of the mean rows, and the randomness drops out.
- *Products* never beat plain Gershgorin. With the detection cap |W|w² ≤ 1 + mμ_y,
  U_prod = (1 + mμ_xμ_y)/w² ≥ (m + 1)(1 + mμ_xμ_y)/(1 + mμ_y) ≥ 1 + mμ_x = U_plain, since the middle term decreases in
  μ_y. This sharpens `TensorAmplify`: the coherence that matters is the rows' own, inside W.
  [Lean: `lean/arvi_rip/ProductCertificate.lean`, `product_certificate_ge_plain`, with the detection cap from
  `bessel_of_gershgorin`.]
- *Row Gauss sums.* After Poisson in the moduli, the pair phase is g̃(z)·conj g̃(z′) times a reciprocity sign
  s(z, z′) (Hilbert symbols at 2 and 3, so O(1) classes). The g̃(z) form a diagonal unitary, which changes no
  restricted norm and no spectral moment on W. So Gauss sums add no randomness, and at L ≈ B the off-diagonal Gram
  on each class is ± its own dual: the reflection's self-duality as a matrix identity.

**What does transfer: a centered moment of fixed order [Lean: `lean/arvi_rip/FourthMoment.lean`].**
`fourth_moment_rip`: for any vectors u_z on a support S and any coefficients c,

  |‖Σ c_z u_z‖² − Σ |c_z|²‖u_z‖²| ≤ (tr O⁴)^{1/4}·Σ |c_z|²,

where O is the off-diagonal Gram on S and tr O⁴ = Σ_{z₁,z₃} |Σ_{z₂} O(z₁, z₂)O(z₂, z₃)|².
- In the random model tr O⁴ ≈ 2|S|³L² (unnormalized rows of length L), so the certificate is o(L) up to |S| ≈ L^{2/3}.
  In the K-wall, |W| = B^{1−δ}, so it covers every δ > 1/3: the whole barrier range of `arvi_kwall`.
- Lower orders: mean-square coherence (order 2) is exactly the √-barrier. Uncentered traces tr(G_W^p) ≤ C|W|L^p give
  γ = (1 − δ)/p and need p ≈ 35 to reach γ ≈ 0.015.

**The missing inequality (M₄) [conjecture].** For the slot-selected W at slope δ ∈ (1/3, 1/2) and L ≤ B^{1+o(1)},

  Σ_{z₁,z₃∈W} |Σ_{z₂∈W∖{z₁,z₃}} G(z₁, z₂)G(z₂, z₃)|² ≤ B^{4γ}L⁴.

- With `fourth_moment_rip` it gives ‖G_W‖ ≤ L(1 + B^γ), the selected norm the leaf needs (γ ≲ 0.015 at the corner).
- It splits into two parts:
  - (M₄a) row mean-square coherence on W, from the backtracking walks: Σ_{z′∈W} |G(z, z′)|² ≲ B^{2γ}L²|W|^{−1/2}.
  - (M₄b) the non-backtracking 4-cycles, which must cancel by B^{1/2−δ−γ} per step beyond square-root coherence:
    B^{0.13} in total at δ = 0.452.
- Square-root pointwise coherence (GRH strength) gives (M₄) only for δ ≥ 0.485.
- Fourier form: an order-4 multiplicative energy of Ŵ(r) = Σ_{z∈W} χ_z(r) on source ratios. This is the centered,
  order-4 analogue of Guth–Maynard's energy bound, in the multiplicative group, for a thin family with multiplying
  conductors. Nothing of that strength is known.
- The centered moment is not monotone in the row weights (G_W − D_W is indefinite). So the amplifier majorant
  1_W ≤ |T|^{2k}/V^{2k} cannot be inserted, which is why amplify–reflect (monotone, uncentered) stalls. A proof must
  use W itself.

**Numerics [numerical; B = 3000 and 12000; |W| = B^{0.42}–B^{0.67}; slots of 4–20 primes].**
- tr(E_W⁴) is 0.93–1.6 times 2|W|³/S². Sextic/model is 0.77–1.08: the excess is the slot spike, which the model
  shares.
- Row mean-square coherence on W has mean (0.96–1.24)·|W|/S and maximum ≤ 2|W|/S.
- The 4-cycles cancel to 0.08–1.4% of their no-cancellation size. They are model-like at B = 12000. They are about 2×
  the model (2–2.6σ) only with 14 slot primes at B = 3000.
- The top eigenvalue is within ±4% of the slot-conditioned multiplicative model. An i.i.d. random Schur multiplier
  sits 1.6–4% below every multiplicative model, so wide i.i.d. modulations are not a safe comparison class.
- Caveat: B ≤ 12000 cannot tell a B^{−0.13} saving from a constant, and these slots are wide (s ≈ 0.4–0.6, against
  0.03 at the corner).

**Design D1, the dictionary's role.** The slot-conditioned random multiplicative dictionary keeps the slot and
divisor values exact and draws every other prime value as an independent sixth root of unity per row. It satisfies
the fourth-moment bound in the model with margin B^{3δ−1}, by a walk count plus Markov in counting style. It is not
a step in the chain: it calibrates (M₄) and shows the certificate is sharp for model-typical W.

**Reading.**
- The transfer lemmas close the coherence-type ties. They do not close the factorization (dual-frame) route, which is
  a reformulation. Whether some Q chosen without knowing W gives λ_max(P_W Q^{−1} P_W)·λ_max(M*QM) below the closure
  is open.
- The K-wall now has two concrete sufficient statements: (LS off V) for the full family (previous entry), or (M₄) on
  W. Both sit at the self-dual point L = B, where Poisson maps each to itself.

## 2026-10-30 · Where the theta excess lives: one Poisson spike per twist, so V is not low-dimensional (correction)

**Numerics [`rip/theta/theta_twists.py`, `theta_powers.py`; logs `theta_twists_B30000.log`, `theta_powers_B30000.log`].**
At B = L = 3·10⁴ (R = 8474 rows, S = 7768 sources), r = ‖Eᵀc‖²/(S‖c‖²), against random phases with the same profile
(r = 0.946 ± 0.012).

- **Only conj G carries an excess** (range over the six unit twists):

  | row vector | r |
  |---|---|
  | plain | 0.85–0.93 (a deficit) |
  | conj G | 1.16–1.18 |
  | G | 0.93–0.97 |
  | conj G², G², conj G³ | 0.90–0.98 |

  The higher powers carry angular Hecke twists (Davenport–Hasse: g(χ)² = J(χ, χ)·g(χ²)). These kill the
  Patterson pole.
- **Twisted thetas conj G·χ_z(u)·χ_z(m)**, averaged over the six units, against random phases with the same twist.
  There are 200 twists m in 16 log bins; the per-bin noise is ≈ 0.003.

  | N(m) | excess |
  |---|---|
  | 1 (untwisted) | +0.221 |
  | 7–34 | +0.093 to +0.105 |
  | 34–2200 | +0.084 ± 0.005, flat |
  | 2200–6250 | +0.067, +0.049 |
  | 6250–30000 | +0.028, +0.010, −0.004 |

  Conjugate twists conj G·conj χ_z(m) and plain twists χ_z(m) show none (within ±0.01). Over 2.5 decades the
  excess does not decay like a power of N(m). It is a constant per twist, a little higher for the smallest twists,
  and it ends near N(m) ≈ H = B²/L.

**Mechanism [derived; matches the numbers].**
- Poisson in the sources writes the off-diagonal row Gram at length L as a Gauss-conjugated Gram of the dual
  dictionary {χ̄_z(h) : h ≲ H = B²/L}, up to bounded sign blocks (`rip/wide/FRESH_LOOK.md` §1.5).
- The dual frequencies h = m·j⁶ all act on the rows as the same atom χ̄(m). So atom m has multiplicity
  μ_m = #{j : N(m)N(j)⁶ ≲ H}, weighted by the dual cutoff.
- conj G·χ(m) maps exactly onto atom m, and each aligned copy adds a fixed amount: +0.084 at this size.
- m = 1 has three copies, j ∈ {1, √−3, 2}, with N(j)⁶ = 1, 729, 4096 against H = 3·10⁴. That is about 2.6 copies
  after the cutoff, so 0.221 ≈ 2.6 × 0.084.
- Twists with N(m) ≲ 34 keep part of the √−3 copy. Twists near H lose even the j = 1 copy.
- Asymptotically μ_m ≈ c·(H/N(m))^{1/6}. At length X = B^x the m = 1 spike has norm (X/B)·R·μ₁ = B^{1/3+5x/6},
  which is Θ₆'s term 1/3 + 5x/6. The other term, 5/6 + x/3, is the same spike from the Poisson in the rows
  [heuristic].
- So Θ₆'s excess is the spikes of repeated dual atoms. At L = B, twist m carries excess ≈ (B/N(m))^{1/6}.

**Correction to "Replacing M".**
- That entry took V to be a few small twists and called (LS off V) for such a V the single statement the K-wall
  needs. Asymptotically that statement is false:
  - every twist with N(m) ≤ B^{1−6γ} keeps an excess ≥ B^γ;
  - the twists are nearly orthogonal, so removing B^{o(1)} of them leaves the rest.
- The right V is span{conj G·χ(m) : N(m) ≤ B^{1−6γ}}, of dimension ≈ B^{1−6γ}.
  - Then `norm_restrict_le` gives nothing for an adversarial detector, since k·c·|W|/R ≈ B^{1−6γ−δ} ≫ 1.
  - Its weighted form needs the selected norm of the twist dictionary at lengths X ≤ H/729 with weights
    (H/X)^{1/6}.
  - The amplify–reflect closure n*(x) = 7/6 − δ(1 − x) supplies that only for twist lengths log_B X ≤ 0.52
    (δ = 0.48, γ = 0.015). Longer twists are copies of the core problem at length B/N(j)⁶.
- **What survives** [derived]:
  - (LS off V) for this high-dimensional V. It is weaker than the old statement, and still at the balanced point.
  - The detector condition ‖P_V M a‖² ≲ L·B^γ‖a‖² for the leaf's product vectors.
- With both, no thin-set argument is needed at all: ‖P_W M a‖ ≤ ‖P_V M a‖ + ‖(I − P_V)M‖·‖a‖.
- The detector condition is a large sieve over the twists at length B^{1−6γ} for the row vector conj G·profile·Ma.
  - It is unbalanced (dual length B^{1+6γ}), not at the self-dual point.
  - A detector aligns with a twist spike only through coefficients at norms ≲ (B^{1+6γ})^{1/5} ≈ B^{0.22}. Spread
    detectors like the leaf's should satisfy it [heuristic].
- **The K-wall itself is unchanged.** In this picture the spikes are flat rank-one pieces and dilute on thin W.
  What is left is the generic off-diagonal part at the self-dual point: the fresh look's (M₄).

## 2026-10-30 · The top of the sextic spectrum is a reciprocity effect on low-frequency rows (not theta, not the mask)

**Question.** The top singular value of the sextic matrix sat above the Marchenko–Pastur edge: +2.5% at B = 10⁴ and
+9% at 3·10⁴ (the "block structure"; mechanism open). Is it the coprimality mask, generic multiplicativity,
small-prime structure, or arithmetic?

**Numerics [`rip/theta/theta_mask.py`, `theta_models.py`, `theta_locate.py`, `theta_reciprocity.py`; logs
`theta_mask_B*.log`, `theta_models_B10000.log`, `theta_locate_B10000.log`, `theta_reciprocity_B10000.log`].**
The table gives the top singular value s²/S at B = L. Every model keeps E's zero pattern (shared primes) exactly.

| B | sextic | i.i.d. phases | RSYM | RMM | EXACT(30), EXACT(300) | RCHAR |
|---|---|---|---|---|---|---|
| 3000 | 4.061 | 3.926 | 3.923 | 3.936 | – | – |
| 10⁴ | 4.261 | 3.931–3.984 | 3.939–3.944 | 3.941–3.951 | 3.933–3.954 | 3.945–3.950 |
| 3·10⁴ | 4.550 | 3.987–3.995 | – | – | – | – |

The models:
- RSYM: an independent uniform symbol for every pair (row prime, source prime). This is bi-multiplicative, but has no
  reciprocity and no character structure.
- RMM: independent random multiplicative rows.
- EXACT(P₀): RMM with the true values at source primes of norm ≤ P₀, so each row is periodic in z modulo those primes.
- RCHAR: the true symbols, with each row prime's character conjugated at random. Every row is still a genuine
  character of the source mod z, but reciprocity fails.

**Reading.**
- **The right baseline is masked.** The mask lowers the random edge (4.14 → 3.95 at 10⁴). Against it the sextic top
  is +3.4%, +7.8% and +14% at 3·10³, 10⁴ and 3·10⁴, so the excess grows.
- **It is reciprocity.** Every model without reciprocity sits at the random level. That includes RCHAR, whose rows are
  all genuine characters.
- **Where it lives (10⁴).**
  - Projecting the rows off the block span {χ_z(m)χ_z(u) : N(m) ≤ 100} (dimension 156) brings the top to 3.926, the
    random level.
  - Off the twisted-theta span of the same dimension it only falls to 4.123, which is what any subspace that size
    removes (−0.12 for Marchenko–Pastur with 156 fewer rows).
  - So the excess lives on low-frequency row directions: characters of z of small conductor. The top combination is
    a short prime-pool row vector (`theta_topspan_B30000.log`).
- **The small-prime mass deficit of the top vectors is the mask.** Rows and sources divisible by 7, 13 or 19 carry
  less mass, and masked random vectors show the same.
- **Breaking reciprocity also removes most of the theta spike.** RCHAR's theta vectors, built from its own Gauss sums,
  have r = 0.98–1.01 against 0.943 ± 0.024 for random phases. The sextic's conj G has 1.09–1.13 against ≈ 0.95.

**Mechanism [derived].**
- In the Poisson dual the pair factor is χ_z(z′)·conj χ_{z′}(z).
- Under reciprocity it is a sign s(z, z′), constant on O(1) classes. The dual atoms then add coherently, giving the
  multiplicity spikes (theta) and a coherent low-frequency part.
- Without reciprocity it is a varying sixth root of unity. The dual is then Schur-multiplied by a random-like phase
  matrix, and both effects go away.

**Consequences.**
- Every deviation of the sextic sieve from random-matrix behaviour seen so far is a reciprocity (self-duality)
  effect: the theta spikes and the low-frequency top.
- Random models without reciprocity (RSYM, RMM) capture neither. On slot-selected W at B ≤ 12000 the fresh look still
  found the sextic within ±4% of RMM-S, so neither effect shows on W at accessible sizes.
- The low-frequency excess is flat (row characters are unimodular on coprime rows). At B = 10⁴ it spans
  dimension 150–450. On a random thin W it dilutes like the theta part.
- Whether it also dilutes on a slot-selected W is open. Its top combination is a short prime pool, the same kind of
  row vector as the slot that selects W.
- Its growth law is open: there are three points, and Θ₆ caps it at B^{1/6}.
- (LS off V) has to put this low-frequency span into V, next to the twisted thetas.

## 2026-10-30 · No anti-self-dual row class: the reciprocity sign is cancelled by χ_z(−1) [numerical; closes an idea]

**Idea.** At L = B, Poisson gives G_off(z, z′) ≈ s(z, z′)·χ_{z′}(−1)·g̃(z)·conj g̃(z′)·conj G_dual(z, z′), with
s(z, z′) = (z′/z)₆·conj (z/z′)₆. Suppose the effective sign s·χ_{z′}(−1) were −1 on every pair of a row class. Then
the class Gram would be anti-self-dual: its off-diagonal spectrum would be symmetric about 0, and G ≥ 0 would cap
its top at about twice the diagonal. That class would have no excess at the balanced point.

**Test [`rip/theta/theta_classes.py`, log `theta_classes_B30000.log`, B = L = 3·10⁴].** Rows are grouped by their
primary generator mod 4, giving 12 classes = (Z[ω]/4)^×.
- s(z, z′) takes only the values ±1, and it is constant on every pair of classes (21194 pairs). Inside six classes it
  is −1: (1,2), (1,3), (2,1), (2,3), (3,1), (3,2).
- χ_z(−1) = −1 on exactly those six classes and +1 on the other six. So the effective sign is +1 inside every class:
  the family is self-dual class by class.
- This matches the per-class spectra:
  - the off-diagonal λ_max + λ_min is +0.19 to +0.20 in every class, against +0.17 to +0.18 for random phases on the
    same zero pattern and +0.18 for Marchenko–Pastur, with no symmetry in the "anti" classes;
  - the theta excess is +0.11 to +0.14 in every class.

**Reading.** The supplementary law for −1 cancels the reciprocity sign, so there is no anti-self-dual sub-family to
exploit. [dead]

## 2026-10-30 · The low-frequency outlier grows like a B^{1/6} spike, and it is neither theta

**Numerics [`rip/theta/theta_top_free.py` (matrix-free, E stored as int8 codes), `theta_srcspike.py`,
`theta_primepool.py`; logs `theta_top_free_B100000.log`, `theta_srcspike_B10000.log`, `theta_primepool_B10000.log`].**
Top singular value s²/S at B = L, against random phases on E's exact zero pattern:

| B | sextic | masked random | RCHAR | excess | implied BBP spike θ |
|---|---|---|---|---|---|
| 3·10³ | 4.061 | ≈ 3.93 | – | +3.4% | 1.44 |
| 10⁴ | 4.261 | 3.95 | 3.94 | +7.8% | 1.74 |
| 3·10⁴ | 4.550 | 3.99 | – | +14% | 2.08 |
| 10⁵ | 4.949 | 3.990, 3.992 | 3.993 | +24% | 2.57 |

- θ is read off the rank-one spiked-Wishart outlier formula λ/λ_edge = (√θ + 1/√θ)²/4, with aspect ratio ≈ 1. Its local
  slopes d log θ / d log B are 0.154, 0.165 and 0.176, close to 1/6.
- So the outlier behaves like a spike of strength ∝ B^{1/6}: Θ₆'s excess rate. At accessible sizes it is the dominant
  non-random structure. Its constant is far larger than the conj G theta's (whose Rayleigh excess is only +0.22 at
  3·10⁴).
- RCHAR, the same family with reciprocity broken, sits at the random level even at 10⁵.

**What it is not (10⁴).**
- Not the row theta: the top vector's overlap with conj G·χ(u)·profile is ≤ 0.01.
- Not a single source theta. The source vectors G(x)χ_x(u)N(x)^{−1/2} and their conjugates have Rayleigh excess
  +0.11 to +0.15 (conj) or none (G), and overlaps with the top right vectors of 0.006 to 0.061 (random level 0.020).
- Only partly the span of twisted source thetas G(x)χ_x(h)χ_x(u)N(x)^{−1/2}, N(h) ≤ 30 (dimension 144):
  - the top vector has mass 0.315 there, against 0.243 for a random span of the same dimension;
  - projecting it off lowers the top to 4.013, against 4.106 for a random span.
- Not a prime pool. Flat or N^{−1/2}-weighted pools of small primes have r = 0.95 to 0.99 (random pools 0.90 to
  0.95), and overlaps with the top left vector ≤ 0.10.
- Where it is: the low-frequency row span χ_u(m)χ_u(u₀), N(m) ≤ 100, as before. The top block combination loads on
  conjugate pairs of small split primes (norms 7, 13, 31, 37) with specific phases.

**Reading.**
- At these sizes the extremal structure of the full-family sextic sieve is this low-frequency, reciprocity-driven
  spike. It grows at Θ₆'s rate. Xu–Sang's Gauss-sum vectors attain the same exponent with a smaller constant.
- Mechanism open. Candidate [conjecture]: a corner main term of the double Dirichlet series Σ (u/n)₆ N(u)^{−w}N(n)^{−s},
  where the two theta polar lines (one per Poisson direction) meet. That would explain why it is neither the row
  theta nor the source theta, why it needs reciprocity, and why it lives on low frequencies.
- For the K-wall:
  - it is flat, so it dilutes on random thin row sets;
  - the slot-selected W is cut out by low-frequency functions of the rows (short prime sums), so whether it dilutes
    on W is a real question. The fresh look's W-numerics (B ≤ 12000, sextic within ±4% of RMM-S) show nothing yet,
    but there the spike is just above threshold (θ ≈ 1.4–1.8).
  - Next check: selected norms on slot-selected W against RCHAR-W at B = 3·10⁴ to 10⁵.

## 2026-10-31 · Fortified claims: four elementary Lean files behind the K-wall and RIP entries (agent; verified)

**Lean [`lean/arvi_kwall/DualFrame.lean`, `AntiSelfDual.lean`, `SpikeFree.lean`, `TransferLemmas.lean`].**
- All four are Mathlib only and check in about 10 s each on a warm cache.
- I compiled them independently after the agent's report. Every printed theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- There is no `sorry`, `admit`, `axiom` or `native_decide`, and the repo copies match the build tree.

**DualFrame (the fresh look's Q-metric bound).**
- `dual_frame_bound`: for Q positive definite, Σ_{z∈W} |y_z|² ≤ c_W(Q)·⟨y, Qy⟩, where
  c_W(Q) = sup{⟨v, Q⁻¹v⟩ : v a unit vector supported on W}.
- `dual_frame_large_sieve` is the same bound for y = Ma.
- Q = 1 gives the trivial restriction bound (`cW_one_eq`, `dual_frame_large_sieve_one`).
- It is an exact reformulation, so the choice of Q is the whole content. The numerical test of a wide-kernel Q at
  B = 10⁴ is with the large-B agent.

**AntiSelfDual (closes the "No anti-self-dual row class" idea formally).**
- `two_d_bound`: suppose A = −U Ā Uᴴ (U unitary, Ā the entrywise conjugate) and D + A ⪰ 0 with 0 ≤ D ≤ d. Then
  D + A ≼ 2d.
- The constant is sharp (`two_d_bound_sharp`), and the "+" sign gives no cap (`plus_sign_no_cap`).
- So an anti-self-dual row class would have capped the sextic row Gram at twice its diagonal. The numerics found
  that χ_z(−1) cancels the reciprocity sign, so no such class exists.

**SpikeFree (corrected large sieve, source side).**
- `selected_of_corrected` is by restriction, and `off_spikes` gives the bound off the spikes.
- `detector_condition` turns a small spike projection of a into the selected bound.
- `detectorSpan_finrank_ge`: if a (k+1)-dimensional source subspace has energy ≥ Δ′ > Δ, the spike span has
  dimension ≥ k + 1. This is the formal form of "V must be high-dimensional when many eigenvalues exceed Δ".

**TransferLemmas.**
- `douglas_easy` and `douglas_gram`: if X = AY and ‖A‖ ≤ c, then X*X ≼ c²Y*Y.
- `gram_mixture_offdiag_avg`: over independent atom choices per row, the average off-diagonal Gram entry is the
  Gram entry of the mean rows. So a randomized dictionary transfers only its mean.
- `cross_coherence_no_information`: the identity dictionary has perfect RIP and flat cross-coherence with a flat
  vector, while the dictionary of equal rows has none. So cross-coherence carries no RIP information.

## 2026-10-31 · Random multiplicative dictionaries have RIP of order |S| ≪ m^{2/3} with probability ≥ 1/2 (Lean; agent, verified)

**Lean [`lean/arvi_rip/RandomMultiplicative.lean`, namespace `QRH.ArviRIP`].**
- The file is 1437 lines and checks in about 35 s.
- I compiled it independently. Every printed theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
- There is no `sorry`, `admit`, `axiom` or `native_decide`.

**The model (RMM).**
- Each row z gets an independent uniform assignment w_z : P → ℤ/6.
- Sources are sets of primes n ⊆ P, i.e. squarefree products.
- The atom is ψ_n(w_z) = ∏_{p∈n} ζ^{w_z(p)}, with ζ a primitive sixth root of unity.

**The proof.**
- Orthogonality, exactly: `sum_psi_mul_conj`. For four factors, `sum_psi_four`; exponent sums with |e| ≤ 4 < 6 are
  separated.
- The averaged centered fourth moment is a closed-walk count, exactly (`sum_fourth_moment`, `walkCount_eq`):
  walkCount = s(s−1)(s−2)(s−3)·m + 2·s(s−1)(s−2)·m² + s(s−1)·E.
  Here s = |S|, m = #sources, and E is the multiplicative energy of the sources.
- Markov: `half_good`.
- `rip_positive_measure`: at least half of all assignments give RIP on S with constant
  (2(s⁴m + 2s³m² + s²E))^{1/4}.
  - For sources with only trivial relations, E ≈ 2m². Then the relative constant is ≈ (4s³/m²)^{1/4}, so RIP holds
    for |S| ≪ m^{2/3}.

**Reading.**
- This is the random-model calibration of (M₄) from the "RIP (4) fresh look" entry. The centered fourth moment
  certifies RIP up to |S| ≈ m^{2/3}, past the √-barrier of coherence.
- For the actual sextic rows, (M₄) on the selected W is still the open input.

## 2026-10-31 · A Deshouillers–Iwaniec spectral large sieve on the sextic cover cannot give (LS off V) (agent report; literature IDs checked)

**Report [`frontier/SPECTRAL_LARGE_SIEVE.md`].** The claims are marked [derived] or [heuristic] there. None is formal.
- **Identification [derived].**
  - Each twisted theta is the residue of Kubota's Eisenstein series on the 6-fold cover at s = 1 + 1/6, twisted by
    z ↦ χ_z(m).
  - It is rank one in the radial profile (Xu–Sang's I(U) is the Mellin transform at the pole) and lives in K-type 0.
  - The excess exponent 1/n is the residual spectral parameter.
  - Kazhdan–Patterson's τ₆(m p⁵) = 0 accounts for the conjugation tables.
- **Obstacle [derived].**
  - The sieve matrix has no cuspidal component. One Poisson step gives Gauss sums, which are Kloosterman sums with
    one frequency 0, so Eisenstein Fourier coefficients. Kuznetsov needs two nonzero frequencies.
  - Off V only the continuous spectrum remains, and a large sieve for it is equivalent to (LS off V).
  - Self-duality at B = L is Kubota's s ↔ 2 − s.
- **Size [heuristic].** A spectral large sieve of Deshouillers–Iwaniec quality has to pay for the whole cuspidal
  spectrum. The best embedding found gives B^{3/2+ε} at B = L, worse than B^{7/6}.
- **Literature (arXiv IDs checked).**
  - de Faveri, "Optimal large sieve for fixed order characters", arXiv 2610.04045 (2 Oct 2026): every n ≥ 3, number
    fields containing the n-th roots of unity, expected optimal in all ranges.
  - Xu–Sang, "A matching lower bound for the sextic large sieve and structured prime moments", arXiv 2610.17675:
    (AB)^{−ε}(A + B + A^{5/6}B^{1/3} + A^{1/3}B^{5/6}) for squarefree rows and columns.
  - Dunn, "Metaplectic cusp forms and the large sieve", arXiv 2403.13151: circle method and Voronoi, no Kuznetsov.
  - Cited by the report but not checked: Louvel's cubic Kuznetsov (Forum Math. 2014) and Pascadi (Forum Math. Pi 2026).
- **Low-frequency outlier [speculative].** It is neither a first-order residual term nor continuous spectrum. If its
  B^{1/6} growth is real, it is a second-order "corner" term.
- **Lean stack.** OAI's Eisenstein directory covers the cubic cover only:
  - Laplacian, Fredholm theory, and the resolvent with the theta projection as its residue at 8/9;
  - Eisenstein series and their Gauss-sum Dirichlet series;
  - Patterson's θ₃, sextic reciprocity, and Heath-Brown's cubic large sieve.

  There is nothing for the 6-fold character and no Kuznetsov.
- **Cheaper tests suggested.** T1: only angular frequency 0 carries the excess. T5: the off-V test on the cubic
  family, where the excess is ≍ B^{1/3}. T5 is run in the next entry.

## 2026-10-31 · The balanced-point large sieve with the theta term removed, as a Lean statement (conjecture + proved reductions)

**Lean [`lean/arvi_kwall/SexticSpikeFree.lean`, namespace `QRH.ArviKWall.BalancedSieve`].** The file imports the OAI
baseline's `Detector.Physical`. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The
conjecture is a `def … : Prop`, and nothing in the file assumes it.

The objects are OAI's own:
- rows: squarefree ideals of ℤ[ω] coprime to 6 with B ≤ N z ≤ 2B;
- sources: ideals coprime to 6 with squarefree norm ≤ L, taken at their primary generators;
- kernel χ_z(n)^k with χ_z = `idealRowHom` (k = 1 sextic, k = 2 cubic).

Each twist m = x + yω with N m ≤ M (all associates) gives three spike shapes:
- the twisted theta g̃(z)·conj χ_z(m)^k, where g̃ is the phase of the row's Gauss sum (OAI's `sexticGauss` at k = 1,
  `powerGauss_one`);
- the plain character χ_z(m)^k;
- its conjugate conj χ_z(m)^k.

Each shape is multiplied by a radial profile (B/N z)^{j/2}, j < J.
- **Conjecture `SpikeFreeLargeSieve k q`** (sextic (1, 6), cubic (2, 3)): for every ε > 0 there is C such that,
  for every B and every row vector b orthogonal to all spikes with N m ≤ C B^{1−qε} and j ≤ C B^ε,
  Σ_n |Σ_z b_z conj χ_z(n)^k|² ≤ C B^{1+ε} ‖b‖².
  - The cutoff is where the Poisson multiplicity (B/N m)^{1/q} of the dual frequencies m j^q falls to B^ε.
  - The family has O(C² B^{1−(q−1)ε}) = o(B) members, so the condition leaves almost all of the row space
    (`exists_orthogonal_of_card_lt`).
  - C also scales the cutoffs. This absorbs the choice of additive character, which only twists g̃ by χ_z(t),
    t | 3^a.
- **Refinement `GradedCorrectedLargeSieve`:** E E* ≼ C B^{1+ε} I + Σ w_i f_i f_i* with the multiplicity weights
  w = C B^ε (B/N m)^{1/q}. It implies the conjecture (`spikeFree_of_graded`).
- **The reduction the chain needs (`selected_of_corrected`, generic).** Suppose E E* ≼ Δ I + Σ w f f* and the
  weighted spikes have Bessel constant Λ_W on a row set W. Then Σ_{z∈W} |Σ_n a_n χ_z(n)^k|² ≤ (Δ + Λ_W)‖a‖².
  - The proof is by duality with the test vector D·1_W. Restriction and the detector condition are one inequality.
  - The union bound gives Λ_W ≤ |W| Σ w for flat spikes (`selected_of_graded_flat`). With the graded weights, Σ w is
    about C³ B^{1−(q−3)ε}, so this helps only for tiny W.
  - A useful Λ_W is itself a large sieve for the twisted thetas on W. That is the same problem one level down
    (recursive).
- **Sanity.** `corrected_trivial` shows Δ = |R||S| always works, so the content is the size of Δ.
- **Relation to the fortification agent's `SpikeFree.lean`.** That file corrects on the source side, where the
  selected bound is plain restriction. The Poisson thetas live on the rows, so the row-side form here is the one that
  matches the mechanism.

**The K-wall from the graded conjecture: the recursion closes.** The formal part is `spikeBessel_of_blocks`,
`isSelected_trivial` and `selected_of_amplified`. The exponent count below is not formal.
- **Λ_W is a selected norm.** For a theta spike, ⟨b, f_{m,j}⟩ = Σ_{z∈W} c_z χ_z(m)^k with
  c_z = b_z conj g̃(z)(B/N z)^{j/2} and |c_z| ≤ |b_z|. The plain kinds are the same with χ or conj χ. So a block of
  twists with N m ≍ M_r has Bessel constant ≤ 6·S_W(M_r). Here S_W(M) is the selected norm on the same rows W with
  the twists of norm ≍ M as sources, and 6 counts associates.
- **Amplification at slope δ.** PR 93's rule n(x) ≤ n(y) − δ(y − x) gives S_W(M_r) ≤ (M_r/B)^δ B^{o(1)} S_W(B). For
  this, the sources at length B must contain the products of twists and slot primes. That is why the conjecture now
  takes all ideals of norm ≤ L as sources. Fewer sources only lower the Gram form (`dualForm_mono_sources`), so the
  squarefree-norm numerics are a special case (`spikeFree_squarefree`).
- **So Λ_W ≤ η·S_W(B)** with η ≲ B^{o(1)} Σ_r C B^{ε/q}(B/M_r)^{1/q}(M_r/B)^δ.
  - For δ > 1/q, the top block M_r ≍ C B^{1−qε} dominates, and η ≲ B^{−ε(qδ − 1 − 1/q) + o(1)}.
  - This tends to 0 exactly when δ > 1/q + 1/q²: 7/36 for the sextic family and 4/9 for the cubic.
  - Then `selected_of_amplified` gives S_W(B) ≤ C B^{1+ε}/(1 − η). The proof iterates S ↦ Δ + ηS from the trivial
    constant and passes to the limit.
- **In log scale this is a new rule outside `Closure.lean`'s closure:**
  n(1) ≤ max(1 + ε, sup_{x ≤ 1−qε} [n(x) + (1 − x + ε)/q]).
  - The barrier function n*(x) = max(x, 7/6 − δ(1 − x)) for x < 1 violates it when δ > 7/36. Then
    n*(x) + (1 − x)/6 = 7/6 − (δ − 1/6)(1 − x) < 7/6 at x ≤ 1 − 6ε, by a margin larger than the ε/6 slack.
- **Consequence [conditional on the graded conjecture with all-ideal sources].** The selected norm at the balanced
  point is B^{1+ε} for every slope δ > 7/36, which contains the whole K-wall range 1/3 ≤ δ < 1/2.
  - So the K-wall reduces to one full-family statement about the sextic row Gram, with no thin-set or detector
    hypothesis left.
  - This revises the FlatDilution correction, which kept a separate detector condition. That condition is supplied
    by the recursion.

**The conjugation of the spikes (numerics `rip/theta/theta_offspan.py`, log `theta_offspan_B10000.log`).**
- The Lean form is b* E E^H b. Poisson writes the off-diagonal row Gram as Σ_h f_h(z) conj f_h(z') with
  f_h = g̃·conj χ(h). The ratio r(c) = |Eᵀ c|²/(S|c|²) used in the earlier theta entries is the same form at b = conj c.
  So the vectors in those entries (conj G·χ(m)χ(u)) are the conjugates of the Lean ones.
- Check at B = L = 10⁴: |E^H b|²/(S|b|²) = 1.09–1.13 for b = G·conj χ(u)·N^{−1/2} (six units); 0.93–0.98 for the
  conjugate; 0.956 ± 0.024 for random phases.
- Three scripts projected conj G·χ out of E E^H, which is the conjugation without the excess: `theta_span.py`
  ("off V"), `theta_locate.py` and `theta_topspan.py` (theta-span overlaps). Re-run in the right convention, the
  conclusions stand:
  - The top singular vector's mass in the span of G·conj χ(u)·N^{−1/2} is 0.040, against 0.046 for a random span of
    the same dimension. So the outlier is still not the row theta.
  - Top s²/S off the spans, N(m) ≤ 30 (seven twists incl. m = 1, six units, J = 2): see the table below. The
    Marchenko–Pastur edge after removing d dimensions is (1 + √((R − d)/S))².

| removed span | dim | top s²/S off it | MP edge for R − d |
|---|---|---|---|
| none | 0 | 4.261 | 4.156 |
| theta, Lean conjugation | 84 | 4.170 | 4.093 |
| theta, other conjugation | 84 | 4.194 | 4.093 |
| block, both conjugations | 156 | 3.995 | 4.038 |
| all | 324 | 3.844 | 3.909 |
| random | 324 | 3.944 | 3.909 |

At N(m) ≤ 100 (27 twists, dimensions about four times larger):

| removed span | dim | top s²/S off it | MP edge for R − d |
|---|---|---|---|
| theta, Lean conjugation | 324 | 3.921 | 3.909 |
| theta, other conjugation | 324 | 3.970 | 3.909 |
| block, both conjugations | 636 | 3.541 | 3.663 |
| all | 1284 | 2.963 | 3.119 |
| random | 1284 | 3.041 | 3.119 |

**The cubic family (the agent's test T5) and the supplementary twists.** Numerics: `theta_cubic.py`,
`theta_cubic_struct.py`, `theta_suptwist.py`, `theta_classtwist.py` and `theta_cubic_top.py` (stopped after V(100)),
with logs `*_B10000.log`.
- **Setup.** The cubic symbol is the square of the sextic one, so the cubic matrix is E3 = E² on the same rows and
  sources. Its theta excess should grow like B^{1/3}, not B^{1/6}.
- **The spectrum at B = L = 10⁴ is far above the bulk.** Top s²/S is 6.69, 5.15, 4.77, 4.55, against an MP edge of
  4.16. The cubic theta in the Lean conjugation, G3·conj χ³(u)·N^{−1/2}, has r_H = 3.30–3.32 (random 0.95), and its
  conjugate is at 0.79–0.85.
- **The numerical V misses the top two outliers.** Off V(30) (twists coprime to 6), the 3rd and 4th outliers drop to
  4.28 and 4.17, against 4.62 and 4.43 off a random span. The top two stay at 6.33 and 4.95 (random span: 6.45 and
  5.00). Their mass in V(30) is 0.27 and 0.29 (random 0.20); in V(100) it is 0.56 and 0.53 (random 0.42).
- **They are thetas twisted by the supplementary symbols.**
  - u₀ has correlation 0.906 with the single vector G3·(λ²u/z)₃, the λ-twist.
  - The 54-dimensional span {G3 × class indicator (z mod 9, z mod 2) × profile} holds 0.917 and 0.81 of u₀ and u₁
    (random 0.14).
  - The same span with conj G3 holds 0.16 (random level), and with 1 it holds 0.36.
- **Theta excess by twist**, r_H of G·conj χ(t)·N^{−1/2} for t = λ^e 2^f u:

| family | strongest twists | t = 1 | random |
|---|---|---|---|
| cubic | λω 5.70; λ·2·ω 4.02; units 3.30; 2·units 2.35–2.39; the rest ≈ 1.0 | 3.32 | 0.95 |
| sextic | λ⁴·2·ω 1.338; λ⁴·2·ω·(−1) 1.291; λ⁴ω 1.196 | 1.133 | 0.954 |

- **So the earlier entries understated the theta.** They used twists coprime to 6, and at this size they understated
  the largest theta spikes by about a factor of 2 in excess (sextic +0.38 against +0.18).
- **Mechanism [derived, standard].** The sources are primary, which is a congruence condition mod 3, and odd.
  Poisson summation over such a set has dual frequencies in λ^{−a}2^{−b}·O. That twists the row Gauss sums by
  (λ/z), (ω/z) and (2/z), which are functions of z mod 9 and mod 2 (cubic) or mod 4 (sextic): thetas at the cusps of
  a congruence subgroup.
- **The Lean statement already contains these twists.** Its twist box holds λ, 2 and every product of norm ≤ M, so V
  contains these vectors. They need N m ≥ 9 for the cubic λ-twist and N m ≥ 324 for λ⁴·2·ω, which is inside
  C B^{1−qε}. The numerical V(M) did not contain them.
- **Off the class-twisted span** (classes mod 9 and mod 4 × {G, conj G, 1} × 2 profiles, together with the twists
  coprime to 6 with N m ≤ 30): 

| cubic, B = L = 10⁴ | dim | top s²/S |
|---|---|---|
| none | 0 | 6.692, 5.153, 4.769, 4.553 (MP edge 4.156) |
| class-twisted span | 648 | 3.774, 3.718, 3.615, 3.589 (MP edge for R − d: 3.653) |
| random span | 648 | 5.437, 4.277, 3.939, 3.844 |
| class span + twists coprime to 6, N(m) ≤ 30 | 756 | 3.602, 3.550, 3.468, 3.455 (MP edge 3.566) |
| random span | 756 | 5.214, 4.083, 3.874, 3.692 |

  - The mass of the top four left vectors in the class span is 0.966, 0.89, 0.76 and 0.81.
  - Off the class-twisted theta span, every cubic outlier is gone and the top is about 3% above the reduced edge.
    A random span of the same dimension leaves the leading outlier at 5.44.
  - This is the first direct numerical evidence for the off-V statement in a family where the theta sits above the
    bulk at accessible sizes. The agent's T5 asked exactly this question.
- **The exact Poisson formula confirms the class structure independently** (numerics agent, `theta_poisson.py`,
  log `theta_poisson_B10000.log`; that agent is still running, and its files will be committed with its report).
  - G_off = √(L/M)·ε·g(z) conj g(z′)·conj G_M holds to relative error 1e-9.
  - The phase ε is constant on every pair of row classes mod 4 and mod 9: 31104 of 31104 blocks pure for type-a pairs.
  - An Euler factor at λ appears for pairs whose character is trivial on the units.
  - So the dual atoms are Gauss sums times class functions mod 36, i.e. the class-twisted thetas.

- **Sextic family, same test.** Here the top outlier is the low-frequency block one, and the thetas sit below the
  bulk.

| sextic, B = L = 10⁴ | dim | top s²/S | random span, same dim |
|---|---|---|---|
| none | 0 | 4.261 (MP edge 4.156) | – |
| class span | 648 | 3.555 | 3.656 |
| class span + twists coprime to 6, N(m) ≤ 30 | 864 | 3.376 (MP edge 3.478) | 3.474 |

  The structured span removes about 3% more than a random span of the same dimension, consistent with the block
  outlier.

**Reading.**
- The top outlier lives in the block span: off it, the top falls below the reduced MP edge. A random subspace of the
  same dimension leaves it above the edge.
- The theta vectors sit far below the bulk edge at these sizes: Rayleigh ≈ 1.1 S against an edge ≈ 4.2 S. So
  removing either conjugation barely moves the top. The theta excess shows only in Rayleigh quotients.
- Extrapolation [numerical, not proved]: with excess ≈ 0.04·B^{1/6} (fit at 3·10⁴), the m = 1 theta reaches the edge
  only near B ≈ 10¹¹.
- So the Lean conjecture is falsifiable numerically through its block part, and through the theta part only via
  Rayleigh quotients.
- What the K-wall needs from theory is now explicit: the conjecture, plus Λ_W for the spikes on the selected rows.

## 2026-10-31 · Cubic family at B = 3·10⁴: the predicted spike family brings the large sieve to the bulk

**Numerics [`rip/theta/theta_cubic_vm.py`, `theta_classtwist.py`; logs `theta_cubic_vm_B30000.log`,
`theta_classtwist_cubic_B30000.log`].** E3 = E² is the cubic symbol on the sextic rows and sources, at B = L = 3·10⁴
(R = 8474, S = 7768).
- **The spike grows like the cubic theta.** The top s²/S goes from 6.69 at 10⁴ to 8.98 at 3·10⁴. Read as a
  rank-one spike, the strength goes from 4.19 to 6.43, a slope of 0.39 in log B. The prediction is 1/3.
- **V(M) is the Lean statement's spike family, theta kind only:** G3·conj χ₃(t·m)·(N z/B)^{−j/2}. Here t runs over
  the 27 supplementary characters λ^e 2^f ω^g, m over 1 and the sources with N(m) ≤ M, and j < 2.

| removed span | dim | top s²/S off it | MP edge for R − d | random span, same dim |
|---|---|---|---|---|
| none | 0 | 8.979, 6.479, 5.725, 5.513 | 4.180 | – |
| class span (mod 9, mod 4) × {G, conj G, 1} × 2 profiles | 648 | 4.983, 4.745, 4.622, 4.578 | 4.015 | 8.355 |
| V(0): m = 1 × 27 twists | 54 | 5.302, 4.975, 4.863, 4.798 | 4.166 | 8.94 |
| V(30) | 378 | 4.499, 4.429, 4.323, 4.263 | 4.084 | 8.63 |
| V(60) | 702 | 4.268, 4.019, 3.962, 3.948 | 4.001 | 8.35 |

**Reading.**
- **Removing V(M) brings the cubic large sieve to the bulk.** Off V(60), one eigenvalue is 7% above the reduced edge
  and the rest sit on it. A random span of the same dimension leaves the leading outlier at 8.35, about twice the edge.
- **The twisted thetas with m ≠ 1 matter here.** The class span has no m ≠ 1 twists and stops at 4.98 with
  dimension 648. V(30) does better (4.50) with dimension 378.
- **The cutoff behaves as predicted.** Each twist m has spike strength ∝ (B/N m)^{1/3}. Raising M removes every spike
  above the threshold that M sets, and the residual at M = 60 is presumably a twist just above 60.
- **The plain kinds were not needed here.** The cubic family shows no low-frequency block outlier at this size; that
  outlier is a sextic phenomenon.
- **For the conjecture.** This is direct numerical support for `CubicSpikeFree`, with the exact spike family of the
  Lean statement, at a size where the theta is far above the bulk. It is one size; the next check is 10⁵,
  matrix-free.

## 2026-10-31 · The block outlier is the source-side theta; the one-sided conjecture misses it (amended in Lean)

**Mechanism [numerical; agent, checked; `rip/theta/theta_mech_*.py`, logs `theta_mech_*_B*.log`].**
- The top singular pair of the sextic matrix is a spiked-Wishart outlier of the source Gram E*E. Its source vector is
  f(x) = A(x mod 4)·(3/x)₃·ε(x)·conj g̃(x)·N(x)^{−1/3}:
  - g̃(x) is the source's own sextic Gauss sum;
  - A is a twelfth root of unity on each class mod 4, stable in B;
  - (3/x)₃ = χ_x(3)² is a cubic character mod 9;
  - ε(x) = −1 on odd-class sources with an odd number of prime factors, and +1 otherwise.
- **BBP fit.** With this spike, the spiked-Wishart formula reproduces the top eigenvalue within 3% at
  B = 3·10³, 10⁴, 3·10⁴, 10⁵, 2·10⁵ and 3·10⁵. The strength is θ ≈ 0.378·B^{1/6}.
- **Mechanism.** Poisson summation in the row variable has dual atoms h = u·j⁶. These add coherently with
  multiplicity (N(x)N(x′)/B)^{1/6}. The fitted kernel is flat in y = N N′/B over 6 ≤ y ≤ 2000. [heuristic derivation]
- **Controls.** Breaking reciprocity (RCHAR), masked random phases and random spans all sit at the random level.
- **Correction.** The journal entry "The low-frequency outlier grows like a B^{1/6} spike, and it is neither theta"
  tested G(x)χ_x(u)N(x)^{−1/2}. That shape lacks the class phases, the cubic character, the parity sign and the
  profile, which is why it failed.
- **Poisson self-duality** of the Gaussian primary-n Gram is exact to 10⁻⁹. The dual is the same family at the
  pair-dependent length 27 N N′/(4L), dilated by the unit type (shares 2/3, 1/6, 1/6). It carries a twelfth-root
  phase that is constant on classes mod 36, not mod 4. The outlier needs the full row range: in a narrow window the
  off-diagonal Gram is Marchenko–Pastur-like.

**Is it in the Lean spike family? [numerical; `theta_blockcover.py`, logs `theta_blockcover_B10000.log`,
`theta_blockcover_B30000.log`].** "Rayleigh" below is s²/S of the vector left after the projection.

| | B = 10⁴ | B = 3·10⁴ |
|---|---|---|
| energy of u0 in the row-theta span g̃·(classes mod 36)·(2 profiles), random baseline | 0.160 (0.153) | 0.062 (0.051) |
| energy of E f in the same span | 0.170 | 0.067 |
| energy of E f in all kinds, m = 1 with classes + twists N(m) ≤ 30 (random) | 0.601 (0.384) | 0.370 (0.127) |
| f on N(x) > 30, image off that family: Rayleigh (random phases) | 2.06 (1.57) | 2.97 (1.85) |
| f on N(x) > 3000, same | 1.74 (1.57) | 2.60 (1.85) |
| share of \|E f\|² on the top 10% / 1% of rows by a slot sum (10 primes) | 0.098 / 0.0096 | 0.102 / 0.0085 |

- The row image is not a row theta. It sits partly in the plain characters, but its weight is at N(x) near B.
- Restricted to large sources, it keeps an excess off the low-twist family, and the excess grows with B.
- **So `SpikeFreeLargeSieve` is expected to fail for ε < 1/6.** Its plain kinds stop at N(m) ≤ C B^{1−qε}, and the
  share of |f|² above that cutoff tends to 1. If θ keeps growing like B^{1/6}, some b orthogonal to the whole family
  has b*Gb ≫ B^{7/6}‖b‖². [derived from the numerical model, not proved]
- The earlier sextic tests that reached the bulk edge (journal 2026-10-31, class span + twists at 10⁴) did so below
  the BBP threshold: θ = 1.74 there, and a partial projection is enough.

**Amendment [Lean: `lean/arvi_kwall/SourceSpike.lean`, ≈5 s, 10 axiom reports standard; `SexticSpikeFree.lean`
docstring caveat].**
- **Source spikes.** The row shapes with the source as the modulus, with or without the Liouville sign, on dyadic
  windows of N(n) with profiles.
- **`TwoSidedSpikeFree k q`.** b must also be orthogonal to the row images of the source spikes; equivalently, its
  dual sum must be orthogonal to them (`rowInner_rowImage`).
- **Proved.**
  - `twoSided_of_spikeFree`: the old statement implies the new one.
  - `GradedTwoSided` ⇒ `TwoSidedSpikeFree`.
  - `selected_of_gradedTwoSided`: on W the selected bound is C B^{1+ε} + Λ_row + Λ_src.
  - `sourceBessel_union`: Λ_src is at most the weighted energy of the source images on W.
- **For the K-wall.** The untwisted source image is flat on the rows and does not concentrate on slot-selected rows.
  With |W| = B^{1−δ} it adds about θ·S·|W|/R ≈ B^{7/6−δ}, which stays below B^{1+ε} for δ ≥ 1/6. The barrier range
  1/3 ≤ δ < 1/2 is untouched. [heuristic]
- **Open.** The twisted source spikes, and whether their images keep the twist-sieve structure that amplification
  needs. Heuristic: if the source-theta series Φ(w) = Σ_x χ_w(x) f(x) is multiplicative in the modulus, then
  E ψ_m(z) = Φ(zm), and Λ_src is again a twist sieve.

**Also verified [Lean; agent, checked: `lean/arvi_kwall/ReciprocityBridge.lean`, 1201 lines, 30 axiom reports
standard].**
- The twist sieve and PR 93's `selectedNorm` agree up to 72 = 6·12 (associates × odd source classes), in both
  directions.
- `twistKernel_one_amplification` runs the amplification end to end. The recursion's convention bridge is therefore
  formal, and with `SpikeRule.lean` so is the exponent count. What remains conditional is the conjecture, now the
  two-sided one, plus the source part of Λ_W.

## 2026-10-31 · Q1: the dual-frame table is free probability

[numerical; `rip/theta/theta_ampframe.py` (model `rand`), `theta_ampfree.py`; details in `frontier/README.md`, Q1]
- At B = 10⁴, every diagonal metric's dual-frame bound is the free-Poisson edge of its weights, times 1.04–1.08 (the
  theta excess). A random matrix with the same zero pattern reproduces the free edge within 2%.
- The amplifier's loss is its dynamic range on W: the single-row test vector alone gives 3.43 of its 4.02. Capping
  the amplifier at 1 on W removes 70% of its excess over the truth.
- These are constant factors. Over R rows the dynamic range of a slot sum is about log R / log(1/ρ).
- With the metric Q = P_V^⊥ + ε P_V, the dual-frame bound becomes the K-wall recursion inequality. So Q1's exponent
  content is the spike-free conjecture, and as a separate lever Q1 is closed.

## 2026-10-31 · The outlier to B = 3·10⁵, selected rows, and arithmetic dual frames (agent; verified logs)

[numerical; `rip/theta/theta_top_free2.py`, `theta_outliers.py`, `theta_selected_free.py`, `theta_dualframe.py`; table
and logs in `rip/theta/README.md`]
- **Growth.** The sextic top is 5.470 at B = L = 3·10⁵, against a masked random edge of 3.995 (+36.9%), so θ = 3.16.
  - The least-squares slope over ten sizes is d log θ / d log B = 0.183 ± 0.005. That is consistent with B^{1/6}
    plus an offset.
  - RCHAR stays at the random level at every size.
- **A cluster, growing with R.** The number of eigenvalues above 1.05 × edge is 1, 5, 18, 37 and ≥ 48 at 10⁴, 3·10⁴,
  10⁵, 2·10⁵ and 3·10⁵, about 6·10⁻⁴ R. This is what the multiplicity law predicts. A spike of strength
  ∝ (B/N m)^{1/6} clears any fixed relative threshold for N(m) up to a fixed fraction of B, so the count is ∝ B.
  [heuristic] Twisted source copies with decreasing excess were seen directly (`theta_mech_cluster`).
- **No concentration on slot-selected rows.** Sextic minus RCHAR of (W − random W) is 0.00 ± 0.01 at 3·10⁴, 10⁵ and
  2·10⁵. A positive control with outlier-aligned rows gives +0.12 to +0.71, so the test would see concentration.
  On random row sets the spike dilutes as `FlatDilution` predicts, and it re-emerges only for ρ > 1/θ². This agrees
  with `theta_blockcover`: the source image's share on W equals the density of W.
- **Dual frames.** No W-independent arithmetic metric (theta and block spans, wide kernels, low-pass) beats the
  trivial bound at B = 10⁴. The best arithmetic choice is 1.16× trivial.
  - The cost is c_W ≈ 1 + (1/ε − 1)·λ_max((P_V)_WW). That is the Haar value, except for spans containing the slot
    primes.
  - Only flattening E's own singular spectrum helps, to 0.64–0.73 of trivial. That is Marchenko–Pastur plus
    delocalization, with no arithmetic. Same conclusion as Q1.

## 2026-10-31 · One theta for n = 3, two thetas for n = 6 (why the order matters)

**Numerics [numerical; `rip/theta/theta_pairs.py`, `theta_cubic_twosided.py`, `theta_cfh.py`].**
- Same spans for both families:
  - **row thetas:** G_k(z)·(class functions mod 36)·(2 profiles);
  - **source thetas:** conj g_k(x) and g_k(x) on cells (x mod 4, x mod 9, parity of ω(x)), with profile
    N(x)^{−(1/2 − 1/q)}.
- Table entries are the energies of the top singular pairs (u_t, v_t) in these spans.

| | B | pair 0 | pair 1 | pair 2 | pair 3 | random |
|---|---|---|---|---|---|---|
| cubic, u_t in row thetas | 10⁴ | 0.86 | 0.70 | 0.50 | 0.60 | 0.153 |
| cubic, v_t in source thetas | 10⁴ | 0.87 | 0.69 | 0.48 | 0.59 | 0.166 |
| sextic, u_t in row thetas | 10⁴ | 0.16 | 0.17 | 0.18 | 0.17 | 0.153 |
| sextic, v_t in source thetas | 10⁴ | 0.45 | 0.22 | 0.28 | 0.22 | 0.166 |
| cubic, u_t in row thetas | 3·10⁴ | 0.89 | 0.80 | 0.61 | 0.65 | 0.051 |
| cubic, v_t in source thetas | 3·10⁴ | 0.90 | 0.78 | 0.58 | 0.64 | 0.056 |
| sextic, u_t in row thetas | 3·10⁴ | 0.06 | 0.07 | 0.08 | 0.07 | 0.051 |
| sextic, v_t in source thetas | 3·10⁴ | 0.46 | 0.12 | 0.18 | 0.14 | 0.056 |

- **Cubic: one spike family.** Each top pair is a row theta on the left and a source theta on the right, with
  matching energies.
  - Removing the row thetas V(60) at 3·10⁴ already removes the source theta. The residual's top right vector has
    energy 0.113 in the source span, against a random 0.111.
  - Removing the source-theta span on top of V(60) gives 3.942. A random source span of the same dimension gives
    3.940.
- **Sextic: two families.** The top pair is a source theta whose row vector has no row-theta content.
- **The sextic row vector looks random** (`theta_cfh_B10000.log`).
  - |u₀|² follows the exponential law on prime rows as well (quantiles 0.11/0.71/2.19/4.31).
  - Its squared phase does not correlate with cubic or sextic Gauss sums × classes (0.116 against 0.105 random).
  - So it is not visibly the coefficient vector of the sextic theta function. The spike's structure lives on the
    source side only.

**Literature [checked: abstracts and secondary statements].**
- **Patterson:** the cubic theta function (3-fold cover of GL(2)) has Fourier coefficients that are essentially
  cubic Gauss sums.
- **Kazhdan–Patterson (Metaplectic forms, 1984):** the theta representation of the n-fold cover of GL(r) has a unique
  Whittaker model only for n = r or n = r + 1. On GL(2) that means n = 2 or 3. For n = 6 the coefficients are not
  determined by local data.
- **Chinta–Friedberg–Hoffstein** conjectured that the sextic theta's coefficients at squares relate to cubic Gauss
  sums. They proved it over rational function fields.
- **Bröker–Hoffstein** ("Fourier coefficients of sextic theta series", Math. Comp. 2016, arXiv 1312.0568) give
  partly proven, partly conjectured values of τ(π)², τ(π²) and τ(π⁴).

**Reading [heuristic].**
- Poisson in the rows produces Gauss-sum Dirichlet series whose poles carry the theta coefficients.
- For n = 3 those coefficients are Gauss sums, so the source theta's row image lands on the row theta: one spike,
  seen from both sides. That explains why the cubic one-sided tests reached the bulk.
- For n = 6 the coefficients are not Gauss sums, and the source spike's row image is a new, unstructured row vector.
  This is why the sextic conjecture has to be two-sided (`SourceSpike.lean`).
- So the order n enters through the theta's Whittaker structure, not only through the theta exponent 1/n. This is
  the concrete answer the numerics give to the question "why this particular n".
- A function-field version (where CFH is a theorem) is the natural laboratory for the two-sided statement.

## 2026-10-31 · Möbius absorption is exact for orders 6 and 4; only the landing object differs

[numerical; `orders/gauss_mobius.py`, logs `orders/gauss_mobius_*_X300000.log`; details in `orders/README.md`]
- **Setting.** Gauss sums of all primary squarefree moduli of norm ≤ 3·10⁵ over ℤ[ω] (orders 6 and 3) and ℤ[i]
  (order 4), by twisted multiplicativity, checked against the definition to 1.6e-15.
- **Order 6.** μ(c)·conj g̃₆(c)·α(c) / g̃₃(c) is constant on each of the 108 classes, on every squarefree modulus.
  This is the baseline's prime identity γ₁γ₂ = −α·G, extended to all moduli. The partial sums of μ·conj g̃₆·α
  therefore carry the cubic theta's main term (slope 0.824, Heath-Brown–Patterson 5/6).
- **Order 4.** μ(c)·conj g̃₄(c)·α(c) / g̃₄(c) is constant on each of the 32 classes. This is the Jacobi-sum
  evaluation, whose minus sign absorbs μ(p) = −1. So the Möbius sign is absorbed into the quartic Gauss sum itself,
  with the Kubota–Patterson main term (slope 0.739, 3/4). This corrects `LOG.md`, "Why order 6".
- **The difference.** Cubic Gauss sums are the cubic theta's coefficients (Patterson). Quartic Gauss sums are
  conjecturally the squares of the biquadratic theta's coefficients at primes (Patterson's quartic conjecture;
  Eckhardt–Patterson 1992; Bröker–Hoffstein). The sextic theta has the analogous Chinta–Friedberg–Hoffstein relation
  to cubic Gauss sums.
- **The inverse-moment mechanism is order-independent.** Without the matching angular factor, the Möbius-weighted
  sums cancel better than random phases in both families (slopes 0.28–0.34, against 0.50). Möbius vectors avoid the
  theta spike.
- **For a quartic detector,** which would start at 7/8 instead of 11/12, the precise missing input is a reflection
  for sums of quartic Gauss sums at each place the baseline uses the cubic theta. The tools are the Kubota–Patterson
  functional equation (any order), Patterson's 1987 general Gauss-sum estimates, and David–Dunn–Hamieh–Lin
  (arXiv 2306.11875).
- **Addendum: the signal identities transfer.**
  - On every squarefree modulus, g̃₆ = g̃₃²·(class) and g̃₃³ = μα·(class) hold exactly. These are the baseline's (4.7),
    extended to all moduli.
  - The quartic analogue g̃₄² = μα·(class) also holds exactly: a square where the sextic has a cube.
  - So the algebra of the signal channel exists for order 4. The missing piece is the automorphic carrier. The
    biquadratic theta's coefficients are conjecturally square roots of quartic Gauss sums (Patterson's
    biquadratic conjecture).
  - Unifying pattern [heuristic]: the n-fold theta coefficient at a prime is an n-th root of −α(p) up to class
    constants, for n = 3 (proven), 4 and 6 (conjectural). "Explicit" means the root is itself a Gauss sum, which
    happens only for n = 3.
  - Map of what a quartic detector needs: `orders/README.md`.
- **Synthesis: rank against explicitness** [literature + heuristic; `orders/README.md`].
  - Explicit thetas exist for every order n at rank r = n or n − 1 (Kazhdan–Patterson). For n = r their coefficients
    are n-th order Gauss sums (Bump–Hoffstein for the cubic case on GL(3)).
  - The detector also needs GL(2)'s efficient reflection, length C²/N against C^r/N in rank r.
  - Explicit and GL(2) together force the carrier to be the cubic theta. The Möbius absorption then forces the row
    order to be 6. So "why ℚ(ζ₃)" has a precise answer: it is the only point where an explicit carrier, GL(2)
    reflection and Möbius absorption meet.
  - The quartic route (starting bound 7/8) needs either Patterson's biquadratic conjecture (a GL(2) carrier) or a
    higher-rank carrier with a weaker reflection.

## 2026-10-31 · The sextic family with both thetas removed sits at the bulk edge (3·10⁴)

[numerical; `rip/theta/theta_twosided.py`, log `theta_twosided_B30000.log`; matrix-free version
`theta_twosided_free.py`, which reproduces the dense run at 10⁴ exactly]

| removed | top s²/S | MP edge |
|---|---|---|
| nothing | 4.550 | 4.180 |
| row family V (dim 1080, 13% of R) | 3.960 | 3.903 |
| V and the source family P (dim 432, 6% of S) | 3.773 | 3.792 |
| V and a random source span | 3.817 | |
| random spans of both dimensions | 4.016 | |

- With both thetas removed, the sextic top sits at the Marchenko–Pastur edge. With the row family alone it stays
  above. The source-theta family does more than a random source span of the same dimension.
- This is numerical support for `TwoSidedSpikeFree` at one size. The runs at 10⁵ and 2·10⁵ (matrix-free) will
  decide whether it persists. (It does not with these fixed families; see "Two-sided at 10⁵ and 2·10⁵" below.)
- **Correction (same day).** The Marchenko–Pastur formula is the wrong null. E is zero where a row and a source
  share a prime, and that puts its bulk edge about 4.5% lower. The masked random matrix (i.i.d. phases on E's zero
  pattern) projected off the same spans gives 3.616 here (`theta_twosided_grow_B30000.log`). So the top off both
  families is 4.3% above the null, not at the edge. See "Growing families against the masked null" below.

## 2026-10-31 · Two-sided at 10⁵ and 2·10⁵: the fixed families stay above the bulk edge

[numerical; `rip/theta/theta_twosided_free.py`, logs `theta_twosided_free_B100000.log`, `theta_twosided_free_B200000.log`]

Same families as at 3·10⁴. V: row thetas and plain characters on classes mod 36, two profiles, twists N(m) ≤ 30
(dimension 1080). P: conj g̃ and g̃ times N^{−1/3} on cells mod 36 × parity (dimension 432). Top s²/S:

| B = L | R / S | full | off V (edge) | off V and P (edge) | off V, random P | random spans |
|---|---|---|---|---|---|---|
| 3·10⁴ | 8474 / 7768 | 4.550 | 3.960 (3.903) | 3.773 (3.792) | 3.817 | 4.016 |
| 10⁵ | 28210 / 25936 | 4.949 | 4.590 (4.092) | 4.442 (4.058) | 4.538 | 4.746 |
| 2·10⁵ | 56470 / 51852 | 5.279 | 4.880 (4.135) | 4.756 (4.118) | 4.852 | 5.171 |

- **The 3·10⁴ result does not persist.** Off both families the top is 9% above the edge at 10⁵ and 15% at 2·10⁵.
  The ratio grows like B^{0.08}.
- **Both families still carry signal.** V removes 0.20, 0.21 and 0.32 more than a random row span of its dimension;
  P removes 0.04, 0.10 and 0.10 more than a random source span.
- **The residual is not one spike.** The top four off both families are 4.442, 4.334, 4.219, 4.177 at 10⁵ and
  4.756, 4.729, 4.487, 4.467 at 2·10⁵. They are spaced by about 0.1, against a Tracy–Widom scale λ S^{−2/3} ≈ 0.005.
- **Reading.** The families are fixed while the spikes are not.
  - Every twisted theta carries the same excess up to N(m) ≈ B²/L (`rip/theta/README.md`, "One spike per twist").
  - The Lean statement removes twists up to C B^{1−qε} and the source images on log B dyadic windows.
  - Here V holds 6 twists at every B and P has one global profile, so the share of the spikes they remove falls.
  - The edge result at 3·10⁴ owed part of itself to V's share of the rows: 13% there, 3.8% and 1.9% here.
- So these numbers neither confirm nor refute `TwoSidedSpikeFree`. They show that a fixed family is not enough, which
  the conjecture allows. The next test grows both families with B (more twists on both sides, source windows), against
  random spans of the same dimensions.

## 2026-10-31 · The price of rank: why no other power-residue family beats the sextic base

[derived from the Oct 5 preprint's outline (§2 Steps 2–5); the rank count is a heuristic; `orders/README.md`]

- **What the base needs.** The 11/12 step uses three moves: copies of the target among the rows (`H^{1/n}` of them
  for a family of order `n`); Poisson in the row, which absorbs μ into a Gauss sum; and a theta transformation.
  The last move needs the absorbed Gauss sum at modulus `n` to be the coefficient of a GL(2) form *at index `n`*.
  For the cubic theta this is Patterson's theorem. Then the Fourier factor `χ_p^{−1}` and the multiplier `χ_p^{−2}`
  leave the quadratic twist `χ_p³`, and the sharp quadratic large sieve closes the dual mean square.
- **Quartic family.** μ is absorbed into the quartic Gauss sum `γ₄(n)`. No GL(2) form has `γ₄(n)` at index `n`.
  The 4-fold theta's prime coefficients are square roots of `γ₄` (Patterson's conjecture), so even the conjecture
  gives a sum of `τ₄(n)²`, a rank-4 object. The quartic Kubota series reflects quartic Gauss sums into quartic
  Gauss sums with a quartic twist, which is the same problem again.
- **Price of rank.** A carrier of rank `r` reflects a sum of length `X`, twisted mod `h`, into one of length
  `N(h)^r/X`. Even with the best leftover twist (quadratic, sharp sieve) the dual mean square is `X𝓗 + 𝓗^r`. The
  base exponent is then `θ₀ = (1 + (2 − 2/r)(1 − 1/n))/2`. That is `1 − 1/(2n)` at rank 2. A quartic family with an
  explicit rank-3 or rank-4 carrier (Kazhdan–Patterson) gets `θ₀ = 1` or `17/16`: no saving, so the 1/24 head start
  is lost entirely.
- **Answer to "why ℚ(ζ₃)".** Among power-residue detectors, the sextic family over ℤ[ω] with the cubic theta is not
  just the only explicit option; within this architecture it is optimal. ℚ(ζ₃) is the smallest field carrying the
  sextic residue symbol, and larger fields give the same exponents with more units. A different order needs a
  specific piece of new mathematics: a GL(2)-type summation formula for quartic Gauss sums at index `n` that leaves
  a quadratic twist.

## 2026-10-31 · The block outlier is a residue: the source theta's row image is one vector at every scale

[numerical; `rip/theta/theta_src_residue.py`, `theta_src_windows.py`, `theta_src_coherence.py`,
`theta_src_lscale.py`, logs `theta_src_*_B10000.log` and `theta_src_coherence_B30000.log`. The identification with
τ₆ is heuristic.]

**Heuristic.** Put the source theta `f(x) = conj g̃₆(x) N(x)^{−1/3}` (times class phases) into E.
- Reciprocity and twisted multiplicativity give `(x/z)₆ conj g̃(x) = conj g̃(z, x)` up to classes. So
  `E f(z) = Σ_x conj g̃(z, x) N(x)^{−1/3}` is a partial sum of the sextic Kubota series
  `ψ₆(z, s) = Σ_x g̃(z, x) N(x)^{−s}` at the index `z`.
- Its pole at `s = 2/3` gives a main term `c L^{1/3} conj τ₆(z)`, with `τ₆` the Fourier coefficients of the sextic
  theta function. So the outlier would be the rank-one residue part of E: `τ₆(z)` on the rows and
  `conj g̃₆(x) N(x)^{−1/3}` on the sources.
- Its energy is about `L^{1/3} Σ_z |τ₆(z)|² ≈ L^{1/3} B^{5/6}`. At `L = B` this is the observed `B^{1/6}` growth of
  the spike strength.
- For `q = 3` the same residue is Patterson's `τ₃ ∝ conj g̃₃(z) N(z)^{−1/6}`, which is the cubic row theta itself:
  one theta. For `q = 6`, `τ₆` is not a Gauss sum: two thetas.
- **Growth exponent for every order.** For order q the pole is at `s = 1/2 + 1/q`, and the source profile is
  `N^{−(1/2 − 1/q)}` (`theta_pairs.py`). The main term is `L^{2/q} τ_q(z)` with `Σ_{z~B} |τ_q(z)|² ≈ B^{1−1/q}`, and
  `|f|² ≈ L^{2/q}`. So the spike strength is `θ ∝ L^{2/q − 1} B^{1 − 1/q}`, which is `B^{1/q}` at `L = B`. That is the
  measured `B^{1/6}` for the sextic family and the `B^{1/3}` theta excess of the cubic one.

**Prior work (found after the tests).** de Faveri–Dunn–Hoffstein, "Non-orthogonality of the cubic and quartic large
sieves via Rankin–Selberg" (arXiv 2607.07911, July 2026), prove the cubic large sieve is essentially optimal and the
quartic one is not orthogonal, by this mechanism: the Gauss-sum bias, Kubota series with Lindelöf-on-average second
moments, and theta coefficients that are large on average (Rankin–Selberg). They conjecture
`Ξ_n(A, B) = (AB)^{o(1)}(A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n})` for every n ≥ 3 (their (1.8)). At n = 6 and
A = B the extremal term is `B^{7/6}`, the `B^{1/6}` excess measured here. So the residue mechanism is known for
n = 3, 4 and expected for all n. What the tests below add is the sextic case and its structure: coherence over source
scales, only the +1 twists, several components. Their second-moment bound is also the input that would make the
identification below a theorem.
- Their proof of the cubic bound (§2.1) is this computation. With sources `β_b = g̃₃(b) H(N(b)/B)` on one dyadic
  window, the row sum is a polar term `P_B(a) ∝ g̃₃(a) N(a)^{−1/6} B^{5/6}` plus a remainder bounded by the
  Kubota second moment of David–de Faveri–Dunn–Stucky (their (2.3)–(2.8)). For q = 3 the identification is
  therefore a theorem. For q = 6 it needs the polar term with `τ₆` and the sextic second moment; they expect the
  lower bound for every n ≥ 5 to be within reach of current tools.

**Tests.** Rows are fixed (`N z ∈ [B, 2B]`); only the sources change.

| test | E | control |
|---|---|---|
| top row vector for sources up to L against L′ (B = 10⁴, neighbouring L in 10³ … 10⁴) | overlaps 0.56–0.74; 0.22 from 10³ to 10⁴ | random 3.6e-4 |
| row images of the class-signed source theta on disjoint dyadic source windows (B = 10⁴, 5 windows) | mean \|corr\|² 0.046, adjacent 0.028–0.055 | masked null 0.0003; random class phases 0.0019 |
| the same at B = 3·10⁴ (6 windows) | 0.052, adjacent 0.022–0.078 | masked null 0.0001; random class phases 0.0027 |
| main energy \|Ef\|² minus the masked null (B = 10⁴; L = 2·10³, 5·10³, 10⁴, 3·10⁴) | 2244, 3257, 4429, 6569; ÷ L^{1/3}: 178, 190, 206, 211 | an L^{1/2} law would give 50, 46, 44, 38 |

- **Coherence across disjoint windows is the decisive test.** A fixed source vector, cut into windows that share no
  source, sends each window to the same row direction. The size matches a residue model: about 23% signal per window
  image gives an expected 0.05.
- **A single window shows no outlier.** E restricted to one dyadic window has its top at the masked null, and the
  windows' top vectors are unrelated. This is expected: each window holds about a fifth of the main energy, which is
  below the BBP threshold. The outlier needs the coherent sum over all scales.
- **The L-dependence.** The main energy grows with local exponents 0.44, 0.44 and 0.36, against the predicted 1/3. A
  lower-order term or a logarithm may account for the difference.
- **Why the row theta is weak.** [heuristic] The same mechanism in the row variable makes `E^H G₆ ∝ τ₆(x)`: the row
  theta pairs with the theta coefficients on the sources, with the same scaling. But the rows fill one dyadic window
  `[B, 2B]`, while the sources fill every scale from 1 to L. The coherent build-up gives the source theta about ten
  times the energy, which matches the observed ratio (θ ≈ 2.1 against a row-theta excess of 0.22 at 3·10⁴).
- **Not checked, and not checkable directly at these sizes.** That the fixed row vector is `τ₆` itself rather than
  some other fixed vector.
  - At squarefree indices `τ₆` is not explicit, even conjecturally. Bröker–Hoffstein (Math. Comp. 85 (2016),
    arXiv 1312.0568, Conj. 5.7) give `τ₆(π)²/τ₆(1) = ζ₆^{k(π)} g̃₃(π) 3^{l(π)} (1 − 3ζ₆)^{m(π)} (−2 + 3ζ₆)^{n(π)}`
    for `|π| ≡ 1 mod 4` (norm-13 elements for `|π| ≡ 3 mod 4`), with `l ∈ {−1, 0}`, `m, n ∈ {0, 2}`, and no pattern
    found for `k(π)`, `m` or `n`. CFH pin down only the square indices: `τ₆(p²) = 2 G₃(1, p)` up to a twelfth root of
    unity and a power of 3.
  - So the earlier negative phase test (`theta_cfh`: `u₀²` against cubic Gauss sums × classes mod 36) is explained.
    The unknown sixth roots `ζ₆^{k(π)}` are not class functions, and such a span cannot see them.
  - Computing `τ₆` independently is out of reach: Bröker–Hoffstein sum Gauss sums to norm 10⁸ to get `τ₆(π)` for
    `N(π) < 900`, while our rows have norm 10⁴ and up. The tests above are the available evidence.
- **Small rows, long sources** (`theta_tau6_small.py`, log `theta_tau6_small_B100_L100000.log`). Rows have
  `N(z) ∈ [100, 200]` (28 rows) and sources go up to 10⁵. The source theta is applied class by class (12 classes of
  x mod 4).
  - The 12 × 28 class-image matrix, divided by `L^{1/3}`, has singular values 0.60, 0.55, 0.47, 0.46, 0.42, 0.38, …
    at `L = 3.3·10⁴` and 0.56, 0.53, 0.48, 0.42, 0.39, 0.34, … at `L = 10⁵`. They are stable in L.
  - The masked null's values decay like `L^{−1/6}`, as noise should: 0.35, 0.31, 0.28, … and 0.29, 0.26, 0.24, ….
  - So about eight directions carry a main term growing like `L^{1/3}`. **The residue is a small family of row
    vectors, not one**: the classes of the source carry different combinations. That fits the several components
    `τ(·, η)` of the sextic theta over Bröker–Hoffstein's twelve representatives η. The outlier at large B is one
    combination.
  - A test of Bröker–Hoffstein's conjectured prime values needs that combination in their normalization. With the
    top singular vector instead, the sixth-power phase test gives 0.18 against about 0.1 for random phases (10 pairs
    of conjugate primes): inconclusive. One clean regularity: `|τ̂(π)|² = |τ̂(π̄)|²` on every pair of conjugate primes.
  - With the outlier's own class combination (the twelve class phases of the 10⁴ fit, near twelfth roots of unity),
    the small rows at `L = 10⁵` carry `|τ̂|²` about 8 times the masked null, and the null decays like noise. On the
    prime rows the magnitudes come in conjugate pairs and spread over a factor 5–10. That is compatible with
    Bröker–Hoffstein's discrete factors (3, 7, 13), but the levels are not resolved. The sixth-power phase test is not
    stable in L (0.02 at 3.3·10⁴, 0.50 at 10⁵; 10 independent pairs). The direct identification stays open.
    [exploratory; scratch scripts, not kept]

## 2026-10-31 · Twisted source spikes are flat on slot-selected rows (Λ_src, 3·10⁴)

[numerical; `rip/theta/theta_src_twisted_selected.py`, logs `theta_src_twisted_selected_B30000.log` (twists
N(m) ≤ 100) and `theta_src_twisted_selected_B30000_M400.log` (N(m) ≤ 400)]

- **Setup.** The source spike is the top right singular vector `v₀` of E. Its twists `v₀(x)(x/m)₆` have row images
  `Φ_m = E(v₀ (·/m)₆)`, which the residue picture predicts to be about `L^{1/3} τ₆(zm)`. The set W is the top ρR
  rows by `|T(z)|`, the slot sum over the split primes of norm in `[P₀, 2P₀]`, as in `theta_selected_free.py`.
  `Λ_src(W)` is the top eigenvalue of the Gram of the `Φ_m` restricted to W.
- **Energy.** The images are flat on W: their mean energy share on W, divided by ρ, is 0.99–1.01 for
  `P₀ ∈ {50, 200}` and `ρ ∈ {0.1, 0.03, 0.01}`. The masked null gives the same.
- **Bessel constant.** `Λ_src(W)` matches random row sets of the same size within about 2σ (98 twists:
  1.238 against 1.216 ± 0.016, 1.667 against 1.680 ± 0.029, …). The masked null scatters the same way.
- **One false lead.** With 26 twists, `P₀ = 50` and `ρ = 0.03` gave +7.5% over random sets (about 5σ of the draw
  spread). A twist-sieve structure (`Φ_π ∝ χ_z(π)^{±}Φ₁` when the twists include the slot primes) would predict that,
  and an excess for `P₀ = 200` once the twists reach 400. With 98 twists neither appears, so the first number was
  most likely noise.
- **For the K-wall.** At these sizes the twisted source spikes behave like the untwisted one: `Λ_src(W) ≈ ρ Λ_src`
  up to random-set fluctuations, with no slot-driven concentration. The structural worry (the sextic `Λ_src` is not
  a twist sieve, frontier README) has no numerical footprint yet. Whether that persists at larger B is open.

## 2026-10-31 · Growing families against the masked null (3·10⁴, 10⁵)

[numerical; `rip/theta/theta_twosided_grow.py` (kernel forward and adjoint products, so families cost nothing to
precompute), logs `theta_twosided_grow_B30000.log`, `theta_twosided_grow_B100000.log`,
`theta_twosided_grow_B100000_300_100.log`]

**The null.** E is zero where a row and a source share a prime, so its bulk edge sits about 4.5% below the
Marchenko–Pastur formula used in the two entries above. The right comparison is the masked random matrix (i.i.d.
phases on E's zero pattern, kernel mode 1) projected off the same spans. Below, each entry is the top `s²/S` of E off
both families as a percentage above that null. "Random" is E off random spans of the same dimensions, against the
same null.

**Families.** The row family V(M) holds the thetas and plain characters on classes mod 36 with two profiles, plus
the twists `N(m) ≤ M` on unit classes. The source family P(M′) holds `conj g̃` and `g̃` times `N^{−1/3}` on cells
mod 36 × parity, plus, for each twist `N(m) ≤ M′`, the class-signed source theta times `(x/m)₆^{±1}` (both
conjugations) and the plain `(x/m)₆^{±1}`, on the twelve classes mod 4.

| (M, M′) | 3·10⁴: dV/R | off both | random | 10⁵: dV/R | off both | random |
|---|---|---|---|---|---|---|
| full matrix | | +14.0% | | | +24.0% | |
| (30, 0) | 0.13 | +4.3% | +10.4% | 0.04 | +14.5% | +22.7% |
| (100, 0) | 0.21 | +2.1% | +9.0% | 0.06 | +13.4% | +21.9% |
| (100, 30) | 0.21 | +1.1% | +8.3% | | | |
| (300, 0) | 0.42 | −0.4% | +4.5% | 0.13 | +10.3% | +20.6% |
| (300, 30) | | | | 0.13 | +7.6% | +19.7% |
| (300, 100) | 0.42 | −1.7% | +2.0% | 0.13 | +2.6% | +18.6% |

- **At 3·10⁴ families that grow reach the null.** Each step (more row twists, then twisted source thetas) removes
  about half of what is left, while random spans of the same dimensions stay several percent above. Once the families
  are large, E off them sits slightly below the null, as expected: they remove directions where E has more than its
  average energy.
- **At 10⁵ the row twists do much less, and the source twists do the rest.** The row family is a third of its
  relative size at 3·10⁴ (dV/R 0.13 against 0.42), and row twists alone take the excess only from 14.5% to 10.3%.
  Source twists then take it to 7.6% (N(m) ≤ 30) and **2.6%** (N(m) ≤ 100, dP/S 0.089), while random spans of the
  same dimensions stay at +19%. So at 10⁵ most of what the row family leaves is the twisted source residue: the
  sextic `(x/m)^{+1}` spikes, which lie outside every row family (next entry). A run with row twists to 1000
  (dV/R ≈ 0.35, J = 1) was stopped before it printed; with the source twists doing the work it is not needed for
  this point. [numerical; log `theta_twosided_grow_B100000_300_100.log`]
- **The cubic family** (`theta_twosided_grow.py … 3`, kernel mode 2, log `theta_twosided_grow_cubic_B30000.log`).
  Same families with cubic Gauss sums and the source profile `N^{−1/6}`. At 3·10⁴ the full matrix is 125% above its
  masked null (the `B^{1/3}` theta). Off the families: +24.3%, +19.9%, +12.2%, +9.4%, **+0.4%** for (30, 0),
  (100, 0), (100, 30), (300, 0), (300, 100); random spans of the same dimensions +108% … +64%. So the one-theta family
  also reaches its null once twists on both sides are removed. The source twists do most of the last step.
  - Why source twists matter even with one theta: with `(x/m)₃^{−1} = (x/m²)₃` the twisted source theta's row image
    is `G(z)·χ_z(m)²`, the other conjugation, while V holds only `G(z)·conj χ_z(m)²`. The Lean statement removes
    every power `χ_z(m)^k`, so the numerical V is a subset of it. A run with both conjugations in V
    (`THETA_ROWCONJ=1`) checks this. [derived]

## 2026-10-31 · Only the +1 twists of the source theta carry a spike, and they decay like N(m)^{−1/q}

[numerical; `rip/theta/theta_twisted_norms.py`, logs `theta_twisted_norms_{cubic,sextic}_B30000.log`;
`theta_twisted_images.py`, logs `theta_twisted_images_cubic_B30000.log`, `…_conjG.log`; the cubic matrix via kernel
mode 2]

**Energy of the twisted images.** For each twist m (N(m) ≤ 30), `|E f_m|²` divided by the masked null, for
`f_m = b(x)(x/m)^{+1}` and `b(x)(x/m)^{−1}` at B = L = 3·10⁴:

| N(m) | 7 | 13 | 19 | untwisted |
|---|---|---|---|---|
| cubic, `(x/m)^{+1}` | 2.10 | 1.93 | 1.77 | 4.12 |
| cubic, `(x/m)^{−1}` | 1.37 | 1.15 | 1.00 | |
| sextic, `(x/m)^{+1}` | 1.58 | 1.49 | 1.45 | 2.16 |
| sextic, `(x/m)^{−1}` | 0.94 | 1.00 | 0.96 | |

- **Only the +1 twist is a spike.** In the residue picture `f_m^{+}` lands on the residue at the index `zm`, and
  `f_m^{−}` on the index `z m^{q−1}`. The theta coefficients vanish there (the cubic ones are zero off squarefree ×
  cube), so the −1 images are noise. The data agree: the −1 images sit at the null by N(m) = 19 (sextic: already at
  N(m) = 7).
- **Decay.** The excess of the +1 images falls like `N(m)^{−0.36}` (cubic) and `N(m)^{−0.25}` (sextic). The residue
  picture predicts `N(m)^{−1/q}` (`Σ_z |τ(zm)|²` over a row window): 0.33 and 0.17. The cubic exponent matches, and
  the sextic one roughly does.
- **Where the cubic +1 images live.** Their energy in the row family V (twisted row thetas `G conj χ_z(m)²` on the 6
  unit classes, twists to 100) is 0.818 against a random level of 0.212. On classes `(z mod 9) × χ_z(−1)` it is
  0.947. The −1 images are at the random level in every row span tried: the other conjugation `G χ_z(m)²`, the
  conjugate theta `conj G χ_z(m)^{±2}`, and mod-9 classes.
- **Sextic, same test** (`theta_twisted_images_sextic_B30000.log`). The +1 images have 0.285 of their energy in V
  (random 0.212), 0.317 with the other conjugation and 0.352 with the conjugate theta (random 0.249 and 0.286). They
  are essentially outside every row family, as two thetas predict: `τ₆(zm)` is not a twisted Gauss-sum vector. For
  the sextic matrix the twisted spikes can only be removed from the source side.
- **This explains the cubic growing-family runs.** Adding source twists helped even though the cubic family has one
  theta. V's unit-class approximation captures only about 82% of each twisted spike, and the source side removes the
  spike exactly. With mod-9 classes on the twisted row family (`THETA_TWCLS=9`), (100, 0) reaches the null on its own
  (−2.0%), but V is then 76% of the rows (random spans: +36%). The other conjugation helps only a little (+9.4% →
  +5.2% at (300, 0), with more dimensions).
- **For the conjecture.** The source family needs only the +1 twists, half the current size. On the row side the
  twisted thetas need class structure finer than the unit classes: the reciprocity and supplementary laws make the
  twisted spike `G(z) conj χ_z(m)^k` times a function of z mod 9 (and mod 4 for q = 6). The Lean statement's
  dyadic-window shapes already allow class functions through the unit and λ twists. [heuristic]

## 2026-10-31 · de Faveri's recursion, run off the spikes, converges to B^{1+γ}: a proof route for (LS off V)

[read: de Faveri, arXiv 2610.04045, §§4–7; derived: the off-spike iteration; heuristic: that each step of the proof
survives the removal; Lean: the iteration's arithmetic, `lean/arvi_kwall/OffSpikeIteration.lean`]

**How the optimal bound is proved [read].** L₁(A, B) is the sieve over n-th-power-free moduli a ∼ A and arguments
b ∼ B. The proof is a recursion:
- complete the a-sum by positivity (Lemma 4.3), then sort by gcd(b₁, b₂) (Lemma 4.4);
- Poisson in a (Lemma 5.1). The dual has length K ≈ B²/A and vector λ_b·β_b, with β the root numbers (Gauss sums).
  It is bounded by Cauchy–Schwarz through L₂(K, ·), the sieve over all dual a′, not only kernels;
- n-th powers (Lemma 6.1): write a′ = d·r^n. Since χ_b(r^n) = 1, the r-sum is trivial, so L₂(K, B) ≤ max_R R·L₁(K/R^n, B)
  with R ≤ K^{1/n};
- monotonicity (Lemma 4.2): L₁(A₁, B) ≲ L₁(A₂, B) for A₂ ≫ A₁. Multiply a by primes p ∼ A₂/A₁ and twist λ by conj χ_p;
- iteration (Prop 7.1). Assume (E_α): L₁ ≲ A^α + B + A(B²/A)^{1/n} + B(A²/B)^{1/n}. One step gives
  L₁ ≲ A + A^{1−α}B^{2α−1} + A(B²/A)^{1/n}. When the middle term wins, monotonicity raises A until it balances the
  theta term. That proves E_{α′} with α′ = 2 − (n−1)/(nα−1), whose attracting fixed point is **1 + 1/n**, the theta
  exponent at A = B.
- The theta term A(B²/A)^{1/n} is R·B at R = (B²/A)^{1/n}: the dual frequencies r^n·m with a small kernel m, each a copy
  of the plain row χ(m). These copies are the twisted source thetas (journal 2026-10-30, "one Poisson spike per
  twist").

**Off the spikes [derived].** Let L(A, B; M) be the same sieve for vectors λ orthogonal to the twisted source thetas
β·χ(m), N(m) ≤ M.
- **Poisson.** A dual frequency with kernel m, N(m) ≤ M, contributes ⟨λ, β χ(m)⟩ = 0. Only kernels above M survive,
  so R ≤ (B²/(AM))^{1/n} and the theta term becomes A·(B²/(AM))^{1/n}.
- **Monotonicity.** λ·conj χ_p is orthogonal to β χ(m₁) for every N(m₁) ≤ M/P (take m = p m₁). So
  L(A, B; M) ≲ L(AP, B; M/P). The product A·M is conserved, and along the orbit the theta term is A·c with
  c := (B²/(AM))^{1/n} fixed. Write c = B^γ.
- **One step** at (A′, B; M′) gives L ≲ A′ + A′^{1−α}B^{2α−1} + A′c. Take A′ = (B^{2α−1}/c)^{1/α}; both terms then equal
  B^{g(α)} with g(α) = 2 + γ − (1+γ)/α. This needs A′ ≥ A = B, which holds exactly when α ≥ 1 + γ.
- **The iteration α ↦ g(α).** g(α) − (1+γ) = (α − 1 − γ)/α. The fixed points are 1 + γ (attracting, g′ = 1/(1+γ)) and
  1 (repelling), so from α = 2 the exponent converges to **1 + γ**.
- At A = B with M = B^{1−nγ}, c = B^γ and the bound is **B^{1+γ}**. That is exactly (LS off V): twist range B^{1−6γ}
  for n = 6, with the forced γ-loss of the 2026-10-30 entry. With γ = 0 (all twists up to B removed) the fixed point
  is 1.
- **Row side.** In monotonicity the row theta transforms as θ_m(ap) = const·θ_{m p^{−2}}(a), by the twisted
  multiplicativity of g̃ and reciprocity. So the row twist range must grow to M_V·P². A²/M_V is conserved, and the
  row theta term B(A²/(B M_V))^{1/n} is the same at every point of the orbit.

**What must be checked before this is a proof [heuristic], in order of difficulty.**
1. **The dual's own thetas at the fixed point.** Near α = 1 + γ the optimal A′ tends to B, so the dual problem
   L₁(K/R^n, B) is balanced again and its theta terms are B^{1+1/n}. de Faveri absorbs them only because α > 1 + 1/n.
   The recursion closes only if the dual is corrected too, so the correction is multi-level.
   - Under the Poisson map the dual's modulus-side theta pulls back to E-directions conj g̃ times that theta, i.e.
     ∝ conj g̃². These carry an angular Hecke twist (Davenport–Hasse) and show no excess (2026-10-30: conj G², G²,
     conj G³ at 0.90–0.98 against 0.946).
   - So the level-2 corrections cost dimension but, as far as the numerics see, no energy. A proof needs them
     identified at every level (the Gauss rotation is periodic mod n up to angular characters) and shown to be
     harmless on the K-wall's vectors.
2. **Restriction to sub-lattices.** The gcd sorting (Lemma 4.4), the split b = b^♮ b^* (Lemma 5.1) and the
   coprimality 1_{(b,r)=1} in Lemma 6.1 all restrict λ to multiples of some d. Orthogonality to β χ(m) is not
   inherited by λ·1_{d|b}.
   - Fix: the corrected form `CorrectedLargeSieve` (G ≼ Δ I + Σ_i w_i f_i f_i*). Subtract the small-kernel dual
     frequencies instead of projecting. The correction is then defined after the sorting, so it survives the
     restriction, and its pieces are restricted twisted thetas.
   - For squarefree λ, b^♮ = 1, and r ≤ c = B^γ in Lemma 6.1.
3. **The row side through Lemma 4.3 and monotonicity.** A projection on the moduli does not localize to sub-ranges
   of a. The fix is the same corrected form for the row Gram, but the two corrections must combine into one two-sided
   statement.

**Monotonicity makes local spikes (numerical, `rip/theta/theta_local_spikes.py`, log
`theta_local_spikes_sextic_B30000.log`).** On a row z = ap, χ_{ap}(x) = χ_a(x)χ_p(x). So the image of f·conj χ_p at
ap is the image of f at a (on x coprime to p): the (x/p)^{−1} twist of the source theta carries the theta of the
smaller problem on the rows divisible by p.
- At 3·10⁴ the (x/p)^{−1} twist has 2.4–4.5 times the null on the rows divisible by p, rising with N(p) = 7 … 79 as
  the smaller problem's theta strengthens. On the other rows it has a deficit (0.73 at N(p) = 7, 0.98 at 79), and its
  total energy is at the null.
- The (x/p)^{+1} twist is uniform: the same ratio on both row sets.
- So the −1 twists redistribute energy rather than adding it, and they do not raise the full operator norm. For the
  corrected recursion this means monotonicity needs no new correction, as long as P is larger than the smaller
  problem's theta excess.
- Scaling: relative to the main theta, the local spike's excess is about N(p)^{−5/6}. It exceeds B^γ only for
  N(p) ≤ B^{(1−6γ)/5}, and those are exactly the twists by p⁵ that the twist box N(m) ≤ B^{1−6γ} of
  `TwoSidedSpikeFree` contains. [derived]

**Restriction carries no spike (numerical, `rip/theta/theta_restricted_spikes.py`, log
`theta_restricted_spikes_B30000.log`).** Obstacle 2 asks whether the twisted thetas restricted to multiples of d,
f·χ(m)·1_{d|x}, carry excess of their own.
- At 3·10⁴, with N(d) = 7–37 and N(m) = 7, 13, the ratio over the masked null is 0.98–1.02. The unrestricted twist
  N(m) = 7 alone is at 1.58.
- Projected off the unrestricted family (N(m′) ≤ 300), the ratio is 0.93–1.01.
- Why the spike disappears [derived]: writing x = dx′, the cross term χ_d(x′)χ_{x′}(d) ≈ χ_{x′}(d)² turns the
  restricted sum into a twist by d^{−2}, which lands off the residue.
- So the gcd sorting needs no restricted corrections, at least at this size. The correction family stays: twisted
  thetas (all twists up to the cutoff) × the finite Poisson levels. Local spikes only redistribute energy.

**Assessment.**
- This is the first route to (LS off V) with the right exponent. The recursion that proves the optimal sieve, with
  the spikes taken out at each Poisson step, has fixed point 1 + γ instead of 1 + 1/n.
- The first sketch in the frontier ("the naive corrected recursion gains a sub-power factor") stayed at the
  self-dual point. Monotonicity moves off it, and the conservation of A·M keeps the theta term linear in A along the
  orbit.
- Nothing analytic is proved. Obstacle 1 is the substantive one: the dual thetas at every level have to be
  identified and shown to be spike-type, or harmless, on the vectors the K-wall uses.
- The same skeleton gives the cubic case, where the level-2 directions conj g̃₃² = g̃₃·(angular character) are again
  pole-free. That makes the cubic family (one theta, explicit Gauss sums) the place to try obstacles 1–3 first.

## 2026-10-31 · The Poisson levels: the source side has spikes along the next Gauss-sum powers, and they close up

[numerical; `rip/theta/theta_level2.py`, `theta_level2_rows.py`, `theta_level_images.py`; logs
`theta_level2_{cubic,sextic}_B{10000,30000,100000}.log`, `theta_level2_rows_sextic_B30000.log`,
`theta_level_images_sextic_B30000.log`; identification by Davenport–Hasse, derived]

**Why look.** In the off-spike recursion (previous entry) the dual problem's own thetas pull back through the Poisson
map to new source directions: the root number β times the dual's modulus theta, i.e. u² with u = conj g̃, up to
angular and class factors. Repeating gives u³, u⁴, …. Obstacle 1 asks whether these carry an excess.

**Test.** For v = u^j (x/|x|)^l N(x)^{−(1/2−1/q)}, restricted to 72 source classes (x mod 4, the parity of the number of
prime factors, the cube-root class mod 9), the top eigenvalue of the class-compressed source Gram (the best class
phases), divided by the same for the masked random matrix. A value of 1 means no spike. The table gives the excess
(ratio − 1); every other (j, l) with |l| ≤ 3 is within 4% of 1, and most are within 1.5%.

| family | 10⁴ | 3·10⁴ | 10⁵ |
|---|---|---|---|
| sextic, level 1: u (the source theta) | 1.03 | 1.58 | 2.24 |
| sextic, level 2: u²·(x/\|x\|) ∝ conj g̃₃ | 0.10 | 0.20 | 0.29 |
| sextic, level 3: conj(x/\|x\|) | 0.11 | 0.22 | 0.28 |
| sextic, plain | 0.01 | 0.05 | 0.09 |
| cubic, level 1: u | 3.28 | 5.71 | 9.43 |
| cubic, level 2: u² | 0.38 | 0.56 | 0.73 |
| cubic, plain | 0.18 | 0.26 | 0.28 |

- **The sextic levels close up after three steps.** The sextic table repeats under (j, l) → (j + 3, l + 2), so
  u³ ∝ (x/|x|)^{−2} up to class functions. Davenport–Hasse gives the same thing [derived]:
  - g(χ)g(χ⁴) = conj χ(4)·g(χ²)g(χ³) gives g̃₆ = conj χ(4)·g̃₃²·g̃₂;
  - g̃₃³ = J(χ², χ²)/√p is an angle (π/|π|)^{±1} times a unit, so g̃₃² ∝ (x/|x|)^{±1}·conj g̃₃;
  - hence level 1 is u ∝ (x/|x|)^{∓1}·g̃₃·conj g̃₂, level 2 is u²·(x/|x|) ∝ conj g̃₃ (the conjugate cubic Gauss sum),
    and level 3 is u³·(x/|x|) ∝ conj(x/|x|)·conj g̃₂, an angular family (g̃₂, the quadratic Gauss sum, is a class
    sign).
  - So the sextic source side has three spike levels and a weak plain one. In terms of the cubic Gauss sum they are
    g̃₃·(angle), conj g̃₃ and the angle.
- **The levels grow with B.** Between 3·10⁴ and 10⁵, sextic level 2 grows by ×1.41, the same rate as level 1 (×1.42).
  The cubic level 2 grows by ×1.29; the cubic plain level saturates (×1.09).
- **The row side has almost none.** The row-side scan (sextic, 3·10⁴; vectors w^j (z/|z|)^l with w = conj g̃(z),
  mapped by the adjoint) shows the row theta (+51%), a plain level (+5%) and one angular level (+2.5%). As with the
  theta itself, the source side carries the structure because the sources span every scale and the rows one dyadic
  window.
- **V removes them only partly.** The row images of the best class combinations have these energy fractions in the
  growing row family V (twists N(m) ≤ 300, 3·10⁴, random level 0.425): theta 0.76, level 2 0.59, level 3 0.58,
  plain 0.60. So the two-sided projection takes out part of each level, and the rest must come off on the source
  side.
- **Flat on slot-selected rows** (`theta_level_selected.py`, logs `theta_level_selected_sextic_B{30000,100000}.log`).
  The concentration of each level's row image on the top ρR rows by a slot sum (P0 = 40, 200, 1000; ρ = 0.1, 0.01),
  over the flat value 1, is 0.83–1.13 at 10⁵ for every level, against 0.97–1.03 for random row sets. The noise at
  ρ = 0.01 (282 rows) is about ±0.1. The angular level's 1.42 at 3·10⁴ (P0 = 40, ρ = 0.01, 85 rows) does not persist.
  So for Λ_src the levels dilute like the theta.
- The 2026-10-30 entry's "conj G², G², conj G³: 0.90–0.98" was the row side without angular twists, which agrees.
- **Row side, exactly [derived from `theta_dualcore.py`'s formula].** For Gaussian-weighted complete sources the
  exact Poisson identity reads G(L) = √(L/M)·ε·(g̃ conj g̃) ∘ conj G(M): the same family at the dual length M, with ε
  a class phase (types a/b/c).
  - So the row spike family is invariant under v ↦ g̃·conj v (up to class phases). That map sends the row theta
    g̃χ(m) to the plain characters conj χ(m) and back: a 2-cycle. The row-level scan sees exactly these two (row theta
    +51%, plain +5%).
  - On the source side the same involution would pair the theta with the plain level only. The observed level 2,
    u²(x/|x|) ∝ conj g̃₃, needs more: either angular structure in ε, or the Hadamard structure χ₆ = χ₂·conj χ₃, through
    which the cubic Gauss sum can enter. Open.

**What it means.**
- **Obstacle 1 is real.** The pull-back of the dual's thetas through the Poisson map shows up as genuine source spikes
  along the next Gauss-sum powers, with the predicted angular twists. It is not an artifact of the recursion's sup
  bound.
- **The family is finite.** Up to angular characters the Gauss rotation is periodic, since u³ is an angle for q = 6
  (u³ = conj g̃₃³, also an angle, for q = 3). So the multi-level correction in the recursion is a finite family: three
  levels for the sextic and two for the cubic, times classes and twists. Obstacle 1 becomes a closure statement: the
  pull-back of each level's dual family is the next level's family.
- **The two-sided conjecture's source family should include the higher levels** (kinds u²·(x/|x|)^l and (x/|x|)^l
  besides u and plain). Otherwise growing spikes are left in it. Done in Lean: `SourceSpike.lean`'s shapes now carry
  a level (`levelFactor`, `idealAngle`).
- **At 10⁵ the levels take a third of what was left** (`theta_twosided_grow.py` with `THETA_SRCLEV=1`, log
  `theta_twosided_grow_srclev_B100000.log`). The levels go on the cells, and their (x/m)^{±1} twists on the classes mod 4
  (dP 2304 → 4200). At (300, 100) E off both families is at 3.471 against the masked null's 3.413, i.e. **+1.7%**
  (+2.6% without the levels). Random spans of the same dimensions give +16.0% (+18.6% before). So the structured
  addition removes 35% of the remaining excess, while the extra dimensions alone account for about 14% of the random
  spans' excess.

## 2026-10-31 · Λ_src is a Rankin–Selberg problem for dilated thetas, and the dilated family is well-conditioned

[derived (heuristic where marked); numerical: `rip/theta/theta_dilation_gram.py`, log
`theta_dilation_gram_sextic_B30000.log`]

**Where the K-wall stands.** With the off-spike recursion as the route to the corrected sieve (two entries up), the
sextic K-wall needs three inputs: the corrected two-sided sieve, Λ_row (twist sieves on W, closed by amplification
for δ > 7/36), and Λ_src, the Bessel constant on the slot-selected rows W of the source spikes' row images. Λ_src was
the open one: duality absorption fails (β_src ≥ 1), and the frontier called its twisted part "shifted convolutions of
τ₆ at products, no known tool".

**Amplification on the source side does not help [derived].** Writing 1_W ≤ |T/T₀|^{2k} turns the amplified energy
of a source image into the row energy of the source vector Σ_Π a_Π f^{(Π)}, the spike shifted to multiples of
slot products Π. That vector lives at source length L·P₀^k > B. PR 93's rule n(x) ≤ n(y) − δ(y − x) then costs
(1 − δ) per unit past the balanced point, so it gains nothing below δ = 1/2. This is the same wall.

**The right reading: dilations, not shifts [heuristic].**
- The twisted source image is a dilation: Φ_m(z) = Φ(zm) (`rowImage_twist_dilation`), with Φ ≈ L^{1/3} conj τ₆.
- With the amplifier, the Gram of {Φ_m} on W becomes Σ_z ψ(z) τ₆(zm) conj τ₆(zm′) w(N z/B), with ψ = χ_·(Π/Π′) of
  conductor ≤ P₀^{2k}. That is a Rankin–Selberg integral of the dilated thetas θ₆(m·) and θ₆(m′·) against an
  Eisenstein series twisted by ψ. It is not an additive shifted convolution.
- ψ trivial (Π = Π′): the main term is B^{5/6} times the Petersson Gram ⟨θ₆(m·), θ₆(m′·)⟩ of the dilated thetas.
  The Bessel constant on W is then ρ times that Gram's top eigenvalue, if the dilated family is well-conditioned.
- ψ nontrivial: the twisted Eisenstein series is entire, so these sums save a power of B over the main term. The
  savings must be polynomial in cond(ψ) and in m m′.
- Tools: de Faveri–Dunn–Hoffstein's regularized Rankin–Selberg for metaplectic forms (Zagier's method on covers;
  arXiv 2607.07911) and their Lindelöf-on-average for Kubota series in the twist aspect. Extending them to the
  6-fold cover with level m m′ and a character is technical but needs no new kind of input.

**Numerics: the dilated family is as well-conditioned as the null.** C_{m,m′} = ⟨Φ_m, Φ_{m′}⟩/(‖Φ_m‖‖Φ_{m′}‖) over all
rows at B = L = 3·10⁴ (sextic, twists N(m) ≤ M with m = 1 included):

| twists | E: top eigenvalue | masked null: top eigenvalue |
|---|---|---|
| N(m) ≤ 30 (6) | 1.063 | 1.089 |
| N(m) ≤ 100 (26) | 1.250 | 1.333 |
| N(m) ≤ 300 (76) | 1.782 | 1.930 |
| N(m) ≤ 1000 (256) | 3.548 | 3.824 |

The mean |C_{m,m′}|² off the diagonal is 0.0003–0.0008 for E, against 0.0005–0.0009 for the null. Its growth with
the number of twists is the null's random-matrix growth, not structure. Together with the flatness on W
(2026-10-31, "Twisted source spikes are flat on slot-selected rows"), this is what the Rankin–Selberg route needs
numerically.

**Revised K-wall chain [heuristic].** The three inputs are now:
- (i) the corrected two-sided sieve: the off-spike de Faveri recursion, a long but elementary bookkeeping task;
- (ii) Λ_row: amplification (formal in `SpikeRule.lean`);
- (iii) Λ_src: metaplectic Rankin–Selberg for dilated thetas with amplifier twists (DFDH technology).

None is a classical open problem of the P1/B2 kind. Each is a long technical program, and none is done.

## 2026-10-31 · The reference wall's detector condition: numerically out of reach, and the m = 1 term is the crux

[numerical: `rip/theta/theta_reference_detector.py`, log `theta_reference_detector_A100000.log`; heuristic derivation]

**Setting.** In the reference regime (rows N(z) ∈ [A, 2A], sources up to L = A^{2/3}) one Poisson step makes the
corrected Gram A·I, so the √-barrier term A^{5/6}L^{1/3} is exactly the spike part (frontier, "Roadmap for the faces").
The question is whether the reference's smooth × prime vectors correlate with the twisted source thetas.

**Numerics: too small to decide.** At A = 10⁵, L = 2154 = A^{0.67} (S = 560 sources), |E v|²/|v|² over the masked
null is:
- 0.985–0.998 for smooth × prime vectors (pool N(p) ∈ [P0, 2P0] with P0 = 8, 20, 50; smooth part up to L/(2P0),
  indicator or bump weight);
- 0.999–1.006 for the same supports with random phases;
- 0.995 for the prime pool, and 0.984/0.991 for the smooth vectors;
- **1.062 for the class-signed source theta itself.**

The spike is too weak in this regime at reachable sizes: its excess is (L²/A)^{1/6} = A^{1/18} times a small constant.
So the detector condition has to come from theory.

**Heuristic reduction [derived, conventions unchecked].** For v(x) = Σ_{x=sp} w(s)a(p) and the twisted theta
g̃(x)χ_x(m):
- twisted multiplicativity and reciprocity give g̃(sp)χ_{sp}(m) = g̃(p)χ_p(m)·g̃(s)χ_s(m p²)·(unit factor);
- the s-sum is a Kubota series at the index (mp²)^{±1}. Its main term is X₁^{5/6} times the theta coefficient there
  (the Patterson bias of the smooth factor).
- In the −1 orientation the index is m⁵p^{10}, where τ₆ vanishes for squarefree m ≠ 1 (Kazhdan–Patterson, τ₆(a p⁵) = 0).
  This is the same vanishing that makes the (x/m)^{−1} twists spike-free. So only m = 1 can correlate.
- For m = 1 the correlation is X₁^{5/6}·Σ_p a(p)·g̃(p)·τ₆(p⁴)·(unit). By Davenport–Hasse and the known values
  τ₆(p²), τ₆(p⁴) (Chinta–Friedberg–Hoffstein, Bröker–Hoffstein), that is a prime sum of a Hecke Grössencharacter over
  the pool.
- Size: the m = 1 spike part, relative to the diagonal, is about A^{1/9}P₀^{1/3}·δ², where δ is the relative
  cancellation of that prime sum over [P₀, 2P₀]. The bootstrap's zero-free half-plane gives δ ≈ P₀^{−1/8}. For
  P₀ = A^{0.03} that is far from the needed A^{−1/18}.

**Reading.**
- If the orientation is right, every twisted spike except m = 1 is harmless for smooth × prime vectors, by the same
  Kazhdan–Patterson vanishing.
- The m = 1 term, the smooth factor's Patterson bias, is the crux of target 2. It must be carried as an explicit main
  term in the reference (a corrected reference energy), not bounded away. Short-pool cancellation for
  Grössencharacters is GRH-strength.
- Next: fix the orientation with exact conventions (`theta_dualcore.py`'s Poisson formula), and check whether Sil's
  reference ledger can absorb a rank-one Patterson main term.

**Correction (same day): the orientation is probably the unfavourable one [derived].** Take the spike orientation from
the twisted-norms numerics: f_m = conj g̃·(class)·(x/m)^{+1} carries the spike. Then
⟨v, f_m⟩ ∝ Σ g̃(sp) conj χ_{sp}(m), and g̃(s)χ_s(t) = g̃(t^{−1}, s) with t = m⁵p², so the s-sum is the Kubota series at
the index t^{−1} ≡ m·p⁴ (mod sixth powers).
- τ₆ does not vanish there, so every twist m ≤ L²/A correlates, weighted by τ₆(m p⁴). The "only m = 1" simplification
  above does not hold.
- The detector condition then needs cancellation in Σ_p a(p) g̃(p) conj χ_p(m) τ₆(m p⁴) over a pool much shorter than
  the conductor m. That is GRH-strength for every m, not only for m = 1.
- **A possible rescue.** In the zero-detection application the plain factors carry N(s)^{−it}, and the Patterson main
  term of a smooth sum twisted by N(s)^{−it} is smaller by about 1/|t|. For the typical |t| (a power of the
  conductor) that is a power saving.
- Whether the reference's plain factors are t-twisted, and at which t the face binds, decides target 2. Not yet
  checked.

**Which spikes does the reference see? This decides whether the faces program is viable [open].**
- The difficulty above assumed the reference vectors meet the Gauss-sum-twisted spikes g̃·χ(m) of our matrix E.
- #96's graded inverse theorem (journal 2026-10-30, "Faces past Λ = 2") says the excess over A + B comes only from
  correlations of the vector with *plain* characters (m₀/n)₆, N m₀ ≤ K₀. That is because after R1's Poisson step the
  row's Gauss sum is a unimodular row factor absorbed into the vector.
- If the reference's post-Poisson vector is smooth × prime with the Gauss sum absorbed, its correlations with
  (m₀/·)₆ are classical small-modulus character sums: Pólya–Vinogradov for the smooth factor (X₁ ≫ m₀),
  Siegel–Walfisz or the bootstrap's zero-free region for the prime factor. m₀ = 1 is the zero frequency, i.e. the
  diagonal. Target 2 would then follow from GS1 (#96, unverified) plus classical inputs.
- If instead the vectors meet the Gauss-sum-twisted spikes, the analysis above applies (GRH-strength, unless
  t-twists rescue it).
- To decide: read which variable Sil's short reference (`MixedFirstActualReference`) sums over, and where the Gauss
  sum sits relative to the vector. Without target 2 the K-wall program buys nothing, so this check comes before any
  further K-wall work.
- **Partly decided [derived, from the R1 entry of 2026-10-29].** R1's Poisson step moves the Gauss sum of the row
  character to a unimodular *row* factor, which |·|² removes. So the vector entering the sieve is plain × plain ×
  prime, with no Gauss sum.
  - In E^H E = A·I + (A/B)Σ_k w_k w_k^H with w_k = β·conj χ(k), the spike part of λ is Σ_k |⟨conj β·λ, χ(k)⟩|²: plain
    blocks (#96's form) for the Gauss-twisted vector conj β·λ.
  - For plain-type λ this is the Patterson-bias case, so the classical reading needs the Gauss sum on the vector,
    which R1 removes.
- **Two rescues to price** (assuming the faces' short reference has R1's structure):
  - (i) height twists N^{−it}, which shrink the Kubota main term by about 1/|t|;
  - (ii) the profile: the theta excess is rank one in the radial profile and vanishes when the weight's Mellin
    transform at the pole is zero (2026-10-30: +18–20% when I(U) ≠ 0, −5%…+3% when I(U) = 0). Splitting the plain
    sums' weights into an I(U) = 0 part plus one explicit rank-one main term could leave the reference diagonal
    up to a single correction.
- Next: check (ii) numerically in the reference regime once a size is found where the source theta's excess is
  visible, and read the face's reference weights.

## 2026-10-31 · The source spikes vanish for radial weights with zero Mellin transform at the pole: the reference wall's rescue

[numerical: `rip/theta/theta_level_profile.py`, logs `theta_level_profile_B{30000,100000}.log`; derived]

**Test.** The spike part of a source vector is a Kubota-type sum. Its main term is L^{s₀} times the Mellin transform
I(U) = ∫ U(t) t^{s₀−1} dt of the vector's radial weight U(N x/L) at the pole. For the sextic matrix, s₀ = 2/3 in
this normalization (the source theta with weight N^{−1/3} grows like L^{1/3}). Three weights are compared, each
times the theta level u or the plain level, with the best class phases (72 classes), over the masked null:
- U1 = t^{−1/3}, the scan's profile, I ≠ 0;
- U2 = t^{−1/3}(1_{t ≤ 1/2} − c·1_{t > 1/2}) with c = 2^{−1/3}/(1 − 2^{−1/3}) = 3.847, so I = 0;
- U3, the same pieces with +c, I ≠ 0, as a control.

| level | B = L | U1 (I ≠ 0) | U2 (I = 0) | U3 (control) |
|---|---|---|---|---|
| theta u | 3·10⁴ | 2.580 | **1.012** | 2.029 |
| theta u | 10⁵ | 3.243 | **1.025** | 2.533 |
| plain | 3·10⁴ | 1.048 | 1.014 | 1.062 |
| plain | 10⁵ | 1.094 | 1.010 | 1.078 |

**The pole located, and the floor (logs `theta_level_profile_B10000.log`, `theta_pole_scan_B100000.log`).**
- Sweeping the split weight's zero across s at 10⁵ (`rip/theta/theta_pole_scan.py`), the theta's excess over the null
  is 1.0553, 1.0284, 1.0250, **1.0246**, 1.0256, 1.0271, 1.0296 at s = 0.55, 0.60, 0.633, **2/3**, 0.70, 0.733, 0.80.
  The minimum is at s₀ = 2/3.
- With the zero at s₀ the theta keeps a floor of 2.7%, 1.2%, 2.5% at 10⁴, 3·10⁴, 10⁵. The floor does not grow and is
  flat in s near s₀, so it is not a mismatch of the zero. The other levels go to 0.997–1.011 at every size. So the
  residue main term is removed exactly (per row it is L^{s₀}·Ũ(s₀)·τ(z)), and what is left is small and bounded.

**The pole against theory (cubic scan, log `theta_pole_scan_cubic_B30000.log`).**
- For normalized n-th order Gauss sums the Kubota series Σ g̃(c) N(c)^{−s} has its pole at 1/2 + 1/n (Patterson: the
  cubic Σ g(c) N(c)^{−s} has it at 4/3). That is 2/3 for n = 6 and 5/6 for n = 3.
- The cubic scan at 3·10⁴ (weight t^{−1/6}, split) gives excess 1.2256, 1.0675, 1.0415, 1.0255, 1.0173, 1.0106, 1.0055,
  1.0100 at s = 0.60, 0.70, 0.75, 0.80, 0.833, 0.867, 0.90, 0.95.
- Fitting excess = floor + slope·|I(U_s)(s₀)|²/‖U_s‖² over candidate poles s₀, the best fits are s₀ ≈ 0.87 (cubic) and
  ≈ 0.70 (sextic, 10⁵ scan). Both are the theoretical value + 0.03.
- A common offset fits the source density in t, which the continuum Mellin transform ignores, rather than a different
  pole. So the weight's zero should be calibrated with the actual density: an empirical zero at s ≈ 0.90 leaves the
  cubic theta at 1.0055.

**All levels share the pole (10⁵, same weights).** The higher Poisson levels vanish with the same I(U) = 0 weight:
u²(x/|x|) (conj g̃₃ up to classes) 1.286 → **1.002** (control 1.165); conj(x/|x|) 1.276 → **1.003** (control 1.125).
So every source spike, at every level and twist, has one common radial direction: the residual pole s₀ = 2/3 of the
metaplectic Eisenstein series, whose residue is the theta function. One Mellin condition on a factor's weight takes
a vector off all of them.

**The source spikes are rank one in the radial profile, and the rank-one direction is the Kubota pole.** With
I(U) = 0 the theta's +224% at 10⁵ falls to +2.5%, and the control with the same two pieces keeps +153%. The
plain level's growing +9.4% falls to +1%. This confirms the residue mechanism quantitatively and locates the pole
at s₀ = 2/3.

**Consequences [derived].**
- **Reference wall (target 2).** The twisted-spike correlations of a plain × prime vector all carry the same
  factor I(U) of the plain factor's weight (the main term at index m·p⁴ is L^{s₀}·I(U)·τ₆(m p⁴)). So a plain factor
  with an I(U) = 0 weight is off every twisted spike to leading order. The Patterson bias of the previous entries
  disappears, and the detector condition is left with the Kubota sums' error terms (random-like) and the prime
  pool's weak bias.
- **Two ways to get I(U) = 0 in the detector.**
  - At height t the plain weight is W(N/X)·N^{−σ−it}, so the main term carries W̃(s₀ − σ − it). This decays like
    |t|^{−A} for smooth W, so zeros away from the real axis need nothing.
  - Near t = 0, split W = W₀ + c·W_ref with W̃₀(s₀ − σ) = 0, using two dyadic pieces as above. W₀ is spike-free, and
    W_ref leaves one explicit rank-one main term per twist, whose coefficient is known.
- **The levels** share the pole (table above), so one Mellin condition covers them.
- **The corrected sieve.** The correction family needs only the I ≠ 0 radial direction per twist and level. The
  Lean statement's windows × profiles span more than this, which is harmless.

So target 2 is now: one Poisson step (known technology) plus I(U) = 0 weights for the plain factors, plus error-term
bounds. That is not GRH-strength. Still to check: the face's reference weights, and whether the reference ledger
tolerates the rank-one W_ref remainder at small heights.

**The K-wall chain loses its Rankin–Selberg input [derived].** The selected bound on W was C B^{1+ε} + Λ_row + Λ_src
(`selected_of_gradedTwoSided`). For a source vector v orthogonal to the source spikes,
Σ_{z∈W} |(Ev)(z)|² ≤ 2 Σ_{z∈W} |(P_V E v)(z)|² + 2 ‖P_V^⊥ E P_P^⊥‖² ‖v‖², so only Λ_row and the off-spike constant
appear.
- The leaf's vectors after R1 are plain × plain × slots. With I(U) = 0 weights on the plain factors (or at large
  height), their source-spike correlations have no main term.
- The remaining correlations are the Kubota sums' error terms, random-like (Lindelöf on average in the twist aspect,
  as in DFDH's (2.9)). Weighted by the spike strengths (B/N m)^{1/6} over N(m) ≤ B^{1−6γ}, they sum to about
  B^{1/6}M^{5/6}/S ≈ B^{−0.08}.
- So for weight-designed leaf vectors the K-wall needs only (i) the off-spike corrected sieve (the recursion) and
  (ii) amplification for Λ_row (`SpikeRule.lean`). The metaplectic Rankin–Selberg input for Λ_src is not needed.
- Still to check: that R1's dualized plain factors can carry such weights. The dual of a smooth sum has the Fourier
  transform of the weight as its weight, so the Mellin condition is imposed at the dual's pole (for radial weights
  on ℂ, M[Ŵ](s) = Γ-factor · M[W](1 − s)).
- **Caveat: low heights.** At height t the main term carries W̃(s₀ − σ − it), an analytic function of t. It decays for
  |t| ≫ 1 but cannot vanish on a whole segment |t| ≤ T₀. So zeros with |t| ≲ 1 leave one rank-one main term per
  spike, with a known bounded coefficient. That slice needs either the Λ_src (Rankin–Selberg) route or a separate
  low-height argument. Its share of the count is about 1/T of the zeros.
- **Measured (`rip/theta/theta_height_twist.py`, log `theta_height_twist_B30000.log`).** The class-signed theta times
  N(x)^{−it} at 3·10⁴, over the masked null, against the Mellin prediction 1 + 1.58·(1/9)/(1/9 + t²):

  | t | 0 | 0.25 | 0.5 | 1 | 2 | 4 | 8 |
  |---|---|---|---|---|---|---|---|
  | measured | 2.580 | 2.212 | 1.596 | 1.153 | 1.016 | 1.003 | 1.017 |
  | predicted | 2.580 | 2.011 | 1.486 | 1.158 | 1.043 | 1.011 | 1.003 |

  The excess follows |1/3 − it|^{−2} and is at the null from t ≈ 2. So the low-height slice is |t| ≲ 2.

## 2026-10-31 · The face's reference, read: free Schwartz weights, explicit heights, and Sil's formal de Faveri recursion

[Lean, read (agent report, citations spot-checked); the files are in Sil's `FourthPower/` directory of the
repeated-marks submission and the OAI baseline's `DirichletL/Moments/`]

**What the short reference estimates.** `uniform_actual_reference` (`MixedFirstActualReference.lean`) bounds a radial
row energy (rows z ∈ ℤ[ω] weighted by Φ(‖z‖²/K), with Φ a caller-supplied Schwartz function) of a rectangle
`heightRectangle`. That is a product of two plain sums and the slot primes.
- **Weights.** Each plain term carries W_j(N n_j/X_j)·(N n_j/X_j)^{i(t_j + t)}. Here W_j ∈ 𝓢(ℝ, ℂ) is supported in
  [a, b] (`normPowerProfile`), t_j are fields of the source, and t is the row height. Slot primes carry
  N(p)^{i(t₀ + t)}.
- **The weights are caller-supplied.** W₁, W₂ are fields of `Source`. The bound depends on them only through finitely
  many Schwartz seminorms (`sourceControl`), and on Φ through sup|Φ|. Only a, b are fixed in advance.
- **Heights are unconstrained** (polynomial cost 1 + |t| + V + ‖t₁‖ + ‖t₂‖). Height windows enter downstream, by
  integration against a smooth compactly supported window.
- **Poisson.** Only the long plain sum is reflected, per row, when √U < X. The Gauss sum is a unimodular
  row-dependent scalar and is dropped, and the dual profile is the radial Fourier transform of the twisted W. The
  short sum and the slots are never dualized.
- **The energy step is Sil's formal optimal sextic sieve** (`OptimalBound`, proved as `optimal_bound` in
  `SieveOptimal.lean`).

**Sil's optimal sieve is de Faveri's recursion, in Lean.**
- `SieveImprovement.step α = (12α − 7)/(6α − 1)` is exactly de Faveri's map 2 − (n−1)/(nα − 1) at n = 6. The fixed
  point 7/6 and the contraction rate 5/6 are proved (`exponent_error_le`).
- `SieveGrowthAlgebra.secondaryCoefficient N M = 2(2N/M)^{1/6} N^{1/6}` is the n-th-power multiplicity term, i.e.
  the theta term.
- The Poisson, gcd and coupling steps are `SievePairPoisson`, `SievePoissonBound`, `SievePoissonRecurrence`,
  `SieveGcdNorm` and `SieveRayCoupling` (about 6,100 lines with the rest of `Sieve*`).

**Consequences.**
- **Target 2 in the face's own terms.** Choose the short factor's weight W₂ with zero Mellin transform at the pole. The
  heights |t₂ + t| ≳ 2 need nothing (measured decay, previous entries). Then replace `OptimalBound` in the reference
  energy by a corrected bound for such vectors: one Poisson step plus the spike-free remainder. The weight freedom
  exists in the code as it stands.
- **The off-spike corrected sieve has a formal starting point.** It is a fork of Sil's `Sieve*` with three changes:
  - the secondary coefficient carries the twist range, (2N/(M·M_tw))^{1/6};
  - monotonicity shifts the range, with A·M conserved;
  - the step map becomes 2 + γ − (1+γ)/α (`OffSpikeIteration.lean`).

  The analytic addition is the small-kernel split of the dual sum inside `SievePoissonBound`, with its correction
  form.
- Both are large Lean projects. Unlike the earlier picture, neither needs a classical open problem.

## 2026-10-31 · Sil's inclusion monotonicity, and where the corrected recursion's closure is decided

[read: Sil's `SieveImprovement`, `SievePoissonRecurrence`, `SieveExponent`, `SieveRanges`; Lean: the arithmetic,
`lean/arvi_kwall/OffSpikeIteration.lean` (Sil's form); derived: the rest]

**Monotonicity by inclusion [read + Lean].**
- In Sil's formal sieve the rows are all moduli of norm ≤ T (`freeRange`, `fullRange`). So θ(M, N) ≤ θ(T, N) for
  T ≥ M by inclusion (`theta_mono`). `improve` then bounds θ(T, N) by T + T^{1−α}N^{2α−1} + T^{5/6}N^{1/3} at
  T = max(M, N^{enlargement α}).
- The source vector is never twisted. Off the twisted source thetas of kernel ≤ μ, the twist range μ stays fixed
  along the orbit, and the theta term is T(N²/(Tμ))^{1/n}. With μ = N^{1−nγ} this is T^{1−1/n}N^{1/n+γ}
  (`sil_theta_eq`).
- Balancing gives silStep n γ α = (1−1/n)(2α−1−1/n−γ)/(α−1/n) + 1/n + γ. At γ = 1/n (nothing removed) and n = 6
  this is exactly Sil's step (12α−7)/(6α−1), and the enlargement is his (12α−8)/(6α−1) (`silStep_sil`,
  `silEnlargement_sil`).
- The fixed point is 1 + γ again. The contraction factor is (1−1/n)/(1−1/n+γ), 0.982 at n = 6, γ = 0.015
  (`tendsto_silIter`), so about 400 steps bring the exponent within 10⁻³ of 1 + γ.
- For the plan: step 5 (monotonicity) needs no twist shift and produces no local spikes on this route.

**Where the dual's own thetas enter [read + derived].**
- Sil bounds the dual with the completed hypothesis λ(L, N) ≲ L^α + L^{1/6}N, L = N²/T ≤ N. `completed_of_exponent`
  obtains it by reciprocity: θ(L/r⁶, N) = θ(N, L/r⁶) ≤ N + (L/r⁶)^α + N^{5/6}(L/r⁶)^{1/3}, summed over sixth
  powers r⁶ ≤ L.
- The L^{1/6}N term is the swapped sub-problems' diagonal "+N", once per r. This is the theta term. Off the spikes
  only the r with L/r⁶ > μ survive, which gives the corrected (L/μ)^{1/6}N.
- The last term, N^{5/6}(L/r⁶)^{1/3}, is the dual's own (row-side) theta. Since L ≤ N it is absorbed by L^{1/6}N.
  Off the spikes it is not: the ratio N^{5/6}L^{1/3}/((L/μ)^{1/6}N) = (Lμ/N)^{1/6} is N^{(1−6γ)/6} at the fixed
  point (T ≈ N ≈ L).
- So the corrected recursion must correct the dual's row-side theta too. That is the two-sided requirement, and it
  sits in one lemma, `completed_of_exponent`.
- The swap θ(L, N) = θ(N, L) is an operator statement. A corrected statement is about vectors, so it must be stated
  in a transposable form: E compressed on both sides, (I − P_rows) E (I − P_cols).

**The precondition set grows by one level per step [derived].**
- The dual vector is c = λ·g̃ (times heights N^{it}). So ⟨c, f⟩ = ⟨λ, u f⟩ with u = conj g̃: each correction of the
  dual pulls back one level up. In precondition form ("λ ⊥ S"), S_{k+1} ⊇ S₁ ∪ u·S_k, so after k steps λ must be
  off u⁰, …, u^{k+1}, with their twists and heights.
- For n = 3, u³ = conj(ang), so u^j = u^{j mod 3}·conj(ang)^{⌊j/3⌋}. The higher levels are the three spiky ones
  with angular Hecke twists. Numerically these carry no excess (every l ≠ 0 entry of the cubic level scan is
  0.98–1.02).
- They are still needed as preconditions. A vector aligned with u³χ_m has a dual aligned with u²χ_m, which is a
  spike of the dual problem. Dropping them would let the recursion "prove" spike-size bounds for vectors whose true
  energy is at the null.
- The number of steps is finite for each target exponent, so the family is finite: three spiky levels, their angular
  twists up to about ang^{−130}, twists ≤ μ, and heights up to about 400·T₀.

**What the K-wall then needs from its vectors [derived; the last two items heuristic].**
- The corrected sieve subtracts Σ_{N(m) ≤ μ} (B/N(m))^{1/n} |⟨λ, f_m⟩|² at each level. For the K-wall this has to
  be ≲ B^{1+γ}‖λ‖² (‖λ‖² ≈ B).
- With the pole killed by a Mellin zero, each correlation is the off-pole part of a twisted Kubota sum. Square-root
  size on average over m is enough: Σ_m (B/N(m))^{1/n}·B = B^{2−(n−1)γ}.
- Pointwise convexity in m is not enough: with an N(m)^{1/2} loss it fails above N(m) ≈ B^{0.64} (n = 6). So the
  K-wall needs a mean value of off-pole twisted Kubota sums over twists N(m) ≤ μ = B^{1−nγ}, i.e. Lindelöf on
  average over the twist.
- By the large sieve in m this follows if the twisted series' approximate functional equation has length about
  N(m)^{1/2}. If the length is about N(m) (degree-2 behaviour, conductor N(m)²), the m-sieve's own theta costs
  N(m)^{1/n}, and the requirement becomes γ ≥ 1/(n(n+1)): 1/42 for n = 6, against the 0.015 needed.
- In that second case the m-sieve is itself a balanced sieve at the smaller scale H ≤ μ, for theta-type vectors
  whose approximate-functional-equation weight can carry a Mellin zero at the level-2 pole. With the corrected bound
  H^{1+γ} at that scale the requirement becomes (1−nγ)(1−1/n+γ) ≤ 1−1/n+γ, which always holds. So the closure is a
  strong induction on the scale, B from B^{1−nγ}.

**Assessment.**
- Sil's inclusion monotonicity removes one obstacle from the plan (local spikes) and puts the dual's own thetas in a
  single named lemma.
- Closure is not fatal but it is not short. The precondition family has about 400 levels, mostly angular twists of
  the three spiky ones. The K-wall's own vectors need a twist-aspect mean value. That mean value is either the large
  sieve (conductor N(m)) or the corrected sieve at the smaller scale B^{1−nγ} (conductor N(m)²).
- Next check: the twist-aspect conductor of Σ_b g̃(b)χ_m(b)N(b)^{−s} from Patterson's functional equation (cubic).

## 2026-10-31 · The Mellin rescue needs Patterson's continuation, which no Lean stack has

[derived; Lean inventory checked by grep over `Submissions/` and `.lake/packages`; numerics
`rip/theta/theta_twist_conductor.py`, log `theta_twist_conductor_q3_L100000.log`]

**What the rescue uses.**
- The rescue (entries above) says: a source vector U(N(b)/B)·α_b whose radial weight has Ũ(s₀) = 0 is off every
  twisted spike. The proof of that statement is the asymptotic
  Σ_b φ(N(b)/X) g̃(b) χ(b) = c_χ X^{s₀} + E_χ(X), with a power saving in E_χ uniform in the twist.
  - With it, the k-th difference U(t) = φ(t) − 2^{s₀}φ(2t) cancels the main term exactly, and only E remains.
  - Without it there is nothing to cancel. Upper bounds alone (Heath-Brown's large-sieve bounds for Gauss-sum sums)
    give back the √-barrier.
- That asymptotic is Patterson's theorem. The twisted Kubota series continues meromorphically, with the residue at
  s₀ given by the theta coefficients. Its only known proof is through the Eisenstein series on the n-fold cover of
  SL₂ over Q(ω), acting on hyperbolic 3-space.
- The K-wall needs more: off-pole sums at square-root size on average over twists. That needs the functional
  equation as well, and with it the twist-aspect conductor.

**Lean inventory.** Nothing in the local stacks (OpenAI baseline, Sil's `FourthPower`/`CubeFree`, PR 93, our forks,
Mathlib, PNT+) mentions Kubota, Patterson or metaplectic forms, except our own docstrings. The analytic tools
present are Poisson summation over Z[ω] with Schwartz weights, Gauss-sum algebra, the optimal sextic large sieve,
and Hecke-type L-function facts. Hecke's continuation (theta series of lattices) is reachable with these. The
metaplectic one is not.

**Consequence for the faces program [assessment].**
- Mathematically the architecture holds: the corrected recursion, the Mellin rescue, and closure by induction on the
  scale.
- Its Lean cost is dominated by an item outside every stack: the metaplectic Eisenstein series for n = 3 and n = 6
  (continuation, residue = theta, functional equation). That is far larger than the sieve fork.
- The part that is formalizable now is the corrected recursion as a conditional reduction, with the spike
  correlations as hypotheses. It moves no θ by itself.
- The same barrier sits under every route that cancels the theta bias: Dunn–Radziwiłł (target 0), D1's (L2), the
  reference detector. P1 and B2 need critical-line moments instead, which is the other open class.

**Twist-aspect conductor: the numerical test is confounded [numerical, inconclusive].**
- Plan: a smooth pole-free sum stops once X exceeds the conductor, so the stopping point of
  Σ_b u_b V(N(b)/X) χ_z(b) against N(z) measures the conductor. V is smooth on [1/8, 1] with three Mellin zeros
  around 5/6. The calibration is the plain sum (conductor N(z)).
- Outcome: the plain sums decay only slowly past N(z) (0.04–0.12 of the null at X/N(z) ≈ 1500–6000). The source set
  keeps only elements of squarefree norm, and that Möbius-type restriction leaves slowly decaying tails.
- The theta sums stay at 0.5–1.5 everywhere the plain sums have dropped (rows N(z) ∈ [16, 32] and [64, 128], X up
  to 10⁵). That is consistent with a conductor larger than N(z), but only 5 and 19 rows are available, so it does
  not fix the exponent.
- Theory: twisting g̃₃ by χ_m is the Kubota series at index m² (g(r, c) = conj(r/c) g(1, c), and r = m² gives
  conj(m²/c) = (m/c)). If the conductor in the index is N(r), as Heath-Brown's convexity bound
  ψ(r, 1 + it) ≪ N(r)^{1/4+ε} suggests, the twist conductor is N(m)². [recollection; not checked against the paper]
  That is the case where the K-wall needs the induction on the scale (previous entry).
- **Checked: double Dirichlet series do not bypass it [literature + derived].** Brubaker–Bump's functional equation
  for Kubota's series is cited as resting on Eisenstein series. The structural reason is this.
  - In Z(s, w) = Σ_{c,d} (d/c)₃ N(c)^{−s} N(d)^{−w}, either order of summation gives Hecke L-functions.
  - Once the functional equation in s has been applied, the d-sum carries cubic Gauss sums g(χ_d). The functional
    equation in w then needs Kubota's series, not a Hecke L-function.
  - So the Kubota series is the rank-one input of the multiple-Dirichlet-series machinery, not one of its outputs.

## 2026-10-31 · The twist-aspect mean value holds numerically: Mellin-zero vectors are at the null against every twist up to B

[numerical; `rip/theta/theta_twist_meanvalue.py`, logs `theta_twist_meanvalue_q3_L100000.log`,
`theta_twist_meanvalue_q6_L100000.log`]

**Question (from "Sil's inclusion monotonicity").** The corrected sieve subtracts Σ_{N(m)≤μ}(B/N(m))^{1/n}|⟨λ, f_m⟩|²,
f_m the twisted source thetas. The K-wall needs this ≲ B^{1+γ}‖λ‖², so the correlations must be at square-root size
on average over twists of every size up to μ = B^{1−nγ}. A theta loss in the twist aspect (growth like N(m)^{1/n})
would cap the method at γ ≥ 1/(n(n+1)).

**Test.**
- λ = V(N(b)/L) is plain and smooth on [L/8, L], L = 10⁵, with Mellin zeros at three points around the pole s₀
  (V~(s₀) ≈ 10⁻¹⁷). The control V₀ is a single bump (V₀~(s₀) ≈ 0.44–0.51).
- For twists m in dyadic ranges from [16, 32] to [65536, 131072]: R = mean_m |Σ_b λ_b g(b) χ_m(b)|²/‖λ‖², in both
  orientations g and conj g. The null is i.i.d. phases on the same zero pattern (≈ 0.94).

| twists N(m) | rows | cubic λ·conj g | cubic V₀·conj g | sextic λ·conj g | sextic V₀·conj g |
|---|---|---|---|---|---|
| [128, 256] | 37 | 0.73 | 28.6 | 1.07 | 1.19 |
| [1024, 2048] | 294 | 0.97 | 13.5 | 1.01 | 1.24 |
| [8192, 16384] | 2311 | 0.89 | 8.2 | 1.00 | 1.31 |
| [65536, 131072] | 18491 | 0.90 | 4.4 | 0.94 | 1.20 |

- The spike sits in the conj g orientation. In the g orientation even the control is at the null.
- Cubic control: 52.7 at [16, 32], falling to 4.4 at [65536, 131072]. That is the slope N(m)^{−0.30}, close to the
  N(m)^{−1/3} that |τ(m)|² predicts. So the pole terms matter for every twist up to B.
- Sextic control: a flat 1.2–1.7, a weaker theta.
- With the Mellin zero both families are at the null in every range with at least 37 rows: 0.73–1.29 (cubic) and
  0.87–1.11 (sextic, from N(m) ≈ 128). There is **no growth with the twist size**.
- Plain (Hecke) calibration: Σ V χ_m is small while N(m) ≪ L (0.04–0.4) and reaches the null at N(m) ≈ L.

**Reading.**
- For the K-wall's simplest vectors the twist-aspect requirement holds as stated. The correction sum is about
  ‖λ‖²Σ_{m≤μ}(B/N(m))^{1/n} = B^{1−(n−1)γ}‖λ‖², below the target B^{1+γ}‖λ‖².
- The conductor question of the previous entry therefore makes no numerical difference here. Either the twist
  conductor is N(m), or the level-2 pole of the twist sieve is killed by the same Mellin zero (the levels share the
  pole).
- Still open numerically: the actual leaf vector is a convolution of two plain factors times a slot. The
  correlations of a convolution are bilinear Kubota sums with poles in each variable, so both factors need the zero.
- Proof status unchanged: the statement is Patterson-type (previous entry).

## 2026-10-31 · Exact orthogonality cannot be the corrected sieve's form: the dilation family fills the space

[derived]

- In each Poisson step the dual vectors are λ·g̃·1_{(b,r)=1} for r up to R = (K/μ)^{1/n} = B^γ. By Möbius, the
  coprimality is a sum of restrictions to multiples of d | r. A restriction to d | b is a dilation: the sub-problem
  with vector λ_{d·} at scale B/N(d), whose spikes pull back to dilated twisted thetas (twisted by d^{±1}; journal,
  "Restriction carries no spike").
- In precondition form ("λ ⊥ S_k"), S_{k+1}(B) must contain the dilations by d ≤ R of u·S_k(B/N(d)). After k steps
  the dilations are by products d₁⋯d_k, up to R^k = B^{kγ}. Convergence needs k ≈ log(1/ε)/γ steps, so the
  dilations reach every d ≤ B.
- Dimension count: dim S ≈ Σ_{N(D) ≤ B} τ_k(D) (B/N(D))^{1−nγ} ≈ B (log B)^{k−1}, the whole source space. Exact
  orthogonality to the accumulated family is vacuous.
- So the corrected sieve has to be stated in weighted form, G ≼ B^{1+γ}·I + Σ_f w_f f f*, with the weights carried
  through the recursion. A dilated spike at scale B/N(d) carries the sub-problem's strength, which falls with N(d).
- The content then sits in the application: Σ_f w_f |⟨λ, f⟩|² must be small for the vectors used. For the K-wall's
  plain vectors this is a twist- and dilation-aspect mean value of off-pole Kubota sums. The twist aspect alone is
  confirmed numerically (previous entry); dilations are untested.
- Consequence for `OFFSPIKE_PROOF_PLAN.md` and `SourceSpike.lean`: the target statement should be the weighted form,
  not orthogonality to a fixed span. The fixed-span statements remain true numerically at the sizes tested but are
  not what the recursion can prove.
- **Dilation aspect = twist aspect at smaller scales [derived + numerical].** A dilated twisted theta 1_{d|b} u(b/d)
  χ_m(b/d) meets the Mellin-zero vector in Σ_{b′} V(N(d)N(b′)/L) g(b′) conj χ_m(b′). This is the twist-aspect sum
  at scale L/N(d) with a rescaled weight, and rescaling keeps the Mellin zero.
  - Rerun at L = 10⁴ and 3·10⁴ (cubic; logs `theta_twist_meanvalue_q3_L10000.log`, `..._L30000.log`): the Mellin-zero
    vector is at the null in every twist range (0.82–1.09 wherever there are ≥ 74 rows).
  - The control at the smallest twists grows with the scale as the pole predicts: 13.7, 28.0 and 52.7 at
    L = 10⁴, 3·10⁴, 10⁵, about L^{0.59} against L^{2/3}.
  - So with weights falling in N(d), the dilated corrections are harmless for these vectors as well.

## 2026-10-31 · Correction: the OpenAI baseline does formalize the cubic metaplectic theory

[Lean, read: `openai_baseline/OAI/NumberTheory/DirichletL/Eisenstein/` (82 files, 53,369 lines) and `GaussSum/`]

- **The entry "The Mellin rescue needs Patterson's continuation, which no Lean stack has" is wrong on its central
  claim.** My grep searched for the words Kubota, Patterson and metaplectic. The baseline does not use those names,
  but it formalizes the objects.
- **What is there.**
  - `Eisenstein/` (namespace `CubicEisenstein`, with `CubicKubota.levelThree`): the Kubota Eisenstein series on the
    cubic cover over hyperbolic 3-space (`HyperbolicSpace`, `FundamentalDomain`, `CoordinateLaplacian`,
    `GreenIdentity`).
  - Its continuation, by a resolvent argument (`MeromorphicResolvent`, `FredholmAlternative`).
  - The scattering coefficients and residues (`ScatteringCoefficients`, `ScatteringResidues`, `CuspResidues`).
  - The residue's Fourier expansion: the cubic theta, `cubicResidualFunction`, `ResidualFourierExpansion`.
  - Patterson's coefficients at squarefree × cube indices (`SquarefreeCoefficients`:
    `infinityCoefficient_squarefree`, `sourceArithmeticResidue_squarefree_cube_support`).
  - `GaussSum/BesselReflection`, `continuedBesselDirichlet_reflection`: a functional equation with the Gamma factors
    Γ(s+1/3)Γ(s+2/3) ↔ Γ(4/3−s)Γ(5/3−s) of the cubic Kubota series.
  - These are used by the baseline's inversion and moments (`Moments/FirstPoisson`, `Inversion/ReflectedArithmeticHeight`,
    `GaussSum/ReflectionPool`, …). The sextic family reaches the cubic theta through Möbius absorption
    (μ·conj g̃₆·α ∝ g̃₃).
- **Consequence.** The "Lean barrier" paragraph and the frontier note are withdrawn. The real question is narrower:
  which of the statements the faces program needs (the asymptotic for smooth twisted cubic Gauss-sum sums with
  residue at 5/6, uniform in the twist and the weight, and the mean values over twists) follow from what the baseline
  proves, and which need extensions (the sextic theta τ₆ is not covered by the cubic theory). Mapping that next.

## 2026-10-31 · Convolution leaf vectors: one Mellin zero in either factor removes the spike

[numerical; `rip/theta/theta_twist_meanvalue_conv.py`, logs `theta_twist_meanvalue_conv_q3_L100000.log`,
`..._q6_L100000.log`; derived: the mechanism]

- **Setting.** The K-wall's leaf vector is a convolution of two plain factors, λ = U₁ * U₂, here with
  X₁ = X₂ = √L, L = 10⁵. On our source set the divisors of b are the subsets of the primes of N(b), so
  λ_b = F(N(b)) with F(n) = Σ_{d|n} U₁(d/X₁) U₂(n/(dX₂)). The correlations with the twisted thetas are bilinear
  Kubota sums.
- **Cubic** (ratio to the null, twist ranges [64, 128] → [65536, 131072]):
  - both factors with Mellin zeros: 0.92–1.00;
  - a zero in either one factor only: 0.76–0.93;
  - neither: 4.2 → 1.26, the spike, decaying with the twist size.
- **Sextic**: all four variants at the null (0.63–1.48 at [64, 128] with 19 rows, 0.84–1.07 elsewhere). The sextic
  theta is weak here (single-factor control 1.2–1.7, previous entries), and a convolution carries a product of two
  residues.
- **Mechanism [derived].**
  - With twisted multiplicativity, the term that keeps the pole in b₂ has residue ∝ τ(b₁)-type coefficients.
  - The remaining b₁-sum is Σ U₁ g̃ τ ∝ Σ U₁ N^{−1/6} (cubic). Its main term needs Ũ₁ at the same point 5/6.
  - So a zero in one factor kills both the double-pole and the single-pole terms. This is the "levels share the pole"
    phenomenon again.
- **Consequence for the K-wall.** Only one of the two plain factors needs the designed weight. The other factor's
  weight stays free (the dyadic partition can be kept).

**Conductor note (cross-reference).** #96's Thm N1, read in the P1 deep-dive (2026-10-30), gives index conductor
N(m)¹ and twist conductor N(a)². So the twist-aspect mean value is the lossy case of the large-sieve accounting
("Sil's inclusion monotonicity", last items). The measured absence of loss (twist-aspect entry) then says the level-2
pole of the twist sieve is killed by the same Mellin zero.

## 2026-10-31 · The weighted corrected bound transposes with explicit image corrections

[derived; short proof]

**Problem.** Sil's recursion bounds the dual (fewer rows than columns) through the swap θ(L, N) = θ(N, L), an
operator-norm identity. A corrected statement is about vectors. It must survive transposition, and the corrections
of the transposed statement must be explicit, so that the application can evaluate them as Kubota-type sums.

**Lemma.** Let E be a matrix. Suppose that for all λ, ‖Eλ‖² ≤ Δ‖λ‖² + Σ_f w_f |⟨λ, f⟩|² with w_f ≥ 0. Then for all x,

  ‖E*x‖² ≤ 2Δ‖x‖² + Δ⁻¹ Σ_f w_f |⟨x, E f⟩|².

**Proof.**
1. Put λ = E*x. Then ‖EE*x‖² ≤ Δ‖E*x‖² + Σ w_f |⟨E*x, f⟩|², and ⟨E*x, f⟩ = ⟨x, Ef⟩.
2. ‖E*x‖⁴ = ⟨x, EE*x⟩² ≤ ‖x‖²‖EE*x‖². With y = ‖E*x‖², a = ‖x‖² and S = Σ w_f|⟨x, Ef⟩|², this gives
   y² ≤ aΔy + aS.
3. Hence y ≤ aΔ + √(aS) ≤ 2aΔ + S/Δ (AM–GM on √(aS) ≤ aΔ + S/(4Δ)).

In precondition form it reads: λ ⊥ F ⇒ ‖Eλ‖² ≤ Δ‖λ‖² gives x ⊥ E(F) ⇒ ‖E*x‖² ≤ Δ‖x‖², by the same three lines with
S = 0.

**Consequence.** The corrections of the transposed problem are the images Ef of the original ones. These are the row
images of twisted thetas, explicit Kubota-type sums (≈ L^{1/3}τ(zm) by the residue picture), not implicit polar
vectors. So the swap in `completed_of_exponent` has a corrected analogue at the cost of a factor 2 in Δ and weights
w_f/Δ.

**State of the corrected recursion's form.**
- Weighted, not precondition: dilations accumulate (entry above).
- Explicit corrections throughout: twisted thetas, closed under the level shift u·f, restriction or dilation, images
  under E (this lemma), and heights.
- Every member's correlation with a Mellin-zero vector is a Kubota-type sum. Numerically all of them are at the null
  (twist, dilation and convolution entries). The proof of each needs the continuation for the relevant cover.

## 2026-10-31 · The faces need the 6-fold cover: plain vectors see the Möbius-signed cubic series

[derived]

- By Davenport–Hasse and Möbius absorption (`orders/`), the sextic source spike direction is
  conj g̃₆(b) = μ(b)·g̃₃(b)·(Hecke character × class function × angular factor). This is the reason
  `SourceSpike.lean`'s source shapes carry an optional `liouvilleSign`.
- So a plain smooth vector's spike correlation, Σ_b U(N(b)/X)·conj f_m(b), is a **Möbius-signed** twisted cubic
  Kubota sum. Its analytic theory is that of the sextic series (6-fold cover, pole at 2/3), not the cubic one.
- Only Liouville-signed source vectors would meet the cubic series directly, and those are coefficients of
  L(2s, χ²)/L(s, χ), the inverse word. The faces' plain sums are coefficients of L(s, χ) itself.
- The same holds for convolutions of plain factors: a product of two Möbius-signed cubic sums with cross symbols.

**Sizing.** The faces program needs the 6-fold Kubota Eisenstein series: continuation, the residue at 2/3, and growth
on Re s = 1/2, uniformly in twists. The baseline's cubic development (`OAI/.../Eisenstein/`, 53k lines) is the
template; how much of it is generic in the order is the question for the mapping in progress. P1 and B2, after
absorption, live in the cubic world the baseline already covers, but they are critical-line (moment) problems.

## 2026-10-31 · Target 2 needs one corrected Poisson step, with the dual bounded by Sil's existing sieve

[read: Sil's `SieveDescent` (`lambda_sixth_extraction`, `lambda_scale_descent`) and `SievePoissonSeries`; derived]

- After one Poisson step in the rows, the original problem's source spikes are the dual frequencies whose
  sixth-power-free kernel is ≤ μ. Removing them is a **row restriction** of the dual, which is an operator-level
  statement. Only the top level is vector-level.
- One step, sources B ≤ rows A, K = B²/A:
  ‖E_{A,B}λ‖² ≤ C(AB)^ε { A‖λ‖² + (A/B)·‖E^{>μ}_{K,B}‖²·‖λ‖² + (A/B) Σ_{N(h) ≤ K, kernel ≤ μ} w_h |⟨λ, f_h⟩|² }.
- Sil's descent restricted to kernels above μ gives ‖E^{>μ}_{K,B}‖² ≤ Σ_{D: K/N(D)⁶ > μ} θ(K/N(D)⁶, B). With his
  proved bound θ(K′, B) ≤ B + K′^{7/6+ε} + B^{5/6}K′^{1/3} (K′ ≤ B), this is at most
  (K/μ)^{1/6}·B + K^{7/6+ε} + B^{5/6}K^{1/3}.
- Times A/B, the terms are A(B²/(Aμ))^{1/6} (the corrected theta term), A^{−1/6}B^{4/3} and A^{2/3}B^{1/2}. In the
  reference regime B ≤ A^{2/3} the last two are ≤ A. With μ = K the first is A.
- **So in the reference regime the sextic large sieve is the diagonal plus the spike part:**
  ‖E_{A,B}λ‖² ≤ C(AB)^ε {A‖λ‖² + (A/B) Σ_{N(h) ≤ K} w_h |⟨λ, f_h⟩|²}, w_h ≈ (K/N(h))^{1/6}.
  - This makes precise the earlier remark ("the √-barrier term is exactly the spike part").
  - It is provable by a moderate fork of Sil's Poisson bound: keep the small-kernel frequencies as correlations, and
    restrict the descent. No recursion is needed.
- **Target 2 then splits into:**
  1. this decomposition (Lean, Sil fork);
  2. the spike part small for the reference vectors: a twist-aspect mean value of Mellin-zero sextic correlations up
     to N(h) ≤ B²/A ≤ A^{1/3} (numerically at the null, entries above; the proof needs the 6-fold Kubota theory).
- The K-wall (balanced point) still needs the full corrected recursion.

## 2026-10-31 · D1 by row splitting needs the K-wall but not the reference wall, and only γ ≲ 0.03

[derived from `lean/arvi_primeface/RowSplit.lean`'s ledger; heuristic where marked]

- **Ledger (RowSplit.lean).** Split the twisted fourth moment Σ_z |A|²|Q|² by the pool's amplitude class
  |Q|² ≈ ‖a‖² Z^{σs}. A class is harmless iff σs + sel(σ) ≤ 1, where Z^{sel(σ)} bounds the plain energy on its rows.
  - PR 93 gives sel(σ) ≤ max(μ, 1 − σ + σμ) for σ > 1/2.
  - At that fixed point every class is harmless on the ideal face μ + s ≤ 1 (`class_le_of_fixPt`).
- **With a corrected K-wall of excess γ″** (sel(σ) ≤ fixPt(σ, μ) + γ″ for σ ≤ 1/2), the worst class is σ = 1/2. It
  needs s/2 + (1/2 + μ/2) + γ″ ≤ 1, i.e. **μ + s ≤ 1 − 2γ″**.
- **The γ″ needed [heuristic, the binding point read as μ ≈ 0.86].** Λ_eff = (1 − μ)/s = 0.14/(0.14 − 2γ″). The bar
  (Λ ≈ 1.95 by D1's price table, interpolated) then needs **γ″ ≲ 0.034**.
- **Low slopes are cheap.** With only the full-family bound (sel = 1), a class costs σs. The recursion route (task
  197) targets slopes above 1/q + 1/q² ≈ 0.19 (n = 6). Below that the cost is ≤ 0.19 s ≈ 0.013–0.027 for
  s = 0.07–0.14, inside the same budget.
- **What D1 avoids.** It is a face proved outside Sil's packing, so it needs no reference wall (target 2) and no fork
  of Sil's reference. It needs:
  1. the corrected sieve with amplification on slot-selected rows (the K-wall), at excess γ″ ≈ 0.03, for slopes
     ≈ 0.19–0.5;
  2. the Mellin rescue for the plain product A = X₁X₂. One designed factor suffices (convolution entry), and it needs
     the 6-fold theory;
  3. the face machinery forked to accept a D1 face.
- **Comparison with the faces route.** That route needs the K-wall (γ ≈ 0.015 at slope 0.48) and target 2. D1 needs
  the K-wall at a comparable or larger γ, over a range of slopes, and no target 2. On present knowledge D1 is the
  cheaper route to the bar.

**Correction to the D1 entry above (same evening) [derived].**
- The item "low slopes are cheap" is wrong. A class with only the full-family bound (sel = 1) cannot be made
  harmless by shrinking the face: σs + 1 ≤ 1 fails for every μ, because sel = 1 does not fall with μ. That is why
  `RowSplit.lean` says row splitting without the K-wall falls back to PR #97's leaf (Λ = 2).
- So D1 by row splitting needs dilution at **every** slope σ ∈ (0, 1/2]. A constant K-wall excess γ″ is absorbable
  (face μ + s ≤ 1 − 2γ″, from the worst class σ = 1/2). A missing range of slopes is not.
- Our K-wall chain covers δ > 7/36 only. `SpikeRule.lean`: the graded block weights C B^{ε/q}(B/M)^{1/q} times the
  amplification (M/B)^δ sum to B^{o(1)} exactly when δ > 1/q + 1/q². With it (and the graded spike-free
  conjecture), sel(σ) ≤ fixPt(σ, μ) + ε for σ > 7/36.
- The gap σ ∈ (0, 7/36] is open. Small σ needs only a small saving Z^{−σs}, so a weaker argument might do. A
  dilution excess γ_low(σ) ≤ c·σ·s with c < 1 would leave a face (σs(1 − c) ≤ shrinkage). Not attempted.
- D1's comparison with the faces route stands for the reference wall, but D1 adds this low-slope gap.
- **Why the faces route has no such gap [read: E5 entry; derived].** In the native step, rows below the slope
  threshold δ are not bounded by energy. They are deleted at rate δ (PR #97's leaf: price δ·deletionNeed), which
  gives the overshoot gate Λ > 6δB/(1 + δ).
  - Λ = 1.95 needs δ ≈ 0.481, inside the spike rule's range δ > 7/36.
  - At δ = 7/36 the overshoot gate would sit at 6(7/36)/(1 + 7/36) ≈ 0.98, i.e. it would stop binding, and the
    reference gate (target 2) decides Λ.
  - So the faces route needs the K-wall only near slope 0.48 (with target 2). D1 needs it at every slope unless D1
    can also delete the low classes. Whether it can is open.

## 2026-10-31 · What the recursion must deliver: a generated-family version of `GradedTwoSided`

[read: `lean/arvi_kwall/SourceSpike.lean`, `SpikeRule.lean`; derived]

- `GradedTwoSided k q` is a weighted corrected form at the balanced point. Its corrections are fixed: row twisted
  thetas (`spikeVector`) and the row images of the source spikes (`rowImage … sourceSpike`), with twists up to
  `twistCutoff`, height profiles up to `profileCutoff`, and graded weights.
  - `selected_of_gradedTwoSided` turns it into the selected bound C B^{1+ε} + Λ_row + Λ_src on any row set W, with
    Λ_row and Λ_src the Bessel constants of the weighted corrections on W.
  - The spike rule (`SpikeRule.lean`) then gives the K-wall for slopes δ > 7/36.
- The recursion (entries above) generates a larger explicit family:
  - the level shifts u·f;
  - dilations and restrictions;
  - images under E (transposition);
  - heights.

  So the statement it can prove is `GradedTwoSided` with the family replaced by the generated one. Nothing
  downstream changes: `selected_of_corrected` and the spike rule take any family, and only the Bessel constants on W
  grow. In the application these are sums of Kubota-type correlations of the K-wall vectors, killed by the Mellin
  zero numerically.
- **The program in Lean, in dependency order:**
  1. the generated-family corrected sieve (a Sil fork: kernel split in the Poisson bound, restricted descent,
     transposition via `TransposeCorrection.lean`, `silStep` iteration);
  2. Bessel bounds for the K-wall vectors on slot-selected rows: the Mellin rescue (6-fold Kubota theory, after
     the cubic template in the baseline) and Λ_row (row thetas on W);
  3. the spike rule plus PR 93 amplification (in Lean);
  4. the face forks: native or density with target 2 (faces route), or D1 with the low-slope gap.

## 2026-10-31 · What the baseline's metaplectic Lean theory covers: pole-free sums only

[agent mapping of `openai_baseline/OAI/NumberTheory/DirichletL/` (Eisenstein/, GaussSum/, …); two central claims
spot-checked in the source by me]

**What is proved [Lean, read].**
- **The cubic Kubota Eisenstein series.** The constant term ζ-ratio is proved. The h ≠ 0 coefficients are
  continued only meromorphically on {1 < Re s, 0 < Im s} and at s = 4/3, via the resolvent and a Fredholm
  argument (`E/WhittakerContinuation`, `E/MeromorphicResolvent`).
- The residue at 4/3 is the cubic theta (5/6 normalized). Its coefficients at squarefree c are Patterson's Gauss
  sums (`infinityCoefficient_squarefree`), with squarefree × cube support and a prime recurrence. There is no
  continuation to a half-plane and no bound on any line left of the pole.
- **Reflection exists only for the pole-free series.** Every cusp-reflection theorem is for the horizontal
  Wirtinger-∂̄ derivative of conj θ₃ (`cuspBarProfile`; spot-checked). That derivative kills the constant term
  v^{2/3}, i.e. the pole.
  - The reflected coefficients are `squarefreeGaussCoefficient c = conj(c/|c|)·g̃₃(c)` (spot-checked), the
    angular-twisted cubic Gauss sums.
  - The exact Voronoi identity is `completedT_canonical_smoothed_reflection` (`E/FullFrequencyExpansion:530`), for
    periodic twists ψ and smooth compactly supported weights.
  - With the proved kernel decay and coefficient bounds it gives Σ_c W(N(c)/X) conj(c/|c|) g̃₃(c) ψ(c) ≪
    X^{1/2}·cond^{O(1)}. The assembly into one statement is not in Lean.
- **Sextic.** Only Möbius absorption, `moebius_star_gauss_one_eq_coefficient` (spot-checked):
  μ(c)·conj g̃₆(c) = G(c)⁻¹·conj(c/|c|)·g̃₃(c), with G depending only on c mod 4. There is no 6-fold cover.

**Reading.**
- Pole-free sums are covered: Möbius-signed sextic sums (equivalently angular-twisted cubic ones) have square-root
  bounds via the baseline's reflection. This is the baseline's own mechanism ("Möbius vectors avoid the theta
  spike").
- **Polar sums are not covered, even for n = 3.** The Mellin rescue needs exactly the polar asymptotic: plain smooth
  vectors against sextic (or cubic) thetas.
- Liouville-signed plain vectors (μ(b)U(b)) would be pole-free and covered. The faces' plain sums are coefficients
  of L(s, χ) and carry no sign.
- **A concrete formalization target.** The expansions of the cubic residue with constant term
  3π·(residue)·v^{2/3} are in Lean (`cubicResidualFunction`, `sourceCusp_bessel_expansion`). Extending the cusp
  reflection from ∂̄ conj θ₃ to conj θ₃ itself, keeping the constant term, would give the cubic polar Voronoi
  formula: main term from v^{2/3} plus a dual sum. That is the cubic Mellin rescue.
- The faces' sextic case needs the 6-fold cover besides; the cubic development is its template.

## 2026-10-31 · Liouville-signed test: inconclusive, the cached Gauss sums use another normalization

[numerical; `theta_twist_meanvalue.py` with Liouville-signed columns, logs `theta_twist_meanvalue_mu_q{3,6}_L100000.log`]

- **Prediction (baseline's Möbius absorption).** μ(c)·conj g̃₆(c) = G(c)⁻¹·conj(c/|c|)·g̃₃(c) is pole-free. So
  Liouville-signed plain vectors μ(b)V₀ should be at the null against the sextic spikes, with no Mellin zero.
- **Cubic.** As predicted: μV₀·conj g is at the null (0.75–1.40, null ≈ 0.94–1.3 in the small ranges), while
  V₀·conj g runs 35.9 → 4.4.
- **Sextic.** μV₀·conj g keeps the plain control's excess (1.17–1.44 against 1.2–1.7), while a Mellin zero removes
  it.
- **The cached Gauss sums do not satisfy the identity in our normalization.** On the 10⁵ cache, the best
  combination, μ·conj(g6)·ang/g3, equals its class representative (mod 4 × mod 9 in both coordinates) for only 75% of
  sources. The ratio is +0.78 on average at primes and +0.23 for two prime factors. Without μ the result is the same.
  - So the theta cache's g6 and g3 differ from the baseline's `canonicalProductGauss` normalization by a non-class
    sign, likely the cross-term and primary conventions in the product formula. The "Liouville sign" here is not the
    baseline's μ-normalization, and the sextic column cannot be read.
- **The `orders/` numerics, computed in the baseline's convention, already confirm the prediction.** μ·conj g̃₆
  partial sums cancel better than random (slope 0.28–0.30), while g̃₆ grows like X^{2/3} (`orders/README.md`).
- **Consequence for earlier sextic numerics [caveat].** The theta cache is spike-aligned (large, growing, Mellin-killable
  excesses), so the qualitative findings stand. But quantitative sextic excesses may be understated if the cache
  differs from the canonical g̃₆ by a non-class sign. Rebuilding the sextic cache in the baseline's normalization
  (`orders/gauss_mobius.py` has it) is the fix before any further sextic quantities are quoted.

## 2026-10-31 · The cached sextic Gauss sums, resolved; Möbius signs kill the sextic spike as predicted

[numerical; logs `theta_twist_meanvalue_canon_q6_L100000.log`, `theta_twist_meanvalue_conv_canon_q6_L100000.log`;
derived: the mechanism]

- **Why the cache differs from the canonical normalization [derived, then checked].**
  - The theta cache builds g6 of a source c by twisted multiplicativity over its primes, each normalized ≡ 2 mod 3.
    So it computes g6 of the element (−1)^{k+1}c (k = number of prime factors). That changes the sum by
    χ_c(−1)^{k+1}.
  - This is a factor μ(c) exactly on the classes with χ_c(−1) = −1, i.e. N(c) ≡ 7 mod 12. The cubic sum is immune
    (−1 is a cube).
  - Check: μ·conj(g6)·ang/g3 is constant on mod-4 × mod-9 classes for 100% of the N(c) ≡ 1 mod 12 sources and 50.8%
    of the N(c) ≡ 7 mod 12 ones. It is 100% constant once the classes include the parity of k.
- **Which earlier numerics are affected.**
  - The class-compressed tests (`theta_level2`, `theta_pole_scan`, `theta_level_profile`, …) include the parity
    bit in their 72 classes, so they absorb the factor and are unaffected.
  - The raw twist tests mixed polar and pole-free halves. They understated the sextic excess; the conclusions about
    Mellin zeros stand. `THETA_CANON=1` in `theta_twist_meanvalue*.py` applies the correction.
- **Canonical twist test (sextic, L = 10⁵, null ≈ 0.90–1.16):**

  | twists N(m) | plain V₀·conj g | Liouville μV₀·conj g | Mellin-zero λ·conj g |
  |---|---|---|---|
  | [256, 512] | 1.68 | 0.90 | 0.89 |
  | [4096, 8192] | 1.73 | 0.97 | 0.89 |
  | [65536, 131072] | 1.40 | 0.95 | 0.95 |

  - The plain spike is stronger than measured before (1.4–1.76 against 1.2–1.3).
  - **The Liouville-signed vector is at the null, as Möbius absorption predicts** (μ·conj g̃₆ is the angular-twisted
    cubic sum, which the baseline's reflection covers with no main term). This replaces the "inconclusive" reading
    of the previous entry.
  - The convolution of two √L factors stays at the null in all four variants in the canonical normalization too.
- **Reading.** Two mechanisms remove the sextic source spike from a plain-type vector: a Mellin zero at the pole, or a
  Möbius (Liouville) sign. Only the second has a proof route in the baseline's existing Lean (pole-free reflection),
  but the faces' plain sums carry no sign.

## 2026-10-31 · Mollified convolution shapes: the pole sits in the long factor

[numerical; `theta_twist_meanvalue_conv.py` with a Möbius × plain column, logs
`theta_twist_meanvalue_mollified_q{3,6}_X{100,1000}.log`]

- **Test.** λ_b = Σ_{d | N(b)} μ(d)V₀(d/X₁)V₀(N(b)/(dX₂)) at L = 10⁵ (X₁X₂ = L), against the twisted source thetas.
  R is measured per dyadic twist range. The null is ≈ 0.91–1.05. Sextic numbers use `THETA_CANON=1`.
- **Cubic.**

  | twists N(m) | plain × plain | μ short (X₁ = 100) × plain | μ long (X₁ = 1000) × plain | Mellin zero in the long factor | Mellin zero in the short factor |
  |---|---|---|---|---|---|
  | [256, 512] | 3.61 | 3.32 | 1.27 | 1.00 | 1.67 |
  | [4096, 8192] | 2.36 | 2.26 | 1.13 | 0.95 | 1.36 |
  | [65536, 131072] | 1.41 | 1.37 | 0.96 | 0.94 | 1.09 |

- **Sextic, canonical.** Plain × plain is 1.08 / 1.11 / 1.03 in the same ranges (null 1.03 / 0.96 / 0.94). The
  short-Möbius shape is 1.13 / 1.09 / 1.02 and the long-Möbius shape 0.79 / 0.88 / 0.93. A single plain V₀ is
  1.68 / 1.73 / 1.40.
- **Reading.** The pole lives in whichever factor is long. A Möbius sign or a Mellin zero removes the spike only
  there. A mollifier block shorter than the plain block leaves the spike as it was.
  - In the sextic family the bilinear shape alone removes most of the spike. The pole there is weaker: the single-sum
    excess grows like X^{1/3} against the cubic X^{2/3}, so at factor length 10³ little is left.
  - The K-wall's convolution vectors therefore need their design (zero or sign) in the long factor, which is free:
    either factor can carry it.

## 2026-10-31 · The cubic polar Voronoi formula: not blocked, about 3k lines of Lean

[mapping of the baseline's Lean by an agent; spot-checked:
- `fullFunction_horizontal_hasDerivAt` drops the constant through `.const_add`;
- `sourceCuspBesselConstant = ![3π·cAR, 0, 0]`;
- `fixedThetaTwist` vanishes off primary elements;
- the multiplier algebra below.]

- **Why the baseline differentiates.** Its Mellin shift (`completedT_mellin_shift`, GaussSum/BesselReflection) needs
  an entire Mellin transform of the cusp profile. The undifferentiated profile is ~v^{2/3} at ∞, so that fails. ∂̄
  kills the constant term v^{2/3}. The angular factor and the v⁻² of the reflection law are by-products of this
  choice.
- **Already in Lean.**
  - Expansions with constants at the three cusp types (`sourceCusp_bessel_expansion`, constants 3π·cAR, 0, 0) and
    arbitrary cusps through `three_cusp_decomposition`.
  - The constant's value and nonvanishing (`constantArithmeticResidue_ne_zero`).
  - Automorphy of θ, exponential decay of the undifferentiated series, and finite translations with the zero mode.
  - Pole-crossing contour tools (`verticalIntegral_simple_pole`, the Gaussian-regulated shift).
- **Observation (agent's derivation, not a Lean lemma).** The twisted total has no zero mode at ∞:
  Σ_h w_h = φ(0) = `fixedThetaTwist` of a non-primary element = 0. So only the dual-cusp constants (v → 0)
  contribute: one simple pole, with residue C₁ = conj(3π·cAR)·Σ_{h of type 0} w_h κ_h Q_h^{−2/3}.
- **Missing.**
  - Five templated twins of the ∂̄ chain: the plain reflection at a cusp datum; the polar profile as a Bessel series;
    the polar Dirichlet series and Möbius inversion; the polar reflection algebra (s ↦ −s, no v⁻²).
  - Three new pieces:
    1. Mellin continuation with one simple pole. It must be reorganised around the total, because individual
       profiles are not Mellin-entire.
    2. A contour shift across the pole under the crude e^{2π|t|} bound, by Gaussian-damped pole subtraction.
    3. The polar Voronoi kernel, with multiplier gammaMultiplier(w)/(w² − 1/36) =
       Γ(w − 1/6)Γ(w + 1/6)/(Γ(5/6 − w)Γ(7/6 − w)). The identity is checked from the Lean definition. That this is
       the right kernel is the agent's derivation.
- **Size.** About 3k lines, of which about 1k is the three new pieces. Roughly 1–3 months at human pace.
- **What it buys.** The cubic polar asymptotic Σ g̃₃(c)ψ(c)W(N(c)/X) = main term + dual sum, i.e. the cubic Mellin
  rescue. The faces' sextic spikes need the 6-fold cover besides; the cubic twin is its template.

## 2026-10-31 · The sextic series as a Rankin–Selberg square of the cubic theta: no shortcut past the 6-fold cover

[derived; Lean, read: `infinityCoefficient_squarefree`, `infinityCoefficient_squarefree_cube`; literature, read:
de Faveri–Dunn–Hoffstein arXiv 2607.07911 §§1.2, 2, 5, 7; Bröker–Hoffstein arXiv 1312.0568 §1; X. Li arXiv
2208.07343 Thm 1.1]

**The cubic Mellin rescue is a published theorem [literature].**
- David–de Faveri–Dunn–Stucky (arXiv 2410.03048), Lemma 6.7, as used in dFDH (2.3)–(2.5): for squarefree
  a ≡ 1 mod 3,
  Σ_b (a/b)₃ g̃₃(b)H(N(b)/B) = P_B(a) + R_B(a), with P_B(a) ∝ H̃(5/6)·g̃₃(a)N(a)^{−1/6}B^{5/6} and
  R_B(a) ≪ B^{1/2+ε}Σ_{d | a} N(d)^{−1/2−ε}∫|ψ⁽³⁾(a/d, 1 + ε + iy)|(1 + |y|)^{−100}dy.
- Their Lemma 6.6 (dFDH (2.9)) is Lindelöf on average in the twist: Σ_{N(a)≤A}|ψ⁽³⁾(a, 1 + ε + it)|² ≪
  A^{1+ε}(1 + |t|)^R.
- Together: for H̃(5/6) = 0 the twisted correlations have mean square ≪ (AB)^{1+ε} over twists N(a) ≤ A. That is
  exactly the cubic twist-aspect mean value our numerics found at the null. It is unconditional.
- **The sextic analogue is not in the literature.** dFDH §1.2 expect the n ≥ 5 analogues "within reach of current
  tools", via n-fold metaplectic Eisenstein series with level structure (their §2.2 names the needed sums,
  Σ τ_n(r₁a)τ_n(r₂a) with uniformity in r₁, r₂).

**The Rankin–Selberg identity [derived].**
- On squarefree c, g̃₆ = g̃₃²·(class) (`orders/`, exact). Patterson's coefficients are τ₃(c) = κ·(class)·conj g̃₃(c)
  (`infinityCoefficient_squarefree`). So the sextic Kubota series is, up to class twists, Σ_{c sqfree} τ₃(c)²N(c)^{−w}.
- θ₃ transforms by the Kubota character κ, which has order 3. So θ₃² transforms by κ², and θ₃²·E_κ(·, s) is
  Γ-invariant, where E_κ is the cubic Kubota Eisenstein series whose residue at 4/3 is θ₃. Unfolding gives
  ∫_reg θ₃²E_κ(·, 2w) = γ(w)·D(w), with D(w) = Σ_δ τ₃(δ)τ₃(−δ)N(δ)^{−w} and γ the K_{1/3}² Mellin factor.
  - D has the sextic pole at w = 2/3, i.e. E_κ's theta pole at s = 4/3. Its leading coefficient involves the
    regularized ∫θ₃³.
  - So everything lives on the 3-fold cover, where the baseline already has θ₃, E_κ and the cusp expansions.
    dFDH §5 (Zagier's regularization on H³) is the template.
- **The cube support carries a zeta factor [derived from the Lean theorem].**
  - `infinityCoefficient_squarefree_cube` gives τ₃(c·d³) = N(d)^{1/2}·τ₃(c) for c squarefree and any d, with no
    character.
  - Hence, exactly, D(w) = ζ_K(3w − 1)·S(w), with S the squarefree sextic series.
  - The n-fold normalization (Bröker–Hoffstein: ζ_K(4w − 1)ψ₄ for n = 4; dFDH (2.10): ζ_K(3s − 2)ψ₃ for n = 3) is
    ζ_K(6w − 2)·S(w) nice for n = 6. So D = [ζ_K(u)/ζ_K(2u)]·(nice), with u = 3w − 1: the squarefree zeta.
  - Consistency check: the poles of D at zeros of ζ_K(6w − 2) are E_κ's poles at zeros of its scattering
    denominator ζ_K(3s − 2), s = 2w.
- **The obstruction.**
  - The Rankin–Selberg integral gives D. S = D/ζ_K(3w − 1) can then have poles at zeros of ζ_K(3w − 1), i.e.
    anywhere in 1/3 < Re w < 2/3 as far as the integral knows.
  - Shifting the contour to Re w = 1/2 + ε therefore needs RH for ζ_{ℚ(ω)}. Unconditionally the error is only
    X^{2/3}·exp(−c√log X).
  - The 6-fold theory instead puts the ζ-zero poles at Re w < 1/2 (zeros of ζ_K(6w − 2)). It is needed for a power
    saving.
  - Möbius over cubes does not help: every cube-dilated Rankin–Selberg term is N(d)^{1/2−3w}·D, so the inversion is
    exactly the division by ζ_K(3w − 1).
- **The bootstrap version [derived; partial].** Our own zero-free region (Hecke L-functions over ℚ(√−3) nonzero
  for Re > θ₀ ≈ 0.8734, inside the continuation argument) puts the poles of S at Re w ≤ (1 + θ₀)/3 ≈ 0.6245.
  - So the sextic polar asymptotic holds with error X^{0.6245+ε}·cond^{O(1)} unconditionally inside the
    bootstrap. That is a power saving X^{−0.042} below the main term X^{2/3}.
  - Twisted versions bring L(3w − 1, ψ_m) with ψ_m a quadratic Hecke character of K (the quadratic part of
    χ_m = χ₂·χ̄₃). Those are covered by the same hypothesis.
  - For the faces this is only partial: the squared spike excess drops from X^{1/3} to X^{0.249}, not to O(X^ε).
    Whether a partial rescue moves the walls at all needs the faces' quantitative model. The rescue would also
    become a bootstrap loop (better θ, better error).
- **P1's comparison class, rechecked.** X. Li (Invent. 2024) gets the second moment of quadratic twists of a
  modular L-function unconditionally with error X(log X)^{1/2+ε}: a log saving, as `frontier/README.md` says.

**Verdict.** The 6-fold cover is genuinely needed for a power-saving sextic Mellin rescue. A Rankin–Selberg square of
the cubic theta reaches the same series with the factor ζ_K(3w − 1) in the way. The only unconditional version is the
bootstrap's partial one. [the faces' sextic input stays a paper-level project]

## 2026-10-31 · The face the bar needs, at the banked design: Λ ≈ 1.967 (K ≈ 0.488)

[numerical; float model of the newTop row, `fresh-look/second/base_models/worth.py`, run with h = 0.8097]

- At h = 0.8097 and Λ = 2.0001 the model gives 0.87338228, the bank exactly.
- Against the bar θ ≤ 0.8733319666:

  | Λ (count and physical faces) | 1.98 | 1.97 | 1.96 | 1.95 | 1.94 |
  |---|---|---|---|---|---|
  | θ* − bar | +1.97e-5 | +4.2e-6 | −1.15e-5 | −2.74e-5 | −4.35e-5 |

  So the bar needs **Λ ≈ 1.967**, and Λ ≈ 1.951 at PR 97's design (h = 0.8001361). This corrects the range
  1.95–1.97 first written in `frontier/PROGRAM.md`.
- Through the native overshoot gate Λ = 6K/(1 + K) (B ≈ 1), Λ = 1.967 means K ≈ 0.488: a step of 0.012 below the
  K-wall. Small as it is, the K-wall entry's tolerance (excess γ ≈ 0.015 at slope ≈ 0.48) still asks for nearly the
  whole √-barrier excess to be removed. So the full corrected recursion stays necessary.
- `frontier/PROGRAM.md` collects the faces program on one page: inputs A (6-fold Kubota, index aspect), A′
  (Lindelöf on average), A″ (Mellin rescue), B (target-2 decomposition, a Sil fork), C (corrected recursion), D
  (Λ_row), E (face forks).

## 2026-10-31 · What the cubic polar Voronoi formula would feed (answering "is there a payoff?")

[Lean, read: the baseline's downstream use of cubic Gauss sums; Mathlib, read: `NumberTheory/LSeries/AbstractFuncEq`;
paper, read: PR 96's `02_ch_arithmetic.tex` (Theorem KUB, Theorem voronoi), `05_ch_nonpolar.tex`,
`inc_sec_sqclass.tex`]

- **No direct θ.** Downstream of `Eisenstein/` and `GaussSum/`, the baseline uses only the pole-free coefficient
  `squarefreeGaussCoefficient` (Arithmetic, Cusp, Descent, Detector, MeanSquare, RowCompletion). Patterson's polar
  coefficients occur only inside `Eisenstein/` and `GaussSum/`. That is by design: Möbius vectors meet only
  pole-free sums. So no existing estimate of the stack improves from a polar formula.
- **Consumer 1: the faces (`frontier/PROGRAM.md`).** There the formula is a template, since the faces' spikes are
  sextic. The payoff when the whole program lands is −5e-5 at Λ ≈ 1.967, rising to about −4e-4 near Λ = 5/3.
- **Consumer 2: PR 96's architecture.** Its Chapter 2 imports Kazhdan–Patterson (Publ. IHES 1984, with the 1985
  corrections) for n ∈ {3, 6}:
  - Theorem KUB: continuation, polynomial growth uniform in the index and the conductor, and the functional equation
    with archimedean ratio Φ_{n,l};
  - the Voronoi formula in the index aspect.
  - Downstream (Chapters 3–7, the square-class section) it uses only the cubic series D̃₃. Its D₆ is de Faveri's
    sieve exponent, not a 6-fold Kubota series. So PR 96 avoids the 6-fold cover, while our faces need it.
  - It needs twists θ_f·α^l·N^{−iτ} of nonzero infinity type l: the square-class charts take l ≠ 0, and the detector
    uses Größencharaktere of infinity type z̄/|z|. That needs Eisenstein series of non-spherical K-type. The
    baseline's spherical cubic series does not have them, and its ∂̄ trick carries only one angular factor.
  - So the 3k-line formula (spherical, l = 0, periodic twists) is the l = 0 slice of what PR 96 needs.
  - In PR 96's own constraint model (re-derived in `pr96/CONSTRAINTS.md`): 0.8791 with de Faveri plus the chart, and
    0.8656 with the Voronoi chart dpx. Both exceed the record by far, but they need a new probe layer (the OpenAI
    analogue is ≈ 264k lines) and the paper is unrefereed.
- **Order-generic core, rechecked.** Of the three new pieces of the cubic twin, the Mellin continuation with
  constant terms at both ends of a functional equation is Mathlib's `WeakFEPair`. It handles vector-valued f, g, so
  several cusps at once, and gives meromorphy, poles at 0 and k with explicit residues, and Λ₀(k − s) = ε·Λ₀^{symm}(s).
  - A cusp profile F(v) ~ c·v^{2/3} at ∞ with reflection F(v) = A·G(1/(Qv)) fits after f(x) = x^{−2/3}F(x) and the
    rescaling g̃(x) = g(x/Q): weight k = 4/3, ε = A·Q^{−2/3}.
  - So that piece is a short instantiation. The pole-crossing contour shift and the polar kernel remain the real
    work.

## 2026-10-31 · Polar sketch: the polar theorems with `sorry`, and what they buy downstream

[Lean, built: `lean/arvi_polar_sketch/` (`Polar`, `Bessel`, `KWall`); `polarInput` is the only `sorry`, every
consequence takes it as a hypothesis and is checked with standard axioms; derived: the interface findings]

At Arvi's request the polar theorems are stated first, with `sorry`, before committing to proofs.
- **Stated (`polarInput`, the one `sorry`).** For order q ∈ {6, 3} and smooth W on [v₀, v₁] ⊂ (0, ∞):
  - the pointwise polar asymptotic Σ W(N n/X) g̃(n) conj χ_n(m)^k = ρ(m) W̃(s₀) X^{s₀} + O(X^{1/2+ε}(1 + N m)^A);
  - Lindelöf on average over twists of norm ≤ M, with mean square ≪ (MX)^{1+ε}.
  It is written with the K-wall files' own objects (`gaussPhase`, `idealRowHom`, `twistBox`, `sexticSources`).
- **Proved from it.**
  - Mellin-zero vectors have square-root correlations.
  - The low-height remainder is an explicit term carrying W̃(s₀ − iγ).
  - `weighted_dyadic` / `weighted_bessel`: with spike strengths (B/N m)^{1/q},
    Σ w_m |⟨v, f_m⟩|² ≪ log M · B^{1/q} M^{1+ε−1/q} X^{1+ε}.
  - `kwall_source_term` + `source_exponent_le`: with input C in full-range form (`FullRangeCorrected`, an open
    hypothesis), the source-spike term sits below the diagonal B^{1+γ}‖v‖² once M ≤ B^{1−qγ}.
- **Interface findings.**
  1. Our `GradedTwoSided` (`lean/arvi_kwall/SourceSpike.lean`) corrects by spikes cut into sharp windows with power
     profiles. A Mellin-zero vector meets those with factors W̃(s₀ − j/2) and partial Mellin integrals that do not
     vanish. So input C must be stated with full-range spikes, which is also what a Poisson step produces.
  2. The Poisson coupling, separated by Mellin, twists the corrections by N^{it} with |t| ≲ 1, and a single zero
     at s₀ does not kill those. The numerics (`theta_level_profile`) show that the actual dual polar part acts as rank
     one in the radial direction, with a bounded floor. So C's correction functionals must be the actual dual polar
     functionals, and their rank-one radial structure needs a proof (a Rankin–Selberg-type lattice sum over the
     sixth-power copies). Not yet in any plan.
  3. The leaf and reference vectors are convolutions with prime slots. Their polar input needs the dilation aspect
     (twists m·b₂^{±k}). It is supported numerically but not derived.
  4. In the banked chain the walls are `SelectedRootEnergy K` (proved for K ≥ 0.500001; the bar needs K ≈ 0.488) and
     `ReferenceAt` clause 1, (L − 2)S, consumed in Sil's `RootParameters.interval_gap`.
- **Verdict so far.**
  - The polar input is a small, clean interface, and downstream it delivers exactly the K-wall's source term and the
    reference's spike term.
  - θ still needs input C in full-range form with rank-one correction functionals, the dilation-aspect polar input,
    a low-height argument, and the two bank forks.

## 2026-10-31 · Downstream to the bank: the bar needs K ≈ 0.487 and a short-reference threshold of only 0.51

[Lean: `lean/arvi_polar_sketch/RootEnergyFrom.lean`, `Walls.lean` (no `sorry`, standard axioms); numerical: float
model of the newTop row at h = 0.8097; derived]

**R1 below K = 1/2 reduces to one statement [Lean].**
- The banked R1 (`selectedRootEnergy`, K ∈ [0.500001, 3/4]) uses K ≥ 1/2 only through the threshold of Bebel's
  per-cell selected norm (`NaturalSelectedCellNorm`, slopes δ ≥ 1/2 + gap):
  - `cap_body` needs only 0 ≤ K ≤ 1 and the all-source norm at slope δ = K;
  - the histogram step (`FineSlotHistogram.cell_geometry`) uses δ ≥ 1/2 only for the constant smin/4. At δ ≥ 3/8 it
    gives smin/8;
  - the actual-slot plumbing and the peel/swap reductions do not look at K.
- `selectedRootEnergy_of_cellNormFrom`: the cell norm at slopes ≥ δ₀ (any δ₀ ≥ 3/8) gives `SelectedRootEnergy K` for
  every K ∈ [δ₀ + 10⁻⁶, 3/4]. The fork copies the banked declarations by script, with the threshold as a parameter.
  `selectedRootEnergy_banked` recovers the banked range at δ₀ = 1/2.
- So the K-wall, at the interface the bank consumes, is exactly `NaturalSelectedCellNormFrom δ₀`.

**The reference wall is a constant, not a slope [derived from `CubeFree/RootParameters.lean`].**
- The centred root exponent must lie below upperOne = (P − S − 1/2)/2. The 1/2 is the short reference's threshold
  (diagonal for B ≤ A^{1/2}; the identification is inferred, journal 2026-10-30).
- With a threshold γ, upperOne = (P − S − (1 − γ))/2. The interval condition becomes P + 2S + 9u/2 < 3/4 + γ/2.
  Through the face relation P + LS ≤ B, the first reserve clause reads (3/4 + γ/2 − B) + (L − 2)S − (9/2) sel S
  (`ReferenceAtγ`; `referenceAtγ_half` recovers `ReferenceAt`).
- The 2 in front of S does not move. A face Λ < 2 is paid by the constant: γ − 1/2 ≥ 2(2 − Λ + 9a/2)·cap − 2(1 − B).

**What each end face needs [numerical; `$SCRATCH/walls/walls_table.py`].** Banked cap line
c(Λ) = 1/10 + (3/50)(5143/2000 − Λ), B = 0.99999, a = 10⁻⁵. K is read off the overshoot gate with a 10⁻⁴ end margin.

| Λ | θ* − bar | K needed | γ needed | cap |
|---|---|---|---|---|
| 1.99 | +3.50e-5 | 0.4962 | 0.5027 | 0.1349 |
| 1.97 | +4.2e-6 | 0.4888 | 0.5082 | 0.1361 |
| 1.9675 | +3.1e-7 | 0.4879 | 0.5089 | 0.1362 |
| 1.965 | −3.6e-6 | 0.4870 | 0.5095 | 0.1364 |
| 1.95 | −2.74e-5 | 0.4815 | 0.5137 | 0.1373 |
| 1.93 | −5.98e-5 | 0.4742 | 0.5194 | 0.1385 |
| 1.90 | −1.10e-4 | 0.4634 | 0.5281 | 0.1403 |
| 1.85 | −1.78e-4 | 0.4458 | 0.5430 | 0.1433 |
| 1.80 | −2.07e-4 | 0.4285 | 0.5585 | 0.1463 |

**The walls' line in Lean [Lean].** With K₀ = 0.4869 and γ₀ = 0.51, every step of length ≤ 1/400000000 between faces
of the banked cap line in [1.965, 5143/2000]:
- passes the E5 gates, with `principal` replaced by the γ₀-reference at both ends of S ∈ [0, c] and by the two
  consequences that the ledger's selected branch uses (`walls_gates`);
- keeps Sil's reserves positive with the γ₀-reference (`walls_reference`).

At Λ = 1.965 the float model gives θ* = 0.87332836, 3.6e-6 below the bar. Not proved: that the steps exist. That
needs R1 at K₀, Sil's root reference forked to `ReferenceAtγ` with its short reference valid up to A^{0.51}, and a
small fork of `e5_ledger`.

**Reading.**
1. **The reference wall is small.**
   - The whole useful range needs γ ≤ 0.56 (and 0.51 at the bar), against target 2's 2/3.
   - In target 2's decomposition the corrections run over twists N(h) ≤ B²/A = A^{2γ−1}. That is A^{0.02} at
     γ = 0.51, so only tiny twists enter.
   - So the reference needs the polar input only pointwise, with polynomial dependence on N(h). It does not need
     the mean square over twists (input A′) [derived from target 2's shape].
2. **The K-wall binds.**
   - It must reach slope ≈ 0.487 with no excess (Z^{loss} for every loss > 0).
   - At the banked interface it is an operator bound on slot-selected rows, for all source vectors. A corrected
     sieve gives that only with the spikes' Bessel constants on those rows (Λ_row, Λ_src). The Mellin rescue does
     not reach Λ_src: it bounds correlations of specific vectors.
   - **To use the rescue, R1 must be re-proved per vector** [heuristic]:
     - amplify the leaf's packed polynomial by its heavy block;
     - bound the amplified vector on all rows with a one-sided corrected sieve;
     - then its spike correlations are dilation-aspect correlations of the Mellin-zero plain factors.
   - That is a fork of R1's body (`R1/Body.lean`, `RootBound`), not of the interface.
3. **The margin at the bar is thin.**
   - The bar is crossed at Λ ≈ 1.9673 (K ≈ 0.4877). A 1e-5 margin needs Λ ≈ 1.961 (K ≈ 0.4855).
   - The curve flattens near −2.1e-4 at Λ = 1.80 (K ≈ 0.43, γ ≈ 0.56).

## 2026-10-31 · Scoping the 6-fold Kubota port: the baseline has no functional equation or growth bound, even for n = 3

[agent map of `openai_baseline/OAI/NumberTheory/DirichletL/` (82 Eisenstein files, 53k lines); spot-checked by me:
the continuation region and the absence of any functional equation, scattering matrix or growth bound]

**Reusable [read].**
- About 14k lines are a generic analytic spine. Only 13 lines of it mention a symbol, λ or Gauss sum. It covers:
  - H³ geometry and fundamental domains (already stated for any H ≤ Γ(3));
  - the Laplacian, Green identity and cusp cutoffs;
  - the Dirichlet form, Friedrichs resolvent, Rellich compactness and coercivity;
  - Fredholm and meromorphic continuation;
  - Whittaker/Bessel Fourier expansions.
- n = 3 enters as data: the Kubota character on Γ(3) (cubic reciprocity), the centre 4/3, the cusp lattice 3O and
  9√3/2, and the 3-cusp decomposition. The rest is n = 3 arithmetic: the Fourier-coefficient identification, the
  λ-adic tables and the constant term ζ(3s − 3)/ζ(3s − 2).

**Sextic [agent numerics: random elements, exact arithmetic; evidence, not proof].**
- γ ↦ (c/a)₆ is a character on Γ(12) and Γ(24), but not on Γ(3), Γ(6) or Γ(9). On Γ(12), κ₆ = κ₃²·κ₂, matching the
  baseline's `sexticChar`. Only the quadratic Kubota character κ₂ is new.
- The index grows from 648 to 2,488,320. Γ(12)·SL₂(ℤ) has 21 cusps against 3, so the finite `decide` checks must go
  through CRT.

**Missing even for n = 3 [read; spot-checked].**
- The coefficients are proved `MeromorphicOn {1 < Re s, 0 < Im s}` and meromorphic at the centre 4/3
  (`WhittakerContinuation`), with the residue. There is nothing more:
  - no functional equation, scattering matrix or Maass–Selberg relation;
  - no bound in |Im s|, no Lindelöf.
- Absolute convergence holds only for Re s > 2. The only h-uniform bound is at a fixed s.

**Agent estimates (person-months, 100–150 new lines/day).**

| piece | content | estimate |
|---|---|---|
| N1a | sextic series, continuation on {Im > 0}, germ at 7/6 | 4–7 (5–9k new, 1.5–2.5k edited) |
| N1b | all of Re s > 1; "only pole at 7/6" | +2; +3–6 |
| N3 | functional equation with the scattering matrix over all cusps | 8–18 (10–25k) |
| N2 | polynomial growth: from N3 with Phragmén–Lindelöf, or a quantitative resolvent | +1–2; high risk |

Riskiest, in order: N3, the pole location, the 2-adic and λ-adic factors, N2's uniformity in m, and 21-cusp checks.

**Consequences for the faces program.**
- Input A (continuation, functional equation and growth of ψ⁽⁶⁾(m, w) in the index aspect) is N1a + N1b + N2 +
  probably N3: roughly 15–30 person-months, not the baseline's 53k lines reused.
- The cubic polar Voronoi estimate (about 3k lines) stands. It goes through the theta's own reflection, not the
  Eisenstein functional equation. But it is not a template for this cost: for n = 6 the Gauss-sum series is an
  Eisenstein coefficient, not a theta L-series, so it needs N2.
- Combined with the entry above: the reference wall needs A only pointwise for tiny twists. That still needs
  continuation past the pole with growth in |Im w|, i.e. N1b + N2. The cheaper cubic route covers only the cubic
  analogue.

## 2026-10-31 · The reference wall needs no metaplectic input: a prime-dilated short reference

[derived; every inequality used is a formal theorem of Sil's library or the baseline except the assembly. Not checked:
the higher Poisson levels, the gcd and collision bookkeeping, and how the reference's slot factor matches the face's S]

**Correction to the entry above.** Reading 1 there ("the reference needs the polar input only pointwise") is
superseded. The reference wall at the bar, and down to Λ ≈ 1.80, needs no information on individual spike
correlations.

**The vectors.** Sil's short reference (`uniform_actual_reference`) sieves, after one Poisson step in the long plain
sum, a source vector λ = α ⋆ a.
- α (the dual long plain times the short plain) has length X.
- a (the slot primes) has length P, is squarefree, and has support coprime to α's.
- Rows have norm ∼ A, and B = XP. Exponents in units of log A: b, S, x = b − S, k = 2b − 1.

**Step 1: one Poisson step [Lean pieces: `gram_pairing_poisson`, `pair_coupling`, `SieveUncoupling`].**
- On coprime pairs the Gram is exactly A·I plus dual terms (A/‖IJ‖)·Ŵ(A|k|²/|IJ|²)·f_k(I)·conj f_k(J)·(class sign),
  for k ≠ 0. Here f_k(b) = g̃(b)·conj χ_b(k), and only N(k) ≲ K = B²/A matter.
- Mellin separation of Ŵ and a split by classes mod 4 turn the dual part into
  ≪ (A/B)·Σ_{N k ≲ K} |⟨λ′, f_k⟩|², with λ′ = λ·N^{σ+it}·(class), again a convolution.

**Step 2: each spike correlation is a bilinear cubic form [derived; Gauss-sum multiplicativity and sextic
reciprocity are baseline theorems].**
- For coprime s, q: g̃(sq) = g̃(s)·g̃(q)·(q/s)₆²·η(s, q), with η a sign constant on classes mod 4. So
  ⟨α ⋆ a, f_k⟩ = Σ_{s,q} u_s v_q (q/s)₆^{−2}, where u_s = α_s conj g̃(s) χ_s(k) and v_q = a_q conj g̃(q) χ_q(k).
- Cauchy–Schwarz over q, and (s/q)₆² = (s/q²)₆, give
  |⟨λ, f_k⟩|² ≤ ‖a‖² · Σ_q |Σ_s u_s conj(s/q²)₆|² ≤ C (PX)^ε · majorant(P², X) · ‖λ‖².
  This is Sil's formal `OptimalBound` with rows {q²} (sixth-power-free) and columns {s}. It is **pointwise in k**:
  no information on any single spike, and no large sieve over the twists.

**Step 3: the count.**
- The dual part is ≪ (A/B)·K·majorant(P², X)·‖λ‖², so the sieve is diagonal when K·majorant(P², X) ≤ XP.
- In exponents that is k ≤ S, k + S ≤ x, 3k/2 + S ≤ x and k ≤ S/3 + x/6, i.e.
  b ≤ γ_pd(S) = min((1 + S)/2, 3/4 − S, (6 + S)/11).
- The diagonal pairs q₁ = q₂ reduce to α alone, with X ≤ A^{1/2} because b ≤ 1/2 + S. Sil's bound then gives
  A·‖α‖² there. Partial overlaps of q₁, q₂ give sub-problems of the same form with smaller P and K.

**Step 4: what the faces need [numerical; exponent check].**
- Clause 1 needs γ(S) = 2B − 3/2 + 2(2 − Λ + 9a/2)S at every S ∈ (0, cap]. The table below gives the worst value of
  γ_pd(S) − γ(S) over S ∈ (0, cap] (the binding end is S → 0, where both are ≈ 1/2):

  | Λ | γ needed at cap | γ_pd(cap) | worst γ_pd − γ |
  |---|---|---|---|
  | 1.9675 (the bar) | 0.5088 | 0.5578 | +1e-4 |
  | 1.93 | 0.5194 | 0.5580 | +1e-4 |
  | 1.85 | 0.5430 | 0.5585 | +0 |
  | 1.80 | 0.5585 | 0.5588 | +0 |

- So the prime-dilated reference covers every face down to Λ ≈ 1.80, where the float model flattens anyway.

**Why it works.**
- A theta spike is a Gauss-sum vector, and Gauss sums are only twisted-multiplicative.
- A convolution with a squarefree prime factor turns each spike correlation into a bilinear sextic form in
  (s, q²), and the √-barrier is then paid by the prime factor's length.
- At the balanced point (the K-wall, K ≈ B) the same bound fails by a factor of about X: there are K ≈ B
  frequencies, and pointwise bounds cannot sum them. So the K-wall still needs C and A.

**Remaining checks (all bookkeeping, no new estimate).**
- The higher Poisson levels for non-squarefree sources: imprimitive characters, with dual frequencies divisible by
  the square part. Each level's correlation is again bilinear in (s, q), with the symbol at the conductor part of s
  and τ-bounded fibres.
- The collision part, where a plain variable shares a slot prime (it lands in level 2).
- The gcd sorting of non-coprime pairs (Sil's `SieveGcd`).
- How the slot factor of `uniform_actual_reference`'s rectangle matches the S of `RootParameters.upperOne`.

**Consequences.**
- The bar's dependence on input A is now through the K-wall only.
- The reference fork becomes Lean engineering on Sil's library:
  - fork `SievePoissonBound` to keep the dual terms and bound them with the bilinear `OptimalBound` instead of the
    descent;
  - make `upperOne`'s threshold S-dependent, (P − S − (1 − γ_pd(S)))/2;
  - fork the native gates (`Walls.lean` has the scalar side).
- This does not move θ alone. The K-wall's overshoot gate still pins the native end at 2.003 (journal 2026-10-30).
- **The levels, in Sil's form (same day) [derived].**
  - Sil's sieve uses characters primitive mod the radical (`SievePrimitive.character`, `modulus I` = radical). So
    the coprime-pair dual terms are exact (`pair_poisson`), with no imprimitive levels.
  - Each carries the coupling c(I, J) = idealRowHom(rad J)(I)·conj idealRowHom(rad I)(J) (`pair_coupling`). By
    reciprocity, c(I, J) = (gen I / rad J)₆·conj(rad I / J)₆·(class sign).
  - Write every source as s = ρσ, with ρ = rad s and σ = gen s/rad s its square-full excess. Then, for slot
    factors q, q′ (squarefree, coprime to the plain parts), c(sq, s′q′) = (σ/ρ′q′)₆·conj(ρq/σ′)₆·(sign).
  - That is **rank one on each block pair (σ, σ′)**. Each block pair's dual form is X_{σσ′}·conj Y_{σ′σ}, where
    X_{σσ′} is the block's correlation with f_k twisted by (·/σ′). The bilinear bound of Step 2 applies to it
    pointwise.
  - For divisor-bounded plain factors (the reference's dual-long and short plain sums are), block σ carries mass
    ≪ ‖α‖²_∞·X/N(σ)². The double sum over (σ, σ′) of the square roots then costs only (log X)².
  - So the levels cost logarithms. The remaining bookkeeping is the gcd sorting of non-coprime pairs.
- **Numerical check (same day) [numerical: `rip/theta/theta_prime_dilation.py`, log
  `theta_prime_dilation_A1000000.log`].**
  - Setup: A = 10⁶ rows, sources N(x) ≤ L = 10⁴ = A^{2/3} (2610 sources). The table shows |E v|²/|v|² over the
    masked null.

  | vector | support | ratio |
  |---|---|---|
  | Gauss-sum vector conj g̃·(class sign) | 2610 | 1.193 |
  | Gauss vector ⋆ pool [7, 100] | 1388 | **0.994** |
  | same support, random phases | 1388 | 1.002 |
  | same support, Gauss phases (no dilation) | 1388 | **1.097** |
  | Gauss ⋆ pool [P₀, 2P₀], P₀ = 8, 20, 50 (a = 1 or conj g̃(p)) | 200–284 | 0.997–1.005 |
  | same supports, Gauss phases (no dilation) | 200–284 | 1.012–1.016 |

  - Convolving the spike direction itself with a prime pool removes the theta excess completely. The same support
    with Gauss phases keeps it.
  - The twisted-theta correlations of the convolutions are at the random level. This is the mechanism of Step 2,
    seen directly.
- **Why it cannot do the K-wall (same day) [derived].**
  - The bilinear bound holds for any convolution λ = α ⋆ β, of lengths X ≥ Y, not only for prime factors. It saves
    the factor XY/majorant(Y², X) per spike correlation.
  - That saving is at most B^{1/5} for Y ≤ B^{1/5}, and at most B^{2/9} overall (at Y = B^{1/3}, X = Y²).
  - The balanced corrected recursion (input C at excess γ) carries corrections over twists N(m) ≤ B^{1−6γ}, with
    weights (B/N m)^{1/6}. Absorbing them into B^{1+γ}‖λ‖² by pointwise bounds needs a saving of B^{1−6γ} per
    correlation: B^{0.91} at γ = 0.015, against at most B^{2/9}.
  - So the mechanism is a small-twist-range tool by nature. The reference needs a saving of only K = A^{0.02};
    the K-wall needs near square-root cancellation on average, which is what the Mellin rescue (input A) supplies.
- **Lean status of Step 2 (same day) [Lean: `lean/arvi_prime_dilation/`; no `sorry`, standard axioms].**
  - `bilinear_sieve`: the bilinear Cauchy–Schwarz plus Sil's `OptimalBound` with rows {q²}, as used in Step 2.
  - `phase_mul_unit`: Sil's phase is multiplicative on coprime sources up to `idealRowHom u (IJ)`, where u is the
    unit by which the arbitrary generator of the product's radical differs from the product of the factors'
    generators. The clean identity is not provable as stated (`literal_identity_at_one_iff`).
  - The unit factors are per-source or constant on classes (units × norms mod 36), so Step 2's bound survives.
  - **T3 done (same day)**: `Correlation.lean`. For squarefree supported ideals the radical modulus is the primary
    generator times a unit, so removing that unit gives a canonical phase `phaseCan` of modulus one that is exactly
    multiplicative (`phaseCan_mul`). With Sil's `row_reciprocity` (sign by classes mod 4) and
    `bilinear_sieve_squarefree` this gives `correlation_bound`:
    ‖Σ_{s,q} α_s a_q·conj(phaseCan(sq))·χ_k(sq)‖² ≤ C(P₂X)^ε·majorant(P₂, X)·Σ‖α‖²·Σ‖a‖², C = 16·C₀ (only the
    q-sum is split by class). Sources and slots are squarefree there; the long factor's non-squarefree part is
    still open.
  - Still to formalize: the Poisson fork itself (Sil's `coherent_weighted_bound` with the sixth-power-repeated dual
    rows kept as correlations and bounded by `correlation_bound`).

## 2026-10-31 · What input A must supply for the K-wall, and how much of it the levels supply themselves

[derived; heuristic where marked]

**C's weights close [derived].**
- In Sil's recursion the Poisson prefactors of consecutive levels multiply to 1: (M/N)·(L/N) = 1 with L = N²/M.
- So the correction weights keep their natural size, accumulate additively over the ≈ 400 levels, and pick up
  constant factors per level. With step 1 (the above/below split is an identity; restricted thetas are kept as
  corrections), input C is bookkeeping on Sil's proved code (`OFFSPIKE_PROOF_PLAN.md`).

**What the K-wall application needs [derived].**
- The requirement is Σ_{N m ≤ M} (B/N m)^{1/6} |⟨v, f_m⟩|² ≤ B^{1+γ}‖v‖², with M = B^{1−6γ}. That means average
  correlations of size B^{6γ}‖v‖² (B^{0.09} at γ = 0.015), i.e. square-root cancellation on average.
- **Small twists (N(m) ≤ B^c)** need the pointwise polar input: the Mellin zero removes the polar term, and the
  remainder is X^{1/2} N(m)^{O(1)}.
  - A contour shift to Re s = 1 + η (Re w = 1/2 + η) needs only meromorphy on Re s > 1 and some growth bound
    there.
  - With log-normal weights W(x) = exp(−(log x)²/σ²), whose Mellin transforms decay like exp(−σ²t²/4), even
    exponential growth exp(c|t|) suffices.
  - Exponential growth in t, polynomial in N(m), is what the baseline's resolvent route gives naturally: the
    resolvent norm is ≤ 1/(2η|t|), and the K-Bessel normalization of the coefficient costs e^{π|t|/2}.
  - So the small-twist part needs **no functional equation (N3)**. It needs N1a + N1b plus a quantitative resolvent
    bound that is exponential in t (the agent's "N2 spectral-only", in its easier exponential form).
- **Large twists (N(m) ≥ X²)**: the large sieve over the twists already gives square-root cancellation on average.
- **The middle range** is where A′ (Lindelöf on average) is needed. There the twist-aspect large sieve is balanced,
  and its own excess is the next level's spikes.

**The levels may supply A′ themselves [heuristic, to check].**
- Run C on the twist-aspect problem. The middle-range mean square becomes B^{1+γ} plus the correlations of the
  smooth factor with the level-2 functionals g̃₆²·χ.
- g̃₆² = (normalized Jacobi sum)·g̃₃, and the Jacobi sum is a Hecke character (Weil). So the level-2 correlations of
  smooth vectors are **cubic** Kubota sums twisted by a Hecke character: the cubic polar input. The baseline has
  θ₃ and its reflection, and the cubic polar Voronoi estimate is about 3k lines.
- Level 3 is g̃₆³·χ, an angle times a character: Hecke-character sums of smooth vectors, which are elementary.
- Level 4 returns to the sextic polar type at a smaller twist range.
- If this closes, input A for the bar is:
  - N1a + N1b + an exponential-in-t resolvent bound, for the sextic small-twist polar input;
  - the cubic polar input (baseline plus about 3k lines);
  - no functional equation N3, and no separate A′.
  That would be roughly 8–13 person-months instead of 15–30.
- **To check:**
  - that level 2's Jacobi-sum identity holds with the exact normalizations (Davenport–Hasse for sextic and cubic
    characters over ℤ[ω]);
  - that the level-4 return happens at a strictly smaller twist range, so the recursion terminates;
  - that the exponential resolvent bound is uniform in the index m, the agent's "windows at height 1/|m|" issue.

## 2026-10-31 · The depth family of the corrected recursion: Jacobi types, and a GRH-strength trap in "keep everything"

[numerical: `rip/jacobi/jacobi_type.py`, log `jacobi_type.log`; derived; the Möbius absorption identity is the
baseline's `moebius_star_gauss_one_eq_coefficient` (spot-checked, journal "What the baseline's metaplectic Lean theory
covers")]

**Correction to the entry above ("C's weights close"; "C is bookkeeping").**
- The weight telescoping stands.
- The design rule of step 1 does not: "keep every restricted theta as a correction" pushes GRH-strength sums into
  the application.

**The depth family.**
- Iterated Poisson in the rows always produces Gauss sums of the same source variable. So depth j of the recursion
  corrects by conj(g̃₆)^j·χ_k (journal, "In Sil's form").
- **Jacobi types [numerical].** For all 207 primes p ≡ 1 mod 3 below 3000, J(χ₆, χ₆) and J(χ₆, χ₆²) are unit
  multiples of π, never of π̄: infinity type +1.
- **Powers [derived].**
  - Davenport–Hasse gives g̃₆² = J̃(χ₆, χ₆)·g̃₃ and g̃₆³ = J̃(χ₆, χ₆)·J̃(χ₆, χ₆²)·g̃₂.
  - The CRT cross terms of g̃₆^j are (c₁/c₂)₆^{2j} up to reciprocity signs. They are cubic for j ≢ 0 mod 3 and
    trivial (signs) for j ≡ 0 mod 3.
  - Möbius absorption gives g̃₆ = μ·(mod-4 unit)·(angle)·conj g̃₃, so g̃₆^j carries μ^j.
  - Consistency of the two forces the normalized quadratic Gauss sum g̃₂(c) to carry μ(c).

| depth j | functional type | correlation with a smooth vector |
|---|---|---|
| 1 | μ·angle·cubic Gauss | the sextic pole (Kubota residue): needs the Mellin rescue (input A) |
| 2 | angle·cubic Gauss, no μ | pole-free angular cubic: the baseline's reflection |
| 3 | **μ·Hecke character** (type 2)·unit | **Möbius-signed Hecke sum: unconditionally only exp(−c√log X) saving** |
| 4 | angle·conj cubic Gauss, no μ | pole-free angular cubic |
| 5 | μ·(sextic twisted by a type-4 angle) | pole-free in principle, but sextic non-spherical theory or Heath-Brown–Patterson strength only |
| 6 | Hecke character, no μ | elementary |

**The trap [derived].**
- With "keep everything", the depth-3 corrections for the K-wall vectors (smooth ⋆ smooth ⋆ slots) are
  ⟨v, μ·Ξ·χ_{R₀}⟩.
- Since χ_{R₀} is completely multiplicative, these factor as a product of Möbius-signed Hecke sums over the three
  factors, each with only a PNT-type saving.
- At small R₀ the weights are ≈ B^{1/6}. The K-wall needs square-root cancellation on average (B^{6γ}).
- So the deferred depth-3 terms need GRH-strength input. The design rule must be dropped for depths ≥ 2.

**Why this is an artifact, not a spike [derived].**
- The depth-3 functionals μΞχ are not spikes of the operator. Their correlations with the level-1 spikes are
  Σ μΞχ·conj(g̃₆)χ_k: the μ's cancel (μ² = 1 on squarefree support), leaving a pole-free angular cubic sum.
- This matches the numerics (off the level-1 and row families the excess is +1.7%, against +16% for random spans).
- So the true corrected sieve likely needs only level-1-type corrections. Deeper depths arise only from the
  recursion's upper bounds.

**Where C's risk now sits.**
- C must show, inside the recursion, that the depth-j repeated rows (j ≥ 2) cost at most B^{1+γ} plus the true
  level-1 corrections, without keeping them as explicit corrections.
- The tools would be the pole-free bounds (the baseline's angular cubic reflection at even depths) and an
  operator-level argument at odd depths ≥ 3.
- That is no longer bookkeeping. **The non-classical risk of the faces route is back in C**, now located precisely:
  the odd depths ≥ 3 of the recursion.

## 2026-10-31 · Correction: the depth family alternates; there is no GRH trap

[derived from Sil's `dualTerm` with exact conjugations]

**The previous entry is wrong, and so is the level-family bullet of "In Sil's form".**
- Both assumed that depth j corrects by conj(g̃₆)^j·χ. That came from a conjugation error.
- Redone with `dualTerm`:
  - For fixed dual frequency k, the dual form is |Σ_j λ_j·phase(j)·conj(χ_k(j))|² with χ_k(j) = idealRowHom k (b_j).
    So the spike functional is **f_k = conj(phase)·χ_k**, and the depth-1 problem is E(conj(λ·phase)): rows k,
    since E₁(ν) = E(conj ν) for the conjugated row characters.
  - Applying the hypothesis's corrections to that vector gives
    ⟨conj(λ·phase), conj(phase)·χ_R⟩ = Σ conj(λ)·conj(phase)·phase·conj(χ_R) = conj⟨λ, conj χ_R⟩,
    a **plain character**.
  - The pull-back map is T(f) = conj(phase)·conj(f). It sends conj(phase)·χ to conj χ and conj χ to conj(phase)·χ:
    an involution, as the plan's "rotation f ↦ g̃·conj f" already said.
- So the depth family is **{conj(phase)·χ_R, conj χ_R}**, up to restrictions to columns coprime to D, Galois
  conjugation, N^{it} and class characters. **Phase powers never accumulate.**

**Consequences.**
- No μ·Hecke functionals arise, so there is no GRH-strength trap. The design rule of step 1 (keep the restricted
  thetas as corrections; every metaplectic fact goes to the application) is **reinstated**. Together with the
  telescoping weights, C is again bookkeeping on Sil's proved code.
- The application needs two things:
  - **odd depths** (conj(phase)·χ_R, restricted): the Mellin rescue, input A;
  - **even depths** (plain restricted characters): smooth character sums of the K-wall vectors. These are tiny for
    nontrivial χ_R of conductor ≪ X (Poisson). The trivial character, from sixth-power rows R₀ = 1, gives the mean
    |Σ_b λ_b|². That is removed by also asking W̃(1) = 0 of the plain weights, a second Mellin condition, free
    since the weights are caller-supplied.
- The Jacobi-type numerics (both sextic Jacobi sums are associates of π) and the identities
  g̃₆² = J̃·g̃₃, g̃₆³ = J̃·J̃′·g̃₂ stand as facts. They are not needed by the recursion.
- **Also withdrawn: "the levels may supply A′" (entry "What input A must supply").**
  - That claim rested on the same wrong level structure. With the alternating family, even depths are plain
    restricted characters, which stay elementary. But the middle-range twist mean square still needs Lindelöf on
    average.
  - C applied to the twist-aspect problem gives ≈ (H + B)^{1+γ}‖v‖² per dyadic twist range N(m) ∼ H. That is
    dominated by the source dimension B. The K-wall weights (B/H)^{1/6} need ≈ H·B^{O(γ)}‖v‖², i.e. square-root
    cancellation on average for every H < B.
  - Pointwise bounds X^{1/2}N(m)^{O(1)} cover only N(m) ≤ B^{O(γ)}.
  - Dilation by the short factors (twists m·u⁴) does not help: Cauchy–Schwarz over u inflates the twist dimension
    to M·U⁴.
  - So A′ is needed, and it needs the functional equation (approximate functional equation plus Sil's sieve; the
    cubic model is David–de Faveri–Dunn–Stucky Lemma 6.6). The estimate for input A stays at 15–30
    person-months.
  - What does survive: the small-twist pointwise part needs no functional equation (log-normal weights and an
    exponential-in-t resolvent bound).

## 2026-10-31 · Three Poisson steps give the twist mean square of one smooth factor; the K-wall's balanced corner is out of reach of input A

[derived; sketch with the technical points listed. Numerics cited: entries "The source spikes vanish for radial
weights with zero Mellin transform at the pole" and "Convolution leaf vectors"]

**The requirement, restated.**
- The K-wall's source term is Σ_{N m ≤ M} (B/N m)^{1/6}|⟨v, f_m⟩|² ≤ B^{1+γ}‖v‖², with M = B^{1−6γ}. Per dyadic twist
  range N(m) ∼ H this reads S_v(H) := Σ_{m∼H} |⟨v, f_m⟩|² ≤ B^{5/6+γ}H^{1/6}‖v‖².
- That is weaker than Lindelöf on average (H‖v‖²) for every H < B. The previous entry's "≈ H·B^{O(γ)}‖v‖² for every
  H < B" holds only near H ≈ B^{1−6γ}.
- The twist-aspect large sieve gives (H + X)‖v‖² for sources of length X. It suffices for H ≥ (X/B^{5/6+γ})⁶, which
  at the corner's X = B^{0.96} is H ≥ B^{0.67}. (Its own theta term re-counts the small twists with weights Σ_D N(D)^{−1}:
  a logarithm.)

**Three Poisson steps for one smooth factor [derived; sketch].** Take v_n = W(N n/X) and f_m = conj(phase)·χ_m.
1. **Poisson in m**, modulo n n′. The Gauss sums of conj χ_n·χ_{n′} cancel the phases (the involution of "Correction:
   the depth family alternates"). So S_v(H) is a diagonal of size HX plus
   (H/X)·Σ_{h≠0} φ̂(N(h)H/N(n n′))·Σ_{n,n′} W W′ ε(n, n′) χ_n(−h) conj χ_{n′}(h), with ε a sign by classes mod 4 and
   N(h) ≲ X²/H. The coupling is separated by a dyadic partition in h and a Mellin expansion on the compact box, which
   keeps every h-weight localized.
2. **Poisson in n**, for each h. The plain sum A(h) = Σ_n W(N n/X)χ_n(h) has dual length N(h)/X. It is negligible for
   non-sixth-power h with N(h) < X. Otherwise A(h)·conj A(h) = (X²/N h)·Σ_{k,k′} Ŵ Ŵ′·conj χ_h(k) χ_h(k′).
3. **Poisson in h**, for each (k, k′). By reciprocity conj χ_h(k)χ_h(k′) is a character in h of conductor
   ≤ N(k k′) ≤ (N(h)/X)². On a dyadic range N(h) ∼ H₁ ≤ X²/H the dual length is ≤ H₁/X² ≤ 1/H. So for H ≥ X^ε
   every non-principal pair is negligible.
- **What is left is explicit:**
  - the diagonal, and the pairs k = k′ (≈ −HX, cancelling the diagonal to leading order);
  - pairs with k/k′ a sixth power: O(HX + H^{2/3}X^{4/3}), the second ∝ |W̃(5/6)|²;
  - h a sixth power, where A(h) has a main term.
- **The pole.** After the Mellin separation the frequencies h = D⁶ give ζ_K(6s)·X^{2s+1}·W̃(s + 1/2)². The pole of
  ζ_K(6s) at s = 1/6 is the polar term H^{5/6}X^{4/3}|W̃(2/3)|². That is the numerics' pole at s₀ = 2/3, obtained
  without the 6-fold cover. The mean square needs only Σ_m |ρ(m)|², which comes out through ζ_K(6s); the individual
  residues ρ(m) never appear.
- The other explicit terms are ≤ HX + H^{2/3}X^{4/3}, below the requirement for X, H ≤ B. The bounded floor of the
  numerics (2.5% at H = X) is of this type.
- **Technical points, not yet written out.**
  - The sixth-power-free condition on sources: Möbius over d⁶ | n. Pairs with N(d d′)⁶ < H take steps 2–3. The
    others take step 3 directly in h, since then the conductor N(n n′) ≤ X²/N(d d′)⁶ is below the h-range.
  - Non-squarefree h: square-full parts up to H take the same argument; the rest cost X²H^{−1/2}, which is fine for
    H ≥ X^{1/4}.
- **Consequence.** A″ for a single smooth factor needs neither the functional equation (N3) nor A′. Step 1 is Sil's
  `pair_poisson`/`dualTerm`, and step 2 is the baseline's `actual_original_twisted_reflection`.
- **With a short arbitrary factor.** For v = (smooth, length X/Y) ⋆ (arbitrary, length Y), keep the short factor
  unexpanded in step 3. Its characters add conductor ≤ Y², so step 3 needs H > Y⁴. For H ≤ Y⁴, Cauchy–Schwarz over
  the short factor (twists m·y^{±2}) and the single-factor result at twist range HY² give S_v(H) ≲ HY²‖v‖². That is
  within the requirement when Y ≤ B^{5/32}.

**The K-wall's binding corner is a balanced convolution, and neither route reaches it [derived].**
- The ledger fails without a near-fixed-point norm only at x₁ ≈ x₂ ≈ 0.40–0.47, slots S ≈ 0.03–0.10, t = 0 (entry
  "How much selected norm the leaf needs below K = 1/2", 2026-10-30).
- R1 applies the selected norm to S₁S₂∏T_k or to its reflection S₁*S₂∏T_k. Either way the vector is two smooth plain
  factors of comparable length (B^{0.45–0.55}) times a short slot part.
- **Three Poissons fail there.**
  - Expanding both factors in step 2 gives conductor ≤ N(h)⁴/X² in step 3. Negligibility then needs
    N(h)³ < X²/H, i.e. it holds only on the bottom of the h-range.
  - Expanding one factor leaves the other as a short factor of length ≈ √X, so step 3 needs H > X².
- **A and A′ do not help there either.**
  - With the functional equation and the Mellin zero in U₁:
    c_m(U₁ ⋆ U₂) = X₁^{1/2}∫Ũ₁(1/2+it)X₁^{it}·Σ_{n₂} b_{n₂}(m) ψ(m n₂², 1/2+it) dt.
  - Cauchy–Schwarz over n₂, then A′ over all twists up to HX₂², gives S_v(H) ≲ HX₂²‖v‖². A′ cannot see that only
    the sparse set {m n₂²} is used. With X₂ = B^{0.48}, X₂² > B^{5/6+γ}, so this fails for every H.
  - Even a mean value over the sparse set ("A′ at dilated twists") would reach only H ≤ (B^{5/6+γ}/X₂)^{6/5} ≈ B^{0.44}.
  - The approximate functional equation of ψ(m n₂², ·) has length √H·X₂. The twist large sieve then gives
    (H + √H·X₂²)X₂, which also fails for every H.
  - Convexity pointwise, |ψ(m′, 1/2)| ≤ N(m′)^{1/4+ε}, is worse than trivial here.
- **What is covered without A.**
  - Pointwise, the cross term of twisted multiplicativity is cubic, so c_m(U₁ ⋆ U₂) is a bilinear form with kernel
    (n₂/n₁)₃. Heath-Brown's cubic large sieve [literature] gives |c_m|² ≤ X^{5/3+ε}, within the requirement for
    H ≤ B^{0.25}.
  - The twist large sieve covers H ≥ B^{0.67}.
- **The open band is B^{0.25} < N(m) < B^{0.67}.**
  - After step 1, the band is a power-saving asymptotic for the smoothed fourth moment
    Σ_h φ̂(N(h)H/X²)|A₁(h)A₂(h)|² of short sextic character sums: each of length ≈ √X, with moduli up to X²/H.
  - The saving needed is small: B^{0.11}H^{−1/6} over the trivial bound, about B^{0.04} at H = B^{0.44}.
  - But Poisson in h returns the twist mean square itself (the involution), so the argument is circular without a new
    input.
  - Equivalent forms of the missing input:
    - a large sieve for Kubota values at dilated twists, Σ_m |Σ_{n₂} b_{n₂}(m)ψ(m n₂², 1/2+it)|² ≪ (HX₂)^{1+ε};
    - Lindelöf on average in m for the divisor-weighted series Σ_n g̃(n) conj χ_n(m) σ_{w₁,w₂}(n) at
      w₁ = w₂ = 1/2.
  - For Dirichlet characters the analogous fourth moments are done with Kuznetsov's formula, so the natural tool here
    is the metaplectic Kuznetsov formula on the 6-fold cover. That is beyond input A.
- The corner also sits at t = 0, where a Mellin zero cannot remove the polar term for a whole segment of heights
  (entry "The source spikes vanish ...", low-height caveat).

**Consequences.**
- PROGRAM.md's row A″ ("convolutions with the zero in the long factor ... small once A, A′ exist") holds only when one
  factor dominates: Y ≲ B^{0.16}, or the dilation aspect. At the K-wall's binding corner it is not derived, and the
  15–30 person-months of A do not buy it.
- Away from the balanced corner, everything the K-wall needs is elementary: the three Poisson steps, Sil's sieve and
  C's bookkeeping.
- The open core of the K-wall is now one statement: the twist mean square of balanced smooth convolutions in the band
  B^{0.25} < N(m) < B^{0.67}. Its type is a fourth-moment asymptotic with power saving, with no known elementary or
  Kubota-theory route. So the faces route to the bar no longer has open inputs of known type.

## 2026-10-31 · The K-wall tolerates no excess: the selected norm must sit at its fixed point (ledger rescan)

[numerical: `selected-leaf/ledger_kwall_gamma.py` on `ledger_gamma.py`/`ledger_gamma2.py` (moved from scratch into the
repo), log `selected-leaf/logs/ledger_kwall_gamma_K048.log`; derived]

**Rescan.** Along the native line at K = 0.48, take the best of the selected branch (per-root norm
max(xe, (1 − δ + γ)y + δ·xe)) and the parent face. The quantity shown is max(price) − u.

| γ | worst, default slot grid (21 points) | where |
|---|---|---|
| 0 | −2.5e-3 (passes) | S ≈ 0.005, x₁ = x₂ = 0.495 |
| 0.002 | −5e-4 (passes) | grid edge |
| 0.004 | +4e-8 to +3e-7 | S ≈ 0.004–0.005, x = 0.495 |
| 0.01 | +1e-7 to +1e-6 | S ≈ 0.012–0.02, x ≈ 0.48 |
| 0.06, 0.1, 0.111 | +8e-7 to +7e-6 (the same for all three) | S ≈ 0.08–0.11, x ≈ 0.39–0.41 |

- With a 321-point slot grid, γ = 0.002, 0.001 and 0.0005 all fail, at S ≈ 0.0037, 0.0018 and 0.0009.
- **Reading.** At the balanced point with slot width s the selected price is γ − (1 − δ)s. So for any γ > 0 the
  geometries with s < γ/(1 − δ) need the parent face. There the parent face pays the selection's 6u row cost:
  (P + L₀s − B₀(1 − 6u))/L₀ ≈ 6uB₀/L₀ ≈ 2.6u > u at L₀ ≈ 2.3.
- So the tolerance is γ = 0. The earlier "γ ≲ 0.015" came from a coarse grid.
- **The K-wall needs the selected norm at its fixed point up to Z^ε.** At slot width → 0 that is the sextic large
  sieve at the balanced point at B^{1+ε} for the leaf's balanced convolutions: Lindelöf on average for a fourth
  moment of the sextic family.
- For the corrected recursion this is no change of plan (C targets 1 + ε anyway). But the open band of A‴ (previous
  entry) widens to B^{0.23} < N(m) < B^{0.76} at γ → 0.

**A bilinear improvement of the balanced point, and why it does not help [derived].**
- Take v = a ⋆ b with arbitrary coefficients on factors of length X₁ ≈ X₂ ≈ √X.
- After Sil's Poisson step the dual is the twist correlations c_h(v), h ≲ X²/B, with sixth-power multiplicity
  (L/N h)^{1/6}, L = X²/B.
- By twisted multiplicativity, c_h(v) is a bilinear form with the cubic kernel (n₂/n₁)₃. So Heath-Brown's cubic large
  sieve [literature] gives |c_h|² ≤ X^{2/3+ε}‖a‖²‖b‖² pointwise. The twist large sieve gives (H + X)‖v‖² on average.
- Taking the better of the two on each dyadic range (they cross at H = X^{1/3}):
  Σ_{N z ≤ B}|Σ_n (a ⋆ b)_n χ_z(n)|² ≪ B^ε(B + X + B^{5/6}X^{5/18})‖a‖²‖b‖², for B^{3/5} ≤ X ≤ B.
- At X = B that is B^{10/9} against B^{7/6}, i.e. excess 1/9 instead of Θ₆'s 1/6. It needs no metaplectic input and
  no Mellin zero.
- The rescan above shows that any γ > 0 leaves the K-wall failing at small S. So this is a correct improvement that
  buys nothing in θ.

**The face parameter B cannot replace K [numerical: `worth.theta_star`, h = 0.8097].**
- The overshoot gate is Λ₀ > 6BK/(1 + K). At K = 1/2, B ≈ 0.984 would allow Λ ≈ 1.967 without any K-wall.
- But θ* rises steeply as B falls:
  - (Λ, B) = (1.967, 0.99): +1.6e-4 above the bar;
  - (1.967, 0.985): +2.4e-4;
  - (1.967, 0.98): +3.3e-4;
  - (2.0001, 0.98): +3.7e-4;
  - against +5.0e-5 at (2.0001, 0.99999).
- So the face's B must stay at 1 − 10⁻⁵, and the bar needs K < 1/2.

**Status of the faces route.** The bar needs, at the K-wall's balanced corner, a sharp (Z^ε) fourth-moment bound for
the sextic family on balanced convolutions of smooth plain sums. Nothing in the program reaches it:
- input A and A′ (previous entry);
- three Poisson steps, which need one dominant factor;
- the bilinear cubic sieve (excess 1/9);
- prime dilation (saving ≤ B^{2/9});
- RIP-type designs (journal 2026-10-30).

## 2026-10-31 · Literature check (July 2026): the sextic balanced-point excess is real for general vectors; fourth moments are open

[web, abstracts and introduction read; arXiv 2607.07911, 2607.27131]

- **de Faveri–Dunn–Hoffstein, "Non-orthogonality of the cubic and quartic large sieves via Rankin–Selberg"
  (arXiv 2607.07911, July 2026).**
  - They prove Ξ₃(A, B) ≫ (AB)^{−ε}(A + B + (AB)^{2/3}): the cubic large sieve is optimal, so its (AB)^{2/3} term is
    attained.
  - For the quartic case they prove Ξ₄ ≫ (AB)^{−ε}(A + B + A^{3/4}B^{1/2} + A^{1/2}B^{3/4}).
  - **Conjecture (1.9)** for order n: Ξₙ(A, B) = (AB)^{o(1)}(A + B + A^{1−1/n}B^{2/n} + A^{2/n}B^{1−1/n}). For n = 6 the
    balanced value is X^{7/6}.
  - The extremal vectors are smooth Gauss-sum vectors conj(g̃₃(b))·H(N(b)/B), the program's spike directions.
  - Inputs:
    - (2.10), Lindelöf on average for the cubic Kubota series, Σ_{N(a)≤A}|ψ⁽³⁾(a, 1+ε+it)|² ≪ A^{1+ε}(1+|t|)^R (on the
      critical line in their normalization). That is input A′ for n = 3.
    - A lower bound for Σ|τ(a)|² of a Rankin–Selberg convolution of metaplectic thetas, by Zagier's regularization.
- **Diaconu–Ion–Paşol–Popa, second moments of r-th order Hecke L-functions (arXiv 2607.27131, July 2026).**
  - Asymptotics for the first and second twisted moments, r ≥ 3, over fields containing the 2r-th roots of unity, by
    multiple Dirichlet series.
  - r = 3 over ℚ(ω) qualifies. r = 6 over ℚ(ω) does not, since it needs ζ₁₂.
- **No fourth moment** of cubic or sextic Hecke L-functions at Lindelöf strength turned up.

**What this means here.**
- The excess 1/6 of the sextic sieve at the balanced point is (conjecturally) the true operator norm, attained by
  the spike directions. So the K-wall's fixed point (previous entry) can only come from the leaf vectors' structure.
  That has been the program's working assumption since 2026-10-30, and it is now backed by the literature's
  conjecture and by the n = 3, 4 theorems.
- The open input is A‴: the balanced-point sieve at B^{1+ε} for smooth plain × plain convolutions, i.e. Lindelöf on
  average for a fourth moment of the sextic family. It is beyond the present literature; the second-moment
  technology (DFDH (2.10), DIPP) stops at A′.
- **A check owed.** DFDH's cubic main term, the twist mean square of the smooth Gauss vector in the range
  √A < B < A², has exponent (AB)^{2/3}·B. The three-Poisson sketch ("Three Poisson steps …", above) gives the same
  exponent H^{2/3}X^{5/3}, from the pole of ζ_K(3s), with no Rankin–Selberg or Lindelöf input. DFDH use the heavier
  route, so the sketch must be compared with their method before anything rests on it. The step to check is step 3
  (negligibility of the non-principal (k, k′) after the coupling separation).

## 2026-10-31 · A new lever: the packed envelope's 6u. Each 0.1 off the 6 is worth ≈ 5e-5, with no K-wall

[derived from Sil's `CubeFree/Second/Side.lean` and `CubeFree/StepData.lean`; numerical:
`selected-leaf/envelope_c.py`, log `selected-leaf/logs/envelope_c.log`]

**Where the overshoot gate's 6 comes from.**
- Sil's packed envelope is H = 2a − k + q_C = 1 + t − 6u (CF (6.1), `envelope_identity`). Here u is the selected width,
  and the 6 splits as 2 + 4:
  - **2u**: the selected block D leaves the column, a = A − c − u, and a enters H twice;
  - **4u**: the **D⁴ transfer** (`Second/FourthTransfer.lean`). Twisted multiplicativity gives
    G(Dn; k) = (sign)·χ_n(D)²·G(D; k)·G(n; k), and χ_n(D)²G(n; k) = G(n; kD⁴). So the residual Gauss polynomial is
    evaluated at the row D⁴k, and the Gauss scale grows to k = K + 4u ("K·N(D)⁴").
- **The overshoot gate is this 6.**
  - On the boundary geometry (t = 0, PC + LS = B, s = S − u) the deletion price is
    κ(hS + u(c·B − L₀))/L₀, with c the envelope coefficient.
  - So retention needs a ≥ κh/(L₀(1 + κ) − cκB): that is native_line's `den` with c = 6, and it gives the gate
    Λ₀ > cκB/(1 + κ).
  - The selected-branch gate a ≤ (L − 1)/(c − 2) and the H gate 1 − c·a·cap > 0 carry the same c.

**Payoff [numerical].** Native line with K = 1/2 + 10⁻⁶ (PR 93's selected norm, banked), principal gate from
`ReferenceAtγ` with the prime-dilated short reference γ_pd(S), θ* from `worth.theta_star` (h = 0.8097):

| c | line ends at Λ | θ* − bar |
|---|---|---|
| 6.00 | 2.0007 | +5.1e-5 (the bank) |
| 5.95 | 1.9841 | +2.6e-5 |
| **5.90** | **1.9675** | **+3e-7 (the bar)** |
| 5.85 | 1.9509 | −2.6e-5 |
| 5.80 | 1.9344 | −5.3e-5 |
| 5.70 | 1.9014 | −1.1e-4 |
| 5.50 | 1.8371 | −1.9e-4 |

- With the plain reference (γ = 1/2) the principal gate stops every line near Λ ≈ 2.00–2.01. So the lever needs the
  reference wall, which is the part that needs no metaplectic input.
- **So the bar needs c ≤ 5.9 at K = 1/2, i.e. a saving of 0.1u out of the D⁴ transfer's 4u, and no K-wall.** The
  corner of the K-wall entries does not arise, since K = 1/2 + η keeps PR 93's fixed-point norm.

**Where the slack could be [derived; to check].**
- The transferred rows are z = D⁴k: D runs over the selected blocks (norm Z^u, at most Z^u of them) and k over a
  Gauss dyad of radius K. That is about K·Z^u rows inside a box of radius K·Z^{4u}. The envelope charges the radius.
- The rows are nearly orthogonal: χ_n(kD⁴)·conj χ_n(kD′⁴) = (D′²/D² / n)-type cubic characters of conductor
  ≤ Z^{2u}, small against columns of length Z^a ≫ Z^{2u}. So a sieve that counts rows instead of radius would
  charge u instead of 4u, the large sieve for power moduli in sextic form.
- Doing the D-sum outside instead (no transfer, Z^u separate sieves) costs a full Z^u in energy, the whole budget
  u. So the gain has to come from the dilated rows' structure inside Seam B, not from undoing the transfer.
- A D² transfer is not available: the factor's conjugation always matches the Gauss sum's (χ_n(D)² with G, or its
  conjugate with Ḡ), so the exponent is 4 mod 6 either way.
- **Next:** find where Seam B (WP-H: Seam A → packing dictionary → linear forms → weighted common separation)
  uses the Gauss scale. Whether the packed rows y can carry D as a separate short factor decides whether 0.1u is
  available.

**Addendum (same day): the envelope lever is R2's block-type ledger at the native line; c = 6 stays forced
[read: `newpowers/R2_ledger.md` §§0.2, 2, 4, 5.1; derived].**
- R2 writes a selected block type as (e, c, r): room, scale and width per unit selected width. Its descent condition
  is Λ₀ > c·q·B₀/(e + q·r).
  - Sil's simple D⁴ block is (1, 6, 1) (the `envelope_identity` arithmetic, [L]).
  - At q = K = 1/2 this is exactly the overshoot gate above. The bar needs c/(e + r/2) < 3.93, i.e. c ≤ 5.9 for
    e = r = 1.
- **Barriers at q = 1/2 for each block type:**

  | type | (e, c, r) | barrier |
  |---|---|---|
  | simple D⁴ | (1, 6, 1) | 2B |
  | D¹ with cubic twist, j = 0 | (0, 2 + κ, 1) | (2 + κ)B (no gain at κ ≥ 0) |
  | other twisted types | — | above 2B |
  | doubled D² | (2, 6, 1) | 1.2B |

- So the only known type that beats Λ = 2 at the native line is the doubled block.
  - The mixture law (payments add) gives a barrier of 3B/(1.5 + φ) for a doubled share φ. **The bar needs φ ≈ 2.5%.**
  - Squared-prime slots are not forced by zeros (`DIRECTIONS.md` D2: alignment a ≈ P^{β−1} ≪ 1/√2), so no
    current source supplies them. That needs new math.
- **The sparse-row idea does not escape.**
  - Keeping the rows D⁴w on their sublattices (or jointly, as a sparse union) instead of extending to the ball
    lengthens the second Poisson's dual.
  - R2 §4.3: the child's diagonal becomes W·U^{m′}, returning the count W.
  - The ball extension is the trade that makes the child short. It is not a waste.
  - What the bar would need is a joint estimate for the union ⋃_D D⁴O that keeps the child of the ball and pays
    less than 4u. That is a sparse-moduli (power-moduli) sextic large sieve with a saving of Z^{0.1u}; no route is
    known.
- **Net.** The envelope is a sharper statement of where the bar sits, not a new open door. The two inputs that would
  each clear the bar at the native line are:
  - a 2.5% doubled share (squared slots visible to zeros);
  - c ≤ 5.9 from a new block type.
  Each is new math, and neither is the K-wall's fourth moment.

## 2026-10-31 · Re-pricing the remaining levers on the current design; T8′ is dead here; the corner is the 6u again

[numerical: `worth.theta_star` variants (inline scripts, logged below); derived; summary table in
`frontier/BAR_STATUS.md`]

- **The end face's cap is not a lever.** At L = 2.0001 and 2.0007, θ* is unchanged for cap ∈ [0.134, 0.1666]. The
  binding (δ = 0.426, p = 1/2) does not see it.
- **The long slope.** θ* at L = 2.0001 for long-slope savings 0.16667, 0.16717, 0.16767, 0.16867, 0.17067 and
  0.17737: 0.87338228, 0.87338012, 0.87337796, 0.87337364, 0.87336499, 0.87333591. That is ≈ 4.3e-6 per 0.001,
  and the bar needs a saving of ≈ 0.178 (B2, as recorded on 2026-10-30).
- **The numerator capacity.**
  - In the model, C = min(numCap·d, (2y − (2 − B)d)/L). The face term binds at 0.05857, under numCap·d = 0.06073.
  - Adding ΔC to the face term gives θ* − bar = +3.9e-5, +2.8e-5 and +5.1e-6 at ΔC = 0.0005, 0.001 and 0.002, and
    −9.3e-6 at ΔC ≥ 0.0022, where the numerator cap binds. Raising numCap alone does nothing.
- **T8′ (two numerator packets, Cauchy–Schwarz midpoint) is dead on this design [derived].**
  - The midpoint rule gains only where the face envelope s*(P) is curved. On the old 130-face density chain it
    was (+0.0034 at P = 0.8512).
  - Along the native line B is fixed, so the capacity (B − P)/Λ is maximal at the end face for every P: one
    linear face. The midpoint average of a linear function is the function.
- **The K-wall corner is the 6u again [derived].**
  - At the failing geometries the parent face prices the selected rows at the envelope M = 1 − 6u and misses the
    budget u by (6B₀/L₀ − 1)u.
  - Any deletion tier at cost κ′ imposes L₀(1 + κ′) > 6κ′B. So for Λ < 2 every row with mass ≥ Z^{0.48·w} must
    be bounded by a norm, not deleted. A three-tier scheme (delete [Z^{κw}, Z^{w/2}) at cost 1/2) gives back
    exactly the κ = 1/2 gate.
  - The two obstructions at the native line, the overshoot gate and the corner, are both the ratio of Sil's
    envelope coefficient 6 to the budget.

## 2026-10-31 · The owed check: three Poisson steps against de Faveri–Dunn–Hoffstein; the polar shape is confirmed for n = 3 and 6

[read: arXiv 2607.07911 (abstract and introduction); derived; numerical: existing logs
`rip/theta/theta_twist_meanvalue_q3_L{10000,30000,100000}.log`, `theta_twist_meanvalue_canon_q6_L100000.log`]

**DFDH's route is different from ours [read].**
- Their test vector is β_b = conj g̃₃(b)·1_{b≡1}·H(N b/B) on squarefree twists a ≡ 1 mod 3. They work on the twist
  side: the Kubota series ψ⁽ⁿ⁾(a, s) splits each correlation into a polar term P_B(a) and a remainder R_B(a).
- Two inputs, both from Zagier's regularized Rankin–Selberg:
  - a lower bound for Σ_a |τ_n(a)|² (explicit for n = 3 through Patterson; for n = 4 there is no formula for τ₄);
  - Lindelöf on average for the second moment of ψ⁽ⁿ⁾(a, s), to control Σ_a |R_B(a)|².
- They note that convexity plus GRH, which worked for n = 3 before, does not give the right lower bound for n ≥ 4.

**The three-Poisson route works on the dual side [derived].**
- After Poisson in m, the Gauss sums cancel the phases. The polar term comes from the dual frequencies h = Dⁿ through
  ζ_K(ns) at s = 1/n. The individual theta coefficients never appear; their mean square comes out through ζ_K(ns).
- So it bypasses both of DFDH's inputs. It needs no functional equation and no Rankin–Selberg.
- Points re-derived today:
  1. **Step 3.** For each non-principal pair (k, k′), the h-sum is a smooth sum of a character of conductor
     ≤ C·N(k k′) ≤ C(N h/X)². Its Poisson dual has length ≤ H₁/X² ≤ 1/H. ✓
  2. **Non-squarefree h** (the sketch's "technical point", now checked).
     - Write h = h₁r with h₁ squarefree and r square-full, coprime. The conductor is h₁·rad r.
     - Möbius on h₁ (f² | h₁) is exact by step 3 for N(f) < √H, since the condition reduces to
       N(f)²·Q·N(rad r)²/(N(r)X²) < 1 and N(rad r)² ≤ N(r).
     - For the tail N(f) ≥ √H, Poisson back in k: the formal term equals N(f)·|S_f|², where S_f is a sum of
       length X/N(f). With the sextic large sieve over h′ this costs (H/X)·Σ_f (N(h₁)X/N(f)² + X²/N(f)), i.e.
       X²H^{−1/2} + HX·log Q. That is the sketch's X²H^{−1/2}.
  3. **Squarefree sources** (d² | n). The pairs with N(d d′)³ < H go through steps 2–3, because the cubic symbol
     (h/d)₃ adds conductor N(d). The rest are bounded by Cauchy–Schwarz and the large sieve,
     H·(Q + X)/N(d d′) ≈ X²/N(d d′), giving X²H^{−1/3}.
- **Result [derived; sketch with every step now written].** With the twists m running over all of O and the sources
  squarefree,
  Σ_m φ(N m/H) |Σ_n W(N n/X) conj g̃(n) χ_n(m)|² = C_n·W̃(1/2 + 1/n)²·H^{1−1/n}X^{1+2/n} + O((HX + X²H^{−1/3})(HX)^ε).
  The error terms are below the polar term for X^{4/7} ≪ H ≪ X² (n = 6) and X^{1/3} ≪ H ≪ X² (n = 3). The cubic
  numerics below show the polar shape already from H ≈ X^{0.24}, so the X²H^{−1/3} bound is pessimistic.
- **Where it falls short of DFDH.** Their theorem restricts the twists to squarefree a.
  - Möbius over e² | a is fine for small e: the dilated families have polar terms with weight N(e)^{4/n−3}, which
    is summable.
  - The tail N(e) > E needs Σ_{a: e²|a, N e > E} |c_a|² ≪ A^{1−1/n}B^{1+2/n}. The trivial bound and the large sieve
    both give √A·B² per unit of B, which suffices only for B ≪ √A. But B ≪ √A is exactly the range where the polar
    term is not above the diagonal A.
  - So the tail needs pointwise cancellation in sums of Gauss sums, which is Kubota theory. The elementary route
    proves non-orthogonality only for the large sieve over all twists, in √A < B < A (there the Gauss-sum term
    A^{1−1/n}B^{2/n} beats both A + B and the n-th power obstruction A^{1/n}B). This is weaker than DFDH's statement,
    but it holds for every n.

**Numerical check of the shape [numerical; existing logs, no new runs].** R = mean_m |c_m|²/‖λ‖² for the control
V0 with conj g̃ (no Mellin zero), against the masked null ≈ 0.94. The predicted relative excess is
∝ X^{2/n}H^{−1/n}.

| order | test | predicted | measured |
|---|---|---|---|
| 3 | excess per doubling of H at L = 10⁵ (12 doublings, H = 16 … 65536) | 2^{−1/3} = 0.794 | 0.80 on average; 51.8 → 3.49 against 3.24 |
| 3 | excess at H = 4096 for L = 10⁴ → 3·10⁴ → 10⁵ | ×2.08, ×2.23 | 1.99 → 4.21 → 8.68 (×2.12, ×2.06) |
| 3 | excess at H = 16384, same L | ×2.08, ×2.23 | 1.21 → 2.59 → 5.65 (×2.14, ×2.18) |
| 6 (canonical phases) | excess from H = 2¹² to 2¹⁷ | 2^{−5/6} = 0.56 | 0.79 → 0.45 (0.57) |
| 3, 6 | Mellin zero at s₀ (V) | at the null | at the null |

The non-canonical sextic run (class signs not normalized) shows a smaller, flatter excess (0.29 → 0.26). The class
signs ε(n, n′) of step 1 enter the polar constant as a quadratic form over classes; they shrink it there. The
constant C_n is not checked.

**Consequences.**
- The owed check is closed, up to the constant. The K-wall's single-factor input (twist mean square of a smooth
  factor with a Mellin zero) is elementary. Input A is not needed away from the balanced corner.
- **The corner, re-read once more [derived].**
  - The full-family fourth moment of plain sums is Lindelöf on average in the library (`plain_unmarked`,
    Lemma 18.1 at z = 0). So at zero slot width the corner holds.
  - For small positive slot width s, the full-family route with slots is Lemma 18.1 with slot cost 6κ, which is
    the parent face; it fails by the 6u.
  - The selected norm saves δS but needs γ ≤ δS.
  - So the corner needs the selected norm at its fixed point below slope 1/2 for leaf vectors with vanishing slot
    width, as recorded. No loophole in the ledger model.

**Correction, same day: the gcd(n, n′) pairs [derived].** The sketch above (and the entry "Three Poisson steps give
the twist mean square of one smooth factor") ignores source pairs with d = gcd(n, n′) > 1.
- For such a pair, step 1's modulus is lcm = d n₀ n₀′. The Gauss sums of n₀, n₀′ still cancel the phases.
- What is left:
  - a Ramanujan sum c_d(h) in the dual weight;
  - a character of conductor d in n₀ (the twisted-multiplicativity symbol (d/n₀)₃ times χ_{n₀}(d), together a
    sextic-type symbol mod d).
- So each d-block is the single-factor problem at length X_d = X/N(d), with an extra fixed character of conductor
  d.
- **Steps 2–3 for the d-block.** Write c_d(h) = Σ_{e | (d, h)} μ(d/e)N(e).
  - The terms with d | h (weight ≈ 1, h = d h′, N h′ ≲ X_d²/H) are explicit when N(d)² < H.
  - The terms with (h, d) = 1 (weight μ(d)/N(d), N h ≲ N(d)X_d²/H) are explicit when N(d)³ < H, since the
    step-3 conductor is (N(h)N(d)/X_d)².
- **The rest.** The twist large sieve at length X_d gives |block| ≪ (H + X_d)X_d·X^ε, i.e. X²/N(d)² for
  N(d) < X/H. In total:
  S(H) = (explicit) + O((HX + X²H^{−1/3})X^ε).
  This is the same size as the squarefree-source error, so the asymptotic of the entry above stands with error
  HX + X²H^{−1/3}.
- **Consequence for the K-wall's single-factor input (Mellin zero, need S(H) ≤ B^{5/6}H^{1/6}X).**
  - The error X²H^{−1/3} is within the need for H ≥ (X/B^{5/6})², i.e. H ≥ B^{0.25} at X = B^{0.96} and
    H ≥ B^{0.31} at X = B^{0.99}.
  - Below, the elementary pointwise bound covers H ≤ B^{0.21}–B^{0.23}. That bound comes from
    g̃₆ = μ·α·conj g̃₃·(class): Vaughan, with Heath-Brown's cubic sieve on Type II, gives |c_m|² ≪ X^{5/3}, but
    Type I needs twisted cubic Kubota sums.
  - So "away from the corner everything is elementary" holds only up to a small gap in the twist range,
    [B^{0.23}, B^{0.25}] to [B^{0.21}, B^{0.31}], unless the gcd blocks are handled better. Two candidate fixes:
    - positivity: drop the coprimality (m, f) = 1 in the squares T_f, then apply three Poisson steps to each T_f
      up to N(f) < √H, which would leave X²H^{−1/2};
    - a pointwise bound X^{0.80} at twist size B^{0.3}.
  - Neither is written. The numerics (Mellin-zero vectors at the null from H = 16 up) show no such gap in the
    truth.

**Second correction, same day: the squarefree support is a real gap, not a technical point [derived].**
- With Gauss-sum weights only squarefree n contribute, since the Gauss sum of an imprimitive character mod p² is 0.
  The step-1 dual is therefore A(h) = Σ_n μ²(n)w(n)χ_n(h): plain sums over squarefree n.
- Möbius over d² | n gives χ_{d²n′}(h) = (h/d)₃·χ_{n′}(h). Each block carries a cubic symbol of conductor d.
- The sketch's "Möbius over d⁶ | n" is the sixth-power-free case, where χ_{d⁶} is invisible. It does not apply here.
- The pair (d, d′) can be treated in three ways:
  - steps 2–3, with step-3 conductor N(d d′)·N(k k′) ≤ N(d d′)³N(h)²/X², so explicit when N(d d′)³ < H;
  - Poisson in h directly after step 1, so explicit when N(d d′) > H;
  - Poisson in one sum only, so explicit when N(d′) > N(d)³.
- **What is left.** Pairs with N(d) ≤ N(d′) ≤ N(d)³ and H^{1/3} ≤ N(d d′) ≤ H.
  - Bounded blockwise by the large sieve (X²/N(d d′) each), their sum is X² log²: no better than the twist large
    sieve.
  - Truncating the Möbius at T and using the sparsity of the tail (‖tail‖² ≈ 1/T) gives at best ≈ X²H^{−1/12}.
- **Consequences.**
  - The single-factor asymptotic is proved by this argument only where X²H^{−1/12} is below the terms kept. Against
    the K-wall's need B^{5/6}H^{1/6}X that is H ≥ (X/B^{5/6})⁴, i.e. H ≥ B^{0.51} (X = B^{0.96}) to B^{0.63}
    (X = B^{0.99}). With the pointwise bound for H ≤ B^{0.21}, a band [B^{0.21}, B^{0.5–0.63}] stays open for a
    single smooth factor too.
  - So "away from the balanced corner, everything the K-wall needs is elementary" (entry "Three Poisson steps give
    the twist mean square ...") is withdrawn. Input A, whose Kubota series carries the squarefree condition as a
    finite combination ψ(a/d, s) (as in DFDH), or a squarefree sieve in the dual with power saving, is needed again
    there.
  - The DFDH comparison of the entry above keeps its reading of the polar shape, which is numerical. It loses its
    claim of an elementary route to DFDH's theorem.
  - The corner's status is unchanged.
- The numerics show nothing of this gap: Mellin-zero vectors sit at the null for every twist range measured. The
  gap is in the method, not in the truth.
