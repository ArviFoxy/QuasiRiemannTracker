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
  | long slope | 5/6 | 0.83280 (−0.064%) |
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
applies as stated: long slope 0.83280, inverse slot cost 1.9882, Λ ≈ 1.987 in both faces, p_max 0.4934, fibre
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
