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
