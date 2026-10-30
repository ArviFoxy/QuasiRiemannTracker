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
