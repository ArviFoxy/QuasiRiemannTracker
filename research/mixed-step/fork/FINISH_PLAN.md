# Finish plan: an unconditional `nf_step3`, then the PR (revised 2026-10-26, evening)

## Goal and acceptance
- `#print axioms QRH.MixedStep.Graph.nf_step3` and `#print axioms Candidate.bound` give only
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom` or `native_decide` in the package.
- The package `submissions/arvi-mixed-step-20261026` builds with the pinned toolchain, the canonical wrapper
  (`verifier/challenge.mjs`) accepts it at 437037/500000, and the export fits the hosted budget.
- The PR is opened only after that, and only with Arvi's OK.

A theorem with a hypothesis is not a result. Nothing is submitted until the last item below is proved.

## Where we are
Everything is proved except one hypothesis. `Source/NFStep3.lean` proves `nf_step3` from `PlainTransfer`
(`Downstream/Families.lean:378`). `PlainTransfer` says each label's child energy transfers to plain residual families
only. That is false. Two kinds of terms are missing:

1. **Collisions.** A transferred slot prime `u` divides a plain. The column then contains `u²`, and the transfer's
   factorization of the Gauss sum does not apply.
2. **Seed slots.** The label's seed `L` shares a prime with a transferred slot. The residual then has a smaller seed
   `L' ∣ L`.

What already exists for them:
- `transfer_waist_split` (`Residual/CollisionSplit.lean`): child energy ≤ plain residual + 2·`collisionEnergy`, under
  the seed condition (S).
- `transfer_waist_supplier_column` (`Residual/SupplierWaist.lean`): residual seeds `L' ∣ L`, under no-collision (Col).
- The collision algebra in `Collision/` and `Residual/Collision*`: patterns `(Q, σ)`, the factorization
  `coll_factor_mask`, the square row `coll_row_twist` / `square_twist` (twist `idealRowHom (δ³)`, δ the primary
  generator of the colliding product `D`), the divisor Cauchy–Schwarz `collision_family_energy_div`, and the weight
  bound `collisionWeight_sum` (Σ_D ω(D) ≤ 128^|Q| ∏ hi·M², no `Z^ε`).
- Downstream: per-label seeds are already allowed by `RegularJointSupplier3`.

## The design decision for collision families
A collision family is the plain family of the same piece with two changes:
- the second-layer parent is `P_D := (s.restrict J).shortenPlains D₀ D₁`;
- the dictionary frequency is multiplied by `u₀ := δ³`.

**Why this works.** Collet's dictionary writes every child character as a natural row
`NaturalRow (childCharacter η ray) (u₀ · unit · primeSubsetGenerator E · firstSourceNumerator)`
(`actual_column_dictionary`, `jointFirstFrequency`). The multiplier `u₀` is a parameter of the Cycle61 machinery
(about 425 occurrences); Collet's Source layer fixes it to `1`. A natural row's coefficient is `η(n)·idealRowHom(m⁶z)(n)`,
so `NaturalRow η (z·δ³)` is `NaturalRow η z` twisted by `idealRowHom (δ³)`. That is exactly the collision twist.

Consequences:
- First layer unchanged. The column, label, bin, seed and amplitude are the plain label's, times the weight `ω(D)`.
  So no amplitude comparison and no bin shift.
- Mask unchanged. `idealRowHom (δ³)` vanishes on ideals that share a prime with δ, so the coprimality to `D` needs no
  new mask, and the pin `R = R₀ · columnIdeal` stays as it is.
- Keys unchanged. A key `NonzeroJointSourceLabel left u₀ unit` has the same underlying joint label as at `u₀ = 1`,
  because δ ≠ 0.
- Uniformity. `u₀` enters after `Z`, with `N(u₀) ≤ Z^(3d)`. The LOW parent statements, which fix `η` before their
  constants, are applied with the same `η` and the same finite ray dictionary as before.
- Node: the plain node of the piece. `volume P_D = V_J / N(D)`, so the δ-shift has slack `w = log_Z N(D)`. The node's
  radius at `V_D` exceeds the radius the collision needs by `Z^(3w)`. Plain lengths shrink by `N(D_k)`; padding keeps
  the corners, and the second-layer reference drops by `w`.

**Rejected alternatives, and why.**
- Extended first-layer columns `(C·D², D'·D)`. The twist is `(δ/·)³`, which has order 2. A first-layer label row has
  net exponent `(c + 5d) mod 6 ∈ {1, 5}` for valuations ≤ 2, so no first-layer label carries it. Their existence in
  the source is also unprovable (cancellation in column coefficients).
- Twisting the first-layer `η` by `δ³`. `δ` depends on `Z`, but the LOW parent statements (`UnitFaceSource`) fix `η`
  before their constants.
- A lower collision node. It needs the ledger at `θ > δ`. This is the fallback in Phase 0.

## Phases (in order; Phase 1 and Phase 2 are independent)
**Phase 0. Gates before Lean** (hours).
- 0a. Collision pricing at the plain node. Read the F6 twins' proofs (`InitialRegularToTruncatedMainExceptional(Saving)_mx`,
  `…RemainderOne_mx`). Write the zero, centered/complement and tail terms for a family with parent `P_D`: reference
  `r − w`, the same amplitudes, shift slack `w`, radius factor `Z^(3w)`. Check the resulting inequalities on all 46
  fan steps and grid nodes (`fan_16_1000_cap0.075.json`, `mixed_certs.py`), for every `w ∈ (0, d]`. Output:
  `COLLISION_PRICING.md`, a script, and the exact statement of the collision twin.
  - If the centered term is not paid at the plain node, use a lower collision node `amp = a + δ − w/2`, which gives
    4.5w of room in `9·amp`. That needs the ledger at `θ > δ` (monotone extension plus kernel checks).
  - Last resort: a collision margin in the fan, which means regenerating the certificates at a slightly lower θ.
    This is reported to Arvi before doing it.
- 0b. `u₀` footprint. List every Source-layer and `ForkMx` lemma that fixes `u₀ = 1`: 25 fork files and 39 Collet
  Source-layer files contain the literal, and only those in the closure of `regular_supplier3` and the F6 twins
  matter. For each, record whether `1` is only a type index or is used (`one_ne_zero`, norm `= 1` in key caps).
  Record the budgets that grow by `N(δ³)`: key caps `B`, conductor `ηchar`, the missing-part bounds.

**Phase 1. Full transfer** (our modules; ~1.5–2.5k lines).
- 1a. Ball-energy glue for collisions. `collisionEnergy ≤ K · Σ_(Q,σ) Σ_D ω_Q(D) · N(D) · (twisted family energy at
  radius H/N(D))`, from `colPart_patterns`, `pattern_sum`, `coll_factor_mask`, `coll_row_twist`, `square_row_norm`,
  `collision_family_energy_div` and `divisor_assignments_card` (the pattern of `NoCollisionBall.lean`).
- 1b. The twisted family is a `correctedChildGaussEnergy` of `(s.restrict Q).shortenPlains D₀ D₁` with character
  `twistChar τ (δ³)`, normalized by its own volume. This uses an energy transport as in `transfer_waist_split`, and
  the `N(D)` and `∏_Q P` factors cancel against `ω(D)`.
- 1c. Transfer of `J \ Q` inside the family. The no-collision part is exactly `noColPart (J \ Q)`, so this is
  `collet_main_selected_transfer_ball_nocol`. Residual parent `P_D`. The twist commutes with the ray shift: equal
  heights on supported ideals, as in `RayShift`.
- 1d. Seeds. Combine the supplier waist with the split in one tuple decomposition: first split by the transferred
  slots that carry seed primes, then by collision pattern. Colliding primes coprime to the seed is checked; otherwise
  they are moved into the seed split.
- Output: `full_transfer_label` (no (S), no (Col)) and `pieces_transfer_full` (`Downstream/Families.lean`). Families
  are plain `(k, ξ, seed shape)` and collision `(k, ξ, (Q,σ), D, seed shape)`.

**Phase 2. Thread `u₀` through the LOW/HIGH supply** (mechanical; ~40–60 files).
- `Anchor_mx` gets `u₀ : O` with `u₀ ≠ 0`.
- The pins become the dictionary property at `u₀`: the input character equals the natural row at
  `u₀ · (frequency of column l)` on coprime ideals. They no longer require literal equality with `columnCharacter`.
- `rawKey` and keys are moved to `NonzeroJointSourceLabel left u₀ unit`, and the budgets carry `N(u₀)`.
- Collet's Source-layer lemmas in the closure that fix `u₀ = 1` are forked into `ForkMx` (same names with `_mx`,
  header policy as usual).
- Plain families instantiate `u₀ = 1`. Regression check: `regular_supplier3`, `balanced_of_regular3` and `nf_step3_of`
  rebuild unchanged.

**Phase 3. Collision supplier.** `RegularJointSupplierCol3`: `RegularJointSupplier3` with second-layer parent `P_D` and
`u₀ = δ³`, proved like `regular_supplier3`.
- Second-layer record: the shortened, restricted initial input, with lengths `X_k / N(D_k)` and padded reference
  `Z^(r − w)`.
- Needs the lemma "`shortenPlains` of `initialInput` = `initialInput` of the shortened data, same energies (padding)".
- `InitialGeometry` at the same vnode: `globalFace_downward`, the same slot cell, corners by padding.

**Phase 4. Collision F6 twins.** Zero, complement and tail for collision families at the plain node, with the
statement fixed by Phase 0a: parent `P_D`, `u₀ = δ³`, reference `r − w`, the shift slack as an explicit saving.

**Phase 5. Assembly.**
- `balanced_of_regular3` takes `pieces_transfer_full`.
- `eventual_selected_second` runs once per family, plain and collision. Regular parts are paid by
  `RegularJointSupplier3` and `…Col3` with constants uniform in `D`. Zero, complement and tail are paid by the twins.
- Collision families are summed with Σ_D ω(D) ≤ 128^N · Mmax^(2N).
- `nf_step3` is proved without hypotheses. Then `#print axioms` on `nf_step3` and on `Candidate.bound`.

**Phase 6. Package and PR** (`package/CHECKLIST.md`).
- `package_mixed.py` with the final roots, then `make_submission.py`, which enforces the forbidden-construct gate and
  the header gate.
- Full packaged build, axioms, the canonical wrapper, export size and time.
- A branch from `upstream/main` with only `submissions/arvi-mixed-step-20261026`, and "Local checks" filled in
  `PR_BODY_DRAFT.md`.
- Commits by Arvi <arvi.pub@gmail.com> with the Claude co-author line, no session links. Open the PR on Arvi's OK.

## Risks
| risk | sign | response |
|------|------|----------|
| centered gate for collision families | Phase 0a inequality fails on some fan step | lower collision node (ledger at θ > δ), else fan margin (report first) |
| `u₀ = 1` used essentially | a lemma needs `‖u₀‖ = 1` beyond budgets | put δ³ into the key's numerator budget; if a count genuinely needs it, stop and report the exact lemma |
| seeds among colliding primes | 1d case analysis | treat the colliding seed prime as seed-supplied (seed split first) |
| a statement turns out false | any phase | stop, record the exact statement, inequality and numbers in HANDOFF; never weaken silently |

## Working rules
- I do the work myself; no subagents.
- One Lean process at a time: `/home/user/lean-env/mk_mixed.sh <path>`. Closure builds go through `build/build_roots.py`.
- Commit and push after each green module; the pushed tree never claims a result that is not compiled.
- No `sorry`, `admit`, `axiom` or `native_decide` in finished modules; `#print axioms` on every top theorem.
- Headers: our modules carry no copyright line; `ForkMx` copies carry one holder list (`fork/headers.py`).
- Commits are authored as Arvi <arvi.pub@gmail.com> with the Claude co-author line. No session links or model names in
  files.
- `HANDOFF.md` records every top statement as it lands. The task list mirrors the phases.
