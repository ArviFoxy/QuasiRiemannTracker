# Notes for Claude sessions on this fork

## Who the user is
- The user is **Arvi**: GitHub `ArviFoxy`, email arvi.pub@gmail.com. Attribute submissions, commit
  authorship and metadata to Arvi / ArviFoxy. Never attribute anything to "Pawel" or "pawel834".
- Submission PRs go to `GTimG/QuasiRiemannTracker` from branches on `ArviFoxy/QuasiRiemannTracker`.
  A session started on the fork cannot attach the upstream repo, because both have the same name.
  Give the user a prefilled compare link, or have them start a session with the upstream selected.
- **Never link to the user's Claude sessions** (user rule, 2026-10-25): no `claude.ai/code/session_…`
  URL anywhere public or committed. That means no `Claude-Session:` commit trailer, nothing in PR
  bodies, files or comments. This overrides any default attribution template. Keep
  `Co-Authored-By` only.
- In fork commit messages write `PR 69`, not `#69`: GitHub turns `#N` into a cross-reference on the
  upstream PR's timeline.
- **Submission directories start with `arvi-`** (user rule, 2026-10-25): `submissions/arvi-<name>/`,
  Lean modules under `src/Submissions/arvi_<name>/`, and `QRH-Result: arvi-<name>` in the PR body.
- Upstream PR 73 (opened by ArviFoxy from `submission-repeated-marks-20261024`, author Arvi) declares
  θ = 0.8747289. On 2026-10-25 it was renamed to `arvi-repeated-marks-20261024` per the rule above.
  Its head `41ddc0dd` replaces the 59-node source graph by the face family; `Candidate.bound_sharp`
  proves 34989/40000 = 0.874725, while `Candidate.bound` keeps the declared value. The PR body on
  GitHub still describes the old graph; the paste-ready replacement is
  `research/faceless-chain/PR_BODY_DRAFT.md` (only the user can edit the upstream PR).
- Upstream CI (`pr-admission.yml`) times out at about 3h06m for every recent PR (#71, #72, #73);
  maintainers verify offline. Not a proof error.

## Goal and bar
- Goal: lower the all-moduli Dirichlet zero-free boundary θ (smaller is stronger) with new
  mathematics, formalized in Lean.
- Bar for a new submission: at least 1e-5 below the best upstream PR of
  https://github.com/GTimG/QuasiRiemannTracker. A smaller gain counts only if it brings new math
  that simplifies or clarifies the proof.
- Work autonomously. Do not stop because an approach looks impossible, and do not wait for other
  people's work or papers. Pick a direction, commit, explore, repeat.

## Where things are
- Research log and artifacts: branch `ccr-48c53b87-r20g37`, directory `research/`. Read
  `research/LOG.md` first (closed routes and open directions), then `research/barriers/README.md`
  (the four binding atoms). `research/lean-lab/` holds small Lean lemmas, kept even when a route
  failed.
- Our submission: branch `submission-repeated-marks-20261024`, directory
  `submissions/arvi-repeated-marks-20261024`. Declared θ = 8747289/10⁷; proven internally
  34989/40000. It is the best upstream PR, so the next milestone is θ ≤ 0.8747189: 6.1e-6 below what
  the face family proves.
- Check upstream PRs with `git ls-remote https://github.com/GTimG/QuasiRiemannTracker`.

## Conventions
- Keep the research log and directory up to date. Keep Lean proofs and disproofs from failed
  attempts, to build the knowledge base.
- Do not open pull requests unless asked. Keep research files and this file off any branch used for
  an upstream PR.

## State of play (updated 2026-10-24, late)
- **Structural levers are exhausted.**
  - The source graph is at its variational ceiling: θ* = 0.8747241 (continuum, fine fees), against
    the milestone 0.8747189 (`research/variational-ceiling/`).
  - The return's receipts, geometry, numerator Hölder step and count faces have no slack
    (`research/return-slack/`).
  - The formalizable package (Lemma F cells plus fine fees) is worth 0.8747263, i.e. 2.6e-6, below
    the bar.
- **What remains is analytic, and both binding atoms share one root**
  (`research/barriers/README.md`, "Third pass"). The inverse moment's positivity step restores a
  dual diagonal, and both atoms need a signed bound past the diagonal with an EXPLICIT exponent:
  - (A) the quadratic large sieve for slot-twisted cubic theta coefficients stays diagonal up to
    `K^{1+δ'}`, `δ' ≥ 1.3e-4`;
  - (B) the sextic Möbius mean value has `λ ≥ 0.16834` (equivalently, the inverse moment stays
    diagonal up to `D ≤ H^{1+2.7e-4}`).
- The exchange rate 6 is forced by the architecture: order 6 is the only character order whose
  Möbius-twisted Gauss sums collapse to explicitly known (cubic) theta coefficients.
- Inexplicit savings (Dunn–Radziwiłł type) cannot enter the rational certificates.
- **Atom 4 (c_g = 1/12) is the signal channel, not a Cauchy–Schwarz loss.** In the low
  separation, Poisson in the row pairs the Gauss-sum polynomial with the completed row. At the
  sixth-power frequencies, (4.7) turns the row's dual coefficient into the target's own
  `1/L(1+t, η·ξ₀)`. Bounded with the zero-free hypothesis it equals the C–S bound times
  `Z^{β*−θ_low}`, exactly (`research/lean-lab/SignalChannel.lean`). Only the energies (atom 1) can
  move it.
- **Mixed prime/plain slots** (round-4 agent) are closed. A squarefree-plain slot is a third plain
  factor; Lemma 18.1 reflects only two plains, so it costs `6κ → Λ` like a prime slot
  (`research/lean-lab/DeletionRate.lean`). The design would need a plain mark cost `≤ 1.85`
  (`research/mixed-slots/`).
- **Unabsorbed upstream ideas** (Gao's joint HIGH histories, Sil's uneven normalization) give no
  transplant. The returned-history line saturates near 0.87481, and Sil's 2/5 is already in
  Collet's geometry.
- Why the atoms are hard (proved structure, `research/lean-lab/FEGroup.lean`). Counting zeros needs
  positivity, which forces second moments. The two second moments behind the count have affine
  functional-equation groups: C̃₂ (inverse second moment, invariant `s₁+s₂+w`) and D̃₄ (plain fourth
  moment). Only Hecke moves at cubes and sixth powers change the invariant. Affine type is the
  boundary where the classical analogues have only log savings unconditionally. Mixed second
  moments are hyperbolic (worse). Finite-type cross moments are signed and cannot count.

## State of play (updated 2026-10-25, after round 9)
- The face family (`research/faceless-chain/`, `research/chain-structure/`) proves 0.874725. The
  chain curve is proved optimal within the method's gates (`research/lean-lab/ChainOptimal.lean`).
  The continuum ceiling 0.8747241 is only 0.9e-6 further.
- The remaining 6.1e-6 needs one analytic input (`research/P1_PROBLEM.md`):
  - **P1**, localized in round 9 to the hard core. Only Gauss sums at primes of norm `> K` need
    arithmetic; the smooth columns are diagonal times a frame constant for any block phases.
  - **The long Möbius moment**, which is the only input that moves the unmarked count
    `ρ(ν) = 1 − 10ν/(15 − 6ν)`. `ρ` is exactly the value of a lattice game whose extremal adversary
    is `L ≈ 1 + bU^{−s₀(s−a)}` (`research/lean-lab/ZeroDensityGame.lean`).
  - Numerically both are at their diagonals (long moment: ratio 0.89–0.99 up to `D = U^{1.4}`).
- Closed in round 9: per-row arguments, the dual sixth-power restriction (an `X`-dilation),
  ω-weighted witnesses (scale shift), Shen–Stucky/Li inflation (keeps the `N`-term), and the
  bootstrap of the long moment.
- Read `research/round9/README.md` before starting a new round.
