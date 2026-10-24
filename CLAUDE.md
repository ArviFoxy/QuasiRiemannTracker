# Notes for Claude sessions on this fork

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
- Our submission: `submissions/repeated-marks-20261024` on that branch, θ = 8747289/10⁷ = 0.8747289.
  As of 2026-10-24 that is 4.4e-5 below the best upstream PR (#71, 0.87477290596). It has not been
  opened upstream.
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
- Why the atoms are hard (proved structure, `research/lean-lab/FEGroup.lean`). Counting zeros needs
  positivity, which forces second moments. The two second moments behind the count have affine
  functional-equation groups: C̃₂ (inverse second moment, invariant `s₁+s₂+w`) and D̃₄ (plain fourth
  moment). Only Hecke moves at cubes and sixth powers change the invariant. Affine type is the
  boundary where the classical analogues have only log savings unconditionally. Mixed second
  moments are hyperbolic (worse). Finite-type cross moments are signed and cannot count.
