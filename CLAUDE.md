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
